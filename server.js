#!/usr/bin/env node

/**
 * Ultimate Browser MCP v4.3 - JavaScript 极速版 (性能优化+bug修复)
 *
 * 特性：
 * - 15层反检测
 * - 快速选择器 (get_by_text/role/placeholder)
 * - 人类化操作 (贝塞尔曲线、自然输入)
 * - iframe 支持
 * - 增强下拉选择
 * - 短超时快速响应
 *
 * v4.3 性能优化+bug修复:
 * - 移除双重消息队列，消除不必要的延迟
 * - 工具列表缓存，避免每次 tools/list 重建60+对象
 * - JSON 输出改用紧凑格式，减少传输开销
 * - connectBrowser 并行注入 stealth 脚本
 * - smart 模式与 human 模式分离 (smart更快更实用)
 * - 修复 snapshot 中 ensurePage() 重复调用
 * - 修复 wait type=time 误用 timeout 参数而非 ms
 * - getValidPages() 就地清理，减少重复 filter
 * - stdin buffer 优化 (indexOf 替代 split)
 *
 * v4.1 修复:
 * - 页面关闭检测与自动清理
 * - eval 安全序列化 + timeout 支持
 * - 滚动方向逻辑 + center 支持
 * - navigate 后清理 frameStack
 * - 类型安全转换
 * - 断开重连状态清理
 * - 修复 press_key/hotkey 在 iframe 中崩溃
 * - 修复 list_tabs 索引与 switch/close_tab 不一致
 * - MCP 工具错误返回格式修正 (isError)
 * - batch/retry 递归深度保护
 * - validatePath 相对路径安全修复
 * - WebGL/Canvas 指纹保护增强
 */

const { chromium } = require('playwright');
const fs = require('fs');
const path = require('path');
const os = require('os');

// ============ 配置 ============
// 超时配置 (可通过环境变量或 set_config 工具调整)
let FAST_TIMEOUT = parseInt(process.env.FAST_TIMEOUT) || 3000;     // 3秒快速超时
let DEFAULT_TIMEOUT = parseInt(process.env.DEFAULT_TIMEOUT) || 5000; // 5秒默认超时
let LONG_TIMEOUT = parseInt(process.env.LONG_TIMEOUT) || 10000;    // 10秒长超时

// 调试配置
let DEBUG_MODE = process.env.DEBUG === '1' || process.env.DEBUG === 'true';

// 请求统计
const requestStats = {
    total: 0,
    success: 0,
    errors: 0,
    totalTime: 0,
    byTool: new Map()
};

// 调试日志
function debug(...args) {
    if (DEBUG_MODE) {
        console.error('[DEBUG]', new Date().toISOString(), ...args);
    }
}

// 记录请求统计
function recordRequest(toolName, duration, success) {
    requestStats.total++;
    requestStats.totalTime += duration;
    if (success) {
        requestStats.success++;
    } else {
        requestStats.errors++;
    }
    
    // 按工具统计
    if (!requestStats.byTool.has(toolName)) {
        requestStats.byTool.set(toolName, { count: 0, totalTime: 0, errors: 0 });
    }
    const toolStats = requestStats.byTool.get(toolName);
    toolStats.count++;
    toolStats.totalTime += duration;
    if (!success) toolStats.errors++;
}

// CDP 端口 (可通过环境变量 CDP_PORT 配置)
const CDP_PORT = process.env.CDP_PORT || 9222;
const CDP_URL = `http://127.0.0.1:${CDP_PORT}`;

// 绕过代理 (重要: 防止本地连接被系统代理拦截)
process.env.NO_PROXY = '127.0.0.1,localhost';
process.env.no_proxy = '127.0.0.1,localhost';

// 跨平台: Mac 用 Meta, Windows/Linux 用 Control
const SELECT_ALL_KEY = os.platform() === 'darwin' ? 'Meta+a' : 'Control+a';

// 预计算 validatePath 允许的目录 (避免每次调用重建 Set + path.resolve)
const DEFAULT_ALLOWED_DIRS_RESOLVED = [...new Set(
    ['/tmp', '/var/tmp', os.tmpdir(), os.homedir()].map(d => path.resolve(d))
)];

// ============ 状态管理 ============
let browser = null;
let browserContext = null;  // 新增: 保存 context 引用
let page = null;
let frameStack = [];
let allPages = [];
let consoleListeners = new Map();  // 追踪 console 监听器

// 环形缓冲区替代 consoleLogs 数组 (O(1) 插入，无 shift 开销)
const CONSOLE_LOG_MAX = 100;
let _clBuf = new Array(CONSOLE_LOG_MAX);
let _clHead = 0;   // 下一个写入位置
let _clCount = 0;  // 当前元素数

function pushConsoleLog(entry) {
    _clBuf[_clHead] = entry;
    _clHead = (_clHead + 1) % CONSOLE_LOG_MAX;
    if (_clCount < CONSOLE_LOG_MAX) _clCount++;
}

function getConsoleLogs(limit) {
    const count = Math.min(limit, _clCount);
    const start = (_clHead - _clCount + CONSOLE_LOG_MAX) % CONSOLE_LOG_MAX;
    const result = [];
    for (let i = _clCount - count; i < _clCount; i++) {
        result.push(_clBuf[(start + i) % CONSOLE_LOG_MAX]);
    }
    return result;
}

function clearConsoleLogs() {
    _clCount = 0;
    _clHead = 0;
}
let contextPageListener = null;  // 追踪 context 的 page 事件监听器
// messageQueue/isProcessing 已移除 — stdin processBuffer 保证串行处理

// ============ 工具函数 ============

// 获取有效页面列表 (清除已关闭的页面，避免重复 filter)
function getValidPages() {
    // 就地清理已关闭的页面
    for (let i = allPages.length - 1; i >= 0; i--) {
        if (allPages[i].isClosed()) {
            removeConsoleListener(allPages[i]);
            allPages.splice(i, 1);
        }
    }
    return allPages;
}

function getCurrentContext() {
    return frameStack.length > 0 ? frameStack[frameStack.length - 1] : page;
}

// 合并 ensurePage + getCurrentContext，减少重复调用
function getPageAndContext() {
    const p = ensurePage();
    const ctx = frameStack.length > 0 ? frameStack[frameStack.length - 1] : p;
    return { page: p, ctx };
}

// ★ 从工具结果中提取精简摘要，让 LLM 不用截图就能理解每步发生了什么
function _extractBrief(tool, result) {
    if (!result || typeof result !== 'object') return undefined;
    switch (tool) {
        case 'click':      return [result.elementText && `"${result.elementText}"`, result.url].filter(Boolean).join(' → ') || 'ok';
        case 'type':        return result.currentValue !== undefined ? `value="${result.currentValue}"` : 'ok';
        case 'fill':        return result.currentValue !== undefined ? `value="${result.currentValue}"` : 'ok';
        case 'navigate':    return `${result.title || ''} (${result.finalUrl || result.navigated || ''})`.slice(0, 120);
        case 'get_page':    return result.url || result.title || result.text?.slice(0, 100) || JSON.stringify(result).slice(0, 100);
        case 'get':         return JSON.stringify(result).slice(0, 150);
        case 'get_text':    return (result.text || '').slice(0, 100);
        case 'eval':        return typeof result.result === 'string' ? result.result.slice(0, 150) : JSON.stringify(result.result).slice(0, 100);
        case 'find':        return `found=${result.found}/${result.total}`;
        case 'check':       return `${result.state}=${result.result}`;
        case 'assert':      return result.passed ? 'passed' : `failed: ${result.message || ''}`.slice(0, 80);
        case 'wait':        return `waited ${result.waited || ''}ms`;
        case 'select':      return result.selected || 'ok';
        case 'status':      return result.connected ? `connected, ${result.tabCount} tabs` : 'disconnected';
        case 'list_tabs':   return `${result.count} tabs`;
        case 'switch_tab':  return `tab ${result.switched}`;
        case 'screenshot':  return 'captured';
        case 'press_key':   return result.pressed || 'ok';
        case 'hotkey':      return result.pressed || 'ok';
        default:            return undefined; // 不认识的工具不附加 brief
    }
}

function isInFrame() {
    return frameStack.length > 0;
}

function randomInt(min, max) {
    return Math.floor(Math.random() * (max - min + 1)) + min;
}

function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

// 安全获取 URL (page.url() 是同步方法)
function safeGetUrl(p, fallback = 'unknown') {
    try {
        return p && !p.isClosed() ? p.url() : fallback;
    } catch (e) {
        return fallback;
    }
}

// 安全获取标题 (page.title() 是异步方法)
async function safeGetTitle(p, fallback = '') {
    try {
        return p && !p.isClosed() ? await p.title() : fallback;
    } catch (e) {
        return fallback;
    }
}

// 确保 page 有效且未关闭
// 注意: 自动重连已移至 handleMessageInternal 中 (tools/call 分支)，
// 在每次工具调用前异步等待重连完成，避免此处同步函数无法等待异步重连的问题
function ensurePage() {
    if (!page) throw new Error('浏览器未连接或无活动页面');
    if (page.isClosed()) {
        // 页面已关闭，尝试切换到其他有效页面
        const validPage = allPages.find(p => !p.isClosed());
        if (validPage) {
            page = validPage;
            frameStack = [];  // 切换页面后清理 iframe 栈
        } else {
            page = null;
            allPages = [];
            frameStack = [];
            throw new Error('所有页面已关闭');
        }
    }
    return page;
}

// 转义选择器中的特殊字符
function escapeSelector(text) {
    return text
        .replace(/\\/g, '\\\\')  // 反斜杠 (必须先处理)
        .replace(/"/g, '\\"')
        .replace(/'/g, "\\'")
        .replace(/\n/g, '\\n')
        .replace(/\r/g, '\\r')
        .replace(/\t/g, '\\t');
}

// 安全路径验证 (防止路径遍历攻击)
function validatePath(inputPath, allowedDirs = ['/tmp', os.tmpdir(), os.homedir()]) {
    if (!inputPath || typeof inputPath !== 'string') {
        return { valid: false, error: '路径为空' };
    }
    
    // 规范化路径
    const normalizedPath = path.resolve(inputPath);
    
    // 检查是否包含路径遍历
    if (inputPath.includes('..')) {
        // 允许在合法目录下使用 ..
        let isAllowed = false;
        for (const dir of allowedDirs) {
            if (normalizedPath.startsWith(path.resolve(dir))) {
                isAllowed = true;
                break;
            }
        }
        if (!isAllowed) {
            return { valid: false, error: '路径包含不允许的遍历', path: normalizedPath };
        }
    }
    
    // 检查规范化后的路径是否在允许的目录下 (使用预计算的目录列表)
    let inAllowedDir = false;
    for (const resolvedDir of DEFAULT_ALLOWED_DIRS_RESOLVED) {
        if (normalizedPath.startsWith(resolvedDir + path.sep) || normalizedPath === resolvedDir) {
            inAllowedDir = true;
            break;
        }
    }

    // 无论原始路径是相对还是绝对，都必须在允许目录下
    if (!inAllowedDir) {
        return { valid: false, error: '路径不在允许的目录中', path: normalizedPath };
    }

    return { valid: true, path: normalizedPath };
}

// 安全 JSON 序列化 (处理循环引用和特殊值)
function safeStringify(obj) {
    const seen = new WeakSet();
    return JSON.stringify(obj, (key, value) => {
        if (value === undefined) return '__undefined__';
        if (value === null) return null;
        if (typeof value === 'function') return '__function__';
        if (typeof value === 'symbol') return value.toString();
        if (typeof value === 'bigint') return value.toString() + 'n';
        if (typeof value === 'object' && value !== null) {
            if (seen.has(value)) return '__circular__';
            seen.add(value);
        }
        return value;
    });
}

// 类型安全的数字转换 (支持整数和浮点，处理 NaN/Infinity)
function toNumber(val, defaultVal, allowFloat = false) {
    if (typeof val === 'number') {
        if (!Number.isFinite(val)) return defaultVal;  // 处理 NaN, Infinity, -Infinity
        return allowFloat ? val : Math.floor(val);
    }
    if (typeof val === 'string') {
        const n = allowFloat ? parseFloat(val) : parseInt(val, 10);
        if (!Number.isFinite(n)) return defaultVal;  // 处理 NaN, Infinity
        return n;
    }
    return defaultVal;
}

// 贝塞尔曲线计算
function bezierCurve(t, p0, p1, p2, p3) {
    const u = 1 - t;
    return u * u * u * p0 + 3 * u * u * t * p1 + 3 * u * t * t * p2 + t * t * t * p3;
}

// 生成人类化鼠标轨迹
function generateHumanPath(startX, startY, endX, endY) {
    const points = [];
    const steps = randomInt(15, 25);
    
    const cp1x = startX + (endX - startX) * 0.3 + randomInt(-50, 50);
    const cp1y = startY + (endY - startY) * 0.1 + randomInt(-30, 30);
    const cp2x = startX + (endX - startX) * 0.7 + randomInt(-50, 50);
    const cp2y = startY + (endY - startY) * 0.9 + randomInt(-30, 30);
    
    for (let i = 0; i <= steps; i++) {
        const t = i / steps;
        const jitterX = randomInt(-2, 2);
        const jitterY = randomInt(-2, 2);
        // 确保坐标不为负数
        const x = Math.max(0, bezierCurve(t, startX, cp1x, cp2x, endX) + jitterX);
        const y = Math.max(0, bezierCurve(t, startY, cp1y, cp2y, endY) + jitterY);
        points.push({ x, y });
    }
    return points;
}

// 添加 console 监听器 (带追踪)
function addConsoleListener(targetPage) {
    // 移除旧监听器
    if (consoleListeners.has(targetPage)) {
        const oldListener = consoleListeners.get(targetPage);
        targetPage.off('console', oldListener);
    }
    
    // 添加新监听器
    const listener = msg => {
        try {
            pushConsoleLog({
                type: msg.type(),
                text: msg.text(),
                timestamp: Date.now()
            });
        } catch (e) {
            pushConsoleLog({ type: 'error', text: '[无法获取消息]', timestamp: Date.now() });
        }
    };
    targetPage.on('console', listener);
    consoleListeners.set(targetPage, listener);
}

// 移除 console 监听器
function removeConsoleListener(targetPage) {
    if (consoleListeners.has(targetPage)) {
        const listener = consoleListeners.get(targetPage);
        targetPage.off('console', listener);
        consoleListeners.delete(targetPage);
    }
}

// 追踪已添加 close 监听器的页面
const closeListeners = new WeakSet();

// 添加 close 监听器 (防重复)
function addCloseListener(targetPage) {
    if (closeListeners.has(targetPage)) return;  // 已添加过
    closeListeners.add(targetPage);
    
    targetPage.on('close', () => {
        const idx = allPages.indexOf(targetPage);
        if (idx >= 0) {
            removeConsoleListener(targetPage);
            allPages.splice(idx, 1);
            if (page === targetPage) {
                page = allPages.find(p => !p.isClosed()) || null;
                frameStack = [];
            }
        }
    });
}

// ============ 15层反检测脚本 ============

const STEALTH_SCRIPT = `
// === 第1层: WebDriver 检测 ===
Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
try { delete navigator.__proto__.webdriver; } catch(e) {}

// === 第2层: 自动化痕迹 ===
const cdcProps = ['cdc_adoQpoasnfa76pfcZLmcfl_Array', 'cdc_adoQpoasnfa76pfcZLmcfl_Promise', 
                  'cdc_adoQpoasnfa76pfcZLmcfl_Symbol'];
cdcProps.forEach(p => { try { delete window[p]; } catch(e) {} });
try { delete document.$cdc_asdjflasutopfhvcZLmcfl_; } catch(e) {}

// === 第3层: Chrome 对象 ===
window.chrome = {
    runtime: {
        connect: () => {},
        sendMessage: () => {},
        onMessage: { addListener: () => {} }
    },
    loadTimes: () => ({
        requestTime: Date.now() / 1000 - Math.random() * 100,
        startLoadTime: Date.now() / 1000 - Math.random() * 50,
        firstPaintTime: Date.now() / 1000 - Math.random() * 10
    }),
    csi: () => ({ pageT: Date.now() }),
    app: { isInstalled: false, InstallState: { INSTALLED: 'installed' } }
};

// === 第4层: Navigator 属性 ===
const navProps = {
    languages: ['zh-CN', 'zh', 'en-US', 'en'],
    platform: navigator.platform || 'MacIntel',
    hardwareConcurrency: navigator.hardwareConcurrency || 8,
    deviceMemory: navigator.deviceMemory || 8,
    maxTouchPoints: 0
};
Object.keys(navProps).forEach(key => {
    try {
        Object.defineProperty(navigator, key, { get: () => navProps[key] });
    } catch(e) {}
});

// === 第5层: Plugins (完整模拟 PluginArray) ===
try {
    const fakePlugins = [
        { name: 'Chrome PDF Plugin', filename: 'internal-pdf-viewer', description: 'Portable Document Format' },
        { name: 'Chrome PDF Viewer', filename: 'mhjfbmdgcfjbbpaeojofohoefgiehjai', description: '' },
        { name: 'Native Client', filename: 'internal-nacl-plugin', description: '' }
    ];
    
    const pluginArray = {
        length: fakePlugins.length,
        item: function(i) { return fakePlugins[i] || null; },
        namedItem: function(n) { return fakePlugins.find(p => p.name === n) || null; },
        refresh: function() {},
        [Symbol.iterator]: function*() { for (const p of fakePlugins) yield p; }
    };
    
    // 添加数字索引访问
    fakePlugins.forEach((p, i) => { pluginArray[i] = p; });
    
    Object.defineProperty(navigator, 'plugins', { get: () => pluginArray });
} catch(e) {}

// === 第6层: WebGL (在原型上修补，覆盖所有实例) ===
try {
    const getParameterProxyHandler = {
        apply: function(target, ctx, args) {
            if (args[0] === 37445) return 'Intel Inc.';
            if (args[0] === 37446) return 'Intel Iris OpenGL Engine';
            return Reflect.apply(target, ctx, args);
        }
    };
    if (WebGLRenderingContext && WebGLRenderingContext.prototype.getParameter) {
        WebGLRenderingContext.prototype.getParameter = new Proxy(
            WebGLRenderingContext.prototype.getParameter, getParameterProxyHandler
        );
    }
    if (typeof WebGL2RenderingContext !== 'undefined' && WebGL2RenderingContext.prototype.getParameter) {
        WebGL2RenderingContext.prototype.getParameter = new Proxy(
            WebGL2RenderingContext.prototype.getParameter, getParameterProxyHandler
        );
    }
} catch(e) {}

// === 第7层: Permissions API ===
try {
    if (navigator.permissions && navigator.permissions.query) {
        const originalQuery = navigator.permissions.query.bind(navigator.permissions);
        navigator.permissions.query = (params) => {
            if (params.name === 'notifications') {
                return Promise.resolve({ state: Notification.permission || 'default' });
            }
            return originalQuery(params);
        };
    }
} catch(e) {}

// === 第8层: Screen 属性 ===
try {
    Object.defineProperty(screen, 'availWidth', { get: () => screen.width });
    Object.defineProperty(screen, 'availHeight', { get: () => screen.height });
    Object.defineProperty(window, 'outerWidth', { get: () => window.innerWidth });
    Object.defineProperty(window, 'outerHeight', { get: () => window.innerHeight + 85 });
} catch(e) {}

// === 第9层: Canvas 指纹噪声 (所有图片格式) ===
try {
    const originalToDataURL = HTMLCanvasElement.prototype.toDataURL;
    HTMLCanvasElement.prototype.toDataURL = function(type) {
        if (this.width > 16 && this.height > 16) {
            try {
                const ctx = this.getContext('2d');
                if (ctx) {
                    const imageData = ctx.getImageData(0, 0, Math.min(10, this.width), Math.min(10, this.height));
                    for (let i = 0; i < imageData.data.length; i += 4) {
                        imageData.data[i] = imageData.data[i] ^ (Math.random() > 0.5 ? 1 : 0);
                    }
                    ctx.putImageData(imageData, 0, 0);
                }
            } catch(e) {}
        }
        return originalToDataURL.apply(this, arguments);
    };
} catch(e) {}

// === 第10层: AudioContext 指纹噪声 ===
try {
    const AC = window.AudioContext || window.webkitAudioContext;
    if (AC) {
        const originalCreateAnalyser = AC.prototype.createAnalyser;
        AC.prototype.createAnalyser = function() {
            const analyser = originalCreateAnalyser.call(this);
            const originalGetFloatFrequencyData = analyser.getFloatFrequencyData.bind(analyser);
            analyser.getFloatFrequencyData = function(array) {
                originalGetFloatFrequencyData(array);
                for (let i = 0; i < array.length; i++) {
                    array[i] += Math.random() * 0.0001;
                }
            };
            return analyser;
        };
    }
} catch(e) {}

// === 第11层: WebRTC 保护 ===
try {
    if (window.RTCPeerConnection) {
        const OriginalRTC = window.RTCPeerConnection;
        window.RTCPeerConnection = function(...args) {
            const pc = new OriginalRTC(...args);
            const origCreateOffer = pc.createOffer.bind(pc);
            pc.createOffer = async function(options) {
                const offer = await origCreateOffer(options);
                if (offer.sdp) {
                    offer.sdp = offer.sdp.replace(/a=candidate.*udp.*\\r\\n/gi, '');
                }
                return offer;
            };
            return pc;
        };
        window.RTCPeerConnection.prototype = OriginalRTC.prototype;
    }
} catch(e) {}

// === 第12层: Battery API ===
try {
    if (navigator.getBattery) {
        navigator.getBattery = () => Promise.resolve({
            charging: true,
            chargingTime: 0,
            dischargingTime: Infinity,
            level: 1.0,
            addEventListener: () => {},
            removeEventListener: () => {}
        });
    }
} catch(e) {}

// === 第13层: Function.toString 伪装 ===
try {
    const originalToString = Function.prototype.toString;
    const nativeFuncs = new Set();
    if (navigator.permissions?.query) nativeFuncs.add(navigator.permissions.query);
    if (navigator.getBattery) nativeFuncs.add(navigator.getBattery);
    if (window.chrome?.loadTimes) nativeFuncs.add(window.chrome.loadTimes);
    
    Function.prototype.toString = function() {
        if (nativeFuncs.has(this)) {
            return 'function ' + (this.name || '') + '() { [native code] }';
        }
        return originalToString.call(this);
    };
} catch(e) {}

// === 第14层: iframe 检测 (修复无限递归) ===
try {
    const iframeContentWindowDesc = Object.getOwnPropertyDescriptor(HTMLIFrameElement.prototype, 'contentWindow');
    if (iframeContentWindowDesc && iframeContentWindowDesc.get) {
        const originalGetter = iframeContentWindowDesc.get;
        Object.defineProperty(HTMLIFrameElement.prototype, 'contentWindow', {
            get: function() {
                const win = originalGetter.call(this);
                if (win && win.navigator) {
                    try {
                        Object.defineProperty(win.navigator, 'webdriver', { 
                            get: () => undefined,
                            configurable: true 
                        });
                    } catch(e) {}
                }
                return win;
            },
            configurable: true
        });
    }
} catch(e) {}

// === 第15层: 清理错误堆栈 ===
try {
    const OriginalError = Error;
    window.Error = function(...args) {
        const error = new OriginalError(...args);
        if (error.stack) {
            error.stack = error.stack.split('\\n').filter(line => 
                !line.includes('playwright') && !line.includes('puppeteer')
            ).join('\\n');
        }
        return error;
    };
    window.Error.prototype = OriginalError.prototype;
    window.Error.captureStackTrace = OriginalError.captureStackTrace;
} catch(e) {}

console.log('[Stealth] 15层反检测已激活 v4.1');
`;

// ============ 快速选择器 ============

function getFastLocator(ctx, selector) {
    if (!ctx) throw new Error('Context 不存在');
    if (!selector || typeof selector !== 'string') {
        throw new Error('selector 参数无效');
    }
    
    // id= 选择器 → #id (快速转换)
    if (selector.startsWith('id=')) {
        const id = selector.slice(3).trim();
        if (!id) throw new Error('id= 选择器内容不能为空');
        // 转义 CSS 特殊字符 (., :, [, ], >, +, ~, #, 空格等)
        const escapedId = id.replace(/([.:\[\]>+~#(){}|^$*=!,/ ])/g, '\\$1');
        return ctx.locator(`#${escapedId}`).first();
    }
    // data-testid= 选择器 → getByTestId (快)
    if (selector.startsWith('data-testid=')) {
        const testId = selector.slice(12).trim();
        if (!testId) throw new Error('data-testid= 选择器内容不能为空');
        return ctx.getByTestId(testId).first();
    }
    // text= 选择器 → getByText (快)
    if (selector.startsWith('text=')) {
        const textContent = selector.slice(5);
        if (!textContent) throw new Error('text= 选择器内容不能为空');
        return ctx.getByText(textContent, { exact: false }).first();
    }
    // placeholder= 选择器 → getByPlaceholder (快)
    if (selector.startsWith('placeholder=')) {
        const placeholder = selector.slice(12);
        if (!placeholder) throw new Error('placeholder= 选择器内容不能为空');
        return ctx.getByPlaceholder(placeholder).first();
    }
    // label= 选择器 → getByLabel (快)
    if (selector.startsWith('label=')) {
        const label = selector.slice(6);
        if (!label) throw new Error('label= 选择器内容不能为空');
        return ctx.getByLabel(label).first();
    }
    // role= 选择器 → getByRole (快)
    if (selector.startsWith('role=')) {
        const parts = selector.slice(5).split('[');
        const role = parts[0].trim();
        if (!role) throw new Error('role= 选择器角色不能为空');
        if (parts.length > 1 && parts[1].includes('name=')) {
            const namePart = parts[1].split('name=')[1];
            if (namePart) {
                const name = namePart.replace(/[\]"']/g, '').trim();
                if (name) {
                    return ctx.getByRole(role, { name }).first();
                }
            }
        }
        return ctx.getByRole(role).first();
    }
    // 普通选择器
    return ctx.locator(selector).first();
}

// 不带 .first() 的版本，用于 count() 等需要匹配所有元素的场景
function getFastLocatorAll(ctx, selector) {
    if (!ctx) throw new Error('Context 不存在');
    if (!selector || typeof selector !== 'string') {
        throw new Error('selector 参数无效');
    }
    if (selector.startsWith('id=')) {
        const id = selector.slice(3).trim();
        if (!id) throw new Error('id= 选择器内容不能为空');
        const escapedId = id.replace(/([.:\[\]>+~#(){}|^$*=!,/ ])/g, '\\$1');
        return ctx.locator(`#${escapedId}`);
    }
    if (selector.startsWith('data-testid=')) {
        return ctx.getByTestId(selector.slice(12).trim());
    }
    if (selector.startsWith('text=')) {
        return ctx.getByText(selector.slice(5), { exact: false });
    }
    if (selector.startsWith('placeholder=')) {
        return ctx.getByPlaceholder(selector.slice(12));
    }
    if (selector.startsWith('label=')) {
        return ctx.getByLabel(selector.slice(6));
    }
    if (selector.startsWith('role=')) {
        const parts = selector.slice(5).split('[');
        const role = parts[0].trim();
        if (parts.length > 1 && parts[1].includes('name=')) {
            const namePart = parts[1].split('name=')[1];
            if (namePart) {
                const name = namePart.replace(/[\]"']/g, '').trim();
                if (name) return ctx.getByRole(role, { name });
            }
        }
        return ctx.getByRole(role);
    }
    return ctx.locator(selector);
}

// ============ 工具实现 ============
// ============ 精简版工具实现 (合并后约60个工具) ============

const tools = {
    // ==================== 系统管理 ====================
    async status() {
        const hasValidPage = !!page && !page.isClosed();
        let connected = false;
        try {
            connected = !!browser && browser.isConnected();
        } catch (e) {
            connected = false;
        }
        let currentUrl = null;
        let title = null;
        if (hasValidPage) {
            currentUrl = safeGetUrl(page);
            title = await safeGetTitle(page);
        }
        return {
            connected,
            hasPage: hasValidPage,
            url: currentUrl,
            title,
            tabCount: getValidPages().length,
            inFrame: isInFrame(),
            frameDepth: frameStack.length
        };
    },

    async get_config() {
        return {
            timeouts: { fast: FAST_TIMEOUT, default: DEFAULT_TIMEOUT, long: LONG_TIMEOUT },
            cdpPort: CDP_PORT,
            debug: DEBUG_MODE,
            inFrame: isInFrame()
        };
    },

    async set_config({ fast_timeout, default_timeout, long_timeout }) {
        const changes = [];
        if (fast_timeout !== undefined) { FAST_TIMEOUT = toNumber(fast_timeout, FAST_TIMEOUT); changes.push('fast_timeout'); }
        if (default_timeout !== undefined) { DEFAULT_TIMEOUT = toNumber(default_timeout, DEFAULT_TIMEOUT); changes.push('default_timeout'); }
        if (long_timeout !== undefined) { LONG_TIMEOUT = toNumber(long_timeout, LONG_TIMEOUT); changes.push('long_timeout'); }
        return { updated: changes.length > 0, changes, current: { fast: FAST_TIMEOUT, default: DEFAULT_TIMEOUT, long: LONG_TIMEOUT } };
    },

    async reconnect() {
        cleanupState();
        const success = await connectBrowser();
        return { reconnected: success, tabCount: getValidPages().length };
    },

    async cleanup() {
        const before = { consoleLogs: _clCount, requestStats: requestStats.total };
        clearConsoleLogs();
        requestStats.total = 0;
        requestStats.success = 0;
        requestStats.errors = 0;
        requestStats.totalTime = 0;
        requestStats.byTool.clear();
        if (global.gc) { try { global.gc(); } catch (e) {} }
        return { cleaned: true, before, after: { consoleLogs: _clCount, requestStats: requestStats.total } };
    },

    async health_check() {
        let browserOk = false;
        try { browserOk = !!browser && browser.isConnected(); } catch (e) {}
        const pageOk = !!page && !page.isClosed();
        return { browser: browserOk, page: pageOk, tabs: getValidPages().length, healthy: browserOk && pageOk };
    },

    async set_debug({ enabled }) {
        DEBUG_MODE = !!enabled;
        return { debug: DEBUG_MODE };
    },

    async request_stats() {
        const toolStats = {};
        for (const [name, stats] of requestStats.byTool) {
            toolStats[name] = { count: stats.count, avgTime: Math.round(stats.totalTime / stats.count), errors: stats.errors };
        }
        return { total: requestStats.total, success: requestStats.success, errors: requestStats.errors, avgTime: requestStats.total > 0 ? Math.round(requestStats.totalTime / requestStats.total) : 0, byTool: toolStats };
    },

    // ==================== 导航 ====================
    async navigate({ url, wait_until = 'load', timeout }) {
        const p = ensurePage();
        frameStack = [];
        await p.goto(url, { waitUntil: wait_until, timeout: toNumber(timeout, LONG_TIMEOUT) });
        const finalUrl = safeGetUrl(p);
        const title = await safeGetTitle(p);
        // ★ 检测是否有登录弹窗/对话框等常见元素
        let hasDialog = false;
        try { hasDialog = await p.locator('[role="dialog"], [class*="modal"], [class*="dialog"], [class*="popup"]').first().isVisible({ timeout: 300 }); } catch {}
        return { navigated: url, finalUrl, title, redirected: finalUrl !== url, hasDialog, inFrame: false };
    },

    async reload({ timeout }) {
        const p = ensurePage();
        frameStack = [];
        await p.reload({ timeout: toNumber(timeout, LONG_TIMEOUT) });
        return { reloaded: true, url: safeGetUrl(p) };
    },

    async go_back() {
        const p = ensurePage();
        frameStack = [];
        await p.goBack();
        return { url: safeGetUrl(p) };
    },

    async go_forward() {
        const p = ensurePage();
        frameStack = [];
        await p.goForward();
        return { url: safeGetUrl(p) };
    },

    async stop_loading() {
        ensurePage();
        const ctx = getCurrentContext();
        if (!ctx) throw new Error('无有效上下文');
        await ctx.evaluate(() => window.stop());
        return { stopped: true };
    },

    // ==================== 统一点击工具 ====================
    async click({ 
        selector, text, x, y,           // 目标：选择器、文本或坐标
        mode = 'fast',                   // 模式：fast, human, smart
        type = 'single',                 // 类型：single, double, triple, right, long
        index,                           // 第N个元素
        if_exists = false,               // 条件点击
        wait_after,                      // 点击后等待：load, networkidle
        scroll_first = false,            // 先滚动到元素
        hover_first,                     // 先悬停另一元素
        timeout,
        duration                         // 长按时长
    }) {
        const { page: p, ctx } = getPageAndContext();
        const to = toNumber(timeout, FAST_TIMEOUT);

        // 确定点击目标
        let locator;
        let clickType = 'selector';

        if (x !== undefined && y !== undefined) {
            // 坐标点击
            clickType = 'coordinate';
        } else if (text) {
            // 文本点击
            locator = ctx.getByText(text, { exact: false });
            if (index !== undefined) {
                locator = locator.nth(toNumber(index, 0));
            } else {
                locator = locator.first();
            }
            clickType = 'text';
        } else if (selector) {
            if (index !== undefined) {
                // 有 index 时，仍通过 getFastLocator 解析选择器类型，但去掉 .first()
                // 对于特殊选择器 (text=, role= 等) 使用对应的快速定位方法
                if (selector.startsWith('text=')) {
                    locator = ctx.getByText(selector.slice(5), { exact: false }).nth(toNumber(index, 0));
                } else if (selector.startsWith('role=')) {
                    const parts = selector.slice(5).split('[');
                    const role = parts[0].trim();
                    locator = ctx.getByRole(role).nth(toNumber(index, 0));
                } else if (selector.startsWith('placeholder=')) {
                    locator = ctx.getByPlaceholder(selector.slice(12)).nth(toNumber(index, 0));
                } else if (selector.startsWith('label=')) {
                    locator = ctx.getByLabel(selector.slice(6)).nth(toNumber(index, 0));
                } else {
                    locator = ctx.locator(selector).nth(toNumber(index, 0));
                }
            } else {
                locator = getFastLocator(ctx, selector);
            }
        } else {
            throw new Error('必须提供 selector、text 或坐标');
        }

        // 条件点击检查
        if (if_exists && clickType !== 'coordinate') {
            try {
                const count = await locator.count();
                if (count === 0) return { clicked: false, reason: '元素不存在' };
            } catch (e) {
                return { clicked: false, reason: e.message };
            }
        }

        // 先悬停
        if (hover_first) {
            const hoverLocator = getFastLocator(ctx, hover_first);
            await hoverLocator.hover({ timeout: to });
            await sleep(randomInt(100, 300));
        }

        // 先滚动
        if (scroll_first && clickType !== 'coordinate') {
            await locator.scrollIntoViewIfNeeded({ timeout: to });
        }

        // 执行点击
        if (clickType === 'coordinate') {
            const cx = toNumber(x, 0);
            const cy = toNumber(y, 0);
            const button = type === 'right' ? 'right' : 'left';
            if (type === 'double') {
                await p.mouse.dblclick(cx, cy, { button });
            } else if (type === 'triple') {
                await p.mouse.click(cx, cy, { button, clickCount: 3 });
            } else if (type === 'long') {
                await p.mouse.move(cx, cy);
                await p.mouse.down({ button });
                await sleep(toNumber(duration, 500));
                await p.mouse.up({ button });
            } else {
                await p.mouse.click(cx, cy, { button });
            }
        } else if (mode === 'smart') {
            // smart 模式：轻微随机偏移 + 直接点击，比 human 快很多但比 fast 更自然
            const box = await locator.boundingBox();
            if (!box) throw new Error('无法获取元素位置');
            const targetX = box.x + box.width / 2 + randomInt(-3, 3);
            const targetY = box.y + box.height / 2 + randomInt(-2, 2);
            // 直接移动到目标附近再点击，不走贝塞尔曲线
            await p.mouse.move(targetX, targetY, { steps: randomInt(2, 5) });
            await sleep(randomInt(10, 40));
            if (type === 'double') {
                await p.mouse.dblclick(targetX, targetY);
            } else if (type === 'triple') {
                await p.mouse.click(targetX, targetY, { clickCount: 3 });
            } else if (type === 'right') {
                await p.mouse.click(targetX, targetY, { button: 'right' });
            } else if (type === 'long') {
                await p.mouse.down();
                await sleep(toNumber(duration, 500));
                await p.mouse.up();
            } else {
                await p.mouse.click(targetX, targetY);
            }
        } else if (mode === 'human') {
            // human 模式：完整贝塞尔曲线模拟
            const box = await locator.boundingBox();
            if (!box) throw new Error('无法获取元素位置');
            const targetX = box.x + box.width / 2 + randomInt(-5, 5);
            const targetY = box.y + box.height / 2 + randomInt(-3, 3);
            const startX = randomInt(100, 300);
            const startY = randomInt(100, 300);
            await p.mouse.move(startX, startY);
            const pathPoints = generateHumanPath(startX, startY, targetX, targetY);
            for (const point of pathPoints) {
                await p.mouse.move(point.x, point.y);
                await sleep(randomInt(5, 15));
            }
            await sleep(randomInt(50, 150));
            if (type === 'double') {
                await p.mouse.dblclick(targetX, targetY);
            } else if (type === 'triple') {
                await p.mouse.click(targetX, targetY, { clickCount: 3 });
            } else if (type === 'right') {
                await p.mouse.click(targetX, targetY, { button: 'right' });
            } else if (type === 'long') {
                await p.mouse.down();
                await sleep(toNumber(duration, 500));
                await p.mouse.up();
            } else {
                await p.mouse.click(targetX, targetY);
            }
        } else {
            // 普通点击
            const clickOptions = { timeout: to };
            if (type === 'right') clickOptions.button = 'right';
            if (type === 'triple') clickOptions.clickCount = 3;
            
            if (type === 'long') {
                const box = await locator.boundingBox();
                if (!box) throw new Error('无法获取元素位置');
                const cx = box.x + box.width / 2;
                const cy = box.y + box.height / 2;
                await p.mouse.move(cx, cy);
                await p.mouse.down();
                await sleep(toNumber(duration, 500));
                await p.mouse.up();
            } else if (type === 'double') {
                await locator.dblclick(clickOptions);
            } else {
                await locator.click(clickOptions);
            }
        }

        // 点击后等待
        if (wait_after) {
            await p.waitForLoadState(wait_after, { timeout: LONG_TIMEOUT });
        }

        // ★ 返回丰富的状态信息，避免 LLM 需要截图判断结果
        const result = { clicked: true, mode, type, inFrame: isInFrame() };
        try {
            const afterUrl = safeGetUrl(p);
            result.url = afterUrl;
            result.title = await safeGetTitle(p);
            // 如果是 locator 点击，获取点击元素的文本
            if (locator) {
                try { result.elementText = (await locator.textContent({ timeout: 500 }))?.trim().slice(0, 100) || ''; } catch {}
            }
        } catch {}
        return result;
    },

    // ==================== 统一输入工具 ====================
    async type({
        selector, label, placeholder, index,  // 目标
        text,
        mode = 'fast',                         // 模式：fast, human, slow
        clear = true,
        press_enter = false,
        if_exists = false,
        delay,
        timeout
    }) {
        const { page: p, ctx } = getPageAndContext();
        if (text === undefined || text === null) text = '';
        const textStr = String(text);
        const to = toNumber(timeout, FAST_TIMEOUT);

        // 确定输入目标
        let locator;
        if (label) {
            locator = ctx.getByLabel(label).first();
        } else if (placeholder) {
            locator = ctx.getByPlaceholder(placeholder).first();
        } else if (index !== undefined) {
            locator = ctx.locator('input:visible, textarea:visible').nth(toNumber(index, 0));
        } else if (selector) {
            locator = getFastLocator(ctx, selector);
        } else {
            throw new Error('必须提供 selector、label、placeholder 或 index');
        }

        // 条件输入检查
        if (if_exists) {
            try {
                const count = await locator.count();
                if (count === 0) return { typed: false, reason: '元素不存在' };
            } catch (e) {
                return { typed: false, reason: e.message };
            }
        }

        // ★ 判断字符是否为"安全"可用 pressSequentially 的字符
        // 字母、数字、空格可以安全用键盘事件输入
        // 特殊字符如 -`~!@#$%^&*()_+=[]{}|;:'",.<>?/\ 需要用 insertText
        const isSafeForKeyboard = (ch) => /^[a-zA-Z0-9 ]$/.test(ch);
        // 输入
        if (mode === 'human') {
            // 人类化输入 (带错误修正) — 自行处理清空，不使用外部 clear 块
            await locator.click({ timeout: to });
            if (clear) {
                await p.keyboard.press(SELECT_ALL_KEY);
                await sleep(randomInt(30, 80));
            }
            for (let i = 0; i < textStr.length; i++) {
                const ch = textStr[i];
                // 偶尔打错字再改正 (仅对安全字符)
                if (isSafeForKeyboard(ch) && Math.random() < 0.03 && i > 0) {
                    const wrongChar = String.fromCharCode(ch.charCodeAt(0) + randomInt(-1, 1));
                    await p.keyboard.insertText(wrongChar);
                    await sleep(randomInt(100, 200));
                    await p.keyboard.press('Backspace');
                    await sleep(randomInt(50, 100));
                }
                // ★ 用 insertText 代替 type，确保所有特殊字符都能正确输入
                await p.keyboard.insertText(ch);
                await sleep(randomInt(50, 150));
                if (Math.random() < 0.1) await sleep(randomInt(100, 300));
            }
        } else if (mode === 'slow') {
            const minDelay = toNumber(delay, 50);
            const maxDelay = minDelay * 3;
            await locator.click({ timeout: to });
            if (clear) {
                await p.keyboard.press(SELECT_ALL_KEY);
                await sleep(50);
            }
            for (const char of textStr) {
                // ★ 用 insertText 代替 type
                await p.keyboard.insertText(char);
                await sleep(randomInt(minDelay, maxDelay));
            }
        } else {
            // ★ 快速输入：优先用 fill (最可靠，支持所有字符)
            // fill 会正确触发 input/change 事件
            // 仅在 fill 失败时 (如 contenteditable) 回退到逐字 insertText
            try {
                if (clear) {
                    await locator.fill(textStr, { timeout: to });
                } else {
                    // 不清空时，先获取当前值再追加
                    const current = await locator.inputValue().catch(() => '');
                    await locator.fill(current + textStr, { timeout: to });
                }
            } catch (fillErr) {
                // fill 失败 (contenteditable 等)，用 insertText 逐字输入
                debug('fill 失败，回退到 insertText:', fillErr.message);
                await locator.click({ timeout: to });
                if (clear) {
                    await p.keyboard.press(SELECT_ALL_KEY);
                }
                await p.keyboard.insertText(textStr);
            }
        }

        if (press_enter) {
            await p.keyboard.press('Enter');
        }

        // ★ 返回输入框的实际值，避免 LLM 需要截图确认
        const result = { typed: true, length: textStr.length, mode, inFrame: isInFrame() };
        try { result.currentValue = await locator.inputValue({ timeout: 500 }); } catch {
            try { result.currentValue = (await locator.textContent({ timeout: 500 }))?.trim().slice(0, 200) || ''; } catch {}
        }
        if (press_enter) {
            try { result.url = safeGetUrl(p); result.title = await safeGetTitle(p); } catch {}
        }
        return result;
    },

    // 快速填充 (直接替换值)
    async fill({ selector, text, timeout }) {
        ensurePage();
        const ctx = getCurrentContext();
        if (!ctx) throw new Error('无有效上下文');
        if (text === undefined || text === null) text = '';
        const locator = getFastLocator(ctx, selector);
        await locator.fill(String(text), { timeout: toNumber(timeout, FAST_TIMEOUT) });
        // ★ 返回实际值确认
        let currentValue;
        try { currentValue = await locator.inputValue({ timeout: 500 }); } catch {}
        return { filled: selector, text: String(text).slice(0, 50), currentValue, inFrame: isInFrame() };
    },

    // 批量填表
    async fill_form({ fields, submit = false }) {
        ensurePage();
        const ctx = getCurrentContext();
        if (!ctx) throw new Error('无有效上下文');
        const results = [];
        for (const [key, value] of Object.entries(fields)) {
            try {
                let locator;
                if (key.startsWith('#') || key.startsWith('.') || key.startsWith('[')) {
                    locator = ctx.locator(key).first();
                } else {
                    locator = ctx.getByLabel(key).first();
                    const count = await locator.count();
                    if (count === 0) locator = ctx.locator(`[name="${escapeSelector(key)}"]`).first();
                }
                await locator.fill(String(value), { timeout: FAST_TIMEOUT });
                results.push({ field: key, success: true });
            } catch (e) {
                results.push({ field: key, success: false, error: e.message });
            }
        }
        if (submit) {
            try {
                const submitBtn = ctx.locator('button[type="submit"], input[type="submit"]').first();
                await submitBtn.click({ timeout: FAST_TIMEOUT });
            } catch (e) {}
        }
        return { filled: results.filter(r => r.success).length, total: results.length, results, inFrame: isInFrame() };
    },

    // ==================== 统一等待工具 ====================
    async wait({
        ms,                              // 固定时间
        type,                            // 类型
        selector, text, pattern, expression,
        state = 'visible',
        timeout
    }) {
        const p = ensurePage();
        const ctx = getCurrentContext();
        const to = toNumber(timeout, DEFAULT_TIMEOUT);

        // 固定时间等待
        if (ms !== undefined) {
            await sleep(toNumber(ms, 1000));
            return { waited: ms };
        }

        if (!type) type = selector ? 'element' : (text ? 'text' : 'time');

        switch (type) {
            case 'element':
                if (!selector) throw new Error('element 类型需要 selector');
                await getFastLocator(ctx, selector).waitFor({ state, timeout: to });
                return { found: true, selector };

            case 'gone':
            case 'hidden':
                if (!selector) throw new Error('gone 类型需要 selector');
                await getFastLocator(ctx, selector).waitFor({ state: 'hidden', timeout: to });
                return { gone: true, selector };

            case 'text':
                if (!text) throw new Error('text 类型需要 text');
                await ctx.getByText(text).first().waitFor({ timeout: to });
                return { found: true, text };

            case 'url':
                if (!pattern) throw new Error('url 类型需要 pattern');
                await p.waitForURL(pattern.includes('*') ? pattern : `**${pattern}**`, { timeout: to });
                return { matched: true, url: safeGetUrl(p) };

            case 'load':
            case 'networkidle':
            case 'domcontentloaded':
                await p.waitForLoadState(type, { timeout: to });
                return { loaded: type };

            case 'network_idle':
                await p.waitForLoadState('networkidle', { timeout: to });
                return { idle: true };

            case 'function':
                if (!expression) throw new Error('function 类型需要 expression');
                await p.waitForFunction(expression, { timeout: to });
                return { condition: true };

            case 'time':
                const waitMs = toNumber(ms, toNumber(timeout, 1000));
                await sleep(waitMs);
                return { waited: waitMs };

            default:
                throw new Error(`未知等待类型: ${type}`);
        }
    },

    // ==================== 统一滚动工具 ====================
    async scroll({
        to,                              // 目标：top, bottom, center, selector
        text,                            // 滚动到文本
        position,                        // 滚动到坐标 {x, y}
        by,                              // 相对滚动 {x, y}
        direction,                       // 方向：up, down, left, right
        amount,                          // 滚动量
        within,                          // 元素内滚动
        load_more = false,               // 滚动加载更多
        max_scrolls = 10
    }) {
        const { page: p, ctx } = getPageAndContext();

        // 滚动加载更多
        if (load_more) {
            let scrollCount = 0;
            let lastHeight = 0;
            for (let i = 0; i < max_scrolls; i++) {
                const height = await ctx.evaluate(() => document.body.scrollHeight);
                if (height === lastHeight) break;
                lastHeight = height;
                await ctx.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
                await sleep(500);  // 从 1000ms 降至 500ms，仍足够大部分加载场景
                scrollCount++;
            }
            return { scrolls: scrollCount };
        }

        // 元素内滚动
        if (within) {
            const locator = getFastLocator(ctx, within);
            const scrollX = by?.x || 0;
            const scrollY = by?.y || 0;
            await locator.evaluate((el, {x, y}) => el.scrollBy(x, y), {x: scrollX, y: scrollY});
            return { scrolled: within, by: {x: scrollX, y: scrollY} };
        }

        // 滚动到特定位置
        if (to === 'top') {
            await ctx.evaluate(() => window.scrollTo(0, 0));
            return { scrolled: 'top' };
        }
        if (to === 'bottom') {
            await ctx.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
            return { scrolled: 'bottom' };
        }
        if (to === 'center') {
            await ctx.evaluate(() => window.scrollTo(0, document.body.scrollHeight / 2));
            return { scrolled: 'center' };
        }
        if (to && to !== 'top' && to !== 'bottom' && to !== 'center') {
            // to 是选择器
            const locator = getFastLocator(ctx, to);
            await locator.scrollIntoViewIfNeeded();
            return { scrolled: to };
        }

        // 滚动到文本
        if (text) {
            const locator = ctx.getByText(text).first();
            await locator.scrollIntoViewIfNeeded();
            return { scrolled: text };
        }

        // 滚动到坐标
        if (position) {
            await ctx.evaluate(({x, y}) => window.scrollTo(x, y), position);
            return { scrolled: position };
        }

        // 相对滚动
        if (by) {
            await ctx.evaluate(({x, y}) => window.scrollBy(x, y), by);
            return { scrolled: by };
        }

        // 方向滚动
        if (direction) {
            const amt = toNumber(amount, 300);
            let dx = 0, dy = 0;
            switch (direction) {
                case 'up': dy = -amt; break;
                case 'down': dy = amt; break;
                case 'left': dx = -amt; break;
                case 'right': dx = amt; break;
            }
            await ctx.evaluate(({x, y}) => window.scrollBy(x, y), {x: dx, y: dy});
            return { scrolled: direction, amount: amt };
        }

        return { scrolled: false };
    },

    // ==================== 统一检查工具 ====================
    async check({
        selector,
        state = 'exists',                // exists, visible, hidden, enabled, disabled, checked, focused, editable, in_viewport
        text,                            // 检查文本
        class_name,                      // 检查类名
        timeout
    }) {
        ensurePage();
        const ctx = getCurrentContext();
        if (!ctx) throw new Error('无有效上下文');
        const to = toNumber(timeout, FAST_TIMEOUT);

        // 检查文本存在
        if (text && !selector) {
            try {
                const count = await ctx.getByText(text).count();
                return { exists: count > 0, text, count };
            } catch (e) {
                return { exists: false, text };
            }
        }

        if (!selector) throw new Error('需要 selector');
        const locator = getFastLocator(ctx, selector);

        // 检查类名
        if (class_name) {
            const classes = await locator.evaluate(el => el.className);
            const hasClass = classes.split(' ').includes(class_name);
            return { has_class: hasClass, class_name, all_classes: classes };
        }

        try {
            switch (state) {
                case 'exists':
                    const count = await locator.count();
                    return { exists: count > 0, count };

                case 'visible':
                    const visible = await locator.isVisible();
                    return { visible };

                case 'hidden':
                    const hidden = await locator.isHidden();
                    return { hidden };

                case 'enabled':
                    const enabled = await locator.isEnabled();
                    return { enabled };

                case 'disabled':
                    const disabled = await locator.isDisabled();
                    return { disabled };

                case 'checked':
                    const checked = await locator.isChecked();
                    return { checked };

                case 'focused':
                    const focused = await locator.evaluate(el => el === document.activeElement);
                    return { focused };

                case 'editable':
                    const editable = await locator.isEditable();
                    return { editable };

                case 'in_viewport':
                    const inViewport = await locator.evaluate(el => {
                        const rect = el.getBoundingClientRect();
                        return rect.top >= 0 && rect.left >= 0 && 
                               rect.bottom <= window.innerHeight && 
                               rect.right <= window.innerWidth;
                    });
                    return { in_viewport: inViewport };

                default:
                    throw new Error(`未知状态: ${state}`);
            }
        } catch (e) {
            return { error: e.message, exists: false };
        }
    },

    // ==================== 统一断言工具 ====================
    async assert({
        type,                            // text, visible, hidden, url, count, element
        selector, text, pattern, expected, operator = '==',
        state,                           // 元素状态
        timeout
    }) {
        const p = ensurePage();
        const ctx = getCurrentContext();
        const to = toNumber(timeout, FAST_TIMEOUT);

        try {
            switch (type) {
                case 'text':
                    if (!text) throw new Error('text 断言需要 text');
                    const textLocator = ctx.getByText(text).first();
                    await textLocator.waitFor({ timeout: to });
                    return { passed: true, type: 'text', text };

                case 'visible':
                    if (!selector) throw new Error('visible 断言需要 selector');
                    await getFastLocator(ctx, selector).waitFor({ state: 'visible', timeout: to });
                    return { passed: true, type: 'visible', selector };

                case 'hidden':
                    if (!selector) throw new Error('hidden 断言需要 selector');
                    await getFastLocator(ctx, selector).waitFor({ state: 'hidden', timeout: to });
                    return { passed: true, type: 'hidden', selector };

                case 'url':
                    if (!pattern) throw new Error('url 断言需要 pattern');
                    const url = safeGetUrl(p);
                    let matched = url.includes(pattern);
                    if (!matched) {
                        try { matched = new RegExp(pattern).test(url); } catch (e) { /* invalid regex, ignore */ }
                    }
                    if (!matched) throw new Error(`URL 不匹配: ${url}`);
                    return { passed: true, type: 'url', url };

                case 'count':
                    if (!selector || expected === undefined) throw new Error('count 断言需要 selector 和 expected');
                    const countLocator = getFastLocatorAll(ctx, selector);
                    const count = await countLocator.count();
                    const exp = toNumber(expected, 0);
                    let countPassed = false;
                    switch (operator) {
                        case '==': countPassed = count === exp; break;
                        case '>': countPassed = count > exp; break;
                        case '>=': countPassed = count >= exp; break;
                        case '<': countPassed = count < exp; break;
                        case '<=': countPassed = count <= exp; break;
                        case '!=': countPassed = count !== exp; break;
                    }
                    if (!countPassed) throw new Error(`元素数量 ${count} 不满足 ${operator} ${expected}`);
                    return { passed: true, type: 'count', count, expected, operator };

                case 'element':
                    if (!selector || !state) throw new Error('element 断言需要 selector 和 state');
                    const checkResult = await tools.check({ selector, state, timeout: to });
                    const passed = checkResult[state] === true;
                    if (!passed) throw new Error(`元素状态 ${state} 断言失败`);
                    return { passed: true, type: 'element', state };

                default:
                    throw new Error(`未知断言类型: ${type}`);
            }
        } catch (e) {
            return { passed: false, type, error: e.message };
        }
    },

    // ==================== 统一获取工具 ====================
    async get({
        type,                            // text, html, attribute, value, position, dimensions, styles, ...
        selector,
        attribute,                       // 属性名
        properties,                      // 样式属性
        outer = false,                   // 外部HTML
        fallback
    }) {
        const { ctx } = getPageAndContext();
        if (!selector) throw new Error('需要 selector');
        const locator = getFastLocator(ctx, selector);

        switch (type) {
            case 'text':
                try {
                    const text = await locator.textContent({ timeout: FAST_TIMEOUT });
                    return { text: text || fallback || '' };
                } catch (e) {
                    return { text: fallback || '', error: e.message };
                }

            case 'html':
                const html = outer 
                    ? await locator.evaluate(el => el.outerHTML)
                    : await locator.evaluate(el => el.innerHTML);
                return { html };

            case 'attribute':
                if (!attribute) throw new Error('需要 attribute');
                const value = await locator.getAttribute(attribute);
                return { [attribute]: value };

            case 'value':
                const inputValue = await locator.inputValue();
                return { value: inputValue };

            case 'position':
            case 'dimensions':
            case 'bounding_box':
                const box = await locator.boundingBox();
                return box || { error: '无法获取边界' };

            case 'styles':
                const styles = await locator.evaluate((el, props) => {
                    const computed = window.getComputedStyle(el);
                    if (props && props.length) {
                        const result = {};
                        props.forEach(p => result[p] = computed.getPropertyValue(p));
                        return result;
                    }
                    return { display: computed.display, color: computed.color, backgroundColor: computed.backgroundColor };
                }, properties || []);
                return { styles };

            case 'count':
                const countAll = await getFastLocatorAll(ctx, selector).count();
                return { count: countAll };

            case 'classes':
                const classes = await locator.evaluate(el => el.className.split(' ').filter(c => c));
                return { classes };

            case 'tag':
                const tag = await locator.evaluate(el => el.tagName.toLowerCase());
                return { tag };

            case 'dataset':
                const dataset = await locator.evaluate(el => ({...el.dataset}));
                return { dataset };

            default:
                // 默认获取全部信息
                const info = await locator.evaluate(el => ({
                    tag: el.tagName.toLowerCase(),
                    id: el.id,
                    classes: el.className,
                    text: el.textContent?.slice(0, 200),
                    value: el.value,
                    href: el.href,
                    src: el.src
                }));
                return info;
        }
    },

    // 获取页面信息
    async get_page({
        type                             // url, title, source, text, metrics
    }) {
        const p = ensurePage();
        const ctx = getCurrentContext();

        if (!type) {
            // 返回完整信息
            return {
                url: safeGetUrl(p),
                title: await safeGetTitle(p),
                viewport: p.viewportSize(),
                inFrame: isInFrame()
            };
        }

        switch (type) {
            case 'url':
                return { url: safeGetUrl(p) };
            case 'title':
                return { title: await safeGetTitle(p) };
            case 'source':
                const source = await ctx.content();
                return { source: source.slice(0, 50000) };
            case 'text':
                const text = await ctx.evaluate(() => document.body.innerText);
                return { text: text.slice(0, 20000) };
            case 'viewport':
                return { viewport: p.viewportSize() };
            default:
                throw new Error(`未知类型: ${type}`);
        }
    },

    // ==================== 标签页管理 ====================
    async new_tab({ url }) {
        if (!browserContext) throw new Error('无浏览器上下文');
        const newPage = await browserContext.newPage();
        allPages.push(newPage);
        page = newPage;
        frameStack = [];
        addConsoleListener(newPage);
        addCloseListener(newPage);
        // context.addInitScript 已覆盖，无需再次 per-page 注入
        if (url) await newPage.goto(url, { timeout: LONG_TIMEOUT });
        const validPages = getValidPages();
        return { created: true, index: validPages.indexOf(newPage), url: safeGetUrl(newPage) };
    },

    async switch_tab({ index }) {
        const validPages = getValidPages();
        const idx = toNumber(index, 0);
        if (idx < 0 || idx >= validPages.length) throw new Error(`无效索引: ${idx}`);
        page = validPages[idx];
        frameStack = [];
        return { switched: idx, url: safeGetUrl(page) };
    },

    async close_tab({ index }) {
        const validPages = getValidPages();
        const idx = index !== undefined ? toNumber(index, validPages.length - 1) : validPages.length - 1;
        if (idx < 0 || idx >= validPages.length) throw new Error(`无效索引: ${idx}`);
        const targetPage = validPages[idx];
        await targetPage.close();
        return { closed: idx, remaining: getValidPages().length };
    },

    async list_tabs() {
        const validPages = getValidPages();
        const tabs = await Promise.all(validPages.map(async (p, i) => ({
            index: i,
            url: safeGetUrl(p),
            title: await safeGetTitle(p),
            active: p === page
        })));
        return { tabs, count: tabs.length };
    },

    // ==================== iframe 管理 ====================
    async enter_frame({ selector, timeout }) {
        ensurePage();
        const ctx = getCurrentContext();
        const locator = getFastLocator(ctx, selector);
        const frameElement = await locator.elementHandle({ timeout: toNumber(timeout, DEFAULT_TIMEOUT) });
        if (!frameElement) throw new Error('找不到 iframe 元素');
        const frame = await frameElement.contentFrame();
        if (!frame) throw new Error('无法进入 iframe');
        frameStack.push(frame);
        return { entered: selector, depth: frameStack.length };
    },

    async exit_frame() {
        if (frameStack.length === 0) return { exited: false, reason: '不在 iframe 中' };
        frameStack.pop();
        return { exited: true, depth: frameStack.length };
    },

    async exit_all_frames() {
        const depth = frameStack.length;
        frameStack = [];
        return { exited: depth };
    },

    async list_frames() {
        const p = ensurePage();
        const frames = p.frames().map((f, i) => ({
            index: i,
            url: f.url(),
            name: f.name()
        }));
        return { frames, current_depth: frameStack.length };
    },

    // ==================== 键盘操作 ====================
    async press_key({ key, modifiers }) {
        const p = ensurePage();  // keyboard 只存在于 Page 对象上，Frame 没有
        let keyCombo = key;
        if (modifiers && modifiers.length) {
            keyCombo = [...modifiers, key].join('+');
        }
        await p.keyboard.press(keyCombo);
        return { pressed: keyCombo };
    },

    async hotkey({ keys }) {
        const p = ensurePage();  // keyboard 只存在于 Page 对象上，Frame 没有
        await p.keyboard.press(keys);
        return { pressed: keys };
    },

    // ==================== 鼠标操作 ====================
    async mouse({ action, x, y, button = 'left', steps }) {
        const p = ensurePage();
        switch (action) {
            case 'move':
                await p.mouse.move(toNumber(x, 0), toNumber(y, 0), { steps: toNumber(steps, 1) });
                return { moved: { x, y } };
            case 'down':
                await p.mouse.down({ button });
                return { down: button };
            case 'up':
                await p.mouse.up({ button });
                return { up: button };
            case 'click':
                await p.mouse.click(toNumber(x, 0), toNumber(y, 0), { button });
                return { clicked: { x, y } };
            default:
                throw new Error(`未知鼠标动作: ${action}`);
        }
    },

    async hover({ selector }) {
        ensurePage();
        const ctx = getCurrentContext();
        const locator = getFastLocator(ctx, selector);
        await locator.hover({ timeout: FAST_TIMEOUT });
        return { hovered: selector };
    },

    async drag({ from_selector, to_selector, from_x, from_y, to_x, to_y, offset_x, offset_y }) {
        const p = ensurePage();
        const ctx = getCurrentContext();
        let startX, startY, endX, endY;

        if (from_selector) {
            const fromLocator = getFastLocator(ctx, from_selector);
            const fromBox = await fromLocator.boundingBox();
            if (!fromBox) throw new Error('找不到起始元素');
            startX = fromBox.x + fromBox.width / 2;
            startY = fromBox.y + fromBox.height / 2;
        } else {
            startX = toNumber(from_x, 0);
            startY = toNumber(from_y, 0);
        }

        if (to_selector) {
            const toLocator = getFastLocator(ctx, to_selector);
            const toBox = await toLocator.boundingBox();
            if (!toBox) throw new Error('找不到目标元素');
            endX = toBox.x + toBox.width / 2;
            endY = toBox.y + toBox.height / 2;
        } else if (offset_x !== undefined || offset_y !== undefined) {
            endX = startX + toNumber(offset_x, 0);
            endY = startY + toNumber(offset_y, 0);
        } else {
            endX = toNumber(to_x, startX);
            endY = toNumber(to_y, startY);
        }

        await p.mouse.move(startX, startY);
        await sleep(randomInt(50, 100));
        await p.mouse.down();
        await sleep(randomInt(50, 100));

        const path = generateHumanPath(startX, startY, endX, endY);
        for (const point of path) {
            await p.mouse.move(point.x, point.y);
            await sleep(randomInt(10, 25));
        }
        await sleep(randomInt(50, 150));
        await p.mouse.up();

        return { dragged: true, from: { x: startX, y: startY }, to: { x: endX, y: endY } };
    },

    // ==================== 截图 ====================
    async screenshot({ path: savePath, fullPage = false, selector }) {
        const p = ensurePage();
        const ctx = getCurrentContext();
        const options = { fullPage };
        
        if (savePath) {
            const validation = validatePath(savePath);
            if (!validation.valid) throw new Error(validation.error);
            options.path = validation.path;
        }

        let buffer;
        if (selector) {
            const locator = getFastLocator(ctx, selector);
            buffer = await locator.screenshot(options);
        } else {
            buffer = await p.screenshot(options);
        }

        if (!savePath) {
            const base64 = buffer.toString('base64');
            return { screenshot: base64.length > 100000 ? base64.slice(0, 100000) + '...(truncated)' : base64, size: buffer.length };
        }
        return { saved: options.path, size: buffer.length };
    },

    // ==================== JavaScript 执行 ====================
    async eval({ script, timeout }) {
        const { ctx } = getPageAndContext();
        const to = toNumber(timeout, LONG_TIMEOUT);
        let timer;
        try {
            const result = await Promise.race([
                ctx.evaluate(script),
                new Promise((_, reject) => { timer = setTimeout(() => reject(new Error(`eval 超时 (${to}ms)`)), to); })
            ]);
            return { result: safeStringify(result) };
        } finally {
            clearTimeout(timer);
        }
    },

    // ==================== Cookie & Storage ====================
    async cookies({ action = 'get', name, value, domain, path: cookiePath, expires, httpOnly, secure }) {
        const ctx = browserContext;
        if (!ctx) throw new Error('无浏览器上下文');

        switch (action) {
            case 'get':
                const cookies = await ctx.cookies();
                if (name) {
                    const filtered = cookies.filter(c => c.name === name);
                    return { cookies: filtered };
                }
                return { cookies };
            case 'set':
                if (!name || !value || !domain) throw new Error('set 需要 name, value, domain');
                const cookie = { name, value, domain, path: cookiePath || '/' };
                if (expires) cookie.expires = expires;
                if (httpOnly !== undefined) cookie.httpOnly = httpOnly;
                if (secure !== undefined) cookie.secure = secure;
                await ctx.addCookies([cookie]);
                return { set: name };
            case 'delete':
                if (!name) throw new Error('delete 需要 name');
                await ctx.clearCookies({ name, domain, path: cookiePath });
                return { deleted: name };
            case 'clear':
                await ctx.clearCookies();
                return { cleared: true };
            default:
                throw new Error(`未知操作: ${action}`);
        }
    },

    async storage({ action = 'get', type = 'local', key, value }) {
        ensurePage();
        const ctx = getCurrentContext();
        if (!ctx) throw new Error('无有效上下文');
        const storageType = type === 'session' ? 'sessionStorage' : 'localStorage';

        switch (action) {
            case 'get':
                if (key) {
                    const val = await ctx.evaluate(({st, k}) => window[st].getItem(k), {st: storageType, k: key});
                    return { [key]: val };
                } else {
                    const all = await ctx.evaluate(st => {
                        const result = {};
                        for (let i = 0; i < window[st].length; i++) {
                            const k = window[st].key(i);
                            result[k] = window[st].getItem(k);
                        }
                        return result;
                    }, storageType);
                    return { storage: all };
                }
            case 'set':
                if (!key) throw new Error('set 需要 key');
                await ctx.evaluate(({st, k, v}) => window[st].setItem(k, v || ''), {st: storageType, k: key, v: value});
                return { set: key };
            case 'remove':
                if (!key) throw new Error('remove 需要 key');
                await ctx.evaluate(({st, k}) => window[st].removeItem(k), {st: storageType, k: key});
                return { removed: key };
            case 'clear':
                await ctx.evaluate(st => window[st].clear(), storageType);
                return { cleared: type };
            default:
                throw new Error(`未知操作: ${action}`);
        }
    },

    // ==================== 表单控件 ====================
    async select({ selector, value, index, text }) {
        ensurePage();
        const ctx = getCurrentContext();
        const locator = getFastLocator(ctx, selector);
        
        if (value !== undefined) {
            await locator.selectOption({ value: String(value) });
            return { selected: value };
        }
        if (index !== undefined) {
            await locator.selectOption({ index: toNumber(index, 0) });
            return { selected: index };
        }
        if (text !== undefined) {
            await locator.selectOption({ label: text });
            return { selected: text };
        }
        throw new Error('需要 value, index 或 text');
    },

    async checkbox({ selector, checked }) {
        ensurePage();
        const ctx = getCurrentContext();
        const locator = getFastLocator(ctx, selector);
        
        if (checked === undefined) {
            // 切换
            const current = await locator.isChecked();
            if (current) await locator.uncheck();
            else await locator.check();
            return { checked: !current };
        } else {
            if (checked) await locator.check();
            else await locator.uncheck();
            return { checked };
        }
    },

    async upload_file({ selector, files }) {
        ensurePage();
        const ctx = getCurrentContext();
        const locator = getFastLocator(ctx, selector);
        const fileList = Array.isArray(files) ? files : [files];
        // 验证所有文件路径
        for (const f of fileList) {
            const validation = validatePath(f);
            if (!validation.valid) throw new Error(`文件路径无效: ${validation.error} (${f})`);
        }
        const validatedFiles = fileList.map(f => validatePath(f).path);
        await locator.setInputFiles(validatedFiles);
        return { uploaded: validatedFiles.length };
    },

    // ==================== 对话框 ====================
    async dialog({ action = 'accept', text }) {
        const p = ensurePage();
        p.once('dialog', async dialog => {
            if (action === 'dismiss') await dialog.dismiss();
            else await dialog.accept(text);
        });
        return { handler: action };
    },

    // ==================== 查找元素 ====================
    async find({ selector, text, attribute, value, tag, limit = 10 }) {
        ensurePage();
        const ctx = getCurrentContext();
        if (!ctx) throw new Error('无有效上下文');
        const max = toNumber(limit, 10);

        let locator;
        if (text) {
            locator = tag ? ctx.locator(tag).filter({ hasText: text }) : ctx.getByText(text);
        } else if (attribute) {
            const escapedValue = value ? value.replace(/\\/g, '\\\\').replace(/"/g, '\\"') : '';
            const attrSelector = value
                ? `${tag || '*'}[${attribute}="${escapedValue}"]`
                : `${tag || '*'}[${attribute}]`;
            locator = ctx.locator(attrSelector);
        } else if (selector) {
            locator = ctx.locator(selector);
        } else {
            throw new Error('需要 selector, text 或 attribute');
        }

        // ★ 用 evaluateAll 一次性批量获取，替代逐元素 evaluate (N次CDP→1次)
        const total = await locator.count();
        const elements = await locator.evaluateAll((els, maxCount) =>
            els.slice(0, maxCount).map((el, i) => ({
                index: i,
                tag: el.tagName.toLowerCase(),
                text: (el.textContent || '').slice(0, 100),
                id: el.id || '',
                class: el.className || ''
            })),
            max
        );

        return { found: elements.length, total, elements };
    },

    // ==================== 辅助工具 ====================
    async highlight({ selector, duration = 2000, color = 'red' }) {
        ensurePage();
        const ctx = getCurrentContext();
        const locator = getFastLocator(ctx, selector);
        // 仅允许安全的 CSS 颜色值 (字母、数字、#、括号、逗号、空格、点、%)
        const safeColor = String(color).replace(/[^a-zA-Z0-9#(),.\s%]/g, '');
        await locator.evaluate((el, {c, d}) => {
            const orig = el.style.outline;
            el.style.outline = `3px solid ${c}`;
            setTimeout(() => el.style.outline = orig, d);
        }, {c: safeColor, d: duration});
        return { highlighted: selector };
    },

    async batch({ actions, _depth = 0 }) {
        if (_depth > 5) throw new Error('batch 递归嵌套过深 (最大 5 层)');
        const results = [];
        for (const action of actions) {
            try {
                if (!tools[action.tool]) throw new Error(`未知工具: ${action.tool}`);
                // 传递递归深度给嵌套的 batch/retry
                const toolArgs = action.args || {};
                if (action.tool === 'batch' || action.tool === 'retry') {
                    toolArgs._depth = _depth + 1;
                }
                const result = await tools[action.tool](toolArgs);
                results.push({ tool: action.tool, success: true, result });
            } catch (e) {
                results.push({ tool: action.tool, success: false, error: e.message });
                if (action.stopOnError) break;
            }
        }
        return { executed: results.length, results };
    },

    async retry({ tool, args = {}, max_retries = 3, delay_ms = 1000, success_check, _depth = 0 }) {
        if (_depth > 5) throw new Error('retry 递归嵌套过深 (最大 5 层)');
        for (let i = 0; i < max_retries; i++) {
            try {
                const toolArgs = { ...args };
                if (tool === 'batch' || tool === 'retry') {
                    toolArgs._depth = _depth + 1;
                }
                const result = await tools[tool](toolArgs);
                if (!success_check || result[success_check]) {
                    return { success: true, attempts: i + 1, result };
                }
            } catch (e) {
                if (i === max_retries - 1) return { success: false, attempts: i + 1, error: e.message };
            }
            await sleep(delay_ms);
        }
        return { success: false, attempts: max_retries };
    },

    // ★ run_steps: 一次往返执行多步操作，内置智能等待和错误重试
    async run_steps({ steps, auto_wait = true, retry_on_fail = true, max_step_retries = 2, step_timeout = 10000, stop_on_error = true, return_intermediate = false }) {
        if (!Array.isArray(steps) || steps.length === 0) throw new Error('steps 必须是非空数组');
        if (steps.length > 50) throw new Error('steps 最多 50 步');

        const BLOCKED_TOOLS = new Set(['run_steps', 'batch', 'retry']); // 禁止嵌套
        const results = [];
        let lastResult = null;
        const totalStart = Date.now();

        for (let i = 0; i < steps.length; i++) {
            const step = steps[i];
            const { tool, args = {}, wait_before, wait_after, optional = false } = step;

            // 校验工具
            if (!tool) { results.push({ step: i, tool: '?', success: false, error: '缺少 tool 字段' }); if (stop_on_error && !optional) break; continue; }
            if (BLOCKED_TOOLS.has(tool)) { results.push({ step: i, tool, success: false, error: `run_steps 内不允许使用 ${tool}` }); if (stop_on_error && !optional) break; continue; }
            if (!tools[tool]) { results.push({ step: i, tool, success: false, error: `未知工具: ${tool}` }); if (stop_on_error && !optional) break; continue; }

            // 步骤前等待
            if (wait_before > 0) await sleep(Math.min(wait_before, 5000));

            // 执行 (带重试)
            const retries = retry_on_fail ? max_step_retries : 1;
            let stepResult = null;
            let stepError = null;
            let attempts = 0;

            for (let r = 0; r < retries; r++) {
                attempts = r + 1;
                try {
                    // 超时保护
                    const to = step.timeout || step_timeout;
                    let timer;
                    stepResult = await Promise.race([
                        tools[tool](args),
                        new Promise((_, rej) => { timer = setTimeout(() => rej(new Error(`步骤 ${i} (${tool}) 超时 ${to}ms`)), to); })
                    ]);
                    clearTimeout(timer);
                    stepError = null;
                    break; // 成功，跳出重试循环
                } catch (e) {
                    stepError = e.message;
                    // 重试前短暂等待
                    if (r < retries - 1) {
                        if (auto_wait) await sleep(500);
                    }
                }
            }

            if (stepError) {
                results.push({ step: i, tool, success: false, error: stepError, attempts });
                if (stop_on_error && !optional) break;
            } else {
                lastResult = stepResult;
                // ★ 自动提取精简状态摘要 — 不需要截图就能知道每步发生了什么
                const brief = _extractBrief(tool, stepResult);
                if (return_intermediate) {
                    results.push({ step: i, tool, success: true, brief, result: stepResult, attempts });
                } else {
                    results.push({ step: i, tool, success: true, brief, attempts });
                }
            }

            // 步骤后等待
            if (wait_after > 0) await sleep(Math.min(wait_after, 5000));
        }

        const totalTime = Date.now() - totalStart;
        const succeeded = results.filter(r => r.success).length;
        const failed = results.filter(r => !r.success).length;

        // ★ 附加最终页面状态（URL + title），省去一次额外的 status/screenshot 调用
        let pageState;
        try {
            const p = ensurePage();
            pageState = { url: safeGetUrl(p), title: await safeGetTitle(p) };
        } catch {}

        return {
            total_steps: steps.length,
            executed: results.length,
            succeeded,
            failed,
            total_time_ms: totalTime,
            steps: results,
            last_result: lastResult,
            page: pageState
        };
    },

    async console_logs({ limit = 50, clear = false }) {
        const total = _clCount;
        const logs = getConsoleLogs(toNumber(limit, 50));
        if (clear) clearConsoleLogs();
        return { logs, total };
    },

    async snapshot() {
        const p = ensurePage();
        const tree = await p.accessibility.snapshot();
        return { snapshot: tree };
    },

    // 兼容性别名
    async get_text({ selector, fallback }) { return tools.get({ type: 'text', selector, fallback }); },
    async get_html({ selector, outer }) { return tools.get({ type: 'html', selector, outer }); },
    async get_attribute({ selector, attribute }) { return tools.get({ type: 'attribute', selector, attribute }); },
    async get_url() { return tools.get_page({ type: 'url' }); },
    async get_title() { return tools.get_page({ type: 'title' }); },
    async exists({ selector, timeout }) { return tools.check({ selector, state: 'exists', timeout }); },
    async is_visible({ selector }) { return tools.check({ selector, state: 'visible' }); },
    async wait_for({ selector, state, timeout }) { return tools.wait({ type: 'element', selector, state, timeout }); },
    async wait_for_text({ text, timeout }) { return tools.wait({ type: 'text', text, timeout }); },
    async get_cookies() { return tools.cookies({ action: 'get' }); },
    async set_cookie(opts) { return tools.cookies({ action: 'set', ...opts }); },
    async clear_cookies() { return tools.cookies({ action: 'clear' }); },
    async get_storage({ key, type }) { return tools.storage({ action: 'get', key, type }); },
    async set_storage({ key, value, type }) { return tools.storage({ action: 'set', key, value, type }); },
    async clear_storage({ type }) { return tools.storage({ action: 'clear', type }); },
    async focus({ selector }) { ensurePage(); const ctx = getCurrentContext(); await getFastLocator(ctx, selector).focus(); return { focused: selector }; },
    async blur({ selector }) { ensurePage(); const ctx = getCurrentContext(); await getFastLocator(ctx, selector).evaluate(el => el.blur()); return { blurred: selector }; },
    async count({ selector }) { ensurePage(); const ctx = getCurrentContext(); const c = await ctx.locator(selector).count(); return { count: c }; },
    async move_mouse({ x, y, steps }) { return tools.mouse({ action: 'move', x, y, steps }); },
    async mouse_down({ button }) { return tools.mouse({ action: 'down', button }); },
    async mouse_up({ button }) { return tools.mouse({ action: 'up', button }); },
    async select_option({ selector, value }) { return tools.select({ selector, value }); },
    async set_checked({ selector, checked }) { return tools.checkbox({ selector, checked }); },
    async toggle_checkbox({ selector }) { return tools.checkbox({ selector }); }
};
// ============ MCP 协议处理 ============

async function connectBrowser() {
    cleanupState();
    
    try {
        browser = await chromium.connectOverCDP(CDP_URL);
        
        // ★ 关键: 阻止 Playwright 在进程退出时关闭浏览器
        // Playwright 内部会注册 exit 钩子调用 browser.close()，这会杀掉用户的 Chrome
        // 我们只是"连接"到已有浏览器，不应该关闭它
        browser.close = async () => {
            console.error('[Ultimate Browser MCP] 拦截 browser.close() — 不关闭用户浏览器，仅断开连接');
            // 不执行任何操作，保持浏览器运行
        };
        
        const contexts = browser.contexts();
        
        if (contexts.length > 0) {
            browserContext = contexts[0];
            
            // ★ 同样阻止 context.close()，防止关闭用户的浏览器上下文
            browserContext.close = async () => {
                console.error('[Ultimate Browser MCP] 拦截 context.close() — 不关闭用户上下文');
            };
            
            const pages = browserContext.pages();

            if (pages.length > 0) {
                page = pages[0];
                allPages = [...pages];

                // ★ context 级注入: 一次注册，所有未来页面/导航自动继承
                try { await browserContext.addInitScript(STEALTH_SCRIPT); } catch (e) {}

                // 对已加载的页面只需 evaluate 注入当前状态 (addInitScript 仅在下次导航生效)
                await Promise.allSettled(allPages.map(async (p) => {
                    if (p.isClosed()) return;
                    addConsoleListener(p);
                    try { await p.evaluate(`(function(){${STEALTH_SCRIPT}})()`); } catch (e) {}
                }));

                contextPageListener = async (newPage) => {
                    if (!allPages.includes(newPage)) {
                        allPages.push(newPage);
                        addConsoleListener(newPage);
                        addCloseListener(newPage);
                        // context.addInitScript 已覆盖未来导航，仅 evaluate 当前页面
                        try { await newPage.evaluate(`(function(){${STEALTH_SCRIPT}})()`); } catch (e) {}
                    }
                };
                browserContext.on('page', contextPageListener);
                
                browser.on('disconnected', () => {
                    console.error('[Ultimate Browser MCP] 浏览器连接断开 (浏览器仍在运行)');
                    cleanupState();
                });
                
                for (const p of allPages) {
                    addCloseListener(p);
                }
                
                console.error('[Ultimate Browser MCP] 连接成功，页面数:', allPages.length, '(已启用浏览器保护)');
                return true;
            }
        }
        
        throw new Error('无可用页面');
    } catch (e) {
        console.error('[Ultimate Browser MCP] 连接失败:', e.message);
        cleanupState();
        return false;
    }
}

function cleanupState() {
    if (browserContext && contextPageListener) {
        try { browserContext.off('page', contextPageListener); } catch (e) {}
    }
    contextPageListener = null;
    
    for (const [p, listener] of consoleListeners) {
        try { p.off('console', listener); } catch (e) {}
    }
    consoleListeners.clear();
    
    browser = null;
    browserContext = null;
    page = null;
    allPages = [];
    frameStack = [];
    clearConsoleLogs();
}

// ============ 精简版工具列表 (约60个) ============
// 缓存工具列表，避免每次 tools/list 调用都重建数组
let _cachedToolsList = null;

function getToolsList() {
    if (_cachedToolsList) return _cachedToolsList;
    _cachedToolsList = [
        // ===== 系统管理 (8个) =====
        { name: 'status', description: '获取浏览器状态', inputSchema: { type: 'object', properties: {} } },
        { name: 'get_config', description: '获取配置', inputSchema: { type: 'object', properties: {} } },
        { name: 'set_config', description: '设置配置', inputSchema: { type: 'object', properties: { fast_timeout: { type: 'number' }, default_timeout: { type: 'number' }, long_timeout: { type: 'number' } } } },
        { name: 'reconnect', description: '重新连接浏览器', inputSchema: { type: 'object', properties: {} } },
        { name: 'cleanup', description: '清理缓存', inputSchema: { type: 'object', properties: {} } },
        { name: 'health_check', description: '健康检查', inputSchema: { type: 'object', properties: {} } },
        { name: 'set_debug', description: '设置调试模式', inputSchema: { type: 'object', properties: { enabled: { type: 'boolean' } }, required: ['enabled'] } },
        { name: 'request_stats', description: '请求统计', inputSchema: { type: 'object', properties: {} } },

        // ===== 导航 (5个) =====
        { name: 'navigate', description: '导航到URL', inputSchema: { type: 'object', properties: { url: { type: 'string' }, wait_until: { type: 'string', enum: ['load', 'domcontentloaded', 'networkidle'] }, timeout: { type: 'number' } }, required: ['url'] } },
        { name: 'reload', description: '刷新页面', inputSchema: { type: 'object', properties: { timeout: { type: 'number' } } } },
        { name: 'go_back', description: '后退', inputSchema: { type: 'object', properties: {} } },
        { name: 'go_forward', description: '前进', inputSchema: { type: 'object', properties: {} } },
        { name: 'stop_loading', description: '停止加载', inputSchema: { type: 'object', properties: {} } },

        // ===== 统一点击 (1个合并工具) =====
        { 
            name: 'click', 
            description: '统一点击 (支持选择器/文本/坐标,single/double/triple/right/long,fast/human/smart模式)', 
            inputSchema: { 
                type: 'object', 
                properties: { 
                    selector: { type: 'string', description: 'CSS选择器' },
                    text: { type: 'string', description: '按文本查找点击' },
                    x: { type: 'number', description: '坐标X' },
                    y: { type: 'number', description: '坐标Y' },
                    mode: { type: 'string', enum: ['fast', 'human', 'smart'], description: '点击模式' },
                    type: { type: 'string', enum: ['single', 'double', 'triple', 'right', 'long'], description: '点击类型' },
                    index: { type: 'number', description: '第N个元素' },
                    if_exists: { type: 'boolean', description: '仅存在时点击' },
                    wait_after: { type: 'string', enum: ['load', 'networkidle'], description: '点击后等待' },
                    scroll_first: { type: 'boolean', description: '先滚动到元素' },
                    hover_first: { type: 'string', description: '先悬停此选择器' },
                    timeout: { type: 'number' },
                    duration: { type: 'number', description: '长按时长(ms)' }
                }
            } 
        },

        // ===== 统一输入 (2个) =====
        { 
            name: 'type', 
            description: '统一输入 (支持选择器/标签/占位符/索引,fast/human/slow模式)', 
            inputSchema: { 
                type: 'object', 
                properties: { 
                    selector: { type: 'string' },
                    label: { type: 'string', description: '按标签查找' },
                    placeholder: { type: 'string', description: '按占位符查找' },
                    index: { type: 'number', description: '按索引' },
                    text: { type: 'string' },
                    mode: { type: 'string', enum: ['fast', 'human', 'slow'] },
                    clear: { type: 'boolean' },
                    press_enter: { type: 'boolean' },
                    if_exists: { type: 'boolean' },
                    delay: { type: 'number' },
                    timeout: { type: 'number' }
                },
                required: ['text']
            } 
        },
        { name: 'fill', description: '快速填充(直接替换)', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, text: { type: 'string' }, timeout: { type: 'number' } }, required: ['selector', 'text'] } },
        { name: 'fill_form', description: '批量填表', inputSchema: { type: 'object', properties: { fields: { type: 'object' }, submit: { type: 'boolean' } }, required: ['fields'] } },

        // ===== 统一等待 (1个合并工具) =====
        { 
            name: 'wait', 
            description: '统一等待 (支持时间/元素/消失/文本/URL/加载/网络空闲/DOM稳定/JS条件)', 
            inputSchema: { 
                type: 'object', 
                properties: { 
                    ms: { type: 'number', description: '等待毫秒' },
                    type: { type: 'string', enum: ['element', 'gone', 'hidden', 'text', 'url', 'load', 'networkidle', 'network_idle', 'domcontentloaded', 'function', 'time'] },
                    selector: { type: 'string' },
                    text: { type: 'string' },
                    pattern: { type: 'string', description: 'URL匹配' },
                    expression: { type: 'string', description: 'JS表达式' },
                    state: { type: 'string', enum: ['visible', 'hidden', 'attached', 'detached'] },
                    timeout: { type: 'number' }
                }
            } 
        },

        // ===== 统一滚动 (1个合并工具) =====
        { 
            name: 'scroll', 
            description: '统一滚动 (支持top/bottom/元素/文本/坐标/相对/方向/加载更多)', 
            inputSchema: { 
                type: 'object', 
                properties: { 
                    to: { type: 'string', description: 'top/bottom/center或选择器' },
                    text: { type: 'string', description: '滚动到文本' },
                    position: { type: 'object', properties: { x: { type: 'number' }, y: { type: 'number' } } },
                    by: { type: 'object', properties: { x: { type: 'number' }, y: { type: 'number' } } },
                    direction: { type: 'string', enum: ['up', 'down', 'left', 'right'] },
                    amount: { type: 'number' },
                    within: { type: 'string', description: '元素内滚动' },
                    load_more: { type: 'boolean' },
                    max_scrolls: { type: 'number' }
                }
            } 
        },

        // ===== 统一检查 (1个合并工具) =====
        { 
            name: 'check', 
            description: '统一检查元素状态 (exists/visible/hidden/enabled/disabled/checked/focused/editable/in_viewport)', 
            inputSchema: { 
                type: 'object', 
                properties: { 
                    selector: { type: 'string' },
                    state: { type: 'string', enum: ['exists', 'visible', 'hidden', 'enabled', 'disabled', 'checked', 'focused', 'editable', 'in_viewport'] },
                    text: { type: 'string', description: '检查文本存在' },
                    class_name: { type: 'string', description: '检查类名' },
                    timeout: { type: 'number' }
                }
            } 
        },

        // ===== 统一断言 (1个合并工具) =====
        { 
            name: 'assert', 
            description: '统一断言 (text/visible/hidden/url/count/element)', 
            inputSchema: { 
                type: 'object', 
                properties: { 
                    type: { type: 'string', enum: ['text', 'visible', 'hidden', 'url', 'count', 'element'] },
                    selector: { type: 'string' },
                    text: { type: 'string' },
                    pattern: { type: 'string' },
                    expected: { type: 'number' },
                    operator: { type: 'string', enum: ['==', '>', '>=', '<', '<=', '!='] },
                    state: { type: 'string' },
                    timeout: { type: 'number' }
                },
                required: ['type']
            } 
        },

        // ===== 统一获取 (2个合并工具) =====
        { 
            name: 'get', 
            description: '统一获取元素信息 (text/html/attribute/value/position/dimensions/styles/count/classes/tag/dataset)', 
            inputSchema: { 
                type: 'object', 
                properties: { 
                    type: { type: 'string', enum: ['text', 'html', 'attribute', 'value', 'position', 'dimensions', 'bounding_box', 'styles', 'count', 'classes', 'tag', 'dataset'] },
                    selector: { type: 'string' },
                    attribute: { type: 'string' },
                    properties: { type: 'array', items: { type: 'string' } },
                    outer: { type: 'boolean' },
                    fallback: { type: 'string' }
                },
                required: ['selector']
            } 
        },
        { 
            name: 'get_page', 
            description: '获取页面信息 (url/title/source/text/viewport)', 
            inputSchema: { 
                type: 'object', 
                properties: { 
                    type: { type: 'string', enum: ['url', 'title', 'source', 'text', 'viewport'] }
                }
            } 
        },

        // ===== 标签页管理 (4个) =====
        { name: 'new_tab', description: '新建标签页', inputSchema: { type: 'object', properties: { url: { type: 'string' } } } },
        { name: 'switch_tab', description: '切换标签页', inputSchema: { type: 'object', properties: { index: { type: 'number' } }, required: ['index'] } },
        { name: 'close_tab', description: '关闭标签页', inputSchema: { type: 'object', properties: { index: { type: 'number' } } } },
        { name: 'list_tabs', description: '列出所有标签页', inputSchema: { type: 'object', properties: {} } },

        // ===== iframe管理 (4个) =====
        { name: 'enter_frame', description: '进入iframe', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, timeout: { type: 'number' } }, required: ['selector'] } },
        { name: 'exit_frame', description: '退出当前iframe', inputSchema: { type: 'object', properties: {} } },
        { name: 'exit_all_frames', description: '退出所有iframe', inputSchema: { type: 'object', properties: {} } },
        { name: 'list_frames', description: '列出所有iframe', inputSchema: { type: 'object', properties: {} } },

        // ===== 键盘鼠标 (5个) =====
        { name: 'press_key', description: '按键', inputSchema: { type: 'object', properties: { key: { type: 'string' }, modifiers: { type: 'array', items: { type: 'string' } } }, required: ['key'] } },
        { name: 'hotkey', description: '组合键', inputSchema: { type: 'object', properties: { keys: { type: 'string' } }, required: ['keys'] } },
        { name: 'mouse', description: '鼠标操作 (move/down/up/click)', inputSchema: { type: 'object', properties: { action: { type: 'string', enum: ['move', 'down', 'up', 'click'] }, x: { type: 'number' }, y: { type: 'number' }, button: { type: 'string', enum: ['left', 'right', 'middle'] }, steps: { type: 'number' } }, required: ['action'] } },
        { name: 'hover', description: '悬停', inputSchema: { type: 'object', properties: { selector: { type: 'string' } }, required: ['selector'] } },
        { name: 'drag', description: '拖拽', inputSchema: { type: 'object', properties: { from_selector: { type: 'string' }, to_selector: { type: 'string' }, from_x: { type: 'number' }, from_y: { type: 'number' }, to_x: { type: 'number' }, to_y: { type: 'number' }, offset_x: { type: 'number' }, offset_y: { type: 'number' } } } },

        // ===== 表单控件 (4个) =====
        { name: 'select', description: '下拉选择', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, value: { type: 'string' }, index: { type: 'number' }, text: { type: 'string' } }, required: ['selector'] } },
        { name: 'checkbox', description: '复选框操作', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, checked: { type: 'boolean' } }, required: ['selector'] } },
        { name: 'upload_file', description: '文件上传', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, files: { oneOf: [{ type: 'string' }, { type: 'array', items: { type: 'string' } }] } }, required: ['selector', 'files'] } },
        { name: 'dialog', description: '对话框处理', inputSchema: { type: 'object', properties: { action: { type: 'string', enum: ['accept', 'dismiss'] }, text: { type: 'string' } } } },

        // ===== Cookie & Storage (2个合并工具) =====
        { name: 'cookies', description: 'Cookie操作 (get/set/delete/clear)', inputSchema: { type: 'object', properties: { action: { type: 'string', enum: ['get', 'set', 'delete', 'clear'] }, name: { type: 'string' }, value: { type: 'string' }, domain: { type: 'string' }, path: { type: 'string' }, expires: { type: 'number' }, httpOnly: { type: 'boolean' }, secure: { type: 'boolean' } } } },
        { name: 'storage', description: 'Storage操作 (get/set/remove/clear)', inputSchema: { type: 'object', properties: { action: { type: 'string', enum: ['get', 'set', 'remove', 'clear'] }, type: { type: 'string', enum: ['local', 'session'] }, key: { type: 'string' }, value: { type: 'string' } } } },

        // ===== 查找元素 (1个合并工具) =====
        { name: 'find', description: '查找元素', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, text: { type: 'string' }, attribute: { type: 'string' }, value: { type: 'string' }, tag: { type: 'string' }, limit: { type: 'number' } } } },

        // ===== 截图 & JS (2个) =====
        { name: 'screenshot', description: '截图', inputSchema: { type: 'object', properties: { path: { type: 'string' }, fullPage: { type: 'boolean' }, selector: { type: 'string' } } } },
        { name: 'eval', description: '执行JavaScript', inputSchema: { type: 'object', properties: { script: { type: 'string' }, timeout: { type: 'number' } }, required: ['script'] } },

        // ===== 辅助工具 (6个) =====
        { name: 'highlight', description: '高亮元素(调试)', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, duration: { type: 'number' }, color: { type: 'string' } }, required: ['selector'] } },
        { name: 'batch', description: '批量执行', inputSchema: { type: 'object', properties: { actions: { type: 'array', items: { type: 'object', properties: { tool: { type: 'string' }, args: { type: 'object' }, stopOnError: { type: 'boolean' } }, required: ['tool'] } } }, required: ['actions'] } },
        { name: 'retry', description: '自动重试', inputSchema: { type: 'object', properties: { tool: { type: 'string' }, args: { type: 'object' }, max_retries: { type: 'number' }, delay_ms: { type: 'number' }, success_check: { type: 'string' } }, required: ['tool'] } },
        { name: 'run_steps', description: '智能多步执行 - 一次调用执行多个操作步骤，内置自动等待和错误重试。适合登录、表单填写等多步流程，比逐步调用快10倍', inputSchema: { type: 'object', properties: { steps: { type: 'array', description: '操作步骤数组，按顺序执行', items: { type: 'object', properties: { tool: { type: 'string', description: '工具名(click/type/fill/navigate/scroll/wait/eval/screenshot等)' }, args: { type: 'object', description: '工具参数' }, wait_before: { type: 'number', description: '步骤前等待ms' }, wait_after: { type: 'number', description: '步骤后等待ms' }, optional: { type: 'boolean', description: '失败时是否继续(默认false)' }, timeout: { type: 'number', description: '此步骤超时ms' } }, required: ['tool'] } }, auto_wait: { type: 'boolean', description: '自动等待元素就绪(默认true)' }, retry_on_fail: { type: 'boolean', description: '失败自动重试(默认true)' }, max_step_retries: { type: 'number', description: '每步最大重试次数(默认2)' }, step_timeout: { type: 'number', description: '每步默认超时ms(默认10000)' }, stop_on_error: { type: 'boolean', description: '遇错停止(默认true)' }, return_intermediate: { type: 'boolean', description: '返回中间步骤结果(默认false)' } }, required: ['steps'] } },
        { name: 'console_logs', description: '控制台日志', inputSchema: { type: 'object', properties: { limit: { type: 'number' }, clear: { type: 'boolean' } } } },
        { name: 'snapshot', description: '获取可访问性树', inputSchema: { type: 'object', properties: {} } },
        { name: 'focus', description: '聚焦元素', inputSchema: { type: 'object', properties: { selector: { type: 'string' } }, required: ['selector'] } },
        { name: 'blur', description: '失焦元素', inputSchema: { type: 'object', properties: { selector: { type: 'string' } }, required: ['selector'] } },
        { name: 'count', description: '元素计数', inputSchema: { type: 'object', properties: { selector: { type: 'string' } }, required: ['selector'] } },

        // ===== 兼容性别名 (保持向后兼容) =====
        { name: 'get_text', description: '获取文本(别名)', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, fallback: { type: 'string' } }, required: ['selector'] } },
        { name: 'get_html', description: '获取HTML(别名)', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, outer: { type: 'boolean' } }, required: ['selector'] } },
        { name: 'get_attribute', description: '获取属性(别名)', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, attribute: { type: 'string' } }, required: ['selector', 'attribute'] } },
        { name: 'get_url', description: '获取URL(别名)', inputSchema: { type: 'object', properties: {} } },
        { name: 'get_title', description: '获取标题(别名)', inputSchema: { type: 'object', properties: {} } },
        { name: 'exists', description: '检查存在(别名)', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, timeout: { type: 'number' } }, required: ['selector'] } },
        { name: 'is_visible', description: '检查可见(别名)', inputSchema: { type: 'object', properties: { selector: { type: 'string' } }, required: ['selector'] } },
        { name: 'wait_for', description: '等待元素(别名)', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, state: { type: 'string' }, timeout: { type: 'number' } }, required: ['selector'] } },
        { name: 'wait_for_text', description: '等待文本(别名)', inputSchema: { type: 'object', properties: { text: { type: 'string' }, timeout: { type: 'number' } }, required: ['text'] } },
        { name: 'get_cookies', description: '获取Cookies(别名)', inputSchema: { type: 'object', properties: {} } },
        { name: 'set_cookie', description: '设置Cookie(别名)', inputSchema: { type: 'object', properties: { name: { type: 'string' }, value: { type: 'string' }, domain: { type: 'string' } }, required: ['name', 'value', 'domain'] } },
        { name: 'clear_cookies', description: '清除Cookies(别名)', inputSchema: { type: 'object', properties: {} } },
        { name: 'get_storage', description: '获取Storage(别名)', inputSchema: { type: 'object', properties: { key: { type: 'string' }, type: { type: 'string', enum: ['local', 'session'] } } } },
        { name: 'set_storage', description: '设置Storage(别名)', inputSchema: { type: 'object', properties: { key: { type: 'string' }, value: { type: 'string' }, type: { type: 'string', enum: ['local', 'session'] } }, required: ['key'] } },
        { name: 'clear_storage', description: '清除Storage(别名)', inputSchema: { type: 'object', properties: { type: { type: 'string', enum: ['local', 'session'] } } } },
        { name: 'move_mouse', description: '移动鼠标(别名)', inputSchema: { type: 'object', properties: { x: { type: 'number' }, y: { type: 'number' }, steps: { type: 'number' } }, required: ['x', 'y'] } },
        { name: 'mouse_down', description: '鼠标按下(别名)', inputSchema: { type: 'object', properties: { button: { type: 'string', enum: ['left', 'right', 'middle'] } } } },
        { name: 'mouse_up', description: '鼠标释放(别名)', inputSchema: { type: 'object', properties: { button: { type: 'string', enum: ['left', 'right', 'middle'] } } } },
        { name: 'select_option', description: '选择选项(别名)', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, value: { type: 'string' } }, required: ['selector', 'value'] } },
        { name: 'set_checked', description: '设置勾选(别名)', inputSchema: { type: 'object', properties: { selector: { type: 'string' }, checked: { type: 'boolean' } }, required: ['selector'] } },
        { name: 'toggle_checkbox', description: '切换复选框(别名)', inputSchema: { type: 'object', properties: { selector: { type: 'string' } }, required: ['selector'] } }
    ];
    return _cachedToolsList;
}

// MCP 消息处理 (直接处理，不再经过多余的消息队列)
async function handleMessageInternal(message) {
    const { method, params, id } = message;
    
    switch (method) {
        case 'initialize':
            const connected = await connectBrowser();
            return {
                jsonrpc: '2.0',
                id,
                result: {
                    protocolVersion: '2024-11-05',
                    capabilities: { tools: {} },
                    serverInfo: { name: 'ultimate-browser', version: '4.3.0' }
                }
            };
        
        case 'notifications/initialized':
            return null;
        
        case 'tools/list':
            return {
                jsonrpc: '2.0',
                id,
                result: { tools: getToolsList() }
            };
        
        case 'tools/call':
            const { name, arguments: args } = params;
            const startTime = Date.now();
            const idJson = JSON.stringify(id);

            // ★ 先校验工具名（快速失败，避免触发不必要的重连）
            if (!tools[name]) {
                return `{"jsonrpc":"2.0","id":${idJson},"result":{"content":[{"type":"text","text":${JSON.stringify(`错误: 未知工具: ${name}`)}}],"isError":true}}`;
            }

            if (DEBUG_MODE) {
                debug(`调用工具: ${name}`, args ? JSON.stringify(args).slice(0, 100) : '{}');
            }

            if (!browser || !browser.isConnected()) {
                const reconnected = await connectBrowser();
                if (!reconnected) {
                    const errText = `错误: 无法连接到浏览器，请确保 Chrome 已启动并开启调试端口 (--remote-debugging-port=${CDP_PORT})`;
                    return `{"jsonrpc":"2.0","id":${idJson},"result":{"content":[{"type":"text","text":${JSON.stringify(errText)}}],"isError":true}}`;
                }
            }

            try {
                const result = await tools[name](args || {});
                const duration = Date.now() - startTime;

                recordRequest(name, duration, true);
                if (DEBUG_MODE) debug(`工具完成: ${name}, 耗时: ${duration}ms`);

                // ★ 手动拼接响应字符串，避免双重 JSON 序列化
                const resultJson = JSON.stringify(result);
                return `{"jsonrpc":"2.0","id":${idJson},"result":{"content":[{"type":"text","text":${JSON.stringify(resultJson)}}]}}`;
            } catch (toolError) {
                const duration = Date.now() - startTime;
                recordRequest(name, duration, false);
                if (DEBUG_MODE) debug(`工具错误: ${name}, 耗时: ${duration}ms, 错误: ${toolError.message}`);
                const errText = `错误: ${toolError.message}`;
                return `{"jsonrpc":"2.0","id":${idJson},"result":{"content":[{"type":"text","text":${JSON.stringify(errText)}}],"isError":true}}`;
            }
        
        default:
            return {
                jsonrpc: '2.0',
                id,
                error: { code: -32601, message: `未知方法: ${method}` }
            };
    }
}

// 直接处理消息，不再通过队列中转 (stdin 的 processBuffer 已保证串行)
async function handleMessage(message) {
    try {
        return await handleMessageInternal(message);
    } catch (e) {
        return {
            jsonrpc: '2.0',
            id: message.id,
            error: { code: -32000, message: e.message || 'Unknown error' }
        };
    }
}

// 启动服务器
let isShuttingDown = false;

async function gracefulShutdown(signal) {
    if (isShuttingDown) return;
    isShuttingDown = true;

    console.error(`\n[Ultimate Browser MCP] 收到 ${signal}，正在优雅关闭 (不关闭浏览器)...`);

    try {
        // 使用 cleanupState 正确移除所有监听器并清理状态
        cleanupState();
        console.error('[Ultimate Browser MCP] 已断开连接，浏览器保持运行');
    } catch (e) {
        console.error('[Ultimate Browser MCP] 清理出错:', e.message);
    }

    process.exit(0);
}

process.on('SIGINT', () => gracefulShutdown('SIGINT'));
process.on('SIGTERM', () => gracefulShutdown('SIGTERM'));
process.on('uncaughtException', (err) => {
    console.error('[Ultimate Browser MCP] 未捕获异常:', err.message);
    if (!isShuttingDown) gracefulShutdown('uncaughtException');
});
process.on('unhandledRejection', (reason) => {
    console.error('[Ultimate Browser MCP] 未处理的 Promise 拒绝:', reason);
});

async function main() {
    console.error('[Ultimate Browser MCP v4.3] 启动中... (性能优化版 - 约60个工具)');

    let buffer = '';
    let stdinProcessing = false;
    let stdinEnded = false;
    let processingPromise = null;

    async function processBuffer() {
        if (stdinProcessing) return;
        stdinProcessing = true;

        try {
            while (true) {
                // 快速查找换行符位置，避免 split 整个 buffer
                const nlIdx = buffer.indexOf('\n');
                if (nlIdx === -1) break;

                const line = buffer.slice(0, nlIdx);
                buffer = buffer.slice(nlIdx + 1);

                if (!line.trim()) continue;

                try {
                    const message = JSON.parse(line);
                    const response = await handleMessage(message);

                    if (response) {
                        // 响应可能是预构建的字符串(tools/call热路径)或对象
                        if (typeof response === 'string') {
                            process.stdout.write(response + '\n');
                        } else {
                            process.stdout.write(JSON.stringify(response) + '\n');
                        }
                    }
                } catch (e) {
                    console.error('解析错误:', e.message);
                    process.stdout.write(JSON.stringify({
                        jsonrpc: '2.0',
                        id: null,
                        error: { code: -32700, message: 'JSON 解析错误: ' + e.message }
                    }) + '\n');
                }
            }
        } finally {
            stdinProcessing = false;
            // stdin 已关闭且所有消息已处理完 → 安全退出
            if (stdinEnded) {
                console.error('[Ultimate Browser MCP] 结束');
                process.exit(0);
            }
        }
    }

    process.stdin.setEncoding('utf8');
    process.stdin.on('data', (chunk) => {
        buffer += chunk;
        processingPromise = processBuffer();
    });

    process.stdin.on('end', async () => {
        stdinEnded = true;
        // 如果 processBuffer 正在运行，等它处理完所有消息后在 finally 中退出
        // 如果 processBuffer 已完成，直接处理剩余 buffer 再退出
        if (!stdinProcessing) {
            if (buffer.trim()) {
                await processBuffer();
            } else {
                console.error('[Ultimate Browser MCP] 结束');
                process.exit(0);
            }
        }
    });
}

main();
