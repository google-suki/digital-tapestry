/**
 * ChromaMosaic - Core Application Logic (High-Performance Structural Edition)
 * Programmatic pixelated video mosaic renderer utilizing a dynamic grid of dual-color tiles
 * or retro pixel glyph sprites with dual-color matching, rotation, and mirroring.
 * Super-optimized search using color pair segment filtering, running at 60-120 FPS.
 * High-fidelity color matching in Perceptual LAB space and RGB Euclidean space.
 */

// Configuration & State
let stream = null;
let animationFrameId = null;
let isPaused = false;
let currentCameraId = '';
let matchingMethod = 'lab'; // 'lab' or 'rgb'
let tileSize = 16; // Size of each mosaic block in pixels
let blendFactor = 0; // 0.0 to 1.0 (overlay factor for original video)
let flickerCooldownMs = 0; // Default: 0ms (no temporal cooldown stability)

// Force Linear Transition State
let forceLinearHorizontal = false;
let forceLinearVertical = false;
let forceLinearDiagonal = false;

// Traverse Lag (motion-blur catch-up delay) State
let traverseLagMs = 0;

// Temporal matching cache to reduce high-frequency noise/flicker
const lastMatches = new Array(200 * 150).fill(null);
const lastMatchTimes = new Float64Array(200 * 150);
const lastTransitionTimes = new Float64Array(200 * 150);

function resetMatchHistory() {
    lastMatches.fill(null);
    lastMatchTimes.fill(0);
    lastTransitionTimes.fill(0);
}


// Style Selection State
let tileStyle = 'geometric'; // 'geometric' (concentric squares), 'sprites' (retro pixel glyphs), or 'custom' (uploaded image slices)
let customImageElement = null;
let customImageCols = 8;
let customImageRows = 8;
let customSlices = [];

// Procedural Pattern Simulation State
let inputSource = 'webcam'; // 'webcam' or 'procedural'
let patternType = 'plasma'; // 'plasma', 'spiral', 'ripple', 'mandala'
let patternSpeed = 1.0;
let patternScale = 1.0;
let patternColorMode = 'custom'; // 'custom', 'rainbow', 'fire', 'ocean'
let rippleCenter = { x: 0.5, y: 0.5 }; // Click or hover normalized coordinate

// Color Channel Customizations (Dynamic hex properties mapped to CSS variables)
const currentColors = {
    blue: '#0072e3',
    green: '#00cc00',
    yellow: '#ffd800',
    red: '#eb1414',
    black: '#000000',
    white: '#ffffff'
};

// Dynamic CSS Variable Prefixes for Color Channels to avoid name collisions (e.g., blue vs black)
const CSS_PREFIX = {
    blue: 'b',
    green: 'g',
    yellow: 'y',
    red: 'r',
    black: 'bk',
    white: 'w'
};

// Theme Presets mapping channel colors
const PRESET_THEMES = {
    original: {
        blue: '#0072e3',
        green: '#00cc00',
        yellow: '#ffd800',
        red: '#eb1414',
        black: '#000000',
        white: '#ffffff'
    },
    cyberpunk: {
        blue: '#00f0ff',
        green: '#00ff66',
        yellow: '#ff00ff',
        red: '#ff0055',
        black: '#0a0b10',
        white: '#ffffff'
    },
    forest: {
        blue: '#1b4332',
        green: '#40916c',
        yellow: '#d8f3dc',
        red: '#b7094c',
        black: '#081c15',
        white: '#f4f9f4'
    },
    sunset: {
        blue: '#3d348b',
        green: '#f7b801',
        yellow: '#f18701',
        red: '#f35b04',
        black: '#180f2b',
        white: '#fffdf9'
    },
    monochrome: {
        blue: '#111827',
        green: '#4b5563',
        yellow: '#d1d5db',
        red: '#f9fafb',
        black: '#000000',
        white: '#ffffff'
    }
};

// 14 Unique pairs corresponding to columns (0 to 13)
// Rows represent concentric transitions between Background (A) and Foreground (B)
const COLOR_PAIRS = [
    // 6 original color pairings
    { A: 'blue', B: 'green', name: 'Blue & Green' },
    { A: 'blue', B: 'yellow', name: 'Blue & Yellow' },
    { A: 'blue', B: 'red', name: 'Blue & Red' },
    { A: 'green', B: 'yellow', name: 'Green & Yellow' },
    { A: 'green', B: 'red', name: 'Green & Red' },
    { A: 'yellow', B: 'red', name: 'Yellow & Red' },
    
    // 4 black color pairings
    { A: 'blue', B: 'black', name: 'Blue & Black' },
    { A: 'green', B: 'black', name: 'Green & Black' },
    { A: 'red', B: 'black', name: 'Red & Black' },
    { A: 'yellow', B: 'black', name: 'Yellow & Black' },
    
    // 4 white color pairings
    { A: 'blue', B: 'white', name: 'Blue & White' },
    { A: 'green', B: 'white', name: 'Green & White' },
    { A: 'red', B: 'white', name: 'Red & White' },
    { A: 'yellow', B: 'white', name: 'Yellow & White' }
];

// Weight definitions of background (A) vs foreground (B) for each row (0 to 5)
const ROW_WEIGHTS = [
    { A: 0.96, B: 0.04 }, // Row 0: Tiny solid square of B inside A
    { A: 0.84, B: 0.16 }, // Row 1: Medium square ring of B inside A
    { A: 0.72, B: 0.28 }, // Row 2: Large square ring of B inside A
    { A: 0.28, B: 0.72 }, // Row 3: Large square ring of A inside B (inverted)
    { A: 0.16, B: 0.84 }, // Row 4: Medium square ring of A inside B (inverted)
    { A: 0.04, B: 0.96 }  // Row 5: Tiny solid square of A inside B (inverted)
];

// Precomputed metadata for the dynamic geometric tiles (84 tiles)
let precomputedTiles = [];

// Precomputed metadata for the 12x8 pre-designed sprite tiles (96 tiles)
let precomputedSpriteTiles = [];

// DOM Elements Cache
const elements = {
    video: document.getElementById('webcam-video'),
    uploadedVideo: document.getElementById('uploaded-video'),
    canvas: document.getElementById('mosaic-canvas'),
    cameraSelect: document.getElementById('select-camera'),
    tileSizeInput: document.getElementById('input-tile-size'),
    tileSizeValue: document.getElementById('tile-size-value'),
    blendFactorInput: document.getElementById('input-blend-factor'),
    blendFactorValue: document.getElementById('blend-factor-value'),
    flickerCooldownInput: document.getElementById('input-flicker-cooldown'),
    flickerCooldownValue: document.getElementById('flicker-cooldown-value'),
    forceLinearHorizontalCheckbox: document.getElementById('force-linear-horizontal'),
    forceLinearVerticalCheckbox: document.getElementById('force-linear-vertical'),
    forceLinearDiagonalCheckbox: document.getElementById('force-linear-diagonal'),
    traverseLagInput: document.getElementById('input-traverse-lag'),
    traverseLagValue: document.getElementById('traverse-lag-value'),

    imageDropZone: document.getElementById('image-drop-zone'),
    gridImageInput: document.getElementById('input-grid-image'),
    gridColsInput: document.getElementById('input-grid-cols'),
    gridRowsInput: document.getElementById('input-grid-rows'),
    referenceGridContainer: document.getElementById('reference-grid-container'),
    toggleReference: document.getElementById('toggle-reference-grid'),
    referenceGridWrapper: document.getElementById('reference-grid-wrapper'),
    fpsDisplay: document.getElementById('fps-display'),
    resolutionDisplay: document.getElementById('resolution-display'),
    toast: document.getElementById('toast-notification')
};

// Dynamic pickers cached on runtime creation
const pickers = {};

// Offscreen Canvas for downsampling frames
const offscreenCanvas = document.createElement('canvas');
const offscreenCtx = offscreenCanvas.getContext('2d', { willReadFrequently: true });
const displayCtx = elements.canvas.getContext('2d');

// Performance / FPS Tracking
let lastFrameTime = performance.now();
let frameCount = 0;
let fps = 30;

/**
 * Convert hexadecimal color to RGB object
 */
function hexToRgb(hex) {
    const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
    return result ? {
        r: parseInt(result[1], 16),
        g: parseInt(result[2], 16),
        b: parseInt(result[3], 16)
    } : { r: 0, g: 0, b: 0 };
}

/**
 * Convert RGB values to LAB Color Space (Standard D65 Reference)
 * Perceptually uniform space for optimal color matching distances
 */
function rgbToLab(r, g, b) {
    let rL = r / 255;
    let gL = g / 255;
    let bL = b / 255;

    rL = (rL > 0.04045) ? Math.pow((rL + 0.055) / 1.055, 2.4) : (rL / 12.92);
    gL = (gL > 0.04045) ? Math.pow((gL + 0.055) / 1.055, 2.4) : (gL / 12.92);
    bL = (bL > 0.04045) ? Math.pow((bL + 0.055) / 1.055, 2.4) : (bL / 12.92);

    rL *= 100;
    gL *= 100;
    bL *= 100;

    const x = rL * 0.4124 + gL * 0.3576 + bL * 0.1805;
    const y = rL * 0.2126 + gL * 0.7152 + bL * 0.0722;
    const z = rL * 0.0193 + gL * 0.1192 + bL * 0.9505;

    const xN = x / 95.047;
    const yN = y / 100.000;
    const zN = z / 108.883;

    const fx = (xN > 0.008856) ? Math.pow(xN, 1/3) : (7.787 * xN) + (16 / 116);
    const fy = (yN > 0.008856) ? Math.pow(yN, 1/3) : (7.787 * yN) + (16 / 116);
    const fz = (zN > 0.008856) ? Math.pow(zN, 1/3) : (7.787 * zN) + (16 / 116);

    const l = (116 * fy) - 16;
    const a = 500 * (fx - fy);
    const lB = 200 * (fy - fz);

    return { l, a, b: lB };
}

/**
 * Linear interpolation between color stops
 */
function interpolateColors(val, stops) {
    val = Math.max(0, Math.min(1, val));
    const numStops = stops.length;
    const idx = val * (numStops - 1);
    const i = Math.floor(idx);
    const f = idx - i;
    
    if (i >= numStops - 1) return stops[numStops - 1];
    
    const c1 = stops[i];
    const c2 = stops[i + 1];
    
    return {
        r: Math.round(c1.r + (c2.r - c1.r) * f),
        g: Math.round(c1.g + (c2.g - c1.g) * f),
        b: Math.round(c1.b + (c2.b - c1.b) * f)
    };
}

/**
 * Interpolate along the current active customized channel palette
 */
function interpolatePalette(val) {
    const channels = ['blue', 'green', 'yellow', 'red', 'black', 'white'];
    const stops = channels.map(c => hexToRgb(currentColors[c]));
    return interpolateColors(val, stops);
}

/**
 * Standard HSL to RGB converter
 */
function hslToRgb(h, s, l) {
    let r, g, b;
    if (s === 0) {
        r = g = b = l;
    } else {
        const hue2rgb = (p, q, t) => {
            if (t < 0) t += 1;
            if (t > 1) t -= 1;
            if (t < 1/6) return p + (q - p) * 6 * t;
            if (t < 1/2) return q;
            if (t < 2/3) return p + (q - p) * (2/3 - t) * 6;
            return p;
        };
        const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
        const p = 2 * l - q;
        r = hue2rgb(p, q, h + 1/3);
        g = hue2rgb(p, q, h);
        b = hue2rgb(p, q, h - 1/3);
    }
    return {
        r: Math.round(r * 255),
        g: Math.round(g * 255),
        b: Math.round(b * 255)
    };
}



/**
 * Dynamically construct UI color pickers from defined channels
 */
function buildColorPickers() {
    const container = document.getElementById('color-pickers-container');
    container.innerHTML = '';
    
    Object.keys(currentColors).forEach(channel => {
        const item = document.createElement('div');
        item.className = 'picker-item';
        
        const prefix = CSS_PREFIX[channel];
        
        const dot = document.createElement('span');
        dot.className = 'picker-dot';
        dot.style.backgroundColor = `var(--color-${prefix})`;
        
        const details = document.createElement('div');
        details.className = 'picker-details';
        
        const name = document.createElement('span');
        name.className = 'picker-name';
        name.textContent = `Primary ${channel.charAt(0).toUpperCase() + channel.slice(1)}`;
        
        const input = document.createElement('input');
        input.type = 'color';
        input.id = `picker-${channel}`;
        input.value = currentColors[channel];
        
        details.appendChild(name);
        details.appendChild(input);
        item.appendChild(dot);
        item.appendChild(details);
        container.appendChild(item);
        
        pickers[channel] = input;
    });
}

/**
 * Update combination count badges
 */
function updateBadges() {
    let total;
    if (tileStyle === 'geometric') {
        total = COLOR_PAIRS.length * 6;
    } else if (tileStyle === 'sprites') {
        total = 96;
    } else {
        total = customImageCols * customImageRows;
    }
    document.getElementById('total-combinations-badge').textContent = total;
    document.getElementById('total-combinations-desc').textContent = total;
}

/**
 * Precalculate aggregate RGB/LAB colors of geometric concentric tiles (84 configurations)
 */
function precomputeGeometricTiles() {
    precomputedTiles = [];
    const numCols = COLOR_PAIRS.length;
    
    for (let row = 0; row < 6; row++) {
        for (let col = 0; col < numCols; col++) {
            const pair = COLOR_PAIRS[col];
            const hexA = currentColors[pair.A];
            const hexB = currentColors[pair.B];
            
            const rgbA = hexToRgb(hexA);
            const rgbB = hexToRgb(hexB);
            
            const w = ROW_WEIGHTS[row];
            
            const r = Math.round(rgbA.r * w.A + rgbB.r * w.B);
            const g = Math.round(rgbA.g * w.A + rgbB.g * w.B);
            const b = Math.round(rgbA.b * w.A + rgbB.b * w.B);
            
            const lab = rgbToLab(r, g, b);
            
            precomputedTiles.push({
                index: row * numCols + col,
                row,
                col,
                avgRgb: { r, g, b },
                avgLab: lab,
                colorA: hexA,
                colorB: hexB
            });
        }
    }
}

/**
 * Precalculate aggregate RGB/LAB colors of dual-color retro shapes (48 shapes * 36 color pairs = 1728 combinations)
 * Groups candidates by color pair index for pre-filtered sub-pixel searches.
 */
// Quadrant layout specifications for the 12x8 grid of pre-designed tiles
const QUADRANTS = [
    // Quadrant 1 (Top-Left): White background
    {
        bg: 'white',
        fgRows: ['black', 'red', 'blue', 'green'],
        splits: [
            { top: 'black', bottom: 'white' }, // Row 0 (relative)
            { top: 'red', bottom: 'black' },   // Row 1
            { top: 'blue', bottom: 'red' },     // Row 2
            { top: 'green', bottom: 'blue' }    // Row 3
        ]
    },
    // Quadrant 2 (Top-Right): Red background
    {
        bg: 'red',
        fgRows: ['black', 'white', 'blue', 'green'],
        splits: [
            { top: 'black', bottom: 'white' },
            { top: 'white', bottom: 'black' },
            { top: 'blue', bottom: 'red' },
            { top: 'green', bottom: 'blue' }
        ]
    },
    // Quadrant 3 (Bottom-Left): Blue background
    {
        bg: 'blue',
        fgRows: ['black', 'red', 'white', 'green'],
        splits: [
            { top: 'black', bottom: 'green' },
            { top: 'red', bottom: 'black' },
            { top: 'white', bottom: 'red' },
            { top: 'green', bottom: 'white' }
        ]
    },
    // Quadrant 4 (Bottom-Right): Green background
    {
        bg: 'green',
        fgRows: ['black', 'white', 'blue', 'red'],
        splits: [
            { top: 'black', bottom: 'white' },
            { top: 'white', bottom: 'black' },
            { top: 'blue', bottom: 'red' },
            { top: 'red', bottom: 'white' }
        ]
    }
];

function precomputeSpriteTiles() {
    precomputedSpriteTiles = [];
    
    for (let row = 0; row < 8; row++) {
        const qRow = Math.floor(row / 4);
        const rRow = row % 4;
        
        for (let col = 0; col < 12; col++) {
            const qCol = Math.floor(col / 6);
            const rCol = col % 6;
            
            const qIndex = qRow * 2 + qCol;
            const quad = QUADRANTS[qIndex];
            
            const bgColorName = quad.bg;
            const fgColorName = quad.fgRows[rRow];
            
            const tile = {
                index: row * 12 + col,
                row,
                col,
                shapeIndex: rCol,
                bgColorName,
                fgColorName,
                bgColor: currentColors[bgColorName],
                fgColor: currentColors[fgColorName]
            };
            
            // Handle specific top/bottom colors for split circle (Shape 5)
            if (rCol === 5) {
                const split = quad.splits[rRow];
                tile.fgTopName = split.top;
                tile.fgBottomName = split.bottom;
                tile.fgColorName = null;
                tile.fgColor = null;
            }
            
            // Compile the 8x8 pixel grid of RGB colors for this tile
            const pixelGrid = [];
            const shapeGrid = RETRO_SHAPES[rCol];
            const bgRgb = hexToRgb(tile.bgColor);
            
            let sumR = 0, sumG = 0, sumB = 0;
            
            for (let r = 0; r < 8; r++) {
                const rowPixels = [];
                for (let c = 0; c < 8; c++) {
                    let pxColor;
                    if (rCol === 5) {
                        // Split circle (Shape 5)
                        if (shapeGrid[r][c] === 1) {
                            const colorName = r < 4 ? tile.fgTopName : tile.fgBottomName;
                            pxColor = hexToRgb(currentColors[colorName]);
                        } else {
                            pxColor = bgRgb;
                        }
                    } else {
                        // Standard shape
                        if (shapeGrid[r][c] === 1) {
                            pxColor = hexToRgb(tile.fgColor);
                        } else {
                            pxColor = bgRgb;
                        }
                    }
                    rowPixels.push(pxColor);
                    sumR += pxColor.r;
                    sumG += pxColor.g;
                    sumB += pxColor.b;
                }
                pixelGrid.push(rowPixels);
            }
            
            tile.pixelGrid = pixelGrid;
            
            const avgR = Math.round(sumR / 64);
            const avgG = Math.round(sumG / 64);
            const avgB = Math.round(sumB / 64);
            
            tile.avgRgb = { r: avgR, g: avgG, b: avgB };
            tile.avgLab = rgbToLab(avgR, avgG, avgB);
            
            precomputedSpriteTiles.push(tile);
        }
    }
}

/**
 * Helper function to lazy-initialize and cache offscreen canvas slices when needed
 */
function getSliceCanvas(slice) {
    if (!slice) return null;
    if (slice.canvas) return slice.canvas;
    
    const sliceSize = customImageCols > 32 || customImageRows > 32 ? 32 : 64;
    const sliceCanvas = document.createElement('canvas');
    sliceCanvas.width = sliceSize;
    sliceCanvas.height = sliceSize;
    const sliceCtx = sliceCanvas.getContext('2d');
    
    sliceCtx.drawImage(
        customImageElement,
        slice.sx, slice.sy, slice.sw, slice.sh,
        0, 0, sliceSize, sliceSize
    );
    
    slice.canvas = sliceCanvas;
    return sliceCanvas;
}

/**
 * Slice the uploaded grid image into columns and rows, precalculating average colors
 */
function sliceGridImage() {
    if (!customImageElement) return;
    
    customSlices = [];
    
    const imgWidth = customImageElement.naturalWidth || customImageElement.width;
    const imgHeight = customImageElement.naturalHeight || customImageElement.height;
    
    const sliceWidth = imgWidth / customImageCols;
    const sliceHeight = imgHeight / customImageRows;
    
    // Temporarily draw the image onto an offscreen canvas to read pixel data
    const analysisCanvas = document.createElement('canvas');
    analysisCanvas.width = imgWidth;
    analysisCanvas.height = imgHeight;
    const analysisCtx = analysisCanvas.getContext('2d');
    analysisCtx.drawImage(customImageElement, 0, 0);
    
    // HIGH-PERFORMANCE: Read all image pixel bytes exactly once
    const imgData = analysisCtx.getImageData(0, 0, imgWidth, imgHeight);
    const data = imgData.data;
    
    for (let r = 0; r < customImageRows; r++) {
        for (let c = 0; c < customImageCols; c++) {
            const sx = Math.floor(c * sliceWidth);
            const sy = Math.floor(r * sliceHeight);
            const sw = Math.max(1, Math.floor(sliceWidth));
            const sh = Math.max(1, Math.floor(sliceHeight));
            
            // HIGH-PERFORMANCE: Calculate average color from the single loaded buffer
            let sumR = 0, sumG = 0, sumB = 0;
            let count = 0;
            
            for (let y = sy; y < sy + sh && y < imgHeight; y++) {
                for (let x = sx; x < sx + sw && x < imgWidth; x++) {
                    const pixelIdx = (y * imgWidth + x) * 4;
                    sumR += data[pixelIdx];
                    sumG += data[pixelIdx + 1];
                    sumB += data[pixelIdx + 2];
                    count++;
                }
            }
            
            const avgR = count > 0 ? Math.round(sumR / count) : 0;
            const avgG = count > 0 ? Math.round(sumG / count) : 0;
            const avgB = count > 0 ? Math.round(sumB / count) : 0;
            
            customSlices.push({
                index: r * customImageCols + c,
                row: r,
                col: c,
                sx,
                sy,
                sw,
                sh,
                canvas: null, // Lazy loaded on-demand
                avgRgb: { r: avgR, g: avgG, b: avgB },
                avgLab: rgbToLab(avgR, avgG, avgB)
            });
        }
    }
    
    renderReferenceGrid();
}

/**
 * Combined precompute wrapper
 */
function precomputeTiles() {
    precomputeGeometricTiles();
    precomputeSpriteTiles();
    if (customImageElement) {
        sliceGridImage();
    } else {
        renderReferenceGrid();
    }
}

/**
 * Renders a single geometric tile onto a canvas context
 */
function drawTile(ctx, x, y, size, row, col) {
    const pair = COLOR_PAIRS[col];
    const colorA = currentColors[pair.A];
    const colorB = currentColors[pair.B];
    
    let bg, ringColor, innerBg;
    let ringSize = 0;
    let innerSize = 0;
    
    if (row === 0) {
        bg = colorA;
        ringColor = colorB;
        ringSize = 0.2;
        innerSize = 0;
        innerBg = colorA;
    } else if (row === 1) {
        bg = colorA;
        ringColor = colorB;
        ringSize = 0.5;
        innerSize = 0.3;
        innerBg = colorA;
    } else if (row === 2) {
        bg = colorA;
        ringColor = colorB;
        ringSize = 0.8;
        innerSize = 0.6;
        innerBg = colorA;
    } else if (row === 3) {
        bg = colorB;
        ringColor = colorA;
        ringSize = 0.8;
        innerSize = 0.6;
        innerBg = colorB;
    } else if (row === 4) {
        bg = colorB;
        ringColor = colorA;
        ringSize = 0.5;
        innerSize = 0.3;
        innerBg = colorB;
    } else if (row === 5) {
        bg = colorB;
        ringColor = colorA;
        ringSize = 0.2;
        innerSize = 0;
        innerBg = colorB;
    }
    
    ctx.fillStyle = bg;
    ctx.fillRect(x, y, size, size);
    
    if (ringSize > 0) {
        const rWidth = size * ringSize;
        const offset = (size - rWidth) / 2;
        ctx.fillStyle = ringColor;
        ctx.fillRect(x + offset, y + offset, rWidth, rWidth);
    }
    
    if (innerSize > 0) {
        const iWidth = size * innerSize;
        const offset = (size - iWidth) / 2;
        ctx.fillStyle = innerBg;
        ctx.fillRect(x + offset, y + offset, iWidth, iWidth);
    }
}

/**
 * Draw a single fixed pre-designed sprite tile onto a canvas context at full resolution (smooth vector drawing)
 */
function drawPredesignedSpriteTile(ctx, x, y, size, tileIndex) {
    const tile = precomputedSpriteTiles[tileIndex];
    if (!tile) return;
    
    // 1. Draw Background
    ctx.fillStyle = tile.bgColor;
    ctx.fillRect(x, y, size, size);
    
    // 2. Draw Shape
    const cx = x + size / 2;
    const cy = y + size / 2;
    
    if (tile.shapeIndex === 0) {
        // Circle (diameter 75% of tile size)
        const r = size * 0.375;
        ctx.beginPath();
        ctx.arc(cx, cy, r, 0, 2 * Math.PI);
        ctx.fillStyle = tile.fgColor;
        ctx.fill();
    } else if (tile.shapeIndex === 1) {
        // Square (width 75% of tile size)
        const w = size * 0.75;
        const offset = (size - w) / 2;
        ctx.fillStyle = tile.fgColor;
        ctx.fillRect(x + offset, y + offset, w, w);
    } else if (tile.shapeIndex === 2) {
        // Cross (thickness 25% of tile size, touching borders)
        const thickness = size * 0.25;
        const offset = (size - thickness) / 2;
        ctx.fillStyle = tile.fgColor;
        // Vertical bar
        ctx.fillRect(x + offset, y, thickness, size);
        // Horizontal bar
        ctx.fillRect(x, y + offset, size, thickness);
    } else if (tile.shapeIndex === 3) {
        // Horizontal Stripes (4 alternating lines, touching borders)
        const h = size / 8;
        ctx.fillStyle = tile.fgColor;
        ctx.fillRect(x, y, size, h);
        ctx.fillRect(x, y + 2 * h, size, h);
        ctx.fillRect(x, y + 4 * h, size, h);
        ctx.fillRect(x, y + 6 * h, size, h);
    } else if (tile.shapeIndex === 4) {
        // Triangle pointing up (75% size with matching margins)
        const margin = size * 0.125;
        ctx.fillStyle = tile.fgColor;
        ctx.beginPath();
        ctx.moveTo(cx, y + margin);
        ctx.lineTo(x + size - margin, y + size - margin);
        ctx.lineTo(x + margin, y + size - margin);
        ctx.closePath();
        ctx.fill();
    } else if (tile.shapeIndex === 5) {
        // Split Circle (split horizontally)
        const r = size * 0.375;
        const fgTop = currentColors[tile.fgTopName];
        const fgBottom = currentColors[tile.fgBottomName];
        
        // Top Semicircle
        ctx.beginPath();
        ctx.arc(cx, cy, r, Math.PI, 0, false);
        ctx.fillStyle = fgTop;
        ctx.fill();
        
        // Bottom Semicircle
        ctx.beginPath();
        ctx.arc(cx, cy, r, 0, Math.PI, false);
        ctx.fillStyle = fgBottom;
        ctx.fill();
    }
}

/**
 * Populate the reference preview board in the sidebar
 */
function renderReferenceGrid() {
    elements.referenceGridContainer.innerHTML = '';
    
    if (tileStyle === 'geometric') {
        elements.referenceGridContainer.style.gridTemplateColumns = `repeat(${COLOR_PAIRS.length}, 1fr)`;
        
        precomputedTiles.forEach(tile => {
            const wrapper = document.createElement('div');
            wrapper.className = 'reference-tile-wrapper';
            
            const rgbStr = `rgb(${tile.avgRgb.r}, ${tile.avgRgb.g}, ${tile.avgRgb.b})`;
            wrapper.setAttribute('data-tooltip', `Tile [R:${tile.row + 1}, C:${tile.col + 1}]\nAvg: ${rgbStr}`);
            
            const canvas = document.createElement('canvas');
            canvas.width = 36;
            canvas.height = 36;
            canvas.className = 'reference-tile-canvas';
            
            wrapper.appendChild(canvas);
            elements.referenceGridContainer.appendChild(wrapper);
            
            const ctx = canvas.getContext('2d');
            drawTile(ctx, 0, 0, 36, tile.row, tile.col);
        });
    } else if (tileStyle === 'sprites') {
        elements.referenceGridContainer.style.gridTemplateColumns = `repeat(12, 1fr)`;
        
        precomputedSpriteTiles.forEach((tile, i) => {
            const wrapper = document.createElement('div');
            wrapper.className = 'reference-tile-wrapper';
            wrapper.setAttribute('data-tooltip', `Tile [R:${tile.row + 1}, C:${tile.col + 1}]\n${SHAPE_NAMES[tile.shapeIndex]}`);
            
            const canvas = document.createElement('canvas');
            canvas.width = 36;
            canvas.height = 36;
            canvas.className = 'reference-tile-canvas';
            
            wrapper.appendChild(canvas);
            elements.referenceGridContainer.appendChild(wrapper);
            
            const ctx = canvas.getContext('2d');
            drawPredesignedSpriteTile(ctx, 0, 0, 36, i);
        });
    } else if (tileStyle === 'custom') {
        const maxDisplay = 144;
        const displaySlices = customSlices.slice(0, maxDisplay);
        
        elements.referenceGridContainer.style.gridTemplateColumns = `repeat(${Math.min(customImageCols, 12)}, 1fr)`;
        
        displaySlices.forEach(slice => {
            const wrapper = document.createElement('div');
            wrapper.className = 'reference-tile-wrapper';
            
            const rgbStr = `rgb(${slice.avgRgb.r}, ${slice.avgRgb.g}, ${slice.avgRgb.b})`;
            wrapper.setAttribute('data-tooltip', `Slice [R:${slice.row + 1}, C:${slice.col + 1}]\nAvg: ${rgbStr}`);
            
            const canvas = document.createElement('canvas');
            canvas.width = 36;
            canvas.height = 36;
            canvas.className = 'reference-tile-canvas';
            
            wrapper.appendChild(canvas);
            elements.referenceGridContainer.appendChild(wrapper);
            
            const ctx = canvas.getContext('2d');
            ctx.drawImage(getSliceCanvas(slice), 0, 0, 36, 36);
        });
        
        if (customSlices.length > maxDisplay) {
            const note = document.createElement('div');
            note.style.cssText = 'grid-column: 1 / -1; text-align: center; font-size: 0.75rem; color: var(--text-muted); margin-top: 8px; font-family: var(--font-sans);';
            note.textContent = `Showing first ${maxDisplay} of ${customSlices.length} slices (Reference grid limited for performance)`;
            elements.referenceGridContainer.appendChild(note);
        }
    }
}

/**
 * Find closest dynamic geometric tile match
 */
function findBestTile(r, g, b) {
    let bestMatch = null;
    let minDistance = Infinity;
    const pixelLab = rgbToLab(r, g, b);
    
    for (let i = 0; i < precomputedTiles.length; i++) {
        const tile = precomputedTiles[i];
        let dist;
        if (matchingMethod === 'lab') {
            const dL = pixelLab.l - tile.avgLab.l;
            const da = pixelLab.a - tile.avgLab.a;
            const db = pixelLab.b - tile.avgLab.b;
            dist = dL * dL + da * da + db * db;
        } else {
            const dr = r - tile.avgRgb.r;
            const dg = g - tile.avgRgb.g;
            const db = b - tile.avgRgb.b;
            dist = dr * dr + dg * dg + db * db;
        }
        
        if (dist < minDistance) {
            minDistance = dist;
            bestMatch = tile;
        }
    }
    
    return bestMatch;
}

/**
 * Find the closest custom image slice match based on LAB or RGB distance
 */
function findBestCustomSlice(r, g, b) {
    if (customSlices.length === 0) return null;
    
    let bestMatch = null;
    let minDistance = Infinity;
    const pixelLab = rgbToLab(r, g, b);
    
    for (let i = 0; i < customSlices.length; i++) {
        const slice = customSlices[i];
        let dist;
        if (matchingMethod === 'lab') {
            const dL = pixelLab.l - slice.avgLab.l;
            const da = pixelLab.a - slice.avgLab.a;
            const db = pixelLab.b - slice.avgLab.b;
            dist = dL * dL + da * da + db * db;
        } else {
            const dr = r - slice.avgRgb.r;
            const dg = g - slice.avgRgb.g;
            const db = b - slice.avgRgb.b;
            dist = dr * dr + dg * dg + db * db;
        }
        
        if (dist < minDistance) {
            minDistance = dist;
            bestMatch = slice;
        }
    }
    
    return bestMatch;
}

/**
 * Solves the next transition step in reference grid coordinates constrained by force linear checkboxes
 */
function findNextStep(prevRow, prevCol, idealRow, idealCol, hChecked, vChecked, dChecked, maxRows, maxCols) {
    if (!hChecked && !vChecked && !dChecked) {
        return { row: idealRow, col: idealCol };
    }
    
    let bestRow = prevRow;
    let bestCol = prevCol;
    let minDistance = Infinity;
    
    for (let dr = -1; dr <= 1; dr++) {
        for (let dc = -1; dc <= 1; dc++) {
            let isAllowed = false;
            
            if (dr === 0 && dc === 0) {
                isAllowed = true;
            } else if (dr === 0 && Math.abs(dc) === 1) {
                if (hChecked || dChecked) isAllowed = true;
            } else if (Math.abs(dr) === 1 && dc === 0) {
                if (vChecked || dChecked) isAllowed = true;
            } else if (Math.abs(dr) === 1 && Math.abs(dc) === 1) {
                if (dChecked) isAllowed = true;
            }
            
            if (isAllowed) {
                const nextRow = prevRow + dr;
                const nextCol = prevCol + dc;
                
                if (nextRow >= 0 && nextRow < maxRows && nextCol >= 0 && nextCol < maxCols) {
                    const distRow = idealRow - nextRow;
                    const distCol = idealCol - nextCol;
                    const distance = distRow * distRow + distCol * distCol;
                    
                    if (distance < minDistance) {
                        minDistance = distance;
                        bestRow = nextRow;
                        bestCol = nextCol;
                    }
                }
            }
        }
    }
    
    return { row: bestRow, col: bestCol };
}

/**
 * Real-time Fixed Sprite Grid Matching
 * 1. Pre-filters 96 tiles using average color distance (LAB or RGB) to select top 10 candidates.
 * 2. Calculates exact pixel structural distance directly from raw downsampled buffer.
 * 3. Extremely fast and allocation-free execution.
 */
function findBestSpriteMatch(blockAvgRgb, rawBuffer, bufferWidth, startX, startY) {
    let bestTileIndex = 0;
    let minStructuralDistance = Infinity;
    
    const r = blockAvgRgb.r;
    const g = blockAvgRgb.g;
    const b = blockAvgRgb.b;
    const pixelLab = rgbToLab(r, g, b);
    
    // 1. Pre-filter: find top 10 closest pre-designed tiles based on average color distance
    const tileDists = [];
    
    const getDist = (l1, l2) => {
        const dL = l1.l - l2.l;
        const da = l1.a - l2.a;
        const db = l1.b - l2.b;
        return dL * dL + da * da + db * db;
    };
    
    const getDistRgb = (r1, g1, b1, r2, g2, b2) => {
        const dr = r1 - r2;
        const dg = g1 - g2;
        const db = b1 - b2;
        return dr * dr + dg * dg + db * db;
    };
    
    for (let i = 0; i < 96; i++) {
        const tile = precomputedSpriteTiles[i];
        let dist;
        if (matchingMethod === 'lab') {
            dist = getDist(pixelLab, tile.avgLab);
        } else {
            dist = getDistRgb(r, g, b, tile.avgRgb.r, tile.avgRgb.g, tile.avgRgb.b);
        }
        tileDists.push({ index: i, dist });
    }
    
    tileDists.sort((a, b) => a.dist - b.dist);
    
    // 2. Exact pixel-by-pixel structural distance scan on the top 10 closest candidates
    const numCandidates = Math.min(10, tileDists.length);
    for (let c = 0; c < numCandidates; c++) {
        const idx = tileDists[c].index;
        const tile = precomputedSpriteTiles[idx];
        const grid = tile.pixelGrid;
        
        let structDist = 0;
        let pruned = false;
        
        for (let row = 0; row < 8; row++) {
            const py = startY + row;
            for (let col = 0; col < 8; col++) {
                const targetColor = grid[row][col];
                
                const px = startX + col;
                const pIdx = (py * bufferWidth + px) * 4;
                
                const dr = targetColor.r - rawBuffer[pIdx];
                const dg = targetColor.g - rawBuffer[pIdx + 1];
                const db = targetColor.b - rawBuffer[pIdx + 2];
                
                structDist += dr * dr + dg * dg + db * db;
                
                if (structDist >= minStructuralDistance) {
                    pruned = true;
                    break;
                }
            }
            if (pruned) break;
        }
        
        if (!pruned) {
            minStructuralDistance = structDist;
            bestTileIndex = idx;
        }
    }
    
    return bestTileIndex;
}

/**
 * Generate mathematical procedural patterns into offscreen canvas
 */
function generateProceduralFrame(w, h) {
    const t = (performance.now() / 1000) * patternSpeed;
    const imgData = offscreenCtx.createImageData(w, h);
    const data = imgData.data;
    
    for (let y = 0; y < h; y++) {
        for (let x = 0; x < w; x++) {
            const u = x / w;
            const v = y / h;
            let val = 0;
            
            if (patternType === 'plasma') {
                const sX = patternScale * 10;
                const sY = patternScale * 10;
                val = Math.sin(u * sX + t) 
                    + Math.sin(sY * (v * Math.sin(t / 2) + Math.cos(t / 3)) + t)
                    + Math.sin(Math.sqrt(Math.pow(sX * (u - 0.5), 2) + Math.pow(sY * (v - 0.5), 2)) - t);
                val = (val + 3) / 6;
            } else if (patternType === 'spiral') {
                const dx = u - 0.5;
                const dy = v - 0.5;
                const dist = Math.sqrt(dx * dx + dy * dy);
                const angle = Math.atan2(dy, dx);
                val = Math.sin(angle * 3 - dist * patternScale * 25 + t * 4);
                val = (val + 1) / 2;
            } else if (patternType === 'ripple') {
                const dx = u - rippleCenter.x;
                const dy = v - rippleCenter.y;
                const dist = Math.sqrt(dx * dx + dy * dy);
                val = Math.sin(dist * patternScale * 35 - t * 8);
                val = (val + 1) / 2;
            } else if (patternType === 'mandala') {
                const dx = u - 0.5;
                const dy = v - 0.5;
                const dist = Math.sqrt(dx * dx + dy * dy);
                let angle = Math.atan2(dy, dx);
                const segments = 8;
                angle = Math.abs(((angle + Math.PI) % (2 * Math.PI / segments)) - Math.PI / segments);
                const nx = dist * Math.cos(angle);
                const ny = dist * Math.sin(angle);
                val = Math.sin(nx * patternScale * 20 + t) * Math.cos(ny * patternScale * 20 - t);
                val = (val + 1) / 2;
            }
            
            let rgb = { r: 0, g: 0, b: 0 };
            if (patternColorMode === 'custom') {
                rgb = interpolatePalette(val);
            } else if (patternColorMode === 'rainbow') {
                rgb = hslToRgb(val, 0.8, 0.5);
            } else if (patternColorMode === 'fire') {
                rgb = interpolateColors(val, [
                    { r: 0, g: 0, b: 0 },
                    { r: 180, g: 0, b: 0 },
                    { r: 255, g: 200, b: 0 },
                    { r: 255, g: 255, b: 255 }
                ]);
            } else if (patternColorMode === 'ocean') {
                rgb = interpolateColors(val, [
                    { r: 0, g: 10, b: 60 },
                    { r: 0, g: 120, b: 150 },
                    { r: 0, g: 220, b: 200 },
                    { r: 150, g: 240, b: 255 }
                ]);
            }
            
            const idx = (y * w + x) * 4;
            data[idx] = rgb.r;
            data[idx + 1] = rgb.g;
            data[idx + 2] = rgb.b;
            data[idx + 3] = 255;
        }
    }
    
    offscreenCtx.putImageData(imgData, 0, 0);
}

/**
 * Process and render a video frame onto display canvas
 */
function processVideoFrame() {
    if (isPaused) return;
    
    let vWidth = 640;
    let vHeight = 480;
    
    if (inputSource === 'webcam') {
        if (!stream) return;
        vWidth = elements.video.videoWidth;
        vHeight = elements.video.videoHeight;
        if (vWidth === 0 || vHeight === 0) {
            animationFrameId = requestAnimationFrame(processVideoFrame);
            return;
        }
    } else if (inputSource === 'video') {
        vWidth = elements.uploadedVideo.videoWidth;
        vHeight = elements.uploadedVideo.videoHeight;
        if (vWidth === 0 || vHeight === 0 || elements.uploadedVideo.paused) {
            animationFrameId = requestAnimationFrame(processVideoFrame);
            return;
        }
    }
    
    // Enforce even dimensions to ensure perfect compatibility with hardware-accelerated WebCodecs H.264 encoders
    const evenWidth = vWidth % 2 === 0 ? vWidth : vWidth - 1;
    const evenHeight = vHeight % 2 === 0 ? vHeight : vHeight - 1;
    
    if (elements.canvas.width !== evenWidth || elements.canvas.height !== evenHeight) {
        elements.canvas.width = evenWidth;
        elements.canvas.height = evenHeight;
    }
    
    const gridWidth = Math.ceil(vWidth / tileSize);
    const gridHeight = Math.ceil(vHeight / tileSize);
    
    elements.resolutionDisplay.textContent = `Grid: ${gridWidth} x ${gridHeight}`;
    
    // Scale downsampling buffer based on style (8x resolution for sub-pixel matching!)
    const factor = (tileStyle === 'geometric' || tileStyle === 'custom') ? 1 : 8;
    const bufferWidth = gridWidth * factor;
    const bufferHeight = gridHeight * factor;
    
    offscreenCanvas.width = bufferWidth;
    offscreenCanvas.height = bufferHeight;
    
    if (inputSource === 'webcam') {
        offscreenCtx.drawImage(elements.video, 0, 0, bufferWidth, bufferHeight);
    } else if (inputSource === 'video') {
        offscreenCtx.drawImage(elements.uploadedVideo, 0, 0, bufferWidth, bufferHeight);
    } else {
        generateProceduralFrame(bufferWidth, bufferHeight);
    }
    
    const imgData = offscreenCtx.getImageData(0, 0, bufferWidth, bufferHeight);
    const rawBuffer = imgData.data;
    
    displayCtx.clearRect(0, 0, elements.canvas.width, elements.canvas.height);
    
    displayCtx.save();
    if (inputSource === 'webcam') {
        displayCtx.translate(elements.canvas.width, 0);
        displayCtx.scale(-1, 1);
    }
    
    if (tileStyle === 'geometric') {
        // Standard Geometric Rendering (Single pixel downsampling)
        for (let y = 0; y < gridHeight; y++) {
            for (let x = 0; x < gridWidth; x++) {
                const cellIdx = y * gridWidth + x;
                let match;
                const now = performance.now();
                
                if (flickerCooldownMs > 0 && lastMatches[cellIdx] && (now - lastMatchTimes[cellIdx] < flickerCooldownMs)) {
                    match = lastMatches[cellIdx];
                } else {
                    const idx = (y * gridWidth + x) * 4;
                    const r = rawBuffer[idx];
                    const g = rawBuffer[idx + 1];
                    const b = rawBuffer[idx + 2];
                    
                    const idealMatch = findBestTile(r, g, b);
                    
                    if (lastMatches[cellIdx]) {
                        if (traverseLagMs > 0 && (now - lastTransitionTimes[cellIdx] < traverseLagMs)) {
                            match = lastMatches[cellIdx];
                        } else {
                            if (forceLinearHorizontal || forceLinearVertical || forceLinearDiagonal) {
                                const prevMatch = lastMatches[cellIdx];
                                const nextCoords = findNextStep(
                                    prevMatch.row, prevMatch.col,
                                    idealMatch.row, idealMatch.col,
                                    forceLinearHorizontal, forceLinearVertical, forceLinearDiagonal,
                                    6, COLOR_PAIRS.length
                                );
                                const nextIndex = nextCoords.row * COLOR_PAIRS.length + nextCoords.col;
                                match = precomputedTiles[nextIndex];
                            } else {
                                match = idealMatch;
                            }
                            
                            if (match.index !== lastMatches[cellIdx].index) {
                                lastTransitionTimes[cellIdx] = now;
                            }
                        }
                    } else {
                        match = idealMatch;
                        lastTransitionTimes[cellIdx] = now;
                    }
                    
                    lastMatches[cellIdx] = match;
                    lastMatchTimes[cellIdx] = now;
                }
                
                drawTile(displayCtx, x * tileSize, y * tileSize, tileSize, match.row, match.col);
            }
        }
    } else if (tileStyle === 'custom') {
        // Custom Slices Rendering (Single pixel downsampling matching to custom grid image slices)
        for (let y = 0; y < gridHeight; y++) {
            for (let x = 0; x < gridWidth; x++) {
                const cellIdx = y * gridWidth + x;
                let match;
                const now = performance.now();
                
                if (flickerCooldownMs > 0 && lastMatches[cellIdx] && (now - lastMatchTimes[cellIdx] < flickerCooldownMs)) {
                    match = lastMatches[cellIdx];
                } else {
                    const idx = (y * gridWidth + x) * 4;
                    const r = rawBuffer[idx];
                    const g = rawBuffer[idx + 1];
                    const b = rawBuffer[idx + 2];
                    
                    const idealMatch = findBestCustomSlice(r, g, b);
                    
                    if (idealMatch) {
                        if (lastMatches[cellIdx]) {
                            if (traverseLagMs > 0 && (now - lastTransitionTimes[cellIdx] < traverseLagMs)) {
                                match = lastMatches[cellIdx];
                            } else {
                                if (forceLinearHorizontal || forceLinearVertical || forceLinearDiagonal) {
                                    const prevMatch = lastMatches[cellIdx];
                                    const nextCoords = findNextStep(
                                        prevMatch.row, prevMatch.col,
                                        idealMatch.row, idealMatch.col,
                                        forceLinearHorizontal, forceLinearVertical, forceLinearDiagonal,
                                        customImageRows, customImageCols
                                    );
                                    const nextIndex = nextCoords.row * customImageCols + nextCoords.col;
                                    match = customSlices[nextIndex];
                                } else {
                                    match = idealMatch;
                                }
                                
                                if (match.index !== lastMatches[cellIdx].index) {
                                    lastTransitionTimes[cellIdx] = now;
                                }
                            }
                        } else {
                            match = idealMatch;
                            lastTransitionTimes[cellIdx] = now;
                        }
                    } else {
                        match = null;
                    }
                    
                    lastMatches[cellIdx] = match;
                    lastMatchTimes[cellIdx] = now;
                }
                
                if (match) {
                    displayCtx.drawImage(getSliceCanvas(match), x * tileSize, y * tileSize, tileSize, tileSize);
                } else {
                    displayCtx.fillStyle = '#000000';
                    displayCtx.fillRect(x * tileSize, y * tileSize, tileSize, tileSize);
                }
            }
        }
    } else {
        // Retro Dual-Color Structural Rendering (8x8 sub-pixel patch matching - Allocation-free!)
        for (let y = 0; y < gridHeight; y++) {
            for (let x = 0; x < gridWidth; x++) {
                const cellIdx = y * gridWidth + x;
                let bestTileIndex;
                const now = performance.now();
                
                if (flickerCooldownMs > 0 && lastMatches[cellIdx] !== null && (now - lastMatchTimes[cellIdx] < flickerCooldownMs)) {
                    bestTileIndex = lastMatches[cellIdx];
                } else {
                    let sumR = 0, sumG = 0, sumB = 0;
                    const startX = x * 8;
                    const startY = y * 8;
                    
                    for (let row = 0; row < 8; row++) {
                        const py = startY + row;
                        for (let col = 0; col < 8; col++) {
                            const px = startX + col;
                            const idx = (py * bufferWidth + px) * 4;
                            
                            sumR += rawBuffer[idx];
                            sumG += rawBuffer[idx + 1];
                            sumB += rawBuffer[idx + 2];
                        }
                    }
                    
                    const blockAvg = {
                        r: Math.round(sumR / 64),
                        g: Math.round(sumG / 64),
                        b: Math.round(sumB / 64)
                    };
                    
                    const idealTileIndex = findBestSpriteMatch(blockAvg, rawBuffer, bufferWidth, startX, startY);
                    
                    if (lastMatches[cellIdx] !== null) {
                        if (traverseLagMs > 0 && (now - lastTransitionTimes[cellIdx] < traverseLagMs)) {
                            bestTileIndex = lastMatches[cellIdx];
                        } else {
                            if (forceLinearHorizontal || forceLinearVertical || forceLinearDiagonal) {
                                const prevTileIndex = lastMatches[cellIdx];
                                const prevRow = Math.floor(prevTileIndex / 12);
                                const prevCol = prevTileIndex % 12;
                                
                                const idealRow = Math.floor(idealTileIndex / 12);
                                const idealCol = idealTileIndex % 12;
                                
                                const nextCoords = findNextStep(
                                    prevRow, prevCol,
                                    idealRow, idealCol,
                                    forceLinearHorizontal, forceLinearVertical, forceLinearDiagonal,
                                    8, 12
                                );
                                
                                bestTileIndex = nextCoords.row * 12 + nextCoords.col;
                            } else {
                                bestTileIndex = idealTileIndex;
                            }
                            
                            if (bestTileIndex !== lastMatches[cellIdx]) {
                                lastTransitionTimes[cellIdx] = now;
                            }
                        }
                    } else {
                        bestTileIndex = idealTileIndex;
                        lastTransitionTimes[cellIdx] = now;
                    }
                    
                    lastMatches[cellIdx] = bestTileIndex;
                    lastMatchTimes[cellIdx] = now;
                }
                
                drawPredesignedSpriteTile(displayCtx, x * tileSize, y * tileSize, tileSize, bestTileIndex);
            }
        }
    }
    
    displayCtx.restore();
    
    if (blendFactor > 0) {
        displayCtx.save();
        displayCtx.globalAlpha = blendFactor;
        if (inputSource === 'webcam') {
            displayCtx.translate(elements.canvas.width, 0);
            displayCtx.scale(-1, 1);
            displayCtx.drawImage(elements.video, 0, 0, elements.canvas.width, elements.canvas.height);
        } else if (inputSource === 'video') {
            displayCtx.drawImage(elements.uploadedVideo, 0, 0, elements.canvas.width, elements.canvas.height);
        } else {
            displayCtx.drawImage(offscreenCanvas, 0, 0, elements.canvas.width, elements.canvas.height);
        }
        displayCtx.restore();
    }

    
    const now = performance.now();
    frameCount++;
    if (now - lastFrameTime >= 1000) {
        fps = Math.round((frameCount * 1000) / (now - lastFrameTime));
        elements.fpsDisplay.innerHTML = `<span class="dot green"></span> Live: ${fps} FPS`;
        frameCount = 0;
        lastFrameTime = now;
    }
    
    animationFrameId = requestAnimationFrame(processVideoFrame);
}

/**
 * Initialize User Webcam stream
 */
async function initWebcam(deviceId = '') {
    if (stream) {
        stream.getTracks().forEach(track => track.stop());
    }
    
    const constraints = {
        video: {
            width: { ideal: 640 },
            height: { ideal: 480 },
            facingMode: 'user'
        },
        audio: false
    };
    
    if (deviceId) {
        constraints.video.deviceId = { exact: deviceId };
        delete constraints.video.facingMode;
    }
    
    try {
        stream = await navigator.mediaDevices.getUserMedia(constraints);
        elements.video.srcObject = stream;
        
        elements.video.onloadedmetadata = () => {
            elements.video.play().then(() => {
                isPaused = false;
                
                if (animationFrameId) cancelAnimationFrame(animationFrameId);
                animationFrameId = requestAnimationFrame(processVideoFrame);
            });
        };
        
        await enumerateCameras();
    } catch (err) {
        console.error('Error opening camera feed:', err);
        showToast('Webcam access blocked or failed. Switching to Procedural mode!');
        switchToProceduralSource();
    }
}

/**
 * Switches input selection to procedural mode
 */
function switchToProceduralSource() {
    document.getElementById('source-procedural').checked = true;
    inputSource = 'procedural';
    document.getElementById('webcam-settings-group').style.display = 'none';
    document.getElementById('video-settings-group').style.display = 'none';
    document.getElementById('procedural-settings-group').style.display = 'block';
    
    elements.uploadedVideo.pause();
    
    if (stream) {
        stream.getTracks().forEach(track => track.stop());
        stream = null;
    }
    
    isPaused = false;
    
    lastFrameTime = performance.now();
    if (animationFrameId) cancelAnimationFrame(animationFrameId);
    animationFrameId = requestAnimationFrame(processVideoFrame);
}

/**
 * Find all video devices
 */
async function enumerateCameras() {
    try {
        const devices = await navigator.mediaDevices.enumerateDevices();
        const videoDevices = devices.filter(device => device.kind === 'videoinput');
        
        elements.cameraSelect.innerHTML = '';
        
        if (videoDevices.length === 0) {
            elements.cameraSelect.innerHTML = '<option value="">No camera detected</option>';
            return;
        }
        
        videoDevices.forEach((device, i) => {
            const option = document.createElement('option');
            option.value = device.deviceId;
            option.textContent = device.label || `Camera ${i + 1}`;
            
            if (stream) {
                const activeTrack = stream.getVideoTracks()[0];
                if (activeTrack && activeTrack.getSettings().deviceId === device.deviceId) {
                    option.selected = true;
                    currentCameraId = device.deviceId;
                }
            }
            elements.cameraSelect.appendChild(option);
        });
    } catch (err) {
        console.error('Error enumerating cameras:', err);
    }
}

/**
 * Update UI and DOM custom variables matching base colors
 */
function updateColorSystem(channel, hexVal) {
    currentColors[channel] = hexVal;
    
    const prefix = CSS_PREFIX[channel];
    document.documentElement.style.setProperty(`--color-${prefix}`, hexVal);
    
    precomputeTiles();
}

/**
 * Apply a Theme preset to channel inputs
 */
function applyPresetTheme(presetName) {
    const preset = PRESET_THEMES[presetName];
    if (!preset) return;
    
    Object.keys(preset).forEach(channel => {
        currentColors[channel] = preset[channel];
        
        if (pickers[channel]) {
            pickers[channel].value = preset[channel];
        }
        
        const prefix = CSS_PREFIX[channel];
        document.documentElement.style.setProperty(`--color-${prefix}`, preset[channel]);
    });
    
    precomputeTiles();
}

/**
 * Displays a toast message on action
 */
function showToast(message) {
    elements.toast.textContent = message;
    elements.toast.className = 'toast-visible';
    
    setTimeout(() => {
                elements.toast.className = 'toast-hidden';
    }, 2500);
}


/**
 * Bind all user interactions and input controls
 */
function bindEvents() {
    // Input source segmented switcher
    document.querySelectorAll('input[name="input-source"]').forEach(radio => {
        radio.addEventListener('change', (e) => {
            inputSource = e.target.value;
            resetMatchHistory();
            
            // Hide all settings groups
            document.getElementById('webcam-settings-group').style.display = 'none';
            document.getElementById('video-settings-group').style.display = 'none';
            document.getElementById('procedural-settings-group').style.display = 'none';
            
            if (inputSource === 'webcam') {
                document.getElementById('webcam-settings-group').style.display = 'block';
                elements.uploadedVideo.pause();
                initWebcam(currentCameraId);
            } else if (inputSource === 'video') {
                document.getElementById('video-settings-group').style.display = 'block';
                if (stream) {
                    stream.getTracks().forEach(track => track.stop());
                    stream = null;
                }
                if (elements.uploadedVideo.src) {
                    elements.uploadedVideo.play().then(() => {
                        isPaused = false;
                        if (animationFrameId) cancelAnimationFrame(animationFrameId);
                        animationFrameId = requestAnimationFrame(processVideoFrame);
                    }).catch(err => console.error("Error playing video:", err));
                } else {
                    showToast("Please select an MP4 video file to begin!");
                }
            } else if (inputSource === 'procedural') {
                document.getElementById('procedural-settings-group').style.display = 'block';
                elements.uploadedVideo.pause();
                switchToProceduralSource();
            }
        });
    });

    // Video upload drag-and-drop and file-picker event listeners
    const dropZone = document.getElementById('video-drop-zone');
    const fileInput = document.getElementById('input-video-file');
    
    dropZone.addEventListener('click', () => {
        fileInput.click();
    });
    
    fileInput.addEventListener('change', (e) => {
        const file = e.target.files[0];
        if (file) {
            loadVideoFile(file);
        }
    });
    
    dropZone.addEventListener('dragover', (e) => {
        e.preventDefault();
        dropZone.style.borderColor = 'var(--accent-blue)';
        dropZone.style.background = 'rgba(59, 130, 246, 0.05)';
    });
    
    dropZone.addEventListener('dragleave', () => {
        dropZone.style.borderColor = 'rgba(255, 255, 255, 0.15)';
        dropZone.style.background = 'rgba(9, 10, 15, 0.4)';
    });
    
    dropZone.addEventListener('drop', (e) => {
        e.preventDefault();
        dropZone.style.borderColor = 'rgba(255, 255, 255, 0.15)';
        dropZone.style.background = 'rgba(9, 10, 15, 0.4)';
        
        const file = e.dataTransfer.files[0];
        if (file && file.type.startsWith('video/')) {
            loadVideoFile(file);
        } else {
            showToast('Please drop a valid MP4 video file!');
        }
    });
    
    function loadVideoFile(file) {
        const url = URL.createObjectURL(file);
        elements.uploadedVideo.src = url;
        
        document.getElementById('lbl-video-name').textContent = file.name;
        document.getElementById('video-playback-info').style.display = 'block';
        
        elements.uploadedVideo.onloadedmetadata = () => {
            elements.uploadedVideo.play().then(() => {
                isPaused = false;
                if (animationFrameId) cancelAnimationFrame(animationFrameId);
                animationFrameId = requestAnimationFrame(processVideoFrame);
                showToast(`Video loaded successfully!`);
            }).catch(err => {
                console.error('Failed to auto-play loaded video:', err);
                showToast('Failed to play video file.');
            });
        };
    }

    // Tile set style segmented switcher (geometric vs retro sprites vs custom)
    document.querySelectorAll('input[name="tile-style"]').forEach(radio => {
        radio.addEventListener('change', (e) => {
            tileStyle = e.target.value;
            resetMatchHistory();
            
            const customGroup = document.getElementById('custom-image-settings-group');
            if (tileStyle === 'custom') {
                customGroup.style.display = 'block';
                if (!customImageElement) {
                    showToast("Please upload a custom grid image!");
                }
            } else {
                customGroup.style.display = 'none';
            }
            
            updateBadges();
            renderReferenceGrid();
        });
    });

    // Custom Image Upload drop zone and file-picker event listeners
    const imageDropZone = elements.imageDropZone;
    const gridImageInput = elements.gridImageInput;
    
    imageDropZone.addEventListener('click', () => {
        gridImageInput.click();
    });
    
    gridImageInput.addEventListener('change', (e) => {
        const file = e.target.files[0];
        if (file) {
            loadGridImage(file);
        }
    });
    
    imageDropZone.addEventListener('dragover', (e) => {
        e.preventDefault();
        imageDropZone.style.borderColor = 'var(--accent-blue)';
        imageDropZone.style.background = 'rgba(59, 130, 246, 0.05)';
    });
    
    imageDropZone.addEventListener('dragleave', () => {
        imageDropZone.style.borderColor = 'rgba(255, 255, 255, 0.15)';
        imageDropZone.style.background = 'rgba(9, 10, 15, 0.4)';
    });
    
    imageDropZone.addEventListener('drop', (e) => {
        e.preventDefault();
        imageDropZone.style.borderColor = 'rgba(255, 255, 255, 0.15)';
        imageDropZone.style.background = 'rgba(9, 10, 15, 0.4)';
        
        const file = e.dataTransfer.files[0];
        if (file && file.type.startsWith('image/')) {
            loadGridImage(file);
        } else {
            showToast('Please drop a valid image file!');
        }
    });
    
    function loadGridImage(file) {
        const img = new Image();
        img.onload = function() {
            customImageElement = img;
            document.getElementById('lbl-image-name').textContent = file.name;
            document.getElementById('grid-image-info').style.display = 'block';
            document.getElementById('lbl-image-upload').textContent = 'Change image file';
            sliceGridImage();
            showToast('Grid image loaded and sliced successfully!');
        };
        img.src = URL.createObjectURL(file);
    }

    // Cols & Rows Inputs interaction with [1, 120] limits clamping
    const handleDimensionChange = () => {
        let cols = parseInt(elements.gridColsInput.value) || 8;
        let rows = parseInt(elements.gridRowsInput.value) || 8;
        
        // Clamp to [1, 120] range
        if (cols < 1) cols = 1;
        if (cols > 120) cols = 120;
        if (rows < 1) rows = 1;
        if (rows > 120) rows = 120;
        
        elements.gridColsInput.value = cols;
        elements.gridRowsInput.value = rows;
        
        customImageCols = cols;
        customImageRows = rows;
        
        updateBadges();
        
        if (customImageElement) {
            sliceGridImage();
        }
    };
    
    elements.gridColsInput.addEventListener('change', handleDimensionChange);
    elements.gridRowsInput.addEventListener('change', handleDimensionChange);

    // Procedural controllers
    document.getElementById('select-pattern').addEventListener('change', (e) => {
        patternType = e.target.value;
    });

    document.getElementById('input-pattern-speed').addEventListener('input', (e) => {
        patternSpeed = parseFloat(e.target.value);
        document.getElementById('pattern-speed-value').textContent = `${patternSpeed.toFixed(1)}x`;
    });

    document.getElementById('input-pattern-scale').addEventListener('input', (e) => {
        patternScale = parseFloat(e.target.value);
        document.getElementById('pattern-scale-value').textContent = `${patternScale.toFixed(1)}x`;
    });

    document.getElementById('select-pattern-color').addEventListener('change', (e) => {
        patternColorMode = e.target.value;
    });

    // Ripple mouse interactive tracker
    elements.canvas.addEventListener('mousemove', (e) => {
        if (inputSource !== 'procedural' || patternType !== 'ripple') return;
        
        const rect = elements.canvas.getBoundingClientRect();
        const x = e.clientX - rect.left;
        const y = e.clientY - rect.top;
        
        rippleCenter.x = 1.0 - (x / rect.width);
        rippleCenter.y = y / rect.height;
    });

    // Tile size slider
    elements.tileSizeInput.addEventListener('input', (e) => {
        tileSize = parseInt(e.target.value);
        elements.tileSizeValue.textContent = `${tileSize}px`;
        resetMatchHistory();
    });
    
    // Blend factor slider
    elements.blendFactorInput.addEventListener('input', (e) => {
        const pct = parseInt(e.target.value);
        blendFactor = pct / 100;
        elements.blendFactorValue.textContent = `${pct}%`;
    });

    // Flicker control slider
    elements.flickerCooldownInput.addEventListener('input', (e) => {
        flickerCooldownMs = parseInt(e.target.value);
        elements.flickerCooldownValue.textContent = `${flickerCooldownMs}ms`;
        resetMatchHistory();
    });
    
    // Force Linear Checkboxes
    elements.forceLinearHorizontalCheckbox.addEventListener('change', (e) => {
        forceLinearHorizontal = e.target.checked;
        resetMatchHistory();
    });
    elements.forceLinearVerticalCheckbox.addEventListener('change', (e) => {
        forceLinearVertical = e.target.checked;
        resetMatchHistory();
    });
    elements.forceLinearDiagonalCheckbox.addEventListener('change', (e) => {
        forceLinearDiagonal = e.target.checked;
        resetMatchHistory();
    });
    
    // Traverse Lag Slider
    elements.traverseLagInput.addEventListener('input', (e) => {
        traverseLagMs = parseInt(e.target.value);
        elements.traverseLagValue.textContent = `${traverseLagMs}ms`;
        resetMatchHistory();
    });
    
    // Segmented match spaces
    document.querySelectorAll('input[name="match-method"]').forEach(radio => {
        radio.addEventListener('change', (e) => {
            matchingMethod = e.target.value;
        });
    });
    
    // Camera selector changed
    elements.cameraSelect.addEventListener('change', (e) => {
        const id = e.target.value;
        if (id) {
            currentCameraId = id;
            initWebcam(id);
            resetMatchHistory();
        }
    });
    


    
    // Preset button clicks
    document.querySelectorAll('.preset-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            document.querySelectorAll('.preset-btn').forEach(b => b.classList.remove('active'));
            e.target.classList.add('active');
            
            const presetName = e.target.dataset.preset;
            applyPresetTheme(presetName);
            resetMatchHistory();
        });
    });
    
    // Accordion controls
    elements.toggleReference.addEventListener('click', () => {
        elements.toggleReference.classList.toggle('collapsed');
        elements.referenceGridWrapper.parentElement.classList.toggle('collapsed');
    });
}

// Initialize System
window.addEventListener('DOMContentLoaded', () => {
    bindEvents();
    buildColorPickers();
    updateBadges();
    precomputeTiles();
    initWebcam();
});
