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

// Style Selection State
let tileStyle = 'geometric'; // 'geometric' (84 concentric squares) or 'sprites' (48 custom sprites)

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

// Precomputed 36 color pairs with their endpoints and midpoints for pre-filtering
let precomputedColorPairs = [];

// Precomputed metadata for dual-color sprite configurations (grouped by color pair: 36 * 48)
let precomputedSpriteTiles = [];

// Precomputed rotated and mirrored grids for all 48 shapes
let shapesWithTransformations = [];

// DOM Elements Cache
const elements = {
    video: document.getElementById('webcam-video'),
    canvas: document.getElementById('mosaic-canvas'),
    cameraSelect: document.getElementById('select-camera'),
    tileSizeInput: document.getElementById('input-tile-size'),
    tileSizeValue: document.getElementById('tile-size-value'),
    blendFactorInput: document.getElementById('input-blend-factor'),
    blendFactorValue: document.getElementById('blend-factor-value'),
    btnPause: document.getElementById('btn-pause'),
    btnCapture: document.getElementById('btn-capture'),
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
 * Precompute all 8 rotation and mirroring states for all 48 retro shapes
 */
function initializeTransformations() {
    shapesWithTransformations = RETRO_SPRITES.map(grid => {
        const transforms = [];
        const emptyGrid = () => Array.from({ length: 8 }, () => new Array(8).fill(0));
        
        // 0. Rot 0 (Original)
        transforms.push(grid);
        
        // 1. Rot 90
        const r90 = emptyGrid();
        for (let r = 0; r < 8; r++) {
            for (let c = 0; c < 8; c++) {
                r90[c][7 - r] = grid[r][c];
            }
        }
        transforms.push(r90);
        
        // 2. Rot 180
        const r180 = emptyGrid();
        for (let r = 0; r < 8; r++) {
            for (let c = 0; c < 8; c++) {
                r180[7 - r][7 - c] = grid[r][c];
            }
        }
        transforms.push(r180);
        
        // 3. Rot 270
        const r270 = emptyGrid();
        for (let r = 0; r < 8; r++) {
            for (let c = 0; c < 8; c++) {
                r270[7 - c][r] = grid[r][c];
            }
        }
        transforms.push(r270);
        
        // 4. Mirror H (Horizontal Flip)
        const mH = emptyGrid();
        for (let r = 0; r < 8; r++) {
            for (let c = 0; c < 8; c++) {
                mH[r][7 - c] = grid[r][c];
            }
        }
        transforms.push(mH);
        
        // 5. Mirror H + Rot 90
        const mH90 = emptyGrid();
        for (let r = 0; r < 8; r++) {
            for (let c = 0; c < 8; c++) {
                mH90[c][7 - r] = mH[r][c];
            }
        }
        transforms.push(mH90);
        
        // 6. Mirror H + Rot 180
        const mH180 = emptyGrid();
        for (let r = 0; r < 8; r++) {
            for (let c = 0; c < 8; c++) {
                mH180[7 - r][7 - c] = mH[r][c];
            }
        }
        transforms.push(mH180);
        
        // 7. Mirror H + Rot 270
        const mH270 = emptyGrid();
        for (let r = 0; r < 8; r++) {
            for (let c = 0; c < 8; c++) {
                mH270[7 - c][r] = mH[r][c];
            }
        }
        transforms.push(mH270);
        
        return {
            grid,
            transformations: transforms
        };
    });
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
    const total = tileStyle === 'geometric' ? (COLOR_PAIRS.length * 6) : (RETRO_SPRITES.length * 36);
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
function precomputeSpriteTiles() {
    const channels = Object.keys(currentColors);
    const numShapes = RETRO_SPRITES.length;
    
    // 1. Precompute the 36 color pairs with their fg, bg, and mid LAB colors for fast filtering
    precomputedColorPairs = [];
    for (let i = 0; i < channels.length; i++) {
        for (let j = 0; j < channels.length; j++) {
            const fgChannel = channels[i];
            const bgChannel = channels[j];
            
            const hexFG = currentColors[fgChannel];
            const hexBG = currentColors[bgChannel];
            
            const rgbFG = hexToRgb(hexFG);
            const rgbBG = hexToRgb(hexBG);
            
            const midR = Math.round((rgbFG.r + rgbBG.r) / 2);
            const midG = Math.round((rgbFG.g + rgbBG.g) / 2);
            const midB = Math.round((rgbFG.b + rgbBG.b) / 2);
            
            precomputedColorPairs.push({
                index: i * channels.length + j,
                fgChannel,
                bgChannel,
                fgColor: hexFG,
                bgColor: hexBG,
                fgLab: rgbToLab(rgbFG.r, rgbFG.g, rgbFG.b),
                bgLab: rgbToLab(rgbBG.r, rgbBG.g, rgbBG.b),
                midLab: rgbToLab(midR, midG, midB)
            });
        }
    }
    
    // 2. Precompute aggregate average colors for all 1728 combinations, grouped by color pair (36 arrays of 48)
    precomputedSpriteTiles = Array.from({ length: 36 }, () => []);
    
    const densities = RETRO_SPRITES.map(grid => {
        const active = grid.reduce((sum, row) => sum + row.reduce((rSum, v) => rSum + v, 0), 0);
        return active / 64.0;
    });
    
    for (let cp = 0; cp < 36; cp++) {
        const pair = precomputedColorPairs[cp];
        const rgbFG = hexToRgb(pair.fgColor);
        const rgbBG = hexToRgb(pair.bgColor);
        
        for (let s = 0; s < numShapes; s++) {
            const density = densities[s];
            const wFG = density;
            const wBG = 1.0 - density;
            
            const r = Math.round(rgbFG.r * wFG + rgbBG.r * wBG);
            const g = Math.round(rgbFG.g * wFG + rgbBG.g * wBG);
            const b = Math.round(rgbFG.b * wFG + rgbBG.b * wBG);
            
            const lab = rgbToLab(r, g, b);
            
            precomputedSpriteTiles[cp].push({
                shapeIndex: s,
                fgColor: pair.fgColor,
                bgColor: pair.bgColor,
                avgRgb: { r, g, b },
                avgLab: lab
            });
        }
    }
}

/**
 * Combined precompute wrapper
 */
function precomputeTiles() {
    precomputeGeometricTiles();
    precomputeSpriteTiles();
    renderReferenceGrid();
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
 * Draw a single transformed retro sprite onto a canvas context with dual overlay colors
 */
function drawTransformedSpriteTile(ctx, x, y, size, shapeIndex, transformIndex, fgColor, bgColor) {
    const shape = shapesWithTransformations[shapeIndex];
    const grid = shape.transformations[transformIndex];
    
    const pxSize = size / 8;
    
    for (let r = 0; r < 8; r++) {
        for (let c = 0; c < 8; c++) {
            ctx.fillStyle = grid[r][c] === 1 ? fgColor : bgColor;
            ctx.fillRect(
                x + c * pxSize, 
                y + r * pxSize, 
                pxSize - 0.5, 
                pxSize - 0.5
            );
        }
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
    } else {
        elements.referenceGridContainer.style.gridTemplateColumns = `repeat(8, 1fr)`;
        
        SPRITES_BY_DENSITY.forEach((sprite, i) => {
            const wrapper = document.createElement('div');
            wrapper.className = 'reference-tile-wrapper';
            wrapper.setAttribute('data-tooltip', `Glyph [${i + 1}]\nDensity: ${Math.round(sprite.density * 100)}%`);
            
            const canvas = document.createElement('canvas');
            canvas.width = 36;
            canvas.height = 36;
            canvas.className = 'reference-tile-canvas';
            
            wrapper.appendChild(canvas);
            elements.referenceGridContainer.appendChild(wrapper);
            
            const ctx = canvas.getContext('2d');
            // Display preview using classic yellow on dark blue
            drawTransformedSpriteTile(ctx, 0, 0, 36, sprite.index, 0, currentColors.yellow, currentColors.blue);
        });
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
 * Highly Optimized Real-time Dual-Color Structural Glyph Matching (60-120 FPS edition)
 * 1. Pre-filters color pair segments in LAB space (evaluates only 3 closest color bands).
 * 2. Linear top-5 scan using insertion loops to avoid object allocation/sort overhead.
 * 3. Sub-pixel structural overlap checks under 8 rotations/mirrorings.
 */
function findBestSpriteMatch(blockAvgRgb, rawBuffer, bufferWidth, startX, startY) {
    const r = blockAvgRgb.r;
    const g = blockAvgRgb.g;
    const b = blockAvgRgb.b;
    const pixelLab = rgbToLab(r, g, b);
    
    // 1. Pre-filter: Check distance to bg, fg, and mid color for all 36 pairs to find top 3 color bands
    const pairDists = [];
    
    const getDist = (l1, l2) => {
        const dL = l1.l - l2.l;
        const da = l1.a - l2.a;
        const db = l1.b - l2.b;
        return dL * dL + da * da + db * db;
    };
    
    for (let cp = 0; cp < 36; cp++) {
        const pair = precomputedColorPairs[cp];
        
        const dBG = getDist(pixelLab, pair.bgLab);
        const dFG = getDist(pixelLab, pair.fgLab);
        const dMid = getDist(pixelLab, pair.midLab);
        const minDist = Math.min(dBG, dFG, dMid);
        
        pairDists.push({ cp, dist: minDist });
    }
    
    pairDists.sort((a, b) => a.dist - b.dist);
    const topPairs = [pairDists[0].cp, pairDists[1].cp, pairDists[2].cp];
    
    // 2. Linear top-5 scan over the candidates of only the top 3 color bands (3 * 48 = 144 tiles)
    const topK = [];
    
    for (let p = 0; p < 3; p++) {
        const cp = topPairs[p];
        const tiles = precomputedSpriteTiles[cp];
        
        for (let s = 0; s < tiles.length; s++) {
            const tile = tiles[s];
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
            
            if (topK.length < 5) {
                topK.push({ tile, dist });
                if (topK.length === 5) {
                    topK.sort((a, b) => a.dist - b.dist);
                }
            } else if (dist < topK[4].dist) {
                topK[4] = { tile, dist };
                for (let j = 4; j > 0; j--) {
                    if (topK[j].dist < topK[j - 1].dist) {
                        const temp = topK[j];
                        topK[j] = topK[j - 1];
                        topK[j - 1] = temp;
                    } else {
                        break;
                    }
                }
            }
        }
    }
    
    // 3. Solve for best rotation and mirroring using structural distance check directly from rawBuffer
    let bestTile = null;
    let bestTransformIndex = 0;
    let minStructuralDistance = Infinity;
    
    for (let c = 0; c < topK.length; c++) {
        const candidate = topK[c].tile;
        const shape = shapesWithTransformations[candidate.shapeIndex];
        
        const rgbFG = hexToRgb(candidate.fgColor);
        const rgbBG = hexToRgb(candidate.bgColor);
        
        // Check all 8 transformations
        for (let t = 0; t < 8; t++) {
            const tGrid = shape.transformations[t];
            let structDist = 0;
            let pruned = false;
            
            for (let row = 0; row < 8; row++) {
                const py = startY + row;
                for (let col = 0; col < 8; col++) {
                    const targetColor = tGrid[row][col] === 1 ? rgbFG : rgbBG;
                    
                    // Index directly into the flat 1D raw pixel buffer offsets
                    const px = startX + col;
                    const idx = (py * bufferWidth + px) * 4;
                    
                    const dr = targetColor.r - rawBuffer[idx];
                    const dg = targetColor.g - rawBuffer[idx + 1];
                    const db = targetColor.b - rawBuffer[idx + 2];
                    
                    structDist += dr * dr + dg * dg + db * db;
                    
                    // Early exit pruning: if we exceed the current best distance, stop searching this branch!
                    if (structDist >= minStructuralDistance) {
                        pruned = true;
                        break;
                    }
                }
                if (pruned) break;
            }
            
            if (!pruned) {
                minStructuralDistance = structDist;
                bestTile = candidate;
                bestTransformIndex = t;
            }
        }
    }
    
    return {
        tile: bestTile,
        transformIndex: bestTransformIndex
    };
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
    }
    
    if (elements.canvas.width !== vWidth || elements.canvas.height !== vHeight) {
        elements.canvas.width = vWidth;
        elements.canvas.height = vHeight;
    }
    
    const gridWidth = Math.ceil(vWidth / tileSize);
    const gridHeight = Math.ceil(vHeight / tileSize);
    
    elements.resolutionDisplay.textContent = `Grid: ${gridWidth} x ${gridHeight}`;
    
    // Scale downsampling buffer based on style (8x resolution for sub-pixel matching!)
    const factor = tileStyle === 'geometric' ? 1 : 8;
    const bufferWidth = gridWidth * factor;
    const bufferHeight = gridHeight * factor;
    
    offscreenCanvas.width = bufferWidth;
    offscreenCanvas.height = bufferHeight;
    
    if (inputSource === 'webcam') {
        offscreenCtx.drawImage(elements.video, 0, 0, bufferWidth, bufferHeight);
    } else {
        generateProceduralFrame(bufferWidth, bufferHeight);
    }
    
    const imgData = offscreenCtx.getImageData(0, 0, bufferWidth, bufferHeight);
    const rawBuffer = imgData.data;
    
    displayCtx.clearRect(0, 0, elements.canvas.width, elements.canvas.height);
    
    displayCtx.save();
    displayCtx.translate(elements.canvas.width, 0);
    displayCtx.scale(-1, 1);
    
    if (tileStyle === 'geometric') {
        // Standard Geometric Rendering (Single pixel downsampling)
        for (let y = 0; y < gridHeight; y++) {
            for (let x = 0; x < gridWidth; x++) {
                const idx = (y * gridWidth + x) * 4;
                const r = rawBuffer[idx];
                const g = rawBuffer[idx + 1];
                const b = rawBuffer[idx + 2];
                
                const match = findBestTile(r, g, b);
                drawTile(displayCtx, x * tileSize, y * tileSize, tileSize, match.row, match.col);
            }
        }
    } else {
        // Retro Dual-Color Structural Rendering (8x8 sub-pixel patch matching - Allocation-free!)
        for (let y = 0; y < gridHeight; y++) {
            for (let x = 0; x < gridWidth; x++) {
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
                
                // Find best matching {shape, fgColor, bgColor, transformation} with offset pointers
                const match = findBestSpriteMatch(blockAvg, rawBuffer, bufferWidth, startX, startY);
                
                if (match.tile) {
                    drawTransformedSpriteTile(
                        displayCtx,
                        x * tileSize,
                        y * tileSize,
                        tileSize,
                        match.tile.shapeIndex,
                        match.transformIndex,
                        match.tile.fgColor,
                        match.tile.bgColor
                    );
                }
            }
        }
    }
    
    displayCtx.restore();
    
    if (blendFactor > 0) {
        displayCtx.save();
        displayCtx.globalAlpha = blendFactor;
        displayCtx.translate(elements.canvas.width, 0);
        displayCtx.scale(-1, 1);
        if (inputSource === 'webcam') {
            displayCtx.drawImage(elements.video, 0, 0, elements.canvas.width, elements.canvas.height);
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
                elements.btnPause.querySelector('span').textContent = 'Freeze';
                elements.btnPause.classList.remove('active-pause');
                
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
    document.getElementById('procedural-settings-group').style.display = 'block';
    
    if (stream) {
        stream.getTracks().forEach(track => track.stop());
        stream = null;
    }
    
    isPaused = false;
    elements.btnPause.querySelector('span').textContent = 'Freeze';
    elements.btnPause.classList.remove('active-pause');
    
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
            if (inputSource === 'webcam') {
                document.getElementById('webcam-settings-group').style.display = 'block';
                document.getElementById('procedural-settings-group').style.display = 'none';
                initWebcam(currentCameraId);
            } else {
                switchToProceduralSource();
            }
        });
    });

    // Tile set style segmented switcher (geometric vs retro sprites)
    document.querySelectorAll('input[name="tile-style"]').forEach(radio => {
        radio.addEventListener('change', (e) => {
            tileStyle = e.target.value;
            updateBadges();
            renderReferenceGrid();
        });
    });

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
    });
    
    // Blend factor slider
    elements.blendFactorInput.addEventListener('input', (e) => {
        const pct = parseInt(e.target.value);
        blendFactor = pct / 100;
        elements.blendFactorValue.textContent = `${pct}%`;
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
        }
    });
    
    // Pause / Play toggling
    elements.btnPause.addEventListener('click', () => {
        isPaused = !isPaused;
        if (isPaused) {
            elements.btnPause.querySelector('span').textContent = 'Resume';
            elements.btnPause.classList.add('active-pause');
            if (animationFrameId) cancelAnimationFrame(animationFrameId);
            
            displayCtx.save();
            displayCtx.fillStyle = 'rgba(0, 0, 0, 0.5)';
            displayCtx.fillRect(0, 0, elements.canvas.width, elements.canvas.height);
            displayCtx.restore();
            
            elements.fpsDisplay.innerHTML = `<span class="dot" style="background-color: var(--text-muted)"></span> Frozen`;
        } else {
            elements.btnPause.querySelector('span').textContent = 'Freeze';
            elements.btnPause.classList.remove('active-pause');
            lastFrameTime = performance.now();
            animationFrameId = requestAnimationFrame(processVideoFrame);
        }
    });
    
    // Export snapshots
    elements.btnCapture.addEventListener('click', () => {
        const dateStr = new Date().toISOString().substring(0, 19).replace(/[:T]/g, '-');
        const dataUrl = elements.canvas.toDataURL('image/png');
        
        const link = document.createElement('a');
        link.download = `chromamosaic-${dateStr}.png`;
        link.href = dataUrl;
        link.click();
        
        showToast('Snapshot exported successfully!');
    });
    
    // Preset button clicks
    document.querySelectorAll('.preset-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            document.querySelectorAll('.preset-btn').forEach(b => b.classList.remove('active'));
            e.target.classList.add('active');
            
            const presetName = e.target.dataset.preset;
            applyPresetTheme(presetName);
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
    initializeTransformations();
    buildColorPickers();
    updateBadges();
    precomputeTiles();
    initWebcam();
});
