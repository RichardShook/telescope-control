const fs = require('fs');
const path = require('path');
const http = require('http');
const express = require('express');
const { execFile } = require('child_process');
// Optional serial support for mount connectivity checks
let SerialPortLib = null;
try {
  // serialport v10+ CommonJS
  SerialPortLib = require('serialport');
} catch(_) { /* optional */ }
let SerialPort = null;
try { SerialPort = SerialPortLib && (SerialPortLib.SerialPort || SerialPortLib); } catch(_) { SerialPort = null; }

// Express app and middleware (reintroduced)
const app = express();
app.use(express.json({ limit: '200kb' }));
app.use((req,res,next)=>{ console.log('[HTTP]', req.method, req.url); next(); });
const PUBLIC_DIR = path.join(__dirname, 'public');
app.use(express.static(PUBLIC_DIR));

// ---- Core constants and state (restored) ----
// Site coordinates (approx Slater, IA)
let siteLatitudeDeg = parseFloat(process.env.SITE_LAT || '41.88');
let siteLongitudeDeg = parseFloat(process.env.SITE_LON || '-93.68');

// Mechanical resolutions
// RA: define steps per 24h revolution. We use 256000 so steps/hour ~ 10666.67 across 24h,
// matching a ±6h window mapping of 128000 steps around the meridian.
let raStepsPerRev = parseInt(process.env.RA_STEPS_PER_REV || '256000', 10);
// DEC: 51200 steps per 360° (142.22 steps/deg). Half travel (±90°) => 25600 steps
let decStepsPerRev = parseInt(process.env.DEC_STEPS_PER_REV || '51200', 10);

// Absolute mechanical limits
let raMinLimit = 0;
let raMaxLimit = 128000; // 0..128000 absolute mechanical window (±6h around meridian)
let decMinLimit = 0;
let decMaxLimit = 25600; // 0..25600 absolute mechanical window (±90°)

// Positions (absolute mechanical)
let raPosition = 64000;  // firmware home meridian
let decPosition = 12800; // firmware home DEC mid (equator)

// Soft zero + alignment offsets
let raZeroOffsetSteps = 0;
let decZeroOffsetSteps = 0;
let raAlignOffsetSteps = 0;
let decAlignOffsetSteps = 0;

// Pier-specific zero tracking (optional)
let raZeroOffsetEast = 0, decZeroOffsetEast = 0;
let raZeroOffsetWest = 0, decZeroOffsetWest = 0;

// Park state
let parkRaSteps = null, parkDecSteps = null;

// Tracking / integrator
let trackingEnabled = false;
let trackingRateMultiplier = 1.0;
let trackingPpm = 0; // fine ppm trim
let trackingIntervalMs = 250;
let integratorTimer = null;
let lastTrackUpdateMs = Date.now();
let raTrackingFraction = 0;
const SIDEREAL_DAY_MS = 86164090.5; // 23h 56m 4.0905s

// Inversion flags (applied at serial emission layer)
let raInvertActive = true;  // RA inversion default ON per session design
let decInvertActive = false;

// Pier state (advisory only in relative-only model)
let pierFlipState = false;
const PIER_SIDE_INVERT = process.env.PIER_SIDE_INVERT === '1';

// ---- SSE event bus (sendEvent) ----
const sseClients = new Set();
function sendEvent(type, payload){
  const msg = `event: ${type}\n` + `data: ${JSON.stringify(payload)}\n\n`;
  for (const res of sseClients){ try { res.write(msg); } catch(_){} }
}
app.get('/events',(req,res)=>{
  res.writeHead(200, {
    'Content-Type':'text/event-stream',
    'Cache-Control':'no-cache',
    'Connection':'keep-alive',
    'Access-Control-Allow-Origin':'*'
  });
  res.write('\n');
  sseClients.add(res);
  req.on('close', ()=> sseClients.delete(res));
});

// ---- Pier helpers ----
function getHemisphere(decDeg){ return decDeg >= 0 ? 'North' : 'South'; }
function getPierSide(haHours){
  // Convention: HA < 0 (target east of meridian) → East pier; HA ≥ 0 → West pier
  // This matches UI mapping where HA<0 ⇒ 'LstEastPier'.
  const base = haHours < 0 ? 'East' : 'West';
  if (PIER_SIDE_INVERT) return base === 'East' ? 'West' : 'East';
  return base;
}

function resolveDecQuadrant(haHours, decDeg) {
  const pierSide = getPierSide(haHours);
  const hemisphere = getHemisphere(decDeg);

  if (hemisphere === 'North') {
    return pierSide === 'East' ? 'top-left' : 'top-right';
  } else {
    return pierSide === 'East' ? 'bottom-left' : 'bottom-right';
  }
}

// 🧭 SVG Placement Formula (Circular Diagram)
// Maps DEC degrees to circular diagram, split into East/West hemispheres and North/South quadrants
function decToSvgAngle(decDeg, haHours) {
  // Default to HA = 0 (meridian) when HA is missing or invalid
  const validHA = (haHours === undefined || haHours === null || isNaN(haHours)) ? 0 : haHours;
  
  // Special case: DEC = 0° (equator) should anchor to equator line
  if (Math.abs(decDeg) < 0.01) {
    // Place on equator based on pier side only
    return validHA < 0 ? 0 : 180; // East=0° (right), West=180° (left)
  }

  const pierSide = validHA < 0 ? 'East' : 'West';
  const hemisphere = decDeg >= 0 ? 'North' : 'South';

  // Normalize DEC to 0–90 range
  const decAbs = Math.abs(decDeg);
  const offset = (decAbs / 90) * 90; // Each quadrant spans 90°

  // Assign quadrant base angle - proper astronomical positioning
  const quadrantBase = {
    'North-East': 90,    // NE quadrant: DEC > 0, HA < 0
    'North-West': 0,     // NW quadrant: DEC > 0, HA ≥ 0
    'South-East': 180,   // SE quadrant: DEC < 0, HA < 0
    'South-West': 270    // SW quadrant: DEC < 0, HA ≥ 0
  };

  const key = `${hemisphere}-${pierSide}`;
  return quadrantBase[key] + offset;
}

// Enhanced circular DEC dot placement using proper formula
function placeDecDot(haHours, decDeg, radius, cx, cy) {
  // Default to HA = 0 when undefined for mechanically honest placement
  const validHA = (haHours === undefined || haHours === null || isNaN(haHours)) ? 0 : haHours;
  
  const pierSide = getPierSide(validHA);
  const hemisphere = getHemisphere(decDeg);
  const quadrant = resolveDecQuadrant(validHA, decDeg);

  // Use the proper SVG angle formula
  const angleDeg = decToSvgAngle(decDeg, validHA);

  const angleRad = (Math.PI / 180) * angleDeg;
  const x = cx + radius * Math.cos(angleRad);
  const y = cy - radius * Math.sin(angleRad);

  return { 
    x: Math.round(x * 10) / 10,      // Round to 1 decimal for clean SVG
    y: Math.round(y * 10) / 10, 
    quadrant, 
    pierSide,
    hemisphere,
    angleDeg: Math.round(angleDeg * 10) / 10,
    decDeg,
    decAbs: Math.abs(decDeg),
    offset: (Math.abs(decDeg) / 90) * 90,
    quadrantKey: `${hemisphere}-${pierSide}`
  };
}

// Enhanced version with dynamic radius based on DEC magnitude
function placeDecDotScaled(haHours, decDeg, maxRadius, cx, cy, decScale = 0.8) {
  const baseResult = placeDecDot(haHours, decDeg, maxRadius, cx, cy);
  
  // Scale radius based on DEC magnitude (closer to poles = smaller radius)
  const decMagnitude = Math.abs(decDeg);
  const scaledRadius = maxRadius * (1 - (decMagnitude / 90) * decScale);
  
  const angleRad = (Math.PI / 180) * baseResult.angleDeg;
  const x = cx + scaledRadius * Math.cos(angleRad);
  const y = cy - scaledRadius * Math.sin(angleRad);
  
  return {
    ...baseResult,
    x: Math.round(x * 10) / 10,
    y: Math.round(y * 10) / 10,
    scaledRadius: Math.round(scaledRadius * 10) / 10,
    decMagnitude
  };
}

// ---- Focuser State ----
let focuserSteps = 0;           // last known focuser position (steps)
let focuserTarget = null;       // last known commanded target (if reported)
let focuserMoving = 0;          // 1/0 moving flag
let focuserLimit = 0;           // 1/0 limit switch flag
// Logical focuser origin management: when limit sensor is contacted, treat current raw
// position as (2000) and increment from there. We compute focuserSteps logically as
// (rawPos - focuserSoftOrigin). On first limit contact, focuserSoftOrigin = rawPos - 2000.
let focuserSoftOrigin = null;   // raw position offset such that logical = raw - origin
let focuserLastRawPos = null;   // last raw position reported by firmware
const focuserClients = new Set();
app.get('/focuser-status', (req,res)=>{
  res.writeHead(200, { 'Content-Type':'text/event-stream','Cache-Control':'no-cache','Connection':'keep-alive' });
  res.write('\n');
  const c = { res }; focuserClients.add(c);
  req.on('close', ()=> focuserClients.delete(c));
  // Immediately send initial
  try { res.write(`data: ${JSON.stringify({ focuserSteps, focuserTarget, focuserMoving, focuserLimit })}\n\n`); } catch(_){}
});
function broadcastFocuser(){ const payload = `data: ${JSON.stringify({ focuserSteps, focuserTarget, focuserMoving, focuserLimit })}\n\n`; for (const c of focuserClients){ try { c.res.write(payload); } catch(_){} } }

// ---- Serial (Mount + Focuser) Connectivity ----
const mountSerial = { port:null, path:null, baudRate:115200, isOpen:false, lastError:null };
const focuserSerial = { port:null, path:null, baudRate:9600, isOpen:false, lastError:null };
function focuserCandidateSerialPaths(){
  const env = process.env.FOCUSER_SERIAL_PATH ? [process.env.FOCUSER_SERIAL_PATH] : [];
  // Common Linux serial aliases for USB UART bridges
  return [...env, '/dev/ttyUSB1', '/dev/ttyUSB0', '/dev/ttyACM1'];
}

// Auto-identify devices by DEVICE:MOUNT and DEVICE:FOCUSER startup messages
async function identifyDevices() {
  if (!SerialPort) {
    console.warn('[SERIAL] SerialPort not available, skipping device identification');
    return;
  }

  console.log('[SERIAL] Starting device identification scan...');
  const candidates = ['/dev/ttyUSB0', '/dev/ttyUSB1', '/dev/ttyACM0', '/dev/ttyACM1'];
  const baudRates = [9600, 115200]; // Try common rates
  
  console.log(`[SERIAL] Scanning ${candidates.length} ports at ${baudRates.length} baud rates each`);

  // Test each port sequentially to avoid resource conflicts
  for (const path of candidates) {
    // Skip if we've already found both devices
    if (mountSerial.isOpen && focuserSerial.isOpen) break;
    
    let deviceFoundOnThisPort = false;
    for (const baudRate of baudRates) {
      // Skip if we've already found both devices
      if (mountSerial.isOpen && focuserSerial.isOpen) break;
      // Skip remaining baud rates if device already found on this port
      if (deviceFoundOnThisPort) break;
      
      const beforeMount = mountSerial.isOpen;
      const beforeFocuser = focuserSerial.isOpen;
      
      await tryIdentifyDevice(path, baudRate);
      
      // Check if a device was identified on this attempt
      if ((!beforeMount && mountSerial.isOpen && mountSerial.path === path) ||
          (!beforeFocuser && focuserSerial.isOpen && focuserSerial.path === path)) {
        deviceFoundOnThisPort = true;
      }
    }
  }
  
  // Log final assignments
  if (mountSerial.port && mountSerial.isOpen) {
    console.log(`[MOUNT] Auto-identified at ${mountSerial.path}@${mountSerial.baudRate}`);
  } else {
    console.warn('[MOUNT] Not identified via startup messages');
  }
  
  if (focuserSerial.port && focuserSerial.isOpen) {
    console.log(`[FOCUSER] Auto-identified at ${focuserSerial.path}@${focuserSerial.baudRate}`);
  } else {
    console.warn('[FOCUSER] Not identified via startup messages');
  }
}

function tryIdentifyDevice(path, baudRate) {
  return new Promise((resolve) => {
    console.log(`[SERIAL] Trying ${path}@${baudRate}...`);
    let port = null;
    
    const cleanup = () => {
      if (port && port.isOpen) {
        port.close((err) => {
          if (err) console.log(`[SERIAL] Error closing ${path}@${baudRate}: ${err.message}`);
          setTimeout(resolve, 100); // Small delay to ensure port is fully released
        });
      } else {
        setTimeout(resolve, 100);
      }
    };
    
    const timeout = setTimeout(() => {
      console.log(`[SERIAL] Timeout for ${path}@${baudRate}`);
      cleanup();
    }, 3000); // 3 second timeout per attempt

    try {
      port = new SerialPort({ path, baudRate, autoOpen: false });
      
      port.open((err) => {
        if (err) {
          console.log(`[SERIAL] Failed to open ${path}@${baudRate}: ${err.message}`);
          clearTimeout(timeout);
          resolve();
          return;
        }
        console.log(`[SERIAL] Opened ${path}@${baudRate}, listening for device messages...`);

        let buffer = '';
        port.on('data', (chunk) => {
          try {
            buffer += chunk.toString('utf8');
            let idx;
            while ((idx = buffer.indexOf('\n')) >= 0) {
              const line = buffer.slice(0, idx).replace(/\r$/, '').trim();
              buffer = buffer.slice(idx + 1);
              
              if (line.includes('DEVICE:MOUNT') && !mountSerial.isOpen) {
                mountSerial.port = port;
                mountSerial.path = path;
                mountSerial.baudRate = baudRate;
                mountSerial.isOpen = true;
                mountSerial.lastError = null;
                console.log(`[MOUNT] Identified at ${path}@${baudRate}`);
                clearTimeout(timeout);
                setupMountSerial();
                resolve();
                return;
              } else if (line.includes('DEVICE:FOCUSER') && !focuserSerial.isOpen) {
                focuserSerial.port = port;
                focuserSerial.path = path;
                focuserSerial.baudRate = baudRate;
                focuserSerial.isOpen = true;
                focuserSerial.lastError = null;
                console.log(`[FOCUSER] Identified at ${path}@${baudRate}`);
                clearTimeout(timeout);
                setupFocuserSerial();
                resolve();
                return;
              }
            }
          } catch(_) { /* ignore parse errors */ }
        });

        port.on('error', () => {
          clearTimeout(timeout);
          cleanup();
        });
      });
    } catch(_) {
      clearTimeout(timeout);
      resolve();
    }
  });
}

function setupMountSerial() {
  if (!mountSerial.port) return;
  
  mountSerial.buffer = '';
  mountSerial.port.on('data', (chunk) => {
    try {
      mountSerial.buffer += chunk.toString('utf8');
      let idx;
      while((idx = mountSerial.buffer.indexOf('\n')) >= 0){
        const line = mountSerial.buffer.slice(0, idx);
        mountSerial.buffer = mountSerial.buffer.slice(idx+1);
        parseSerialLine(line.replace(/\r$/, ''), 'mount');
      }
      if (mountSerial.buffer.length > 4096){
        mountSerial.buffer = mountSerial.buffer.slice(-1024);
      }
    } catch(_) { /* ignore parse errors */ }
  });

  mountSerial.port.on('close', () => { mountSerial.isOpen = false; });
  mountSerial.port.on('error', (e) => { mountSerial.lastError = e.message; });

  // Start polling timer
  if (mountSerial.pollTimer) clearInterval(mountSerial.pollTimer);
  mountSerial.pollTimer = setInterval(() => {
    if(!mountSerial.port || !mountSerial.isOpen) return;
    try {
      mountSerial.port.write(`GET_POS${MOUNT_EOL}`);
      mountSerial.port.write(`GET_STATUS${MOUNT_EOL}`);
      mountSerial.port.write(`GET_TRACK_STATUS${MOUNT_EOL}`);
    } catch(_) { /* ignore */ }
  }, 2000);

  // Push initial safety/limits configuration after connect
  setTimeout(() => {
    try {
      if (mountSerial.port && mountSerial.isOpen) {
        const raMin = Math.max(0, raMinLimit);
        const raMax = Math.min(128000, raMaxLimit);
        const decMin = Math.max(0, decMinLimit);
        const decMax = Math.min(25600, decMaxLimit);
        writeMountSerial(`SET_RA_LIMITS:${raMin},${raMax}`);
        writeMountSerial(`SET_DEC_LIMITS:${decMin},${decMax}`);
        writeMountSerial('LIMITS_ENABLE:1');
        // Ensure tracking starts disabled until the UI explicitly turns it on
        writeMountSerial('TRACK:0');
        // Snapshot
        writeMountSerial('GET_STATUS');
        writeMountSerial('GET_POS');
        writeMountSerial('GET_TRACK_STATUS');
      }
    } catch(_) { /* ignore init errors */ }
  }, 400);
}

function setupFocuserSerial() {
  if (!focuserSerial.port) return;

  focuserSerial.buffer = '';
  focuserSerial.port.on('data', (chunk) => {
    try {
      focuserSerial.buffer += chunk.toString('utf8');
      let idx;
      while((idx = focuserSerial.buffer.indexOf('\n')) >= 0){
        const line = focuserSerial.buffer.slice(0, idx);
        focuserSerial.buffer = focuserSerial.buffer.slice(idx+1);
        parseSerialLine(line.replace(/\r$/, ''), 'focuser');
      }
      if (focuserSerial.buffer.length > 4096) focuserSerial.buffer = focuserSerial.buffer.slice(-1024);
    } catch(_) { }
  });

  focuserSerial.port.on('close', () => { focuserSerial.isOpen = false; });
  focuserSerial.port.on('error', (e) => { focuserSerial.lastError = e.message; });

  // Poll focuser every ~3s
  if (focuserSerial.pollTimer) clearInterval(focuserSerial.pollTimer);
  focuserSerial.pollTimer = setInterval(() => {
    if(!focuserSerial.port || !focuserSerial.isOpen) return;
    try { focuserSerial.port.write('STATUS\r\n'); } catch(_) { }
  }, 3000);
  
  try { focuserSerial.port.write('STATUS\r\n'); } catch(_) { }
}

function initSerialDevices() {
  // Auto-identify devices instead of hardcoded paths
  identifyDevices().catch(e => {
    console.error('[SERIAL] Device identification failed:', e.message);
  });
}

// Per-port write queues
function makeQueue(portRef, lineEnding='\n'){
  const q = { buf:[], busy:false, ref: portRef, lineEnding };
  q.enqueue = (cmd)=>{
    // Append line ending if no newline present
    const hasNl = /[\r\n]$/.test(cmd);
    q.buf.push(hasNl ? cmd : (cmd + q.lineEnding));
    pump(q);
  };
  function pump(queue){
    if (queue.busy) return;
    if (!queue.ref.port || !queue.ref.isOpen) { queue.buf.length = 0; return; }
    const next = queue.buf.shift();
    if (!next) return;
    queue.busy = true;
    try {
      queue.ref.port.write(next, (err)=>{
        setTimeout(()=>{ queue.busy = false; pump(queue); }, err? 10 : 40);
      });
    } catch(_){ queue.busy = false; }
  }
  return q;
}
// Mount EOL configurable: '\n' or '\r\n'
const MOUNT_EOL = process.env.MOUNT_EOL || '\n';
const mountQueue = makeQueue(mountSerial, MOUNT_EOL);
// Many focuser firmwares expect CRLF; use it for compatibility.
const focuserQueue = makeQueue(focuserSerial, '\r\n');
function enqueueSerial(cmd){ mountQueue.enqueue(cmd); }
function enqueueFocuser(cmd){ 
  console.log(`[FOCUSER-TX] Sending: "${cmd}"`);
  focuserQueue.enqueue(cmd); 
}

// Helper: write to mount serial (queued, newline auto-added)
function serialTxLog(cmd, source='mount'){
  const ts = Date.now();
  serialPushLine({ ts, type:'TX', raw: String(cmd).trim(), source });
}

// Helper: optionally invert RA/DEC step direction at the command layer
function maybeInvertMoveCommand(cmd){
  try {
    const m = String(cmd).match(/^(RA|DEC)_MOVE:([+-]?)(\d+)$/);
    if (!m) return String(cmd);
    const axis = m[1];
    const sign = m[2] === '-' ? -1 : 1;
    const mag = parseInt(m[3], 10) || 0;
    let steps = sign * mag;
    if (axis === 'RA' && raInvertActive) steps = -steps;
    if (axis === 'DEC' && decInvertActive) steps = -steps;
    return `${axis}_MOVE:${steps}`; // for positive numbers, JS string omits '+'
  } catch(_){
    return String(cmd);
  }
}

// Helper: write to mount serial (direct write with EOL + TX log)
const writeMountSerial = (command) => {
  // Apply per-axis inversion only to MOVE commands; all other commands pass-through
  const transformed = maybeInvertMoveCommand(command);
  const trimmed = String(transformed);
  if (mountSerial.port && mountSerial.isOpen) {
    try {
      const fullCommand = trimmed + (MOUNT_EOL || '\n');
      serialTxLog(trimmed, 'mount');
      mountSerial.port.write(fullCommand, (err) => {
        if (err) {
          console.error(`Serial Write Error: ${err.message} for command: ${trimmed}`);
        } else {
          try { mountSerial.port.drain(); } catch(_){}
        }
      });
      // console.log(`Sent mount command: ${trimmed}`);
    } catch(e) {
      console.error(`Serial Exception during write: ${e.message}`);
    }
  } else {
    console.warn(`[MOUNT] Command ignored - no mount connected: ${trimmed}`);
    // For debugging: log that we're in software-only mode
    if (trimmed.includes('_MOVE:')) {
      console.log(`[MOUNT] Software simulation: ${trimmed} (no hardware movement)`);
    }
  }
};

// Format STEP command style: 'colon' -> STEP_RA:100, 'space' -> STEP_RA 100
function formatStepCommand(axis, steps){
  const style = process.env.MOUNT_STEP_STYLE || 'colon'; // 'colon'|'space'
  const token = axis==='RA' ? 'STEP_RA' : 'STEP_DEC';
  return style === 'space' ? `${token} ${steps}` : `${token}:${steps}`;
}

// ---- Parsed serial telemetry ring buffer ----
const serialParsed = { lines:[], max:200, lastPos:null, lastStatus:null, lastTrackStatus:null, lastAck:null, lastError:null, lastDebug:null };
function serialPushLine(entry){
  serialParsed.lines.push(entry);
  if (serialParsed.lines.length > serialParsed.max) serialParsed.lines.splice(0, serialParsed.lines.length - serialParsed.max);
  // Categorize most recent
  const { type } = entry;
  if (type === 'POS') serialParsed.lastPos = entry;
  else if (type === 'STATUS') serialParsed.lastStatus = entry;
  else if (type === 'TRACK_STATUS') serialParsed.lastTrackStatus = entry;
  else if (type === 'ACK') serialParsed.lastAck = entry;
  else if (type === 'ERR') serialParsed.lastError = entry;
  else if (type === 'DEBUG') serialParsed.lastDebug = entry;
}
function parseSerialLine(line, source){
  const raw = line.trim();
  if(!raw) return;
  const ts = Date.now();
  // POS:RA:123456,DEC:-8420
  if (raw.startsWith('POS:')){
    // extract RA and DEC numbers
    // Accept patterns RA:<num>,DEC:<num>
    let raMatch = raw.match(/RA:([+-]?\d+)/);
    let decMatch = raw.match(/DEC:([+-]?\d+)/);
    const ra = raMatch? parseInt(raMatch[1],10): null;
    const dec = decMatch? parseInt(decMatch[1],10): null;
  serialPushLine({ ts, type:'POS', raw, raSteps: ra, decSteps: dec, source });
    // If both values present, update internal positions (hardware authoritative)
    if (Number.isFinite(ra) && Number.isFinite(dec)){
      function clamp(v,min,max){ if(min!=null&&v<min)return min; if(max!=null&&v>max)return max; return v; }
      const newRa = clamp(ra, raMinLimit, raMaxLimit);
      const newDec = clamp(dec, decMinLimit, decMaxLimit);
      let changed = false;
      if (newRa !== raPosition){ raPosition = newRa; changed = true; }
      if (newDec !== decPosition){ decPosition = newDec; changed = true; }
      if (changed){ saveState(); broadcastMount(); }
    }
    return;
  }
  if (raw.startsWith('STATUS:')){
    const rest = raw.substring(7).split(/[,\s]+/).filter(Boolean);
    // Example focuser STATUS:pos=1234,target=2234,moving=1,limit=0
    let posKV = Object.create(null);
    for(const token of rest){ const kv = token.split('='); if(kv.length===2) posKV[kv[0]]=kv[1]; }
    const prevLimit = focuserLimit;
    let rawPos = null;
    if (posKV.pos){ const v=parseInt(posKV.pos,10); if(Number.isFinite(v)){ rawPos = v; focuserLastRawPos = v; } }
    if (posKV.target){ const v=parseInt(posKV.target,10); if(Number.isFinite(v)){ focuserTarget = v; } }
    if (posKV.moving!=null){ const v=parseInt(posKV.moving,10); if(Number.isFinite(v)){ focuserMoving = v; } }
    if (posKV.limit!=null){ const v=parseInt(posKV.limit,10); if(Number.isFinite(v)){ focuserLimit = v; } }

    // On first transition to limit=1, set logical origin so logical position starts at 2000
    if (focuserLimit === 1 && prevLimit !== 1){
      if (Number.isFinite(rawPos)) {
        focuserSoftOrigin = rawPos - 2000;
        focuserSteps = 2000; // initialize logical reading
      } else if (Number.isFinite(focuserLastRawPos)) {
        focuserSoftOrigin = focuserLastRawPos - 2000;
        focuserSteps = 2000;
      } else {
        // No raw position available; seed logical at 2000 and wait for next raw pos to align
        focuserSoftOrigin = null;
        focuserSteps = 2000;
      }
    } else {
      // Normal updates: if we have an origin, compute logical from raw; otherwise pass through raw
      if (Number.isFinite(rawPos)){
        if (Number.isFinite(focuserSoftOrigin)){
          focuserSteps = rawPos - focuserSoftOrigin;
        } else {
          focuserSteps = rawPos;
        }
      }
    }
    if (Object.keys(posKV).length) broadcastFocuser();
    serialPushLine({ ts, type:'STATUS', raw, states: rest, parsed: posKV, source });
    return;
  }
  if (raw.startsWith('POSITION:')){
    const v = parseInt(raw.substring('POSITION:'.length),10);
    if (Number.isFinite(v)) { focuserSteps = v; broadcastFocuser(); }
    serialPushLine({ ts, type:'POSITION', raw, steps: Number.isFinite(v)? v : null, source });
    return;
  }
  if (raw.startsWith('TRACK_STATUS:')){
    const rest = raw.substring('TRACK_STATUS:'.length).trim();
    serialPushLine({ ts, type:'TRACK_STATUS', raw, status: rest, source });
    return;
  }
  if (raw.startsWith('ACK:')){
    serialPushLine({ ts, type:'ACK', raw, message: raw.substring(4), source });
    return;
  }
  if (raw.startsWith('ERR:')){
    serialPushLine({ ts, type:'ERR', raw, message: raw.substring(4), source });
    return;
  }
  if (raw.startsWith('DEBUG:')){
    serialPushLine({ ts, type:'DEBUG', raw, message: raw.substring(6), source });
    return;
  }
  // Unknown - store as generic
  serialPushLine({ ts, type:'RAW', raw, source });
}

async function openMountSerial(path, baudRate){
  if(!SerialPort){ mountSerial.lastError='serialport-not-installed'; return { ok:false, error:'serialport-not-installed' }; }
  if(mountSerial.port && mountSerial.isOpen){ if(path===mountSerial.path) return { ok:true, path:mountSerial.path, baudRate:mountSerial.baudRate }; await closeMountSerial(); }
  return new Promise((resolve)=>{
    try {
      const port = new SerialPort({ path, baudRate: baudRate||115200, autoOpen:true });
      mountSerial.port = port; mountSerial.path = path; mountSerial.baudRate = baudRate||115200; mountSerial.isOpen=false; mountSerial.lastError=null;
      port.on('open', ()=>{ mountSerial.isOpen=true; resolve({ ok:true, path:mountSerial.path, baudRate:mountSerial.baudRate }); });
      port.on('error', (e)=>{ mountSerial.lastError=e.message; resolve({ ok:false, error:e.message }); });
      port.on('close', ()=>{ mountSerial.isOpen=false; });
      // Data listener with simple line buffering (\n or \r\n) using UTF-8
      mountSerial.buffer = '';
      port.on('data', (chunk)=>{
        try {
          mountSerial.buffer += chunk.toString('utf8');
          let idx;
            while((idx = mountSerial.buffer.indexOf('\n')) >= 0){
              const line = mountSerial.buffer.slice(0, idx); // exclude \n
              mountSerial.buffer = mountSerial.buffer.slice(idx+1);
              parseSerialLine(line.replace(/\r$/, ''), 'mount');
            }
          // Safety: prevent unbounded buffer if no newline
          if (mountSerial.buffer.length > 4096){
            mountSerial.buffer = mountSerial.buffer.slice(-1024);
          }
        } catch(_){ /* ignore parse errors */ }
      });
      // Start polling timer (stop previous first)
      if (mountSerial.pollTimer) clearInterval(mountSerial.pollTimer);
      mountSerial.pollTimer = setInterval(()=>{
        if(!mountSerial.port || !mountSerial.isOpen) return;
        try {
          port.write(`GET_POS${MOUNT_EOL}`);
          port.write(`GET_STATUS${MOUNT_EOL}`);
          port.write(`GET_TRACK_STATUS${MOUNT_EOL}`);
        } catch(_){ /* ignore */ }
      }, 2000);
    } catch(e){ mountSerial.lastError=e.message; resolve({ ok:false, error:e.message }); }
  });
}
async function closeMountSerial(){
  return new Promise((resolve)=>{
    if(mountSerial.pollTimer){ clearInterval(mountSerial.pollTimer); mountSerial.pollTimer=null; }
    if(mountSerial.port){ try { mountSerial.port.close(()=>{ mountSerial.isOpen=false; mountSerial.port=null; resolve({ ok:true }); }); } catch(e){ resolve({ ok:false, error:e.message }); } }
    else resolve({ ok:true });
  });
}
function serialStatus(){ return { supported: !!SerialPort, connected: !!mountSerial.port && mountSerial.isOpen, path: mountSerial.path||null, baudRate: mountSerial.baudRate||null, lastError: mountSerial.lastError||null }; }
function candidateSerialPaths(){ const env = process.env.MOUNT_SERIAL_PATH ? [process.env.MOUNT_SERIAL_PATH] : []; return [...env, '/dev/ttyACM0', '/dev/ttyACM1', '/dev/ttyUSB0', '/dev/ttyUSB1']; }

// ---- Focuser Serial Open/Close ----
async function openFocuserSerial(path, baudRate){
  if(!SerialPort){ focuserSerial.lastError='serialport-not-installed'; return { ok:false, error:'serialport-not-installed' }; }
  if(focuserSerial.port && focuserSerial.isOpen){ if(path===focuserSerial.path) return { ok:true, path:focuserSerial.path, baudRate:focuserSerial.baudRate }; await closeFocuserSerial(); }
  return new Promise((resolve)=>{
    try {
      const port = new SerialPort({ path, baudRate: baudRate||9600, autoOpen:true });
      focuserSerial.port = port; focuserSerial.path = path; focuserSerial.baudRate = baudRate||9600; focuserSerial.isOpen=false; focuserSerial.lastError=null;
      port.on('open', ()=>{ focuserSerial.isOpen=true; resolve({ ok:true, path:focuserSerial.path, baudRate:focuserSerial.baudRate }); });
      port.on('error', (e)=>{ focuserSerial.lastError=e.message; resolve({ ok:false, error:e.message }); });
      port.on('close', ()=>{ focuserSerial.isOpen=false; });
      focuserSerial.buffer='';
      port.on('data', (chunk)=>{
        try {
          focuserSerial.buffer += chunk.toString('utf8');
          let idx;
          while((idx = focuserSerial.buffer.indexOf('\n')) >= 0){
            const line = focuserSerial.buffer.slice(0, idx);
            focuserSerial.buffer = focuserSerial.buffer.slice(idx+1);
            parseSerialLine(line.replace(/\r$/, ''), 'focuser');
          }
          if (focuserSerial.buffer.length > 4096) focuserSerial.buffer = focuserSerial.buffer.slice(-1024);
        } catch(_){ }
      });
      // Poll focuser every ~3s
      if (focuserSerial.pollTimer) clearInterval(focuserSerial.pollTimer);
      focuserSerial.pollTimer = setInterval(()=>{
        if(!focuserSerial.port || !focuserSerial.isOpen) return;
        try { port.write('STATUS\r\n'); } catch(_) { }
      }, 3000);
      try { port.write('STATUS\r\n'); } catch(_) { }
    } catch(e){ focuserSerial.lastError=e.message; resolve({ ok:false, error:e.message }); }
  });
}
async function closeFocuserSerial(){
  return new Promise((resolve)=>{
    if(focuserSerial.pollTimer){ clearInterval(focuserSerial.pollTimer); focuserSerial.pollTimer=null; }
    if(focuserSerial.port){ try { focuserSerial.port.close(()=>{ focuserSerial.isOpen=false; focuserSerial.port=null; resolve({ ok:true }); }); } catch(e){ resolve({ ok:false, error:e.message }); } }
    else resolve({ ok:true });
  });
}
function focuserSerialStatus(){ return { supported: !!SerialPort, connected: !!focuserSerial.port && focuserSerial.isOpen, path: focuserSerial.path||null, baudRate: focuserSerial.baudRate||null, lastError: focuserSerial.lastError||null }; }

// Serial endpoints
app.get('/serial/status',(req,res)=>{ res.json(serialStatus()); });
app.get('/serial/ports', async (req,res)=>{
  try {
    if(!SerialPort || !SerialPort.list) return res.json({ supported: !!SerialPort, ports: candidateSerialPaths().map(p=>({ path:p, probable:true })) });
    const ports = await SerialPort.list();
    res.json({ supported:true, ports });
  } catch(e){ res.status(500).json({ error:'list-failed', detail:e.message }); }
});
app.post('/serial/connect', async (req,res)=>{
  const { path, baudRate } = req.body||{};
  if(!path) return res.status(400).json({ error:'no-path' });
  const result = await openMountSerial(path, baudRate);
  if(!result.ok) return res.status(500).json(result);
  res.json({ ok:true, status: serialStatus() });
});
app.post('/serial/disconnect', async (req,res)=>{ const r = await closeMountSerial(); if(!r.ok) return res.status(500).json(r); res.json({ ok:true, status: serialStatus() }); });
app.post('/serial/auto-connect', async (req,res)=>{
  const baudRate = (req.body||{}).baudRate || 115200;
  const candidates = candidateSerialPaths();
  for (const p of candidates){ const r = await openMountSerial(p, baudRate); if(r.ok) return res.json({ ok:true, status: serialStatus(), tried:candidates }); }
  res.status(500).json({ ok:false, error:'no-ports-opened', tried:candidates, status: serialStatus() });
});

// Re-scan and identify devices
app.post('/serial/rescan', async (req,res) => {
  try {
    // Close existing connections
    if (mountSerial.port) { try { mountSerial.port.close(); } catch(_) {} }
    if (focuserSerial.port) { try { focuserSerial.port.close(); } catch(_) {} }
    
    // Reset state
    mountSerial.port = null; mountSerial.isOpen = false;
    focuserSerial.port = null; focuserSerial.isOpen = false;
    
    // Re-identify
    await identifyDevices();
    
    res.json({ 
      ok: true, 
      mount: { connected: mountSerial.isOpen, path: mountSerial.path, baudRate: mountSerial.baudRate },
      focuser: { connected: focuserSerial.isOpen, path: focuserSerial.path, baudRate: focuserSerial.baudRate }
    });
  } catch(e) {
    res.status(500).json({ error: 'rescan-failed', detail: e.message });
  }
});
app.post('/serial/test', async (req,res)=>{
  if(!mountSerial.port || !mountSerial.isOpen) return res.status(400).json({ error:'not-connected' });
  try {
    const payload = (req.body&&req.body.payload) || 'PING\n';
    mountSerial.port.write(payload, (err)=>{
      if(err) return res.status(500).json({ error:'write-failed', detail:err.message });
      mountSerial.port.drain(()=> res.json({ ok:true, wrote: payload.length }));
    });
  } catch(e){ res.status(500).json({ error:'serial-exception', detail:e.message }); }
});

// Focuser serial endpoints
app.get('/focuser/serial/status',(req,res)=>{ res.json(focuserSerialStatus()); });
app.get('/focuser/serial/ports', async (req,res)=>{
  try {
    if(!SerialPort || !SerialPort.list){
      return res.json({ supported: !!SerialPort, ports: focuserCandidateSerialPaths().map(p=>({ path:p, probable:true })) });
    }
    const ports = await SerialPort.list();
    res.json({ supported:true, ports });
  } catch(e){ res.status(500).json({ error:'list-failed', detail:e.message }); }
});
app.post('/focuser/serial/connect', async (req,res)=>{
  const { path, baudRate } = req.body||{};
  if(!path) return res.status(400).json({ error:'no-path' });
  const r = await openFocuserSerial(path, baudRate);
  if(!r.ok) return res.status(500).json(r);
  res.json({ ok:true, status: focuserSerialStatus() });
});
app.post('/focuser/serial/disconnect', async (req,res)=>{
  const r = await closeFocuserSerial(); if(!r.ok) return res.status(500).json(r); res.json({ ok:true, status: focuserSerialStatus() });
});
app.post('/focuser/serial/test', async (req,res)=>{
  const s = focuserSerialStatus();
  if (!s.connected || !focuserSerial.port) return res.status(400).json({ error:'not-connected' });
  try {
    const payload = (req.body&&req.body.payload) || 'STATUS\r\n';
    focuserSerial.port.write(payload, (err)=>{
      if(err) return res.status(500).json({ error:'write-failed', detail:err.message });
      focuserSerial.port.drain(()=> res.json({ ok:true, wrote: payload.length }));
    });
  } catch(e){ res.status(500).json({ error:'serial-exception', detail:e.message }); }
});
// Try to auto-connect focuser by scanning common device paths and baud rates.
app.post('/focuser/serial/auto-connect', async (req,res)=>{
  const body = req.body||{};
  const baudRates = Array.isArray(body.baudRates) && body.baudRates.length ? body.baudRates : [9600, 19200, 38400, 57600, 115200];
  const candidates = focuserCandidateSerialPaths();
  if(!SerialPort){ return res.status(500).json({ ok:false, error:'serialport-not-installed' }); }
  let lastError = null; const tried=[];
  for (const p of candidates){
    for (const b of baudRates){
      tried.push({ path:p, baudRate:b });
      const r = await openFocuserSerial(p, b);
      if (r && r.ok){ return res.json({ ok:true, status: focuserSerialStatus(), tried }); }
      lastError = (r && r.error) || 'open-failed';
    }
  }
  res.status(500).json({ ok:false, error:'no-focuser-ports-opened', lastError, tried, status: focuserSerialStatus() });
});

// --- Simplified focuser endpoints (aliases) ---
app.get('/focuser/ports', async (req,res)=>{
  try {
    if(!SerialPort || !SerialPort.list){
      return res.json({ ok:true, ports: focuserCandidateSerialPaths().map(p=>({ path:p })) });
    }
    const ports = await SerialPort.list();
    res.json({ ok:true, ports });
  } catch(e){ res.status(500).json({ ok:false, error:'list-failed', message:e.message }); }
});
app.post('/focuser/connect', async (req,res)=>{
  const { path: p, baudRate } = req.body || {};
  try {
    if (p){
      const r = await openFocuserSerial(p, baudRate || 9600);
      if (!r.ok) return res.json({ status:'error', message: r.error || 'open-failed' });
      return res.json({ status:'connected', port: r.path, baudRate: r.baudRate });
    }
    // No path: auto-connect
    const baudRates = [9600, 19200, 38400, 57600, 115200];
    const candidates = focuserCandidateSerialPaths();
    let lastErr = 'open-failed';
    for (const cp of candidates){
      for (const b of baudRates){
        const r = await openFocuserSerial(cp, b);
        if (r && r.ok){ return res.json({ status:'connected', port: r.path, baudRate: r.baudRate }); }
        lastErr = (r && r.error) || lastErr;
      }
    }
    return res.json({ status:'error', message: lastErr });
  } catch(e){ return res.json({ status:'error', message: e.message }); }
});
app.post('/focuser/disconnect', async (req,res)=>{
  try { await closeFocuserSerial(); return res.json({ status:'disconnected' }); }
  catch(e){ return res.json({ status:'error', message: e.message }); }
});

// Recent serial parsed log
app.get('/serial/log',(req,res)=>{
  const { limit } = req.query||{};
  let n = parseInt(limit,10); if(!Number.isFinite(n) || n<=0 || n>serialParsed.max) n = 50;
  const lines = serialParsed.lines.slice(-n);
  res.json({ ok:true, lines, last:{ pos: serialParsed.lastPos, status: serialParsed.lastStatus, track: serialParsed.lastTrackStatus, ack: serialParsed.lastAck, error: serialParsed.lastError, debug: serialParsed.lastDebug } });
});

// Manual hardware sync: request fresh POS / STATUS and return latest cached after small delay
app.post('/mount-sync-from-hardware', async (req,res)=>{
  const serial = serialStatus();
  if (!serial.connected || !mountSerial.port) return res.status(400).json({ error:'not-connected' });
  try {
    mountSerial.port.write(`GET_POS${MOUNT_EOL}`);
    mountSerial.port.write(`GET_STATUS${MOUNT_EOL}`);
    mountSerial.port.write(`GET_TRACK_STATUS${MOUNT_EOL}`);
  } catch(e){ return res.status(500).json({ error:'write-failed', detail:e.message }); }
  // Wait briefly (configurable?)
  setTimeout(()=>{
    res.json({ ok:true, last:{ pos: serialParsed.lastPos, status: serialParsed.lastStatus, track: serialParsed.lastTrackStatus }, raSteps: raPosition, decSteps: decPosition });
  }, 150);
});

app.post('/focuser',(req,res)=>{
  const cmd = (req.body||{}).command;
  if (typeof cmd !== 'string') return res.status(400).json({ error:'invalid-command' });
  const m = cmd.match(/^([+-])(\d+)$/);
  if (!m) return res.status(400).json({ error:'unsupported-format' });
  const sign = m[1] === '+' ? 1 : -1;
  const steps = parseInt(m[2],10);
  focuserSteps += sign * steps;
  broadcastFocuser();
  res.json({ ok:true, focuserSteps });
});

// Focuser serial move (uses shared serial queue if connected)
app.post('/focuser/move', (req,res)=>{
  const { steps } = req.body||{}; // positive=in, negative=out per firmware doc
  if (!Number.isFinite(steps) || steps===0) return res.status(400).json({ error:'invalid-steps' });
  const s = focuserSerialStatus();
  if (!s.connected || !focuserSerial.port) return res.status(400).json({ error:'not-connected' });
  enqueueFocuser(`${steps>0?'+':'-'}${Math.abs(parseInt(steps,10))}`);
  enqueueFocuser('STATUS');
  res.json({ ok:true });
});

app.post('/focuser/stop', (req,res)=>{
  const s = focuserSerialStatus();
  if (!s.connected || !focuserSerial.port) return res.status(400).json({ error:'not-connected' });
  enqueueFocuser('STOP');
  enqueueFocuser('STATUS');
  res.json({ ok:true });
});

// Ask firmware for STATUS immediately
app.post('/focuser/status', (req,res)=>{
  const s = focuserSerialStatus();
  if (!s.connected || !focuserSerial.port) return res.status(400).json({ error:'not-connected' });
  enqueueFocuser('STATUS');
  res.json({ ok:true });
});

// Simple GOTO by delta: computes delta to target from last known focuserSteps
app.post('/focuser/goto', (req,res)=>{
  const { target } = req.body||{};
  if (!Number.isFinite(target)) return res.status(400).json({ error:'invalid-target' });
  const s = focuserSerialStatus();
  if (!s.connected || !focuserSerial.port) return res.status(400).json({ error:'not-connected' });
  const delta = Math.round(target - (focuserSteps||0));
  if (delta === 0){ enqueueFocuser('STATUS'); return res.json({ ok:true, noop:true }); }
  enqueueFocuser(`${delta>0?'+':'-'}${Math.abs(delta)}`);
  enqueueFocuser('STATUS');
  res.json({ ok:true, delta });
});

// ---- Persistence ----
const STATE_FILE = path.join(__dirname,'mount_state.json');
function saveState(){
  try {
    fs.writeFileSync(STATE_FILE, JSON.stringify({
      raPosition, decPosition,
      raZeroOffsetSteps, decZeroOffsetSteps,
      raZeroOffsetEast, decZeroOffsetEast,
      raZeroOffsetWest, decZeroOffsetWest,
      raAlignOffsetSteps, decAlignOffsetSteps,
      trackingEnabled, pierFlipState,
      raInvertActive, decInvertActive,
      parkRaSteps, parkDecSteps
    }, null, 2));
  } catch(e){ console.warn('[state-save]', e.message); }
}
(function load(){
  try {
    if (fs.existsSync(STATE_FILE)){
      const d = JSON.parse(fs.readFileSync(STATE_FILE,'utf8'));
      raPosition=d.raPosition??raPosition;
      decPosition=d.decPosition??decPosition;
      raZeroOffsetSteps=d.raZeroOffsetSteps??raZeroOffsetSteps;
      decZeroOffsetSteps=d.decZeroOffsetSteps??decZeroOffsetSteps;
      raZeroOffsetEast=d.raZeroOffsetEast??raZeroOffsetEast;
      decZeroOffsetEast=d.decZeroOffsetEast??decZeroOffsetEast;
      raZeroOffsetWest=d.raZeroOffsetWest??raZeroOffsetWest;
      decZeroOffsetWest=d.decZeroOffsetWest??decZeroOffsetWest;
      raAlignOffsetSteps=d.raAlignOffsetSteps??raAlignOffsetSteps;
      decAlignOffsetSteps=d.decAlignOffsetSteps??decAlignOffsetSteps;
      trackingEnabled=d.trackingEnabled??trackingEnabled;
      pierFlipState=d.pierFlipState??pierFlipState;
      parkRaSteps=d.parkRaSteps??parkRaSteps;
      parkDecSteps=d.parkDecSteps??parkDecSteps;
      // Optional persisted invert state
      if (typeof d.raInvertActive === 'boolean') raInvertActive = d.raInvertActive;
      if (typeof d.decInvertActive === 'boolean') decInvertActive = d.decInvertActive;
    }
  } catch(e){ console.warn('[state-load]', e.message); }
})();

// ---- Conversions ----
function raStepsToReportedHours(steps){ 
  // Remove zero offset and alignment to get raw absolute position
  const rel = steps - raZeroOffsetSteps - raAlignOffsetSteps; 
  
  // Calculate relative position from meridian (64000 steps = 0 relative)
  let relativeSteps = rel - 64000;  // Positive = CW from meridian, Negative = CCW from meridian
  
  // Convert relative steps to relative hours
  // Negative steps = positive hours (CCW tracking), Positive steps = negative hours (CW)
  let relativeHours = -(relativeSteps / (128000/12));  // 10666.67 steps/hour
  
  // Convert back to absolute RA hours (6h = meridian)
  let h = 6 + relativeHours;
  
  // Ensure result is in 0-24h range
  return ((h % 24)+24)%24; 
}
function reportedHoursToRaSteps(h){ 
  // Normalize to 0..24h
  const h24 = ((h % 24) + 24) % 24; 
  
  // Compute delta from meridian reference (6h) in the range [-12, +12]
  // Example: 22h -> delta = 16 -> -8; 14h -> delta = 8
  let deltaFrom6 = h24 - 6;
  if (deltaFrom6 > 12) deltaFrom6 -= 24;
  if (deltaFrom6 < -12) deltaFrom6 += 24;
  const relativeHours = deltaFrom6;
  
  // Convert relative hours to absolute steps about 64000 (meridian)
  const stepsPerHour = 128000/12; // 10666.67 steps/hour across ±6h
  let steps = 64000 - (relativeHours * stepsPerHour);
  
  // Apply soft zero/alignment offsets
  steps = steps + raZeroOffsetSteps + raAlignOffsetSteps;
  
  // Clamp to hardware absolute range [0,128000]
  if (steps > 128000) steps = 128000;
  if (steps < 0) steps = 0;
  
  return Math.round(steps);
}
function decStepsToReportedDeg(steps){
  // Inverse of decToSteps with 51200/360 resolution
  const raw = (typeof steps==='number'? steps: 0) - decZeroOffsetSteps - decAlignOffsetSteps;
  const clamped = Math.max(decMinLimit, Math.min(decMaxLimit, raw));
  const deg = 90 - ((clamped / decStepsPerRev) * 360);
  return Math.max(-90, Math.min(90, deg));
}
// DEC degrees -> mechanical steps helper
// Overload behavior:
//  - If stepsPerDeg provided (4th arg), do simple linear mapping for utility API
//  - Otherwise, map celestial DEC [-90..+90] to mechanical steps [0..25600] with soft zero/alignment
function decToSteps(decDeg, min=0, sec=0, stepsPerDeg){
  if (typeof stepsPerDeg === 'number'){
    const total = (Number(decDeg)||0) + (Number(min)||0)/60 + (Number(sec)||0)/3600;
    return Math.round(total * stepsPerDeg);
  }
  let d = Math.max(-90, Math.min(90, Number(decDeg)||0));
  // +90° => 0 steps; -90° => 25600 steps (half of 51200 per full 360)
  const mechDeg = 90 - d; // 0..180
  const mechSteps = Math.round((mechDeg / 360) * decStepsPerRev); // 0..25600
  const steps = mechSteps + decZeroOffsetSteps + decAlignOffsetSteps;
  return Math.max(decMinLimit, Math.min(decMaxLimit, steps));
}
// Generic inverse for API utility when stepsPerDeg given
function stepsToDec(steps, stepsPerDeg){
  const spd = Number(stepsPerDeg)||1;
  const total = (Number(steps)||0) / spd;
  const sign = total < 0 ? -1 : 1;
  const abs = Math.abs(total);
  const deg = Math.trunc(abs);
  const minFloat = (abs - deg) * 60;
  const min = Math.trunc(minFloat);
  const sec = Math.round((minFloat - min) * 60);
  return { deg: sign*deg, min, sec };
}
function decDegToDualSolutions(decDeg){ if (decDeg>90) decDeg=90; if (decDeg<-90) decDeg=-90; let mechA=90-decDeg; if (mechA<0) mechA+=360; let mechB=(mechA+180)%360; const toSteps=m=>Math.round((m/360)*decStepsPerRev)+decZeroOffsetSteps+decAlignOffsetSteps; return { primary: toSteps(mechA), alternate: toSteps(mechB) }; }
function chooseDecByRaDirection(decDeg, raDelta){ 
  const sols=decDegToDualSolutions(decDeg); 
  if(!raDelta) return { steps: sols.primary, meta:{ reason:'no-ra-delta', sols } }; 
  // Choose DEC solution based on RA direction: 
  // Positive RA delta (moving east) → use primary solution
  // Negative RA delta (moving west) → use alternate solution
  return { steps: raDelta>0?sols.primary:sols.alternate, meta:{ reason:'ra-sign', raDelta, sols } }; 
}

function chooseDecByHourAngle(decDeg, haHours){ 
  // Generate both mechanical solutions for this celestial DEC
  const sols = decDegToDualSolutions(decDeg);
  
  // Range helpers
  const inRange = (v,min,max)=> v>=min && v<=max;
  const clamp = (v,min,max)=> (v<min?min:(v>max?max:v));
  const primaryIn = inRange(sols.primary, decMinLimit, decMaxLimit);
  const alternateIn = inRange(sols.alternate, decMinLimit, decMaxLimit);

  let chosen = null; let reason = '';
  // 1) Prefer a solution that is within limits so the requested DEC is actually achieved
  if (primaryIn && !alternateIn){ chosen = sols.primary; reason = 'within-limits-primary'; }
  else if (alternateIn && !primaryIn){ chosen = sols.alternate; reason = 'within-limits-alternate'; }
  else if (primaryIn && alternateIn){
    // 2) Both valid: choose minimal actual movement
    const dP = Math.abs(sols.primary - decPosition);
    const dA = Math.abs(sols.alternate - decPosition);
    if (dP < dA){ chosen = sols.primary; reason = 'min-motion-primary'; }
    else if (dA < dP){ chosen = sols.alternate; reason = 'min-motion-alternate'; }
    else {
      // Tie-breaker: pier-side expectation
      chosen = (haHours < 0) ? sols.alternate : sols.primary;
      reason = (haHours < 0) ? 'tie-east-pier-alternate' : 'tie-west-pier-primary';
    }
  } else {
    // 3) Both out of range: fall back to clamped minimal motion
    const pC = clamp(sols.primary, decMinLimit, decMaxLimit);
    const aC = clamp(sols.alternate, decMinLimit, decMaxLimit);
    const dP = Math.abs(pC - decPosition);
    const dA = Math.abs(aC - decPosition);
    if (dP <= dA){ chosen = pC; reason = 'both-out-clamped-primary'; }
    else { chosen = aC; reason = 'both-out-clamped-alternate'; }
  }

  // Ensure final chosen steps respect limits
  const finalSteps = clamp(chosen, decMinLimit, decMaxLimit);
  return { steps: finalSteps, meta:{ reason, haHours, sols, limits:{min:decMinLimit,max:decMaxLimit} } };
}

// ---- Astronomy Helpers ----
function julianDate(date){
  const year = date.getUTCFullYear();
  let month = date.getUTCMonth() + 1;
  const day = date.getUTCDate() + (date.getUTCHours() + (date.getUTCMinutes() + date.getUTCSeconds()/60)/60)/24;
  let Y = year; let M = month;
  if (month <= 2) { Y -= 1; M += 12; }
  const A = Math.floor(Y/100);
  const B = 2 - A + Math.floor(A/4);
  return Math.floor(365.25*(Y + 4716)) + Math.floor(30.6001*(M + 1)) + day + B - 1524.5;
}
function gmst(date){
  const JD = julianDate(date);
  const T = (JD - 2451545.0)/36525.0;
  let gmstSec = 67310.54841 + (876600*3600 + 8640184.812866)*T + 0.093104*T*T - 6.2e-6*T*T*T;
  gmstSec = ((gmstSec % 86400) + 86400) % 86400;
  return gmstSec / 3600.0; // hours
}
function localSiderealTimeHours(date){
  let h = gmst(date) + (siteLongitudeDeg/15);
  return ((h%24)+24)%24;
}
function normalizeHoursRange12(h){ return ((h + 12) % 24) - 12; }

function computeHA(lstHours, raHours) {
  let ha = lstHours - raHours;
  if (ha < -12) ha += 24;
  if (ha > 12) ha -= 24;
  return ha;
}

function computeHourAngleHours(raHours, lstHours){
  return computeHA(lstHours, raHours);
}
function computeAltitudeDeg(decDeg, lstHours, raHours){
  const haHours = computeHourAngleHours(raHours, lstHours);
  const haRad = (haHours*15) * Math.PI/180;
  const latRad = siteLatitudeDeg * Math.PI/180;
  const decRad = decDeg * Math.PI/180;
  const sinAlt = Math.sin(latRad)*Math.sin(decRad) + Math.cos(latRad)*Math.cos(decRad)*Math.cos(haRad);
  return { altitudeDeg: Math.asin(Math.min(1,Math.max(-1,sinAlt)))*180/Math.PI, haHours };
}

// ---- HA → Steps conversion helpers ----
function parseHmsToHours(hms){
  if (hms == null) return null;
  if (typeof hms === 'number' && Number.isFinite(hms)) return hms;
  if (typeof hms !== 'string') return null;
  const s = hms.trim();
  const m = s.match(/^([+-]?\d+)(?::(\d+))?(?::(\d+(?:\.\d+)?))?$/);
  if (!m) return null;
  const sign = m[1].startsWith('-') ? -1 : 1;
  const H = Math.abs(parseInt(m[1],10)) || 0;
  const M = m[2] != null ? parseInt(m[2],10) : 0;
  const S = m[3] != null ? parseFloat(m[3]) : 0;
  return sign * (H + (M/60) + (S/3600));
}
function normalizeHaHours(ha){
  // Constrain HA to [-12, +12] hours, preserving sign (wrap at 24h)
  let x = ha;
  while (x <= -12) x += 24;
  while (x > 12) x -= 24;
  return x;
}
function haHoursToRaSteps(haHours){
  const ha = normalizeHaHours(haHours);
  const stepsPerHour = 128000/12; // 10666.67 steps per hour across ±6h about meridian
  const haSteps = ha * stepsPerHour;
  // RA absolute target centered at 64000: target = 64000 - haSteps
  let target = 64000 - haSteps;
  if (target < 0) target = 0;
  if (target > 128000) target = 128000;
  return Math.round(target);
}

// ---- RA shortest-path helper (within absolute model) ----
// Computes the minimal signed delta to reach target from current without using wrap-around cycles.
// For absolute RA in [raMinLimit..raMaxLimit] and safety of half-rev, the shortest legal path is direct delta.
// If that exceeds half-rev, we still cap by safety (caller enforces). We include a variant tag for logging.
function shortestRaDelta(currentSteps, targetSteps){
  const direct = targetSteps - currentSteps;
  const half = raStepsPerRev / 2;
  // Direct path is the only legal path to the absolute target.
  const variant = Math.abs(direct) <= half ? 'direct' : 'over-half-direct';
  return { delta: direct, variant };
}

// ---- Direction assurance helper (probe and correct) ----
async function ensureAxisDirection(axis, desiredRotation, deltaSign, options={}){
  // axis: 'RA' | 'DEC'
  // desiredRotation: 'CCW' | 'CW' | null (rotation we want for positive forward motion)
  // deltaSign: -1 | 0 | +1 (sign of intended axis change toward target)
  // options: { probeSteps?: number, settleMs?: number }
  if (!mountSerial.port || !mountSerial.isOpen) return { ok:false, reason:'no-serial' };
  if (!desiredRotation || !deltaSign) return { ok:true, reason:'no-op' };
  const probeSteps = Math.max(4, Math.min(128, options.probeSteps || 16));
  const settleMs = Math.max(40, Math.min(300, options.settleMs || 120));
  const opposite = d => (d==='CCW'?'CW':d==='CW'?'CCW':null);
  // Choose direction to send for a forward probe according to deltaSign
  const dirToSend = deltaSign >= 0 ? desiredRotation : opposite(desiredRotation);
  const send = (cmd)=>{ try { writeMountSerial(cmd); } catch(_){ } };
  // Stop tracking and axis
  send('TRACK:0');
  if (axis==='RA') send('RA_STOP'); else send('DEC_STOP');
  // Set intended DIR
  send(`${axis}_DIR:${dirToSend}`);
  // Read starting position
  send('GET_POS');
  await new Promise(r=>setTimeout(r, settleMs));
  const key = axis==='RA' ? 'raSteps' : 'decSteps';
  const before = (serialParsed.lastPos && typeof serialParsed.lastPos[key]==='number') ? serialParsed.lastPos[key] : (axis==='RA'? raPosition : decPosition);
  // Probe a tiny forward move
  send(`${axis}_MOVE:${probeSteps}`);
  await new Promise(r=>setTimeout(r, settleMs + 40));
  send('GET_POS');
  await new Promise(r=>setTimeout(r, settleMs));
  const after = (serialParsed.lastPos && typeof serialParsed.lastPos[key]==='number') ? serialParsed.lastPos[key] : before;
  const moved = after - before;
  const ok = moved === 0 ? true : (Math.sign(moved) === Math.sign(deltaSign));
  // Move back (reverse the probe) to avoid position drift
  // Reverse DIR then move forward same magnitude
  send(`${axis}_DIR:${opposite(dirToSend)}`);
  await new Promise(r=>setTimeout(r, 40));
  send(`${axis}_MOVE:${probeSteps}`);
  await new Promise(r=>setTimeout(r, settleMs));
  // Restore intended DIR for the upcoming motion
  const finalDir = ok ? dirToSend : opposite(dirToSend);
  send(`${axis}_DIR:${finalDir}`);
  return { ok:true, corrected: !ok, sent: finalDir };
}

// ---- Broadcast ----
function broadcastMount(){ sendEvent('mount', { raSteps: raPosition, decSteps: decPosition, raHours: raStepsToReportedHours(raPosition), decDeg: decStepsToReportedDeg(decPosition), tracking: trackingEnabled, raInvertActive, decInvertActive }); }

// ---- RA/DEC timeline helpers ----
const RA_STEPS_PER_HOUR = raStepsPerRev / 24;
function haHoursFromNow(){ const lst = localSiderealTimeHours(new Date()); const raH = raStepsToReportedHours(raPosition); return ((lst - raH + 12) % 24) - 12; }
function haToRaTimelineSteps(haHours){ return Math.round(-haHours * RA_STEPS_PER_HOUR); }
function currentRaTimelineSteps(){ return haToRaTimelineSteps(haHoursFromNow()); }
function decDegToTimelineSteps(decDeg, haHours){
  const sPerDeg = decStepsPerRev/360; // 142.22 steps/deg
  const mag = Math.round((90 - Math.max(-90, Math.min(90, decDeg))) * sPerDeg);
  const sign = haHours<0 ? +1 : (haHours>0 ? -1 : 0);
  // 180° mechanical window => max ±12800 from equator reference
  const cap = 12800;
  return Math.max(-cap, Math.min(cap, sign * Math.min(mag, cap)));
}
function currentDecTimelineSteps(){ const ha = haHoursFromNow(); const dd = decStepsToReportedDeg(decPosition); return decDegToTimelineSteps(dd, ha); }
setInterval(broadcastMount, 2000);

// ---- GOTO (Relative-only movement) ----
app.post('/mount-goto', async (req,res)=>{
  // Simple de-duplication: ignore identical targets arriving within a short window
  const nowMs = Date.now();
  const key = JSON.stringify({ raHours:req.body?.raHours, raSteps:req.body?.raSteps, decDeg:req.body?.decDeg, decSteps:req.body?.decSteps });
  if (!global.__lastGoto) global.__lastGoto = { key:null, ts:0 };
  if (global.__lastGoto.key === key && (nowMs - global.__lastGoto.ts) < 600) {
    console.warn('GOTO de-duplicated: identical target within 600ms');
    return res.json({ ok:true, dedup:true, message:'duplicate goto ignored' });
  }
  global.__lastGoto = { key, ts: nowMs };
  const { raHours, raSteps, decDeg, decSteps } = req.body || {};
  
  // Log all input values received
  console.log(`GOTO INPUT: raHours=${raHours}, raSteps=${raSteps}, decDeg=${decDeg}, decSteps=${decSteps}`);
  console.log(`GOTO CONSTANTS: RA=${raStepsPerRev} steps/24h (${(raStepsPerRev/24).toFixed(2)} steps/hour), DEC=${decStepsPerRev} steps/360° (${(decStepsPerRev/360).toFixed(2)} steps/degree)`);
  
  // Parse target coordinates (RA timeline mapping)
  let targetRa = null; let haFromRa = null;
  if (typeof raSteps === 'number') {
    // Treat provided steps as RA timeline steps directly (-64000..+64000)
    targetRa = Math.max(raMinLimit, Math.min(raMaxLimit, raSteps));
    console.log(`GOTO: Using direct RA timeline steps input: ${targetRa}`);
  } else if (typeof raHours === 'number') {
    // Compute HA then convert to timeline steps relative to 0 (meridian)
    const lstNow = localSiderealTimeHours(new Date());
    haFromRa = computeHourAngleHours(raHours, lstNow);
    targetRa = haToRaTimelineSteps(haFromRa);
    console.log(`GOTO: RA ${raHours}h with LST ${lstNow.toFixed(3)}h => HA ${haFromRa.toFixed(3)}h => timeline ${targetRa} steps`);
  }
  
  // Decide DEC target. If DEC degrees provided, pick the mechanical solution that makes DEC move opposite to RA.
  let targetDec = null;
  if (typeof decSteps === 'number') {
    // Mechanical absolute steps (0..51200)
    targetDec = Math.max(decMinLimit, Math.min(decMaxLimit, decSteps));
    console.log(`GOTO: Using direct DEC steps input: ${targetDec}`);
  } else if (typeof decDeg === 'number') {
    // Convert dec degrees to mechanical steps over 180° range
    targetDec = decToSteps(decDeg);
    const sPerDeg = decStepsPerRev/180;
    const haForSign = (haFromRa==null) ? (((localSiderealTimeHours(new Date()) - (raStepsToReportedHours(raPosition)) + 12)%24)-12) : haFromRa;
    const timelineSign = haForSign < 0 ? +1 : (haForSign > 0 ? -1 : 0);
    const tlMag = Math.round((90 - Math.max(-90, Math.min(90, decDeg))) * sPerDeg);
    const tl = timelineSign * Math.min(tlMag, 25600);
    console.log(`GOTO: DEC deg ${decDeg} => mech ${targetDec} steps; timeline ${tl} (sign by HA ${haForSign?.toFixed?.(3)})`);
  }
  
  // Validate inputs
  if (targetRa == null || targetDec == null) {
    console.log(`GOTO ERROR: Invalid input - targetRa=${targetRa}, targetDec=${targetDec}`);
    return res.status(400).json({ error: 'invalid-input' });
  }
  
  // Clamp to limits
  targetRa = Math.max(raMinLimit, Math.min(raMaxLimit, targetRa));
  targetDec = Math.max(decMinLimit, Math.min(decMaxLimit, targetDec));
  
  // Debug coordinate calculations
  // For reporting: compute HA and pier
  const targetRaHours = (function(){ const lst=localSiderealTimeHours(new Date()); const ha= (haFromRa!=null?haFromRa:(((lst - raStepsToReportedHours(raPosition) + 12)%24)-12)); return ((lst - ha + 24)%24); })();
  const targetDecDeg = decStepsToReportedDeg(targetDec);
  const lst = localSiderealTimeHours(new Date());
  const haHours = (haFromRa!=null) ? haFromRa : computeHourAngleHours(targetRaHours, lst);
  const expectedPier = getPierSide(haHours);
  // Relative-only: no pin inversion or meridian flip decisions; pier is advisory only
  let desiredRaRotation = haHours < 0 ? 'CCW' : (haHours > 0 ? 'CW' : null);
  let desiredDecDir = null; // informational only
  
  console.log(`GOTO DEBUG: Target RA=${targetRaHours.toFixed(3)}h (${targetRa} steps), DEC=${targetDecDeg.toFixed(2)}° (${targetDec} steps)`);
  console.log(`GOTO DEBUG: Current RA=${raPosition} steps, DEC=${decPosition} steps`);
  console.log(`GOTO DEBUG: LST=${lst.toFixed(3)}h, HA=${haHours.toFixed(3)}h, Expected Pier=${expectedPier}`);
  
  // Calculate deltas with RA shortest-path helper (keeps relative-only motion)
  console.log(`GOTO CURRENT POSITION: RA=${raPosition} steps (${raStepsToReportedHours(raPosition).toFixed(3)}h), DEC=${decPosition} steps (${decStepsToReportedDeg(decPosition).toFixed(3)}°)`);
  console.log(`GOTO TARGET POSITION: RA=${targetRa} steps (${raStepsToReportedHours(targetRa).toFixed(3)}h), DEC=${targetDec} steps (${decStepsToReportedDeg(targetDec).toFixed(3)}°)`);

  // Determine RA delta using shortest path (bounded by safety later)
  const raChoice = shortestRaDelta(raPosition, targetRa);
  let raDelta = raChoice.delta;
  const decDelta = (targetDec - decPosition);
  // Keep DEC desired direction for logging (opposite of RA)
  const opposite = d => (d === 'CCW' ? 'CW' : d === 'CW' ? 'CCW' : null);
  const desiredDecRotation = desiredRaRotation ? opposite(desiredRaRotation) : null;
  desiredDecDir = desiredDecRotation;
  
  // Send absolute position commands directly to hardware
  // NOTE: Hardware expects raw step counts, no inversion needed
  // The coordinate conversion functions handle the proper transformations
  const serial = serialStatus();
  if (serial.connected && mountSerial.port) {
    try {
      // Safety prelude: ensure tracking is off and axes are stopped before commanding movement
      try { writeMountSerial('TRACK:0'); } catch(_){ }
      try { writeMountSerial('RA_STOP'); writeMountSerial('DEC_STOP'); } catch(_){ }
      // Re-assert limits for safety
      try {
        const raMin = Math.max(0, raMinLimit);
        const raMax = Math.min(128000, raMaxLimit);
        writeMountSerial(`SET_RA_LIMITS:${raMin},${raMax}`);
        writeMountSerial(`SET_DEC_LIMITS:${decMinLimit},${decMaxLimit}`);
        writeMountSerial('LIMITS_ENABLE:1');
      } catch(_){ }
      
  console.log(`GOTO RAW DELTAS: RA=${raDelta} steps (${(raDelta/raStepsPerRev*360).toFixed(3)}°) [variant=${raChoice.variant}], DEC=${decDelta} steps (${(decDelta/decStepsPerRev*360).toFixed(3)}°)`);
      
  // Relative-only movement
      console.log(`GOTO FINAL DELTAS: RA=${raDelta} steps (${(raDelta/raStepsPerRev*360).toFixed(3)}°), DEC=${decDelta} steps (${(decDelta/decStepsPerRev*360).toFixed(3)}°)`);
      
      // Safety check: prevent excessively large movements
  const raMaxSafeMove = raStepsPerRev / 2;   // allow up to 12h (half revolution)
  // Allow DEC moves up to 180° (full mechanical travel within [0..25600])
  // Previously 90° blocked valid moves such as from +90° to -10° (100°)
  const decMaxSafeMove = 25600; // 180° window (±25600)
      if (Math.abs(raDelta) > raMaxSafeMove) {
        console.error(`GOTO BLOCKED: RA delta ${raDelta} exceeds safe limit ${raMaxSafeMove}`);
        return res.status(400).json({ 
          error: 'unsafe-movement', 
          message: `RA movement ${raDelta} steps exceeds safe limit`,
          maxSafeMove: raMaxSafeMove,
          variant: raChoice.variant
        });
      }
      if (Math.abs(decDelta) > decMaxSafeMove) {
        console.error(`GOTO BLOCKED: DEC delta ${decDelta} exceeds safe limit ${decMaxSafeMove}`);
        return res.status(400).json({ 
          error: 'unsafe-movement', 
          message: `DEC movement ${decDelta} steps exceeds safe limit`,
          maxSafeMove: decMaxSafeMove
        });
      }
      
  // Send signed relative moves; no DIR or MERIDIAN_FLIP
  // Route through writeMountSerial so optional inversion is applied
  writeMountSerial(`RA_MOVE:${raDelta}`);
  writeMountSerial(`DEC_MOVE:${decDelta}`);
      console.log(`GOTO: Sent relative RA_MOVE:${raDelta}, DEC_MOVE:${decDelta}`);
      
      // Update software state
      raPosition = raPosition + raDelta;
      decPosition = decPosition + decDelta;
      saveState();
      
      // Broadcast slewing state for real-time indicator
      sendEvent('mount-slewing', {
        target: { raSteps: targetRa, decSteps: targetDec },
        current: { raSteps: raPosition, decSteps: decPosition },
        status: 'slewing'
      });
      
      // Request status update
      setTimeout(() => {
        try {
          if (mountSerial.port && mountSerial.isOpen) {
            writeMountSerial('GET_STATUS');
            writeMountSerial('GET_POS');
          }
        } catch(e) { console.warn('Status request failed:', e.message); }
      }, 500);
      // Small settle window
      await new Promise(r=>setTimeout(r, 150));
      
      // Log movement summary for verification  
  const raHours = raDelta * 24 / raStepsPerRev;
  const decDeg = (decDelta / (decStepsPerRev/180));
  console.log(`GOTO: Movement summary - RA: ${raHours.toFixed(3)}h (${raDelta} steps), DEC: ${decDeg.toFixed(2)}° (${decDelta} steps)`);

      // Resume sidereal tracking if enabled
      if (trackingEnabled) {
        try { writeMountSerial('TRACK:1'); } catch(_){ }
      }
      
    } catch(e) {
      console.error('GOTO ABSOLUTE failed:', e.message);
      return res.status(500).json({ error: 'hardware-error', message: e.message });
    }
  } else {
    console.warn('GOTO: No hardware connection, updating software state only (relative)');
    raPosition = raPosition + raDelta;
    decPosition = decPosition + decDelta;
    saveState();
  }
  
  // Send success response with movement details
  res.json({
    ok: true,
  method: 'relative-move-timeline',
    target: {
      raSteps: targetRa,
      decSteps: targetDec,
      raHours: raStepsToReportedHours(targetRa),
      decDeg: decStepsToReportedDeg(targetDec)
    },
    movement: {
      raSteps: raDelta,
      decSteps: decDelta,
  raHours: raDelta * 24 / raStepsPerRev,
  decDeg: (decDelta / (decStepsPerRev/180))
    },
    current: {
      raSteps: raPosition,
      decSteps: decPosition
    },
    pierSide: expectedPier
  });
});

// ---- GOTO using HA directly (relative-only) ----
// Body: { ha: "H:M:S" | number, decDeg?: number, decSteps?: number }
app.post('/mount-goto-ha', async (req,res)=>{
  try {
    const { ha, decDeg, decSteps } = req.body || {};
    const haHours = parseHmsToHours(ha);
    if (!Number.isFinite(haHours)) return res.status(400).json({ error:'invalid-ha' });

  // Convert HA to RA timeline steps: raTimeline = -HA * stepsPerHour
  let targetRa = haToRaTimelineSteps(haHours);

    // Compute DEC target: choose solution that makes DEC move opposite to RA movement
    let targetDec = null; let decMeta = null;
    if (typeof decSteps === 'number') {
      targetDec = Math.max(decMinLimit, Math.min(decMaxLimit, decSteps));
      decMeta = { reason:'direct-steps' };
    } else if (typeof decDeg === 'number') {
      targetDec = decToSteps(decDeg);
      decMeta = { reason:'mechanical-51200/180' };
    } else {
      return res.status(400).json({ error:'invalid-dec' });
    }

    // Clamp targets
    targetRa = Math.max(raMinLimit, Math.min(raMaxLimit, targetRa));
    targetDec = Math.max(decMinLimit, Math.min(decMaxLimit, targetDec));

  // Decide DEC direction to oppose RA motion (filled after raDelta computed)
  let desiredDecDir = null;

    const serial = serialStatus();
    let raDelta = targetRa - raPosition;
    const decDelta = targetDec - decPosition;
    if (raDelta !== 0) desiredDecDir = raDelta > 0 ? 'CCW' : 'CW';

    if (serial.connected && mountSerial.port){
      try {
        // Safety prelude: stop tracking and motion, reassert limits
        try { writeMountSerial('TRACK:0'); } catch(_){ }
        try { writeMountSerial('RA_STOP'); writeMountSerial('DEC_STOP'); } catch(_){ }
        try {
          const raMin = Math.max(0, raMinLimit);
          const raMax = Math.min(128000, raMaxLimit);
          writeMountSerial(`SET_RA_LIMITS:${raMin},${raMax}`);
          writeMountSerial(`SET_DEC_LIMITS:${decMinLimit},${decMaxLimit}`);
          writeMountSerial('LIMITS_ENABLE:1');
        } catch(_){ }
        // Safety: half-rev RA, half-rev DEC (full ±90° range)
        const raMaxSafeMove = raStepsPerRev / 2;
  const decMaxSafeMove = 25600; // full 180° window allowed
        if (Math.abs(raDelta) > raMaxSafeMove){
          return res.status(400).json({ error:'unsafe-movement', axis:'RA', max: raMaxSafeMove, delta: raDelta, variant: raChoice.variant });
        }
        if (Math.abs(decDelta) > decMaxSafeMove){
          return res.status(400).json({ error:'unsafe-movement', axis:'DEC', max: decMaxSafeMove, delta: decDelta });
        }
        // Send signed relative moves; no pin flips
  writeMountSerial(`RA_MOVE:${raDelta}`);
  writeMountSerial(`DEC_MOVE:${decDelta}`);
  raPosition = raPosition + raDelta; 
  decPosition = decPosition + decDelta; 
        saveState();

        // Request status update
  setTimeout(()=>{ try { writeMountSerial('GET_STATUS'); writeMountSerial('GET_POS'); } catch(_){} }, 300);
  if (trackingEnabled) { try { writeMountSerial('TRACK:1'); } catch(_){} }
      } catch(e){
        return res.status(500).json({ error:'hardware-error', detail:e.message });
      }
    } else {
      raPosition = targetRa; decPosition = targetDec; saveState();
    }

  res.json({ ok:true, method:'ha-goto-relative', input:{ ha, haHours }, target:{ raSteps: targetRa, decSteps: targetDec }, decMeta, deltas:{ ra: raDelta, dec: decDelta }, decDirection: desiredDecDir });
  } catch(e){
    res.status(500).json({ error:'goto-ha-failed', detail: e.message });
  }
});

// ---- EMERGENCY STOP ----
app.post('/mount/emergency-stop', (req, res) => {
  console.log('EMERGENCY STOP: Halting all motor movements');
  
  const serial = serialStatus();
  if (serial.connected && mountSerial.port) {
    try {
      // Send immediate stop commands to hardware
      writeMountSerial('RA_STOP');
      writeMountSerial('DEC_STOP');
      writeMountSerial('HALT_ALL');
      
      console.log('EMERGENCY STOP: Commands sent - RA_STOP, DEC_STOP, HALT_ALL');
      
      // Request status update
      setTimeout(() => {
        try {
          if (mountSerial.port && mountSerial.isOpen) {
            writeMountSerial('GET_STATUS');
            writeMountSerial('GET_POS');
          }
        } catch(e) { console.warn('Status request after emergency stop failed:', e.message); }
      }, 100);
      
    } catch(e) {
      console.error('Emergency stop hardware command failed:', e.message);
    }
  }
  
  // Always respond success for emergency stop
  res.json({
    ok: true,
    message: 'Emergency stop executed',
    timestamp: new Date().toISOString()
  });
});

// Endpoint to evaluate pier flip necessity without executing a goto
app.post('/mount-evaluate-pier', (req,res)=>{
  const { raHours, raSteps } = req.body||{};
  const lstNow = localSiderealTimeHours(new Date());
  const stepsPerHour = RA_STEPS_PER_HOUR; // 256000/24
  let ha = null;
  let targetTimelineSteps = null;
  if (typeof raHours === 'number') {
    // HA = LST - RA (normalized to ±12h)
    ha = computeHourAngleHours(raHours, lstNow);
    targetTimelineSteps = haToRaTimelineSteps(ha); // -HA * steps/hour
  } else if (typeof raSteps === 'number') {
    // Treat provided steps as RA timeline steps directly (±64000)
    targetTimelineSteps = raSteps;
    ha = -(targetTimelineSteps / stepsPerHour);
  }
  if (!Number.isFinite(ha)) return res.status(400).json({ error:'invalid-input' });
  // Clamp timeline steps to ±64000 for reporting consistency
  const tlCap = raStepsPerRev/4; // 64000
  targetTimelineSteps = Math.max(-tlCap, Math.min(tlCap, Math.round(targetTimelineSteps)));
  // Derive RA hours from HA and LST
  const targetRaHours = ((lstNow - ha + 24) % 24);
  const desiredPier = getPierSide(ha);
  res.json({ ok:true, targetRaSteps: targetTimelineSteps, targetRaHours, hourAngle: ha, desiredPier });
});

// Dry-run endpoint is deprecated and will be removed.
app.post('/mount-goto-dry-run',(req,res)=>{
  res.status(410).json({ error: 'deprecated', message: 'The dry-run endpoint is no longer available.' });
});

// ---- Nudge ----
app.post('/nudge',(req,res)=>{ const { raSteps=0, decSteps=0 } = req.body || {}; if(!Number.isFinite(raSteps)||!Number.isFinite(decSteps)) return res.status(400).json({ error:'invalid' }); let newRa=raPosition+raSteps, newDec=decPosition+decSteps; if(newRa<raMinLimit)newRa=raMinLimit; else if(newRa>raMaxLimit)newRa=raMaxLimit; if(newDec<decMinLimit)newDec=decMinLimit; else if(newDec>decMaxLimit)newDec=decMaxLimit; raPosition=newRa; decPosition=newDec; saveState(); broadcastMount(); res.json({ status:'nudged', raSteps:raPosition, decSteps:decPosition }); });

// Alias: UI calls /mount/nudge with { axis, steps, mode }
app.post('/mount/nudge', (req,res)=>{
  const { axis, steps, mode } = req.body || {};
  if (!['RA','DEC'].includes(axis)) return res.status(400).json({ error:'bad-axis' });
  if (!Number.isFinite(steps)) return res.status(400).json({ error:'no-steps' });
  const delta = parseInt(steps,10) || 0;
  let sent = null;
  let blocked = false;
  const alignMode = mode === 'align';
  if (axis === 'RA'){
    let np = raPosition + delta;
    let originalNp = np;
    if (np < raMinLimit) { np = raMinLimit; blocked = true; } 
    else if (np > raMaxLimit) { np = raMaxLimit; blocked = true; }
    
    if (np !== raPosition){
      // Use signed relative move; no DIR
  sent = `RA_MOVE:${delta}`;
  // Route through writeMountSerial so optional inversion is applied
  writeMountSerial(sent);
      console.log(`RA motor command: ${sent} (relative nudge by ${delta}, target ${np})`);
    } else if (blocked && !alignMode) {
      // Movement blocked by limits
      const limitType = originalNp < raMinLimit ? 'minimum' : 'maximum';
      console.log(`RA movement blocked: would exceed ${limitType} limit (${originalNp} -> ${np})`);
      return res.json({ 
        ok: false, 
        error: 'limit-blocked',
        message: `RA movement blocked by ${limitType} limit`,
        axis, 
        requestedSteps: delta,
        currentSteps: raPosition,
        limitReached: np
      });
    }
    raPosition = np;
  } else {
    let np = decPosition + delta;
    let originalNp = np;
    if (np < decMinLimit) { np = decMinLimit; blocked = true; }
    else if (np > decMaxLimit) { np = decMaxLimit; blocked = true; }
    
    if (np !== decPosition){
      // Use signed relative move; no DIR
  sent = `DEC_MOVE:${delta}`;
  // Route through writeMountSerial so optional inversion is applied
  writeMountSerial(sent);
      console.log(`DEC motor command: ${sent} (relative nudge by ${delta}, target ${np})`);
    } else if (blocked && !alignMode) {
      // Movement blocked by limits
      const limitType = originalNp < decMinLimit ? 'minimum' : 'maximum';
      console.log(`DEC movement blocked: would exceed ${limitType} limit (${originalNp} -> ${np})`);
      return res.json({ 
        ok: false, 
        error: 'limit-blocked',
        message: `DEC movement blocked by ${limitType} limit`,
        axis, 
        requestedSteps: delta,
        currentSteps: decPosition,
        limitReached: np
      });
    }
    decPosition = np;
  }
  if (sent){ writeMountSerial('GET_STATUS'); writeMountSerial('GET_POS'); }
  saveState(); broadcastMount();
  const isConnected = mountSerial.port && mountSerial.isOpen;
  res.json({ 
    ok: true, 
    raSteps: raPosition, 
    decSteps: decPosition, 
    sent,
    mode: alignMode ? 'align' : 'normal',
    mountConnected: isConnected,
    warning: !isConnected ? 'Mount not connected - software simulation only' : (blocked && alignMode ? 'Limit reached; align-mode override not executed' : null)
  });
});

// ---- Tracking ----
app.post('/tracking',(req,res)=>{ trackingEnabled=!!(req.body||{}).enabled; saveState(); broadcastMount(); const serial = serialStatus(); if (serial.connected && mountSerial.port){ try { writeMountSerial(`TRACK:${trackingEnabled?1:0}`); } catch(_){} } res.json({ status:'tracking', tracking:trackingEnabled }); });

// Tracking config endpoint (rate multiplier / ppm / interval)
app.post('/mount-tracking-config',(req,res)=>{
  const { rateMultiplier, ppm, intervalMs } = req.body||{};
  if (rateMultiplier != null && isFinite(rateMultiplier)) trackingRateMultiplier = rateMultiplier;
  if (ppm != null && Number.isFinite(ppm)) trackingPpm = ppm;
  if (intervalMs != null && Number.isFinite(intervalMs) && intervalMs >= 100) trackingIntervalMs = intervalMs;
  restartIntegrator();
  // Mirror to serial if connected
  const serial = serialStatus();
  if (serial.connected && mountSerial.port){
    try {
      writeMountSerial(`TRACK_RATE:${trackingRateMultiplier}`);
      writeMountSerial(`TRACK_PPM:${trackingPpm}`);
    } catch(_){ /* ignore */ }
  }
  res.json({ ok:true, trackingRateMultiplier, trackingPpm, trackingIntervalMs });
});

// ---- RA Zero ----
app.post('/ra-zero-here',(req,res)=>{ 
  // Clear alignment first, then set soft zero to current position for a true relative 0
  raAlignOffsetSteps = 0;
  raZeroOffsetSteps = raPosition;
  saveState(); 
  broadcastMount(); 
  res.json({ status:'ra-zero-updated', raZeroOffsetSteps, reportedRaHours: raStepsToReportedHours(raPosition) }); 
});

// ---- DEC Zero ----
app.post('/dec-zero-here',(req,res)=>{
  // Clear alignment first, then set soft zero to current position for a true relative 0
  decAlignOffsetSteps = 0;
  decZeroOffsetSteps = decPosition;
  saveState();
  broadcastMount();
  res.json({ status:'dec-zero-updated', decZeroOffsetSteps, reportedDecDeg: decStepsToReportedDeg(decPosition) });
});

// ---- Mount Zero (RA+DEC) ----
app.post('/mount-zero',(req,res)=>{
  // Clear alignment offsets; set RA soft zero to CURRENT RA timeline position
  // This makes the RA motor diagram read 0 at the current position (±64000 range).
  raAlignOffsetSteps = 0;
  decAlignOffsetSteps = 0;
  raZeroOffsetSteps = raPosition; // soft zero aligns diagram to current RA
  // Keep DEC behavior unchanged unless explicitly requested; do not force DEC zero here
  // decZeroOffsetSteps remains as-is

  console.log(`Zero Mount: Set RA soft zero to current RA position (${raZeroOffsetSteps}). DEC soft zero unchanged (${decZeroOffsetSteps}).`);

  saveState();
  broadcastMount();
  res.json({ 
    status:'mount-zero-updated', 
    raZeroOffsetSteps, 
    decZeroOffsetSteps,
    message: `RA soft zero set to current position (${raZeroOffsetSteps}). DEC unchanged (${decZeroOffsetSteps}).`,
    reported:{ 
      raHours: raStepsToReportedHours(raPosition), 
      decDeg: decStepsToReportedDeg(decPosition) 
    } 
  });
});

// ---- Pier-Specific Alignment ----
app.post('/pier-align-east',(req,res)=>{
  // Set East pier zero offsets as DEVIATION from firmware home (64000, 12800)
  raAlignOffsetSteps = 0;
  decAlignOffsetSteps = 0;
  raZeroOffsetEast = raPosition - 64000; // Offset from firmware RA home
  decZeroOffsetEast = decPosition - 12800; // Offset from firmware DEC home
  console.log(`East Pier Alignment: Current(${raPosition},${decPosition}) - FirmwareHome(64000,12800) = Offset(${raZeroOffsetEast},${decZeroOffsetEast})`);
  saveState();
  broadcastMount();
  res.json({ 
    status:'pier-align-east-updated', 
    raZeroOffsetEast, 
    decZeroOffsetEast,
    pierSide: 'East',
    reported:{ raHours: raStepsToReportedHours(raPosition), decDeg: decStepsToReportedDeg(decPosition) } 
  });
});

app.post('/pier-align-west',(req,res)=>{
  // Set West pier zero offsets as DEVIATION from firmware home (64000, 12800)
  raAlignOffsetSteps = 0;
  decAlignOffsetSteps = 0;
  raZeroOffsetWest = raPosition - 64000; // Offset from firmware RA home
  decZeroOffsetWest = decPosition - 12800; // Offset from firmware DEC home
  console.log(`West Pier Alignment: Current(${raPosition},${decPosition}) - FirmwareHome(64000,12800) = Offset(${raZeroOffsetWest},${decZeroOffsetWest})`);
  saveState();
  broadcastMount();
  res.json({ 
    status:'pier-align-west-updated', 
    raZeroOffsetWest, 
    decZeroOffsetWest,
    pierSide: 'West',
    reported:{ raHours: raStepsToReportedHours(raPosition), decDeg: decStepsToReportedDeg(decPosition) } 
  });
});

// ---- Camera list/zip (no capture) ----
const CAPTURE_DIR = path.join(__dirname,'captures'); if(!fs.existsSync(CAPTURE_DIR)) fs.mkdirSync(CAPTURE_DIR); app.use('/captures', express.static(CAPTURE_DIR));
app.get('/camera/list',(req,res)=>{ try { const files=fs.readdirSync(CAPTURE_DIR).filter(f=>f.endsWith('.jpg')).sort().slice(-100); res.json({ files }); } catch(e){ res.status(500).json({ error:'list-failed', detail:e.message }); } });
app.post('/camera/zip',(req,res)=>{ const { files, all } = req.body || {}; const zipName='captures_'+Date.now()+'.zip'; const zipPath=path.join(CAPTURE_DIR, zipName); let target; try { if(all) target=fs.readdirSync(CAPTURE_DIR).filter(f=>/\.(jpg|json|dng|fits)$/i.test(f)); else if(Array.isArray(files)) target=files.filter(f=>/^[A-Za-z0-9_.-]+$/.test(f)&&fs.existsSync(path.join(CAPTURE_DIR,f))); else return res.status(400).json({ error:'no-files' }); if(!target.length) return res.status(400).json({ error:'empty-selection' }); execFile('zip',['-j',zipPath,...target],{ cwd: CAPTURE_DIR },err=>{ if(err) return res.status(500).json({ error:'zip-failed', detail:err.message }); res.download(zipPath, zipName, e=>{ if(e) console.error(e); }); }); } catch(e){ res.status(500).json({ error:'zip-exception', detail:e.message }); } });

// ---- Real Camera Implementation ----
const { spawn } = require('child_process');

// Camera detection and configuration
var cameraInfo = { detected:false, sensorName:null, listOutput:null, error:null };
let captureBusy = false;
let cameraResolutions = [];
let cameraDetectAttempts = 0;
let cameraLastDetectError = null;
let cameraDetectTimer = null;
const CAMERA_DETECT_CMD = process.env.CAMERA_DETECT_CMD || 'rpicam-still';
const CAMERA_CAPTURE_CMD = process.env.CAMERA_CAPTURE_CMD || 'rpicam-still';
const CAMERA_MAX_RETRIES = parseInt(process.env.CAMERA_MAX_RETRIES||'10',10);
const CAMERA_DEFAULTS_FILE = path.join(__dirname,'camera_defaults.json');

// Camera defaults with astrophotography settings
let cameraDefaults = { 
  width: 1920, 
  height: 1080, 
  exposureMs: 1000,    // 1 second for astro
  gain: 4.0,           // Higher gain for faint objects
  contrast: 8, 
  format: 'jpeg', 
  wantRaw: false, 
  wantFits: false,
  // Focus assist settings
  focusMode: false,
  focusExposureMs: 100,  // Short exposure for focusing
  focusGain: 8.0,        // High gain for star visibility
  // Astro presets
  astroExposureMs: 10000, // 10 second exposure
  astroGain: 2.0,         // Lower noise for long exposures
  astroISO: 100           // Low ISO for best quality
};

try { 
  if(fs.existsSync(CAMERA_DEFAULTS_FILE)) { 
    Object.assign(cameraDefaults, JSON.parse(fs.readFileSync(CAMERA_DEFAULTS_FILE,'utf8'))); 
  } 
} catch(_){ }

function persistCameraDefaults(){ 
  try { 
    fs.writeFileSync(CAMERA_DEFAULTS_FILE, JSON.stringify(cameraDefaults,null,2)); 
  } catch(_){ } 
}

function parseResolutions(listOut){
  const res=[]; 
  if(!listOut) return res;
  const re=/(\d{3,5})x(\d{3,5})/g; 
  let m; 
  const seen=new Set();
  while((m=re.exec(listOut))){ 
    const w=parseInt(m[1],10), h=parseInt(m[2],10); 
    const key=w+'x'+h; 
    if(!seen.has(key)) { 
      seen.add(key); 
      res.push({width:w,height:h}); 
    } 
  }
  res.sort((a,b)=>(b.width*b.height)-(a.width*a.height));
  return res;
}

function detectCamera(){
  cameraDetectAttempts++;
  return new Promise(resolve=>{
    execFile(CAMERA_DETECT_CMD,['--list-cameras'],{timeout:8000},(err,stdout,stderr)=>{
      if(err){
        cameraLastDetectError = err.message;
        cameraInfo={detected:false,sensorName:null,listOutput:stderr||stdout||'',error:err.message};
        scheduleCameraRetry();
        return resolve(cameraInfo);
      }
      const out=stdout||''; 
      const lower=out.toLowerCase();
      const sensorMatch = /imx(\d+)/.exec(lower);
      const isIMX477 = /imx477/.test(lower);
      cameraInfo={ 
        detected: !!sensorMatch, 
        sensorName: isIMX477? 'IMX477' : (sensorMatch? sensorMatch[0].toUpperCase(): null), 
        listOutput: out, 
        error:null 
      };
      cameraResolutions=parseResolutions(out);
      cameraLastDetectError = null;
      if(!cameraInfo.detected) scheduleCameraRetry();
      resolve(cameraInfo);
    });
  });
}

function scheduleCameraRetry(){
  if(cameraInfo.detected) return;
  if(cameraDetectAttempts>=CAMERA_MAX_RETRIES) return;
  if(cameraDetectTimer) return;
  cameraDetectTimer = setTimeout(()=>{ 
    cameraDetectTimer=null; 
    detectCamera(); 
  }, 5000);
}

// Start camera detection
detectCamera();

let lastCaptureMeta = null;
let sequenceState = null;

// Real camera capture function
async function captureImage(opts = {}) {
  if (captureBusy) {
    return { error: 'capture-busy', detail: 'Another capture is in progress' };
  }
  
  if (!cameraInfo.detected) {
    return { error: 'camera-not-detected', detail: 'Camera not available' };
  }

  captureBusy = true;
  const ts = new Date().toISOString().replace(/[:.]/g, '-');
  const base = `capture_${ts}`;
  
  try {
    // Merge options with defaults
    const settings = { ...cameraDefaults, ...opts };
    
    // Use focus settings if in focus mode
    if (settings.focusMode) {
      settings.exposureMs = settings.focusExposureMs;
      settings.gain = settings.focusGain;
    }
    
    const jpgName = `${base}.jpg`;
    const jpgPath = path.join(CAPTURE_DIR, jpgName);
    
    const args = [
      '--output', jpgPath,
      '--width', String(settings.width || 1920),
      '--height', String(settings.height || 1080),
      '--quality', '95',
      '--timeout', '5000'
    ];
    
    // Add exposure (shutter speed in microseconds)
    if (settings.exposureMs) {
      args.push('--shutter', String(settings.exposureMs * 1000));
    }
    
    // Add gain
    if (settings.gain) {
      args.push('--gain', String(settings.gain));
    }
    
    // Add ISO if specified
    if (settings.iso) {
      args.push('--ISO', String(settings.iso));
    }
    
    console.log(`[CAMERA] Capturing with: exposure=${settings.exposureMs}ms, gain=${settings.gain}, size=${settings.width}x${settings.height}`);
    
    return new Promise((resolve) => {
      const proc = spawn(CAMERA_CAPTURE_CMD, args);
      let stderr = '';
      
      proc.stderr.on('data', d => {
        stderr += d.toString();
      });
      
      proc.on('close', (code) => {
        captureBusy = false;
        
        if (code === 0 && fs.existsSync(jpgPath)) {
          const meta = {
            ts: Date.now(),
            files: { jpg: jpgName },
            settings: settings,
            method: 'rpicam-still'
          };
          lastCaptureMeta = meta;
          
          console.log(`[CAMERA] Capture successful: ${jpgName}`);
          resolve({ status: 'captured', meta });
        } else {
          const error = `rpicam-still failed with code ${code}: ${stderr}`;
          console.error('[CAMERA]', error);
          lastCaptureMeta = { ts: Date.now(), error: 'capture-failed', detail: error };
          resolve({ error: 'capture-failed', detail: error });
        }
      });
      
      proc.on('error', (err) => {
        captureBusy = false;
        const error = `Failed to spawn rpicam-still: ${err.message}`;
        console.error('[CAMERA]', error);
        lastCaptureMeta = { ts: Date.now(), error: 'capture-failed', detail: error };
        resolve({ error: 'capture-failed', detail: error });
      });
    });
    
  } catch (e) {
    captureBusy = false;
    const error = `Capture exception: ${e.message}`;
    console.error('[CAMERA]', error);
    lastCaptureMeta = { ts: Date.now(), error: 'capture-failed', detail: error };
    return { error: 'capture-failed', detail: error };
  }
}
app.post('/camera/capture', async (req,res)=>{
  const result = await captureImage(req.body||{});
  res.json(result);
});

// Camera presets endpoint
app.post('/camera/preset/:mode', async (req, res) => {
  const { mode } = req.params;
  let settings = {};
  
  switch(mode) {
    case 'focus':
      settings = {
        focusMode: true,
        width: 640,
        height: 480,
        exposureMs: cameraDefaults.focusExposureMs,
        gain: cameraDefaults.focusGain
      };
      break;
      
    case 'astro':
      settings = {
        focusMode: false,
        width: cameraDefaults.width,
        height: cameraDefaults.height,
        exposureMs: cameraDefaults.astroExposureMs,
        gain: cameraDefaults.astroGain,
        iso: cameraDefaults.astroISO
      };
      break;
      
    case 'day':
      settings = {
        focusMode: false,
        width: 1920,
        height: 1080,
        exposureMs: 100,
        gain: 1.0,
        iso: 200
      };
      break;
      
    default:
      return res.status(400).json({ error: 'invalid-preset', available: ['focus', 'astro', 'day'] });
  }
  
  const result = await captureImage({ ...req.body, ...settings });
  res.json({ preset: mode, settings, result });
});
app.get('/camera/last-capture',(req,res)=>{ res.json({ lastCapture: lastCaptureMeta }); });

// Camera settings endpoints
app.get('/camera/settings', (req, res) => {
  res.json({ 
    current: cameraDefaults,
    presets: {
      focus: {
        name: 'Focus Assist',
        description: 'High gain, short exposure for star focusing',
        width: 640,
        height: 480,
        exposureMs: cameraDefaults.focusExposureMs,
        gain: cameraDefaults.focusGain,
        focusMode: true
      },
      astro: {
        name: 'Astrophotography',
        description: 'Long exposure, low noise for deep sky imaging',
        width: cameraDefaults.width,
        height: cameraDefaults.height,
        exposureMs: cameraDefaults.astroExposureMs,
        gain: cameraDefaults.astroGain,
        iso: cameraDefaults.astroISO,
        focusMode: false
      },
      day: {
        name: 'Daylight',
        description: 'Standard settings for daylight use',
        width: 1920,
        height: 1080,
        exposureMs: 100,
        gain: 1.0,
        iso: 200,
        focusMode: false
      }
    }
  });
});

app.post('/camera/settings', (req, res) => {
  const updates = req.body || {};
  
  // Validate settings
  if (updates.exposureMs && (updates.exposureMs < 1 || updates.exposureMs > 60000)) {
    return res.status(400).json({ error: 'invalid-exposure', range: '1-60000ms' });
  }
  
  if (updates.gain && (updates.gain < 0.1 || updates.gain > 20)) {
    return res.status(400).json({ error: 'invalid-gain', range: '0.1-20' });
  }
  
  // Update defaults
  Object.assign(cameraDefaults, updates);
  persistCameraDefaults();
  
  console.log('[CAMERA] Settings updated:', updates);
  res.json({ ok: true, settings: cameraDefaults });
});

// Focus analysis system
const FocusAnalyzer = require('./focus-analyzer');
const focusAnalyzer = new FocusAnalyzer();
let focusHistory = []; // Store focus measurements over time

// Focus analysis endpoint - analyze image quality
app.post('/camera/focus/analyze', async (req, res) => {
  try {
    const { imagePath } = req.body;
    let targetPath = imagePath;
    
    // If no image specified, use the most recent capture
    if (!targetPath) {
      const files = fs.readdirSync(CAPTURE_DIR)
        .filter(f => f.endsWith('.jpg'))
        .sort()
        .reverse();
      
      if (files.length === 0) {
        return res.status(400).json({ 
          error: 'no-images', 
          message: 'No images available for analysis' 
        });
      }
      
      targetPath = path.join(CAPTURE_DIR, files[0]);
    } else {
      targetPath = path.join(CAPTURE_DIR, path.basename(imagePath));
    }
    
    console.log(`[FOCUS] Analyzing image: ${path.basename(targetPath)}`);
    const analysis = await focusAnalyzer.analyzeImage(targetPath);
    
    // Store in history for tracking focus changes
    focusHistory.push(analysis);
    if (focusHistory.length > 50) {
      focusHistory = focusHistory.slice(-50); // Keep last 50 measurements
    }
    
    res.json({
      success: true,
      analysis,
      trend: focusHistory.length > 1 ? 
        (analysis.focusScore - focusHistory[focusHistory.length - 2].focusScore) : 0
    });
    
  } catch (error) {
    console.error('[FOCUS] Analysis error:', error.message);
    res.status(500).json({ 
      error: 'analysis-failed', 
      detail: error.message 
    });
  }
});

// Get focus history for trending
app.get('/camera/focus/history', (req, res) => {
  const { limit = 20 } = req.query;
  const recentHistory = focusHistory.slice(-parseInt(limit));
  
  res.json({
    history: recentHistory,
    count: focusHistory.length,
    currentScore: focusHistory.length > 0 ? 
      focusHistory[focusHistory.length - 1].focusScore : null
  });
});

// Capture and analyze in one step
app.post('/camera/focus/capture-analyze', async (req, res) => {
  try {
    // First capture an image with focus settings
    const captureResult = await captureImage({
      focusMode: true,
      width: 1920,  // Higher resolution for better star analysis
      height: 1080,
      ...req.body
    });
    
    if (captureResult.error) {
      return res.status(500).json(captureResult);
    }
    
    // Wait a moment for file to be fully written
    await new Promise(resolve => setTimeout(resolve, 500));
    
    // Then analyze the captured image
    const imagePath = path.join(CAPTURE_DIR, captureResult.meta.files.jpg);
    console.log(`[FOCUS] Analyzing fresh capture: ${captureResult.meta.files.jpg}`);
    
    const analysis = await focusAnalyzer.analyzeImage(imagePath);
    
    // Store in history
    focusHistory.push(analysis);
    if (focusHistory.length > 50) {
      focusHistory = focusHistory.slice(-50);
    }
    
    res.json({
      success: true,
      capture: captureResult,
      analysis,
      trend: focusHistory.length > 1 ? 
        (analysis.focusScore - focusHistory[focusHistory.length - 2].focusScore) : 0,
      message: `Found ${analysis.starsDetected} stars, Focus Score: ${analysis.focusScore}/100 (${analysis.quality})`
    });
    
  } catch (error) {
    console.error('[FOCUS] Capture-analyze error:', error.message);
    res.status(500).json({ 
      error: 'capture-analyze-failed', 
      detail: error.message 
    });
  }
});

// Focus assist mode endpoints
app.post('/camera/focus/start', (req, res) => {
  const { width = 640, height = 480, gain, exposure } = req.body || {};
  
  // Enable focus mode in defaults
  cameraDefaults.focusMode = true;
  if (gain) cameraDefaults.focusGain = gain;
  if (exposure) cameraDefaults.focusExposureMs = exposure;
  persistCameraDefaults();
  
  console.log('[CAMERA] Focus assist mode started');
  res.json({ 
    ok: true, 
    focusMode: true,
    settings: {
      width,
      height,
      gain: cameraDefaults.focusGain,
      exposureMs: cameraDefaults.focusExposureMs
    },
    message: 'Focus mode enabled - use /camera/live?focus=true for enhanced preview'
  });
});

app.post('/camera/focus/stop', (req, res) => {
  cameraDefaults.focusMode = false;
  persistCameraDefaults();
  
  console.log('[CAMERA] Focus assist mode stopped');
  res.json({ ok: true, focusMode: false });
});

app.get('/camera/focus/status', (req, res) => {
  res.json({
    focusMode: cameraDefaults.focusMode,
    settings: {
      gain: cameraDefaults.focusGain,
      exposureMs: cameraDefaults.focusExposureMs
    }
  });
});

// Automated focus sweep
let focusSweepState = null;

app.post('/camera/focus/sweep', async (req, res) => {
  if (focusSweepState && focusSweepState.running) {
    return res.status(429).json({ 
      error: 'sweep-running', 
      message: 'Focus sweep already in progress' 
    });
  }

  const { 
    steps = 200,        // Total steps to move focuser
    stepSize = 10,      // Steps per measurement
    direction = 'out',  // 'in' or 'out' 
    returnToBest = true // Return to best focus position when done
  } = req.body;

  const totalMeasurements = Math.floor(steps / stepSize);
  
  focusSweepState = {
    running: true,
    startTime: Date.now(),
    totalSteps: steps,
    stepSize,
    direction,
    currentStep: 0,
    measurements: [],
    bestFocus: null,
    progress: 0
  };

  console.log(`[FOCUS] Starting sweep: ${steps} steps ${direction}, ${totalMeasurements} measurements`);

  res.json({
    success: true,
    sweepId: focusSweepState.startTime,
    totalMeasurements,
    message: `Focus sweep started: ${totalMeasurements} measurements over ${steps} steps`
  });

  // Run sweep asynchronously
  runFocusSweep(totalMeasurements, stepSize, direction, returnToBest);
});

async function runFocusSweep(totalMeasurements, stepSize, direction, returnToBest) {
  try {
    for (let i = 0; i < totalMeasurements; i++) {
      if (!focusSweepState || !focusSweepState.running) {
        console.log('[FOCUS] Sweep cancelled');
        break;
      }

      console.log(`[FOCUS] Sweep measurement ${i + 1}/${totalMeasurements}`);

      // Move focuser
      const moveCommand = direction === 'out' ? `-${stepSize}` : `+${stepSize}`;
      try {
        enqueueFocuser(moveCommand);
        await new Promise(resolve => setTimeout(resolve, 1000)); // Wait for movement
      } catch (error) {
        console.error('[FOCUS] Focuser move error:', error.message);
      }

      // Capture and analyze
      try {
        const captureResult = await captureImage({
          focusMode: true,
          width: 1920,
          height: 1080
        });

        if (!captureResult.error) {
          await new Promise(resolve => setTimeout(resolve, 500));
          
          const imagePath = path.join(CAPTURE_DIR, captureResult.meta.files.jpg);
          const analysis = await focusAnalyzer.analyzeImage(imagePath);
          
          const measurement = {
            step: focusSweepState.currentStep,
            analysis,
            timestamp: Date.now()
          };
          
          focusSweepState.measurements.push(measurement);
          focusSweepState.currentStep += stepSize;
          focusSweepState.progress = Math.round((i + 1) / totalMeasurements * 100);

          // Track best focus
          if (!focusSweepState.bestFocus || 
              analysis.focusScore > focusSweepState.bestFocus.analysis.focusScore) {
            focusSweepState.bestFocus = measurement;
          }

          console.log(`[FOCUS] Step ${focusSweepState.currentStep}: Score ${analysis.focusScore}, HFR ${analysis.averageHFR}`);
          
          // Send real-time update via SSE
          sendEvent('focus-sweep', {
            type: 'focus-sweep',
            progress: focusSweepState.progress,
            current: measurement,
            best: focusSweepState.bestFocus
          });
        }
      } catch (error) {
        console.error('[FOCUS] Sweep analysis error:', error.message);
      }

      // Wait between measurements
      await new Promise(resolve => setTimeout(resolve, 2000));
    }

    // Sweep complete
    focusSweepState.running = false;
    focusSweepState.endTime = Date.now();
    
    console.log(`[FOCUS] Sweep complete. Best focus at step ${focusSweepState.bestFocus?.step || 'unknown'}`);

    // Return to best focus position if requested
    if (returnToBest && focusSweepState.bestFocus) {
      const returnSteps = focusSweepState.currentStep - focusSweepState.bestFocus.step;
      if (Math.abs(returnSteps) > 0) {
        const returnCommand = returnSteps > 0 ? `+${returnSteps}` : `${returnSteps}`;
        console.log(`[FOCUS] Returning to best focus position: ${returnCommand} steps`);
        enqueueFocuser(returnCommand);
      }
    }

    // Send completion event
    sendEvent('focus-sweep', {
      type: 'focus-sweep',
      status: 'complete',
      totalMeasurements: focusSweepState.measurements.length,
      best: focusSweepState.bestFocus,
      duration: focusSweepState.endTime - focusSweepState.startTime
    });

  } catch (error) {
    console.error('[FOCUS] Sweep error:', error.message);
    focusSweepState.running = false;
    focusSweepState.error = error.message;
  }
}

// Focus sweep status
app.get('/camera/focus/sweep/status', (req, res) => {
  if (!focusSweepState) {
    return res.json({ running: false });
  }

  res.json({
    running: focusSweepState.running,
    progress: focusSweepState.progress,
    currentStep: focusSweepState.currentStep,
    measurements: focusSweepState.measurements.length,
    bestFocus: focusSweepState.bestFocus,
    error: focusSweepState.error
  });
});

// Stop focus sweep
app.post('/camera/focus/sweep/stop', (req, res) => {
  if (focusSweepState) {
    focusSweepState.running = false;
    console.log('[FOCUS] Sweep stopped by user');
  }
  
  res.json({ success: true, message: 'Focus sweep stopped' });
});
app.get('/camera/modes',(req,res)=>{
  // Keep legacy field for stills dropdown
  const uniqueResolutions = [
    // IMX477 common full and binning modes (descending)
    { width:4056, height:3040 }, // full sensor 12.3MP 4:3
    { width:4056, height:2288 }, // 16:9 crop
    { width:3840, height:2160 }, // 4K UHD
    { width:2028, height:1520 }, // 2x2 bin 4:3
    { width:1920, height:1080 },
    { width:1280, height:720 },
    { width:640, height:360 }
  ];
  // High-resolution stills list (subset for emphasis in UI)
  const highResResolutions = [
    { width:4056, height:3040 },
    { width:4056, height:2288 },
    { width:3840, height:2160 }
  ];
  // Advertise video support and common modes for rpicam-vid MJPEG stream
  const videoModes = [
    { width:640, height:480, framerates:[5,10,15] },
    { width:1280, height:720, framerates:[5,10,15,30] },
    { width:1920, height:1080, framerates:[5,10,15,30] }
  ];
  const endpoints = {
    liveMultipart: '/camera/live',   // multipart/x-mixed-replace MJPEG (server-generated)
    liveSnapshot: '/camera/stream',  // single-image snapshot fallback
    captures: '/captures'
  };
  res.json({ uniqueResolutions, highResResolutions, videoSupported:true, videoModes, endpoints });
});
app.get('/camera/diagnose',(req,res)=>{ 
  res.json({ 
    summary: { 
      sensorDetected: cameraInfo.detected, 
      sensorName: cameraInfo.sensorName, 
      anyStillBinary: true, 
      autoDryRunActive: !cameraInfo.detected, 
      method: lastCaptureMeta?.method || lastCaptureMeta?.meta?.method, 
      fitsSupported: false 
    }, 
    cameraInfo, 
    resolutions: cameraResolutions, 
    defaults: cameraDefaults, 
    lastCapture: lastCaptureMeta, 
    detection: { 
      attempts: cameraDetectAttempts, 
      lastError: cameraLastDetectError, 
      maxRetries: CAMERA_MAX_RETRIES, 
      retryPending: !!cameraDetectTimer 
    } 
  }); 
});
app.get('/camera/stream',(req,res)=>{ // snapshot fallback
  // Serve most recent capture or placeholder svg/png
  let candidate = null;
  try { const files=fs.readdirSync(CAPTURE_DIR).filter(f=>f.endsWith('.jpg')).sort(); if(files.length) candidate=path.join(CAPTURE_DIR, files[files.length-1]); } catch(_){}
  if (!candidate){ candidate = path.join(__dirname,'test.jpg'); }
  if (!fs.existsSync(candidate)) return res.status(404).end();
  res.sendFile(candidate);
});

// Real MJPEG live streaming with rpicam-vid
let videoStreamProcess = null;

app.get('/camera/live', (req, res) => {
  if (!cameraInfo.detected) {
    return res.status(503).json({ 
      error: 'camera-not-detected', 
      message: 'Camera not available for streaming' 
    });
  }

  const boundary = 'videostream';
  res.writeHead(200, {
    'Content-Type': `multipart/x-mixed-replace; boundary=${boundary}`,
    'Cache-Control': 'no-cache',
    'Connection': 'keep-alive',
    'Pragma': 'no-cache',
    'Access-Control-Allow-Origin': '*'
  });

  // Kill existing stream
  if (videoStreamProcess) {
    try { videoStreamProcess.kill('SIGTERM'); } catch(_){}
    videoStreamProcess = null;
  }

  // Parse parameters with focus assist mode support
  const { 
    width = 640, 
    height = 480, 
    framerate = 15, 
    quality = 80,
    focus = false,
    gain,
    exposure 
  } = req.query;
  
  const camIndex = (req.query.camera != null) ? String(req.query.camera) : (process.env.CAMERA_INDEX || '0');
  
  const streamArgs = [
    '--camera', camIndex,
    '-n', // no preview window
    '--width', String(width),
    '--height', String(height),
    '--framerate', String(Math.min(30, Math.max(1, parseInt(framerate)))),
    '--codec', 'mjpeg',
    '--quality', String(quality),
    '-t', '0', // infinite timeout
    '-o', '-'  // output to stdout
  ];
  
  // Focus assist mode - boost gain and set short exposure
  if (focus === 'true' || focus === '1') {
    streamArgs.push('--gain', String(gain || cameraDefaults.focusGain || 8));
    if (exposure || cameraDefaults.focusExposureMs) {
      streamArgs.push('--shutter', String((exposure || cameraDefaults.focusExposureMs) * 1000));
    }
    console.log('[CAMERA] Focus assist mode enabled');
  } else {
    // Normal streaming mode
    if (gain) streamArgs.push('--gain', String(gain));
    if (exposure) streamArgs.push('--shutter', String(exposure * 1000));
  }

  try {
    console.log(`[CAMERA] Starting video stream: ${width}x${height}@${framerate}fps`);
    videoStreamProcess = spawn('rpicam-vid', streamArgs);
  } catch(e){
    console.error('[CAMERA] Failed to spawn rpicam-vid:', e.message);
    return res.status(500).json({ error: 'stream-failed', detail: e.message });
  }

  let buffer = Buffer.alloc(0);
  const soi = Buffer.from([0xFF,0xD8]); // JPEG Start Of Image
  const eoi = Buffer.from([0xFF,0xD9]); // JPEG End Of Image
  let frameCount = 0;
  let lastFrameTime = Date.now();

  function extractFrames(){
    let start = buffer.indexOf(soi);
    while(start !== -1){
      let end = buffer.indexOf(eoi, start+2);
      if(end === -1) break; // incomplete frame
      end += 2; // include EOI marker
      
      const frame = buffer.slice(start, end);
      buffer = buffer.slice(end);
      start = buffer.indexOf(soi);
      
      // Write multipart frame
      try {
        res.write(`--${boundary}\r\n`);
        res.write('Content-Type: image/jpeg\r\n');
        res.write(`Content-Length: ${frame.length}\r\n\r\n`);
        res.write(frame);
        res.write('\r\n');
        frameCount++; 
        lastFrameTime = Date.now();
      } catch(writeErr){
        // Client disconnected
        cleanup();
        return;
      }
    }
  }

  function cleanup(){
    if(videoStreamProcess){
      try { 
        videoStreamProcess.kill('SIGTERM'); 
        console.log('[CAMERA] Video stream stopped');
      } catch(_){}
      videoStreamProcess = null;
    }
  }

  videoStreamProcess.stdout.on('data', chunk => {
    buffer = Buffer.concat([buffer, chunk]);
    // Prevent unbounded buffer growth
    if(buffer.length > 8*1024*1024){ 
      buffer = buffer.slice(-2*1024*1024); 
    }
    extractFrames();
  });

  videoStreamProcess.stderr.on('data', d => {
    const msg = d.toString();
    if(/error/i.test(msg)) {
      console.error('[CAMERA] rpicam-vid stderr:', msg.trim());
    }
  });

  videoStreamProcess.on('close', (code) => {
    console.log(`[CAMERA] rpicam-vid exited with code ${code}`);
    cleanup();
  });

  videoStreamProcess.on('error', (err) => {
    console.error('[CAMERA] rpicam-vid error:', err.message);
    cleanup();
  });

  // Handle client disconnect
  req.on('close', cleanup);
  req.on('error', cleanup);
});
app.post('/camera/sequence/start', async (req,res)=>{
  const { frames=5, intervalMs=5000, width, height, exposureMs, gain, contrast, format, wantRaw, wantFits } = req.body||{};
  if (sequenceState && sequenceState.captured < sequenceState.total) {
    return res.status(429).json({ error:'sequence-running' });
  }
  
  sequenceState = { 
    total: frames, 
    captured: 0, 
    intervalMs, 
    opts: { width, height, exposureMs, gain, contrast, format, wantRaw, wantFits }, 
    timer: null 
  };
  
  async function tick(){
    if (!sequenceState) return;
    sequenceState.captured++;
    
    console.log(`[CAMERA] Sequence capture ${sequenceState.captured}/${sequenceState.total}`);
    const meta = await captureImage(sequenceState.opts);
    
    sendEvent('camera-sequence', { 
      type: 'camera-sequence', 
      status: sequenceState.captured >= sequenceState.total ? 'done' : 'frame', 
      capturedFrames: sequenceState.captured, 
      totalFrames: sequenceState.total, 
      remainingFrames: Math.max(0, sequenceState.total - sequenceState.captured), 
      last: meta.meta || meta 
    });
    
    if (sequenceState.captured >= sequenceState.total){
      clearInterval(sequenceState.timer); 
      sequenceState.timer = null; 
      sequenceState = null; 
      console.log('[CAMERA] Sequence complete');
      return;
    }
  }
  
  sequenceState.timer = setInterval(tick, intervalMs);
  tick(); // Start immediately
  res.json({ ok:true, sequence:{ total:frames, intervalMs } });
});
app.post('/camera/sequence/stop',(req,res)=>{
  if (sequenceState){ if(sequenceState.timer) clearInterval(sequenceState.timer); sequenceState=null; sendEvent('camera-sequence',{ type:'camera-sequence', status:'stopped' }); }
  res.json({ ok:true });
});

// ---- Status ----
app.get('/status',(req,res)=>{ res.json({ raSteps:raPosition, decSteps:decPosition, raHours: raStepsToReportedHours(raPosition), decDeg: decStepsToReportedDeg(decPosition), tracking: trackingEnabled }); });

// ---- DEC Dot Placement API ----
// Compute DEC dot placement for SVG quadrant diagram
app.get('/dec-dot-placement', (req, res) => {
  const { haHours, decDeg, radius = 100, cx = 150, cy = 150, scaled = false } = req.query;
  
  // Validate inputs
  if (haHours === undefined || decDeg === undefined) {
    return res.status(400).json({ 
      error: 'missing-parameters',
      required: ['haHours', 'decDeg'],
      optional: ['radius', 'cx', 'cy', 'scaled']
    });
  }
  
  let ha = parseFloat(haHours);
  // Normalize HA to ±12h range
  if (ha < -12) ha += 24;
  if (ha > 12) ha -= 24; 
  const dec = parseFloat(decDeg);
  const r = parseFloat(radius);
  const centerX = parseFloat(cx);
  const centerY = parseFloat(cy);
  
  if (isNaN(ha) || isNaN(dec) || isNaN(r) || isNaN(centerX) || isNaN(centerY)) {
    return res.status(400).json({ error: 'invalid-numbers' });
  }
  
  // Compute placement
  const placement = scaled === 'true' 
    ? placeDecDotScaled(ha, dec, r, centerX, centerY)
    : placeDecDot(ha, dec, r, centerX, centerY);
  
  res.json({
    placement,
    inputs: { haHours: ha, decDeg: dec, radius: r, cx: centerX, cy: centerY, scaled: scaled === 'true' },
    timestamp: new Date().toISOString()
  });
});

// Compute DEC dot placement for current telescope position
app.get('/dec-dot-placement/current', (req, res) => {
  const { radius = 100, cx = 150, cy = 150, scaled = false } = req.query;
  
  // Get current telescope position
  const raHours = raStepsToReportedHours(raPosition);
  const decDeg = decStepsToReportedDeg(decPosition);
  const lst = localSiderealTimeHours(new Date());
  const haHours = computeHourAngleHours(raHours, lst);
  
  const r = parseFloat(radius);
  const centerX = parseFloat(cx);
  const centerY = parseFloat(cy);
  
  // Compute placement for current telescope position
  const placement = scaled === 'true' 
    ? placeDecDotScaled(haHours, decDeg, r, centerX, centerY)
    : placeDecDot(haHours, decDeg, r, centerX, centerY);
  
  // Always calculate previous DEC position (before alignment offset) - even if offset is 0
  // Calculate what the DEC position would be without the alignment offset
  const decStepsWithoutAlign = decPosition - decAlignOffsetSteps;
  const decDegWithoutAlign = decStepsToReportedDeg(decStepsWithoutAlign + decAlignOffsetSteps - decAlignOffsetSteps);
  
  // Get the mechanical position without alignment offset applied
  const mechDegWithoutAlign = ((decStepsWithoutAlign - decZeroOffsetSteps)/decStepsPerRev)*360;
  const mechNormalized = ((mechDegWithoutAlign%360)+360)%360;
  const celDecWithoutAlign = 90 - mechNormalized;
  let adjustedCelDec = celDecWithoutAlign;
  if (adjustedCelDec <= -180) adjustedCelDec += 360;
  else if (adjustedCelDec > 180) adjustedCelDec -= 360;
  if (adjustedCelDec > 90) adjustedCelDec = 180 - adjustedCelDec;
  else if (adjustedCelDec < -90) adjustedCelDec = -180 - adjustedCelDec;
  
  const previousPlacement = scaled === 'true' 
    ? placeDecDotScaled(haHours, adjustedCelDec, r, centerX, centerY)
    : placeDecDot(haHours, adjustedCelDec, r, centerX, centerY);
    
  previousPlacement.decDeg = adjustedCelDec;
  previousPlacement.alignOffsetSteps = decAlignOffsetSteps;
  previousPlacement.alignDirection = decAlignOffsetSteps > 0 ? '+' : (decAlignOffsetSteps < 0 ? '-' : '0');
  previousPlacement.hasAlignOffset = decAlignOffsetSteps !== 0;
  
  res.json({
    placement,
    previousPlacement, // DEC arc position before alignment offset (with + indicator)
    telescope: {
      raHours,
      decDeg, 
      haHours,
      lst,
      raSteps: raPosition,
      decSteps: decPosition,
      decAlignOffsetSteps,
      alignOffsetApplied: decAlignOffsetSteps !== 0
    },
    inputs: { radius: r, cx: centerX, cy: centerY, scaled: scaled === 'true' },
    timestamp: new Date().toISOString()
  });
});

// ---- DEC Conversion API Endpoints ----

// 🧮 Mechanical DEC Conversion (Degrees → Steps)
app.get('/dec/to-steps', (req, res) => {
  const { deg, min = 0, sec = 0, stepsPerDegree } = req.query;
  
  if (deg === undefined) {
    return res.status(400).json({ 
      error: 'missing-parameter',
      required: ['deg'],
      optional: ['min', 'sec', 'stepsPerDegree']
    });
  }
  
  const degVal = parseFloat(deg);
  const minVal = parseFloat(min);
  const secVal = parseFloat(sec);
  const stepsPerDeg = stepsPerDegree ? parseFloat(stepsPerDegree) : 568.89;
  
  if (isNaN(degVal) || isNaN(minVal) || isNaN(secVal) || isNaN(stepsPerDeg)) {
    return res.status(400).json({ error: 'invalid-numbers' });
  }
  
  const steps = decToSteps(degVal, minVal, secVal, stepsPerDeg);
  const totalDegrees = degVal + (minVal / 60) + (secVal / 3600);
  
  res.json({
    input: { deg: degVal, min: minVal, sec: secVal },
    output: {
      steps,
      totalDegrees,
      stepsPerDegree: stepsPerDeg
    },
    timestamp: new Date().toISOString()
  });
});

// Steps → Degrees conversion
app.get('/dec/from-steps', (req, res) => {
  const { steps, stepsPerDegree } = req.query;
  
  if (steps === undefined) {
    return res.status(400).json({ 
      error: 'missing-parameter',
      required: ['steps'],
      optional: ['stepsPerDegree']
    });
  }
  
  const stepVal = parseFloat(steps);
  const stepsPerDeg = stepsPerDegree ? parseFloat(stepsPerDegree) : 568.89;
  
  if (isNaN(stepVal) || isNaN(stepsPerDeg)) {
    return res.status(400).json({ error: 'invalid-numbers' });
  }
  
  const decResult = stepsToDec(stepVal, stepsPerDeg);
  
  res.json({
    input: { steps: stepVal, stepsPerDegree: stepsPerDeg },
    output: decResult,
    formatted: `${decResult.deg}° ${decResult.min}' ${decResult.sec}"`,
    timestamp: new Date().toISOString()
  });
});

// 🧭 SVG Placement (Degrees → Visual Position)
app.get('/dec/to-svg', (req, res) => {
  const { deg, min = 0, sec = 0, svgWidth = 300, svgHeight = 300 } = req.query;
  
  if (deg === undefined) {
    return res.status(400).json({ 
      error: 'missing-parameter',
      required: ['deg'],
      optional: ['min', 'sec', 'svgWidth', 'svgHeight']
    });
  }
  
  const degVal = parseFloat(deg);
  const minVal = parseFloat(min);
  const secVal = parseFloat(sec);
  const width = parseFloat(svgWidth);
  const height = parseFloat(svgHeight);
  
  if (isNaN(degVal) || isNaN(minVal) || isNaN(secVal) || isNaN(width) || isNaN(height)) {
    return res.status(400).json({ error: 'invalid-numbers' });
  }
  
  // Simple X position
  const x = decToSvgX(degVal, minVal, secVal, width);
  
  // Enhanced positioning with options
  const position = decToSvgPosition(degVal, minVal, secVal, {
    svgWidth: width,
    svgHeight: height
  });
  
  res.json({
    input: { deg: degVal, min: minVal, sec: secVal, svgWidth: width },
    simple: { x },
    enhanced: position,
    equatorX: width / 2,  // Reference line at DEC=0°
    timestamp: new Date().toISOString()
  });
});

// Helper function to format decimal degrees to DMS
function formatDMS(decimalDeg, isLatitude = true) {
  const absVal = Math.abs(decimalDeg);
  const deg = Math.floor(absVal);
  const minFloat = (absVal - deg) * 60;
  const min = Math.floor(minFloat);
  const sec = Math.round((minFloat - min) * 60);
  
  let direction = '';
  if (isLatitude) {
    direction = decimalDeg >= 0 ? 'N' : 'S';
  } else {
    direction = decimalDeg >= 0 ? 'E' : 'W';
  }
  
  return `${deg}°${min.toString().padStart(2, '0')}'${sec.toString().padStart(2, '0')}"${direction}`;
}

// LST endpoint for UI convenience
app.get('/lst',(req,res)=>{
  const now = new Date();
  const lst = localSiderealTimeHours(now);
  
  // Include site information for UI display
  const site = {
    latitudeDeg: siteLatitudeDeg,
    longitudeDeg: siteLongitudeDeg,
    latitudeDms: formatDMS(siteLatitudeDeg, true),
    longitudeDms: formatDMS(siteLongitudeDeg, false),
    name: 'Slater, IA'
  };
  
  res.json({ 
    lstHours: lst, 
    iso: now.toISOString(), 
    longitudeDeg: siteLongitudeDeg,
    site: site
  });
});

// Test endpoint for southern hemisphere DEC formula
app.get('/dec/test-southern', (req, res) => {
  const { deg = -30, simulateSouthern = false } = req.query; // Default to -30° for testing
  const testDeg = parseFloat(deg);
  const simulate = simulateSouthern === 'true';
  
  // Calculate using both formulas for comparison
  const northernSteps = Math.round(testDeg * 568.89);
  const s = 51200 / 360; // 142.22 steps per degree
  const southernSteps = Math.round(12800 + (Math.abs(testDeg) * s));
  
  // Simulate southern hemisphere if requested
  let actualResult;
  if (simulate) {
    // Temporarily simulate southern hemisphere
    const originalLat = siteLatitudeDeg;
    // Temporarily override for calculation
    if (originalLat > 0) {
      actualResult = southernSteps; // Use southern formula
    } else {
      actualResult = decToSteps(testDeg);
    }
  } else {
    actualResult = decToSteps(testDeg);
  }
  
  res.json({
    inputDeg: testDeg,
    currentLatitude: siteLatitudeDeg,
    hemisphere: siteLatitudeDeg < 0 ? 'Southern' : 'Northern',
    simulation: simulate ? 'Southern hemisphere simulated' : 'Using actual latitude',
    northernFormula: { steps: northernSteps, formula: `${testDeg} * 568.89` },
    southernFormula: { steps: southernSteps, formula: `12800 + (|${testDeg}| * ${s.toFixed(2)})` },
    actualResult: actualResult,
    stepsPerDegree: s,
    formula: simulate || siteLatitudeDeg < 0 ? 'Southern: 12800 + (|deg| * 142.22)' : 'Northern: deg * 568.89'
  });
});

// Mount position (UI polling expectation)
let raHourAngleLimitHours = 6; // default corridor for advisory
app.get('/mount-position',(req,res)=>{
  const raHours = raStepsToReportedHours(raPosition);
  const decDeg = decStepsToReportedDeg(decPosition);
  const lst = localSiderealTimeHours(new Date());
  const haHours = computeHourAngleHours(raHours, lst);
  const pier = getPierSide(haHours) === 'East' ? 'LstEastPier' : 'LstWestPier';
  const mechDeg = ((decPosition - decZeroOffsetSteps - decAlignOffsetSteps)/decStepsPerRev)*360; // raw mechanical (can be outside 0..360)
  const mechNorm = ((mechDeg%360)+360)%360;
  const altitudeInfo = computeAltitudeDeg(decDeg, lst, raHours);
  const raLimitBlocked = Math.abs(haHours) > raHourAngleLimitHours;
  res.json({
    raSteps: raPosition,
    decSteps: decPosition,
    trackingEnabled,
    raZeroOffsetSteps,
    decZeroOffsetSteps,
    raAlignOffsetSteps,
    decAlignOffsetSteps,
    pierFlipState,
    raInvertActive,
    decInvertActive,
  parkRaSteps,
  parkDecSteps,
    reportedRaHours: raHours,
    reportedDecDeg: decDeg,
    hourAngleHours: haHours,
    lstPierSide: pier,
    mechDeg: mechNorm,
    altitudeDeg: altitudeInfo.altitudeDeg,
    raHourAngleLimitHours,
    raLimitBlocked
  });
});

// ---- RA hour-angle limit setter ----
app.post('/mount-ra-limit',(req,res)=>{
  const { hours } = req.body||{};
  if (!Number.isFinite(hours) || hours <= 0 || hours > 12) return res.status(400).json({ error:'invalid-limit' });
  raHourAngleLimitHours = hours;
  res.json({ ok:true, raHourAngleLimitHours });
});

// ---- RA sync to LST (adjust soft zero so reported RA equals LST) ----
app.post('/ra-sync-lst',(req,res)=>{
  const lst = localSiderealTimeHours(new Date());
  const currentReported = raStepsToReportedHours(raPosition);
  const deltaHours = ((lst - currentReported + 12) % 24) - 12; // shortest shift
  const deltaSteps = Math.round((deltaHours/24) * raStepsPerRev);
  raZeroOffsetSteps += deltaSteps;
  saveState();
  broadcastMount();
  res.json({ ok:true, lstHours: lst, was: currentReported, deltaHours, deltaSteps, newReported: raStepsToReportedHours(raPosition) });
});

// ---- Park endpoints ----
app.post('/park/set',(req,res)=>{
  parkRaSteps = raPosition; parkDecSteps = decPosition; saveState();
  res.json({ ok:true, parkRaSteps, parkDecSteps });
});
app.post('/park/goto',(req,res)=>{
  if (parkRaSteps==null || parkDecSteps==null) return res.status(400).json({ error:'no-park-set' });
  // Compute relative deltas to parked positions
  const raDelta = parkRaSteps - raPosition;
  const decDelta = parkDecSteps - decPosition;
  raPosition += raDelta; decPosition += decDelta; saveState(); broadcastMount();
  const serial = serialStatus();
  if (serial.connected && mountSerial.port){
    try {
      writeMountSerial(`RA_MOVE:${raDelta}`);
      setTimeout(()=>{ try { if(mountSerial.port && mountSerial.isOpen) writeMountSerial(`DEC_MOVE:${decDelta}`); } catch(_){} }, 150);
    } catch(_){}
  }
  res.json({ ok:true, raSteps: raPosition, decSteps: decPosition });
});
app.post('/park/clear',(req,res)=>{
  parkRaSteps = null; parkDecSteps = null; saveState();
  res.json({ ok:true });
});

// ---- Restore Settings: reset to initial conditions (no motor movement) ----
app.post('/settings/restore',(req,res)=>{
  try {
    // Reset alignment offsets and zero offsets to firmware defaults
    raAlignOffsetSteps = 0;
    decAlignOffsetSteps = 0;
    raZeroOffsetSteps = 0;
    decZeroOffsetSteps = 0;

    // Clear pier-specific offsets
    raZeroOffsetEast = 0; decZeroOffsetEast = 0;
    raZeroOffsetWest = 0; decZeroOffsetWest = 0;

    // Tracking off
    trackingEnabled = false;
    try { const s = serialStatus(); if (s.connected && mountSerial.port) writeMountSerial('TRACK:0'); } catch(_){ }

    // Motor invert flags off
    raInvertActive = false;
    decInvertActive = false;

    // Restore RA hour-angle limit default
    raHourAngleLimitHours = 6;

    // Clear park
    parkRaSteps = null; parkDecSteps = null;

    // Reset pier flip state to default (East by convention)
    pierFlipState = false;

    saveState();
    broadcastMount();
    res.json({ ok:true, status:'restored', defaults:{ raHourAngleLimitHours, raInvertActive, decInvertActive, trackingEnabled, parkCleared:true } });
  } catch(e){
    res.status(500).json({ ok:false, error:'restore-failed', detail:e.message });
  }
});


// Altitude endpoint
app.get('/altitude',(req,res)=>{
  const q = req.query || {};
  let raHours = null; let decDeg = null;
  if (q.raHours != null) raHours = parseFloat(q.raHours);
  else if (q.raSteps != null) raHours = raStepsToReportedHours(parseInt(q.raSteps,10));
  if (q.decDeg != null) decDeg = parseFloat(q.decDeg);
  else if (q.decSteps != null) decDeg = decStepsToReportedDeg(parseInt(q.decSteps,10));
  if (!Number.isFinite(raHours) || !Number.isFinite(decDeg)) return res.status(400).json({ error:'invalid-input' });
  const lst = localSiderealTimeHours(new Date());
  const { altitudeDeg, haHours } = computeAltitudeDeg(decDeg, lst, raHours);
  const minAltDeg = 0; // horizon
  res.json({ altitudeDeg, raHours: ((raHours%24)+24)%24, decDeg, haHours, belowHorizon: altitudeDeg < minAltDeg, minAltDeg });
});

// ---- Tracking Integrator ----
function integratorTick(){
  if(!trackingEnabled){ lastTrackUpdateMs=Date.now(); return; }
  const now=Date.now(); const dt=now-lastTrackUpdateMs; if(dt<=0){ lastTrackUpdateMs=now; return; }
  // Base sidereal steps advanced during dt (fractional)
  let base = (dt / SIDEREAL_DAY_MS) * raStepsPerRev;
  base *= trackingRateMultiplier;
  if (trackingPpm) base *= (1 + trackingPpm/1_000_000);
  raTrackingFraction += base;
  const whole = Math.trunc(raTrackingFraction);
  if (whole !== 0){
    raTrackingFraction -= whole;
    let newRa = raPosition + whole;
    if(newRa<raMinLimit)newRa=raMinLimit; else if(newRa>raMaxLimit)newRa=raMaxLimit;
    raPosition = newRa;
    broadcastMount();
  }
  lastTrackUpdateMs=now;
}
function restartIntegrator(){
  if (integratorTimer) clearInterval(integratorTimer);
  integratorTimer = setInterval(integratorTick, trackingIntervalMs);
}
restartIntegrator();

// --- Root ----
// Root index served if UI present
app.get('/', (req,res)=>{
  if (fs.existsSync(path.join(PUBLIC_DIR,'index.html'))){
    return res.sendFile(path.join(PUBLIC_DIR,'index.html'));
  }
  res.send('Telescope control server (clean rebuild)');
});

// Serve a favicon to avoid 404s (use existing SVG if present)
app.get('/favicon.ico', (req,res)=>{
  try {
    const svgPath = path.join(PUBLIC_DIR, 'favicon.svg');
    if (fs.existsSync(svgPath)){
      res.type('image/svg+xml');
      return res.send(fs.readFileSync(svgPath));
    }
  } catch(_) { /* ignore */ }
  res.status(204).end();
});

// Health (quick check)
app.get('/health', (req,res)=> res.json({ ok:true }));

// ---- Python calibration integration (optional proxy) ----
// If running Flask backend at http://127.0.0.1:5055, we can proxy selected routes.
// Toggle via env CALIB_PROXY=1
const enableCalibProxy = process.env.CALIB_PROXY === '1';
let fetchLib = null;
try { fetchLib = global.fetch || require('node-fetch'); } catch(_) {}
function proxyToPython(path, method='POST'){
  return async (req,res)=>{
    if (!enableCalibProxy || !fetchLib){ return res.status(503).json({ ok:false, error:'proxy-disabled' }); }
    try {
      const r = await fetchLib(`http://127.0.0.1:5055${path}`, {
        method,
        headers: { 'Content-Type':'application/json' },
        body: method==='GET' ? undefined : JSON.stringify(req.body||{})
      });
      const ct = (r.headers && r.headers.get) ? (r.headers.get('content-type')||'') : '';
      let payload;
      if (/application\/json/i.test(ct)){
        payload = await r.json();
      } else {
        const txt = await r.text();
        payload = { ok:false, error:'proxy-non-json', status:r.status, bodyText: String(txt).slice(0,500) };
      }
      // Log to serialParsed buffer as DEBUG for console capture visibility
      serialPushLine({ ts:Date.now(), type:'DEBUG', raw:`CALIB ${path} -> ${r.status}`, message: JSON.stringify(payload).slice(0,200) });
      res.status(r.status).json(payload);
    } catch(e){ res.status(500).json({ ok:false, error:'proxy-failed', detail:e.message }); }
  };
}
app.post('/calibrate/ra/sweep', proxyToPython('/calibrate/ra/sweep'));
app.post('/calibrate/ra/adjust', proxyToPython('/calibrate/ra/adjust'));
app.post('/calibrate/ra/replay', proxyToPython('/calibrate/ra/replay'));
app.post('/calibrate/dec/sweep', proxyToPython('/calibrate/dec/sweep'));
app.post('/calibrate/dec/adjust', proxyToPython('/calibrate/dec/adjust'));
app.post('/calibrate/dec/replay', proxyToPython('/calibrate/dec/replay'));
app.post('/calibrate/save', async (req,res)=>{
  if (!enableCalibProxy || !fetchLib){ return res.status(503).json({ ok:false, error:'proxy-disabled' }); }
  try {
    const r = await fetchLib('http://127.0.0.1:5055/calibrate/save', { method:'POST', headers:{ 'Content-Type':'application/json' }, body: JSON.stringify(req.body||{}) });
    const ct = (r.headers && r.headers.get) ? (r.headers.get('content-type')||'') : '';
    let j;
    if (/application\/json/i.test(ct)) j = await r.json();
    else {
      const txt = await r.text();
      j = { ok:false, error:'proxy-non-json', status:r.status, bodyText: String(txt).slice(0,500) };
    }
    serialPushLine({ ts:Date.now(), type:'DEBUG', raw:`CALIB /calibrate/save -> ${r.status}`, message: JSON.stringify(j).slice(0,200) });
    // On success, auto-apply into Node alignment offsets
    if (r.ok && j && j.ok){
      try {
        // Fetch current Python status for offsets
        const stR = await fetchLib('http://127.0.0.1:5055/status');
        const stCt = (stR.headers && stR.headers.get) ? (stR.headers.get('content-type')||'') : '';
        const stJ = /application\/json/i.test(stCt) ? await stR.json() : { ctx:{} };
        const raOff = parseInt(stJ?.ctx?.ra_midpoint_offset||0,10) || 0;
        const decOff = parseInt(stJ?.ctx?.dec_center_offset||0,10) || 0;
        raAlignOffsetSteps += raOff;
        decAlignOffsetSteps += decOff;
        alignmentVersion++;
        saveState();
        broadcastMount();
        return res.status(r.status).json({ ...j, applied:{ raAlignOffsetSteps, decAlignOffsetSteps, alignmentVersion }, note:'calibration offsets applied to alignment' });
      } catch(e){
        return res.status(r.status).json({ ...j, warn:'calibration-saved-but-apply-failed', detail:e.message });
      }
    }
    return res.status(r.status).json(j);
  } catch(e){
    return res.status(500).json({ ok:false, error:'proxy-failed', detail:e.message });
  }
});

// Apply calibration offsets manually (fetch from Python and set alignment)
app.post('/calibration/apply', async (req,res)=>{
  try {
    if (!enableCalibProxy || !fetchLib){ return res.status(503).json({ ok:false, error:'proxy-disabled' }); }
    const r = await fetchLib('http://127.0.0.1:5055/status');
    const j = await r.json();
    const raOff = parseInt(j?.ctx?.ra_midpoint_offset||0,10) || 0;
    const decOff = parseInt(j?.ctx?.dec_center_offset||0,10) || 0;
    raAlignOffsetSteps += raOff;
    decAlignOffsetSteps += decOff;
    alignmentVersion++;
    saveState();
    broadcastMount();
    res.json({ ok:true, applied:{ raAlignOffsetSteps, decAlignOffsetSteps, alignmentVersion }, source:j?.ctx||{} });
  } catch(e){ res.status(500).json({ ok:false, error:'apply-failed', detail:e.message }); }
});

// ---- Motor invert toggles ----
app.get('/invert', (req,res)=>{
  res.json({ ok:true, raInvertActive, decInvertActive });
});
app.post('/invert/ra', (req,res)=>{
  if (typeof req.body?.active === 'boolean') raInvertActive = !!req.body.active;
  else raInvertActive = !raInvertActive;
  saveState();
  sendEvent('invert', { axis:'RA', active: raInvertActive });
  res.json({ ok:true, axis:'RA', active: raInvertActive });
});
app.post('/invert/dec', (req,res)=>{
  if (typeof req.body?.active === 'boolean') decInvertActive = !!req.body.active;
  else decInvertActive = !decInvertActive;
  saveState();
  sendEvent('invert', { axis:'DEC', active: decInvertActive });
  res.json({ ok:true, axis:'DEC', active: decInvertActive });
});

// Create the HTTP server if not already created above
const server = http.createServer(app);

// Start listening (bind to 0.0.0.0 so you can reach it from other devices)
const HOST = process.env.HOST || '0.0.0.0';
const PORT = parseInt(process.env.PORT || '3000', 10);
server.listen(PORT, HOST, () => {
  console.log(`[server] listening on http://${HOST}:${PORT}`);
  
  // Initialize serial device auto-discovery on startup
  console.log('[SERIAL] Starting device auto-discovery...');
  initSerialDevices();
});
server.on('error', (e)=>{
  console.error('[server] listen error:', e.message);
});

// ---- Alignment Offsets ----
let alignmentVersion = 1;
app.get('/alignment/offsets',(req,res)=>{
  res.json({ raAlignOffsetSteps, decAlignOffsetSteps, alignmentVersion });
});
app.post('/alignment/offsets',(req,res)=>{
  // FIX TYPO: req.bodynpm -> req.bodyn
  const { raDelta, decDelta } = req.body || {};
  if (Number.isFinite(raDelta)) raAlignOffsetSteps += parseInt(raDelta,10);
  if (Number.isFinite(decDelta)) decAlignOffsetSteps += parseInt(decDelta,10);
  alignmentVersion++;
  saveState();
  res.json({ ok:true, raAlignOffsetSteps, decAlignOffsetSteps, alignmentVersion });
});
app.post('/alignment/reset',(req,res)=>{
  raAlignOffsetSteps = 0; decAlignOffsetSteps = 0; alignmentVersion++; saveState(); res.json({ ok:true, raAlignOffsetSteps, decAlignOffsetSteps, alignmentVersion });
});

// Align-to-inputs: set alignment offsets so current position reports as requested RA/DEC without moving
app.post('/alignment/sync',(req,res)=>{
  const { raHours, decDeg } = req.body||{};
  let changedRA = false, changedDEC = false;
  let info = {};

  // RA: choose alignment so reported RA equals requested raHours at current position
  if (Number.isFinite(raHours)){
    let h = ((raHours % 24) + 24) % 24;
    if (h > 12) h = h - 24; // map to [-12,+12]
    const base = Math.round((h/24) * raStepsPerRev);
    const newAlign = raPosition - raZeroOffsetSteps - base;
    info.raOldAlign = raAlignOffsetSteps;
    raAlignOffsetSteps = newAlign;
    changedRA = true;
  }

  // DEC: choose alignment by current HA pier side; keep mount stationary and adjust offset so reported DEC matches decDeg
  if (Number.isFinite(decDeg)){
    let d = Math.max(-90, Math.min(90, decDeg));
    // Determine HA using current RA and current LST
    const currentReportedRA = raStepsToReportedHours(raPosition);
    const lst = localSiderealTimeHours(new Date());
    let ha = lst - currentReportedRA; if (ha < -12) ha += 24; if (ha > 12) ha -= 24;
    // Compute mechanical angle(s)
    let mechA = 90 - d; if (mechA < 0) mechA += 360; // primary
    let mechB = (mechA + 180) % 360;                // alternate
    const mech = (ha < 0) ? mechB : mechA; // East pier => alternate; West pier => primary
    const mechSteps = Math.round((mech/360) * decStepsPerRev);
    const newAlign = decPosition - decZeroOffsetSteps - mechSteps;
    info.decOldAlign = decAlignOffsetSteps;
    decAlignOffsetSteps = newAlign;
    changedDEC = true;
  }

  if (!changedRA && !changedDEC) return res.status(400).json({ error:'no-input', message:'Provide raHours and/or decDeg' });
  alignmentVersion++;
  saveState();
  broadcastMount();
  res.json({
    ok:true,
    changed: { ra: changedRA, dec: changedDEC },
    raAlignOffsetSteps,
    decAlignOffsetSteps,
    reported: { raHours: raStepsToReportedHours(raPosition), decDeg: decStepsToReportedDeg(decPosition) },
    info
  });
});

// ---- RA soft limit calibration: set mapping so current position equals 0 (west) or 128000 (east) ----
app.post('/ra/soft-limit-here',(req,res)=>{
  try {
    const side = (req.body && req.body.side) || 'west';
    const delta = parseInt(req.body && req.body.delta, 10) || 0; // optional fine adjustment in steps
    const desired = (String(side).toLowerCase() === 'east') ? 128000 : 0;
    // Choose raZeroOffsetSteps so that (steps + delta) maps to desired
    // rel = (steps + delta) - raZeroOffsetSteps - raAlignOffsetSteps = desired
    // => raZeroOffsetSteps = (steps + delta) - desired - raAlignOffsetSteps
    raZeroOffsetSteps = (raPosition + delta) - desired - raAlignOffsetSteps;
    saveState();
    broadcastMount();
    res.json({ ok:true, side: String(side).toLowerCase(), desired, delta, raZeroOffsetSteps, currentSteps: raPosition, reportedRaHours: raStepsToReportedHours(raPosition) });
  } catch(e){
    res.status(500).json({ ok:false, error:'ra-soft-limit-failed', detail: e.message });
  }
});

// ---- Mount Command Endpoint (/mount) ----
// Supports simple commands like RA_MOVE:+12n3, DEC_MOVE:-50, RA_STOP, DEC_STOP (STOP are no-ops placeholder)
app.post('/mount',(req,res)=>{
  const { command } = req.body||{};
  if (typeof command !== 'string' ) return res.status(400).json({ error:'invalid-command' });
  let m = command.match(/^(RA|DEC)_MOVE:([+-]?)(\d+)$/);
  if (m){
    const axis = m[1]; const sign = m[2] === '-' ? -1 : 1; const steps = parseInt(m[3],10) * sign;
    if (axis === 'RA'){
      let np = raPosition + steps; if(np<raMinLimit) np=raMinLimit; else if(np>raMaxLimit) np=raMaxLimit; raPosition=np;
    } else {
      let np = decPosition + steps; if(np<decMinLimit) np=decMinLimit; else if(np>decMaxLimit) np=decMaxLimit; decPosition=np;
    }
    saveState(); broadcastMount();
    return res.json({ ok:true, raSteps:raPosition, decSteps:decPosition });
  }
  if (/^(RA|DEC)_STOP$/.test(command)) return res.json({ ok:true, noop:true });
  // MERIDIAN_FLIP no longer supported in relative-only mode
  return res.status(400).json({ error:'unsupported-command' });
});

// Physical nudge (used by motion anomaly auto-recovery)
app.post('/mount-nudge-physical',(req,res)=>{
  const { axis, direction, steps } = req.body||{};
  if(!['RA','DEC'].includes(axis)) return res.status(400).json({ error:'bad-axis' });

  const mult = direction === '-' ? -1 : 1;
  const amt = Number.isFinite(steps)? parseInt(steps,10):0;
  if(!amt) return res.status(400).json({ error:'no-steps' });

  const stepCount = mult * amt; // can be negative
  let command = null;

  if(axis==='RA'){
    let np = raPosition + stepCount;
    if(np < raMinLimit) np = raMinLimit; else if(np > raMaxLimit) np = raMaxLimit;
    if (np !== raPosition || raPosition === raMaxLimit || raPosition === raMinLimit){
  command = `RA_MOVE:${stepCount}`; // inversion applied in writeMountSerial
    }
    raPosition = np;
  } else { // DEC
    let np = decPosition + stepCount;
    if(np < decMinLimit) np = decMinLimit; else if(np > decMaxLimit) np = decMaxLimit;
    if (np !== decPosition || decPosition === decMaxLimit || decPosition === decMinLimit){
  command = `DEC_MOVE:${stepCount}`; // inversion applied in writeMountSerial
    }
    decPosition = np;
  }

  if (command) writeMountSerial(command);

  saveState(); broadcastMount();
  res.json({ ok:true, raSteps:raPosition, decSteps:decPosition });
});

// ---- Home Mount (move to nearest ±5h HA) ----
app.post('/mount/home',(req,res)=>{
  try {
    // New logic: move to nearest ±5 hour HA position, shortest route. DEC is unchanged.
    const currentLstHours = localSiderealTimeHours(new Date());
    const currentRaHours = raStepsToReportedHours(raPosition);
    const currentHaHours = computeHourAngleHours(currentRaHours, currentLstHours);

    const targetHaPositive = 5;
    const targetHaNegative = -5;

    // Calculate shortest delta to +5h and -5h
    let deltaPos = targetHaPositive - currentHaHours;
    if (deltaPos > 12) deltaPos -= 24;
    if (deltaPos < -12) deltaPos += 24;

    let deltaNeg = targetHaNegative - currentHaHours;
    if (deltaNeg > 12) deltaNeg -= 24;
    if (deltaNeg < -12) deltaNeg += 24;

    // Choose the target with the smaller absolute delta
    const targetHa = Math.abs(deltaPos) <= Math.abs(deltaNeg) ? targetHaPositive : targetHaNegative;
    
    // Convert target HA to RA timeline steps
    const targetRaTimelineSteps = haToRaTimelineSteps(targetHa);
    
    // Current RA in timeline steps
    const currentRaTimelineSteps = haToRaTimelineSteps(currentHaHours);
    
    // Calculate the shortest delta in timeline space
    const raDelta = targetRaTimelineSteps - currentRaTimelineSteps;
    const decDelta = 0; // DEC is unchanged

    console.log(`[HOME] Current HA: ${currentHaHours.toFixed(3)}h. Target HA: ${targetHa}h. RA Delta: ${raDelta} steps.`);

    // Move motors
    const serial = serialStatus();
    if (serial.connected && mountSerial.port) {
      try {
        writeMountSerial(`RA_MOVE:${raDelta}`);
        // No DEC move needed
        setTimeout(() => {
          try {
            writeMountSerial('GET_STATUS');
            writeMountSerial('GET_POS');
          } catch(e) { console.warn('Status request failed:', e.message); }
        }, 500);
      } catch(e) {
        console.warn('Hardware HOME command failed:', e.message);
      }
    }

    // Update software position
    raPosition += raDelta;
    // Clamp to safety limits
    raPosition = Math.max(raMinLimit, Math.min(raMaxLimit, raPosition));

    const finalRaHours = raStepsToReportedHours(raPosition);
    const finalDecDeg = decStepsToReportedDeg(decPosition);
    
    const payload = {
      status: 'homed',
      homeMethod: 'shortest-route-to-ha5',
      targetHa,
      raDelta,
      decDelta,
      reported: { raHours: finalRaHours, decDeg: finalDecDeg },
      steps: { ra: raPosition, dec: decPosition },
    };
    
    saveState();
    broadcastMount();
    res.json(payload);
  } catch(error) {
    console.error('Home mount failed:', error);
    res.status(500).json({ error: 'Home operation failed', message: error.message });
  }
});

// ---- Raw mount serial write (for debugging / fallback) ----
app.post('/serial/mount/write',(req,res)=>{
  const { data } = req.body||{};
  if (typeof data !== 'string') return res.status(400).json({ error:'no-data' });
  
  const serial = serialStatus();
  if (!serial.connected || !mountSerial.port) {
    return res.status(400).json({ error:'not-connected' });
  }
  
  try {
    writeMountSerial(data.trim());
    res.json({ ok: true, sent: data.trim() });
  } catch(e) {
    res.status(500).json({ error:'write-failed', detail: e.message });
  }
});
