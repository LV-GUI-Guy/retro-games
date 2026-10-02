/* Tetris Classic — vanilla JS, no dependencies.
 * Compatible with Safari / Chrome / Firefox (ES2019, Canvas 2D, localStorage).
 * Features: 7-bag, SRS-style wall kicks, ghost piece, hold, next x3,
 * scoring/levels, start-pause-end, localStorage leaderboard, touch controls.
 */
(function () {
  'use strict';

  var COLS = 10;
  var ROWS = 20;
  var CELL = 30; // board canvas is 300x600
  var LEADER_KEY = 'tetris_leaderboard_v1';
  var MAX_SCORES = 10;

  var COLORS = {
    I: '#38e1ff',
    O: '#ffd23f',
    T: '#c26bff',
    S: '#37d67a',
    Z: '#ff5252',
    J: '#5b8cff',
    L: '#ff9f43'
  };

  // Base spawn matrices (4x4 for I, 2x2 for O, 3x3 for the rest)
  var SHAPES = {
    I: [[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
    O: [[1, 1], [1, 1]],
    T: [[0, 1, 0], [1, 1, 1], [0, 0, 0]],
    S: [[0, 1, 1], [1, 1, 0], [0, 0, 0]],
    Z: [[1, 1, 0], [0, 1, 1], [0, 0, 0]],
    J: [[1, 0, 0], [1, 1, 1], [0, 0, 0]],
    L: [[0, 0, 1], [1, 1, 1], [0, 0, 0]]
  };

  // Simplified SRS wall-kick offsets (tried in order). Full SRS has per-rotation
  // tables; this subset handles the common near-wall / near-stack cases and is
  // deterministic across browsers.
  var KICKS_JLSTZ = [[0, 0], [-1, 0], [1, 0], [0, -1], [-1, -1], [1, -1], [0, 1], [-2, 0], [2, 0]];
  var KICKS_I = [[0, 0], [-2, 0], [2, 0], [-1, 0], [1, 0], [0, -1], [0, 1], [-1, -1], [1, -1]];
  var KICKS_O = [[0, 0]];

  var LINE_SCORES = [0, 100, 300, 500, 800];

  // ---------- DOM ----------
  function $(id) { return document.getElementById(id); }

  var boardCanvas = $('board');
  var ctx = boardCanvas.getContext('2d');
  var holdCanvas = $('holdCanvas');
  var holdCtx = holdCanvas.getContext('2d');
  var holdMobile = $('holdCanvasMobile');
  var holdMobileCtx = holdMobile ? holdMobile.getContext('2d') : null;
  var nextCanvas = $('nextCanvas');
  var nextCtx = nextCanvas.getContext('2d');
  var nextMobile = $('nextCanvasMobile');
  var nextMobileCtx = nextMobile ? nextMobile.getContext('2d') : null;

  var elScore = $('score'), elLevel = $('level'), elLines = $('lines');
  var overlay = $('overlay'), overlayTitle = $('overlayTitle'), overlayText = $('overlayText');
  var startBtn = $('startBtn'), resumeBtn = $('resumeBtn'), restartBtn = $('restartBtn');
  var saveScoreBtn = $('saveScoreBtn'), nameRow = $('nameRow'), playerName = $('playerName');
  var startPauseBtn = $('startPauseBtn'), stopBtn = $('stopBtn'), muteBtn = $('muteBtn');
  var holdBtn = $('holdBtn');
  var tHoldBtn = $('tHold');
  var holdBayMobile = $('holdBayMobile');
  var overlayScores = $('overlayScores');
  var boardList = $('leaderboard'), boardListMobile = $('leaderboardMobile');
  var clearScoresBtn = $('clearScoresBtn');

  // ---------- State ----------
  var grid, current, nextQueue, bag;
  var heldType, canHold;
  var score, level, lines, dropInterval;
  var state; // 'ready' | 'playing' | 'paused' | 'over'
  var lastTime, dropCounter;
  var rafId;
  var flashRows, flashUntil;
  var soundOn = false;

  function emptyGrid() {
    var g = [];
    for (var y = 0; y < ROWS; y++) {
      g.push(new Array(COLS).fill(null));
    }
    return g;
  }

  function resetState() {
    grid = emptyGrid();
    bag = [];
    nextQueue = [];
    heldType = null;
    canHold = true;
    score = 0; level = 1; lines = 0;
    dropInterval = speedForLevel(1);
    current = null;
    flashRows = [];
    flashUntil = 0;
    refillQueue();
    updateHud();
  }

  function speedForLevel(lv) {
    // Guideline-ish curve: 800ms at L1 down to ~50ms floor.
    return Math.max(800 * Math.pow(0.85, lv - 1), 50);
  }

  // ---------- 7-bag ----------
  function shuffledBag() {
    var types = ['I', 'O', 'T', 'S', 'Z', 'J', 'L'];
    for (var i = types.length - 1; i > 0; i--) {
      var j = Math.floor(Math.random() * (i + 1));
      var t = types[i]; types[i] = types[j]; types[j] = t;
    }
    return types;
  }

  function refillQueue() {
    while (nextQueue.length < 7) {
      if (bag.length === 0) bag = shuffledBag();
      nextQueue.push(bag.pop());
    }
  }

  // Kept as a named function because TEST_PLAN TG-001 references `randomPiece()`.
  function randomPiece() {
    refillQueue();
    return nextQueue.shift();
  }

  function makePiece(type) {
    return {
      type: type,
      matrix: copyMatrix(SHAPES[type]),
      x: type === 'O' ? 4 : 3,
      y: 0
    };
  }

  function copyMatrix(m) {
    return m.map(function (row) { return row.slice(); });
  }

  function rotateMatrix(m, dir) {
    var n = m.length;
    var out = [];
    for (var y = 0; y < n; y++) {
      out.push(new Array(m[y].length).fill(0));
    }
    for (var r = 0; r < n; r++) {
      for (var c = 0; c < m[r].length; c++) {
        if (dir > 0) out[c][n - 1 - r] = m[r][c];
        else out[n - 1 - c][r] = m[r][c];
      }
    }
    return out;
  }

  function collides(matrix, px, py) {
    for (var r = 0; r < matrix.length; r++) {
      for (var c = 0; c < matrix[r].length; c++) {
        if (!matrix[r][c]) continue;
        var x = px + c, y = py + r;
        if (x < 0 || x >= COLS || y >= ROWS) return true;
        if (y >= 0 && grid[y][x]) return true;
      }
    }
    return false;
  }

  function spawnPiece() {
    refillQueue();
    var type = nextQueue.shift();
    refillQueue();
    current = makePiece(type);
    canHold = true;
    // Game over: new piece immediately collides (top-out / block-out).
    if (collides(current.matrix, current.x, current.y)) {
      current.y = -1;
      if (collides(current.matrix, current.x, current.y)) {
        gameOver();
        return;
      }
    }
    drawSidePanels();
  }

  // ---------- Movement ----------
  function move(dx, dy) {
    if (state !== 'playing' || !current) return false;
    var nx = current.x + dx, ny = current.y + dy;
    if (!collides(current.matrix, nx, ny)) {
      current.x = nx; current.y = ny;
      if (dy > 0) { dropCounter = 0; }
      draw();
      return true;
    }
    return false;
  }

  function rotate(dir) {
    if (state !== 'playing' || !current) return false;
    if (current.type === 'O') return false;
    var rotated = rotateMatrix(current.matrix, dir);
    var kicks = current.type === 'I' ? KICKS_I : KICKS_JLSTZ;
    for (var i = 0; i < kicks.length; i++) {
      var nx = current.x + kicks[i][0];
      var ny = current.y + kicks[i][1];
      if (!collides(rotated, nx, ny)) {
        current.matrix = rotated;
        current.x = nx; current.y = ny;
        beep(520, 0.04);
        draw();
        return true;
      }
    }
    return false;
  }

  function softDrop() {
    if (move(0, 1)) {
      score += 1;
      updateHud();
    } else {
      lockPiece();
    }
  }

  function hardDrop() {
    if (state !== 'playing' || !current) return;
    var dist = 0;
    while (!collides(current.matrix, current.x, current.y + 1)) {
      current.y++;
      dist++;
    }
    score += dist * 2;
    beep(880, 0.06);
    lockPiece();
  }

  function ghostY() {
    if (!current) return 0;
    var y = current.y;
    while (!collides(current.matrix, current.x, y + 1)) y++;
    return y;
  }

  // ---------- Hold ----------
  function holdPiece() {
    if (state !== 'playing' || !current || !canHold) return false;
    beep(440, 0.05);
    if (heldType === null) {
      heldType = current.type;
      spawnPiece();
      canHold = false; // spawnPiece() re-arms hold; lock it until next spawn
    } else {
      var tmp = heldType;
      heldType = current.type;
      current = makePiece(tmp);
      current.x = tmp === 'O' ? 4 : 3;
      current.y = 0;
      canHold = false;
      if (collides(current.matrix, current.x, current.y)) {
        gameOver();
        return true;
      }
    }
    drawSidePanels();
    draw();
    return true;
  }

  // ---------- Lock / clear / score ----------
  function lockPiece() {
    if (!current) return;
    var m = current.matrix;
    var aboveTop = false;
    for (var r = 0; r < m.length; r++) {
      for (var c = 0; c < m[r].length; c++) {
        if (!m[r][c]) continue;
        var x = current.x + c, y = current.y + r;
        if (y < 0) { aboveTop = true; continue; }
        grid[y][x] = current.type;
      }
    }
    if (aboveTop) { gameOver(); return; }
    clearLines();
    spawnPiece();
    draw();
  }

  function fullRow(y) {
    for (var x = 0; x < COLS; x++) {
      if (!grid[y][x]) return false;
    }
    return true;
  }

  function clearLines() {
    var cleared = [];
    for (var y = ROWS - 1; y >= 0; y--) {
      if (fullRow(y)) cleared.push(y);
    }
    if (cleared.length === 0) return;
    // Remove rows bottom-up
    cleared.sort(function (a, b) { return a - b; });
    for (var i = 0; i < cleared.length; i++) {
      grid.splice(cleared[i] - i, 1);
      grid.unshift(new Array(COLS).fill(null));
    }
    var n = cleared.length;
    score += LINE_SCORES[n] * level;
    lines += n;
    var newLevel = Math.floor(lines / 10) + 1;
    if (newLevel !== level) {
      level = newLevel;
      dropInterval = speedForLevel(level);
      beep(660, 0.1);
    }
    flashRows = cleared.map(function () { return true; });
    flashUntil = performance.now() + 180;
    updateHud();
    if (n === 4) beep(990, 0.15);
    else beep(700, 0.08);
  }

  // ---------- Game flow ----------
  function startGame() {
    resetState();
    state = 'playing';
    spawnPiece();
    lastTime = performance.now();
    dropCounter = 0;
    cancelLoop();
    rafId = raf(loop);
    showOverlay(null);
    startPauseBtn.textContent = 'Pause';
    stopBtn.disabled = false;
    draw();
  }

  function pauseGame() {
    if (state !== 'playing') return;
    state = 'paused';
    cancelLoop();
    startPauseBtn.textContent = 'Resume';
    showOverlay('paused');
  }

  function resumeGame() {
    if (state !== 'paused') return;
    state = 'playing';
    lastTime = performance.now();
    cancelLoop();
    rafId = raf(loop);
    showOverlay(null);
    startPauseBtn.textContent = 'Pause';
  }

  function togglePause() {
    if (state === 'playing') pauseGame();
    else if (state === 'paused') resumeGame();
  }

  function endGame(reason) {
    if (state !== 'playing' && state !== 'paused') return;
    state = 'over';
    cancelLoop();
    startPauseBtn.textContent = 'Start';
    stopBtn.disabled = true;
    showOverlay('over', reason);
  }

  function gameOver() {
    state = 'over';
    cancelLoop();
    startPauseBtn.textContent = 'Start';
    stopBtn.disabled = true;
    draw();
    showOverlay('over');
  }

  function cancelLoop() {
    if (rafId) {
      caf(rafId);
      rafId = 0;
    }
  }

  function loop(now) {
    if (state !== 'playing') return;
    var dt = now - lastTime;
    lastTime = now;
    dropCounter += dt;
    if (dropCounter >= dropInterval) {
      dropCounter = 0;
      if (!move(0, 1)) lockPiece();
    }
    draw();
    rafId = raf(loop);
  }

  function raf(cb) {
    if (window.requestAnimationFrame) return window.requestAnimationFrame(cb);
    return window.setTimeout(function () { cb(Date.now()); }, 16);
  }

  function caf(id) {
    if (window.cancelAnimationFrame) window.cancelAnimationFrame(id);
    else window.clearTimeout(id);
  }

  // ---------- Rendering ----------
  function drawCell(g, x, y, color, ghost) {
    var px = x * CELL, py = y * CELL;
    if (ghost) {
      g.strokeStyle = color;
      g.lineWidth = 2;
      g.strokeRect(px + 2, py + 2, CELL - 4, CELL - 4);
      return;
    }
    g.fillStyle = color;
    g.fillRect(px + 1, py + 1, CELL - 2, CELL - 2);
    // Bevel highlight (cheap, works everywhere)
    g.fillStyle = 'rgba(255,255,255,0.35)';
    g.fillRect(px + 1, py + 1, CELL - 2, 4);
    g.fillRect(px + 1, py + 1, 4, CELL - 2);
    g.fillStyle = 'rgba(0,0,0,0.25)';
    g.fillRect(px + 1, py + CELL - 5, CELL - 2, 4);
    g.fillRect(px + CELL - 5, py + 1, 4, CELL - 2);
  }

  function draw() {
    ctx.clearRect(0, 0, boardCanvas.width, boardCanvas.height);
    updateHoldUI();
    var y, x;
    // Locked cells
    for (y = 0; y < ROWS; y++) {
      for (x = 0; x < COLS; x++) {
        if (grid[y] && grid[y][x]) drawCell(ctx, x, y, COLORS[grid[y][x]]);
      }
    }
    // Line-clear flash
    if (flashRows.length && performance.now() < flashUntil) {
      ctx.fillStyle = 'rgba(255,255,255,0.5)';
      // flash the bottom area where lines were cleared (simple + visible)
      ctx.fillRect(0, boardCanvas.height - flashRows.length * CELL, boardCanvas.width, flashRows.length * CELL);
    }
    if (!current) return;
    // Ghost
    var gy = ghostY();
    var m = current.matrix;
    ctx.globalAlpha = 0.9;
    for (var r = 0; r < m.length; r++) {
      for (var c = 0; c < m[r].length; c++) {
        if (!m[r][c]) continue;
        var gx = current.x + c, gr = gy + r;
        if (gr >= 0) drawCell(ctx, gx, gr, COLORS[current.type], true);
      }
    }
    ctx.globalAlpha = 1;
    // Active
    for (var r2 = 0; r2 < m.length; r2++) {
      for (var c2 = 0; c2 < m[r2].length; c2++) {
        if (!m[r2][c2]) continue;
        var ax = current.x + c2, ay = current.y + r2;
        if (ay >= 0) drawCell(ctx, ax, ay, COLORS[current.type]);
      }
    }
  }

  function drawMini(g, canvas, type) {
    g.clearRect(0, 0, canvas.width, canvas.height);
    if (!type) return;
    var m = SHAPES[type];
    var n = m.length;
    var cell = Math.min(canvas.width / 4, canvas.height / 4);
    if (canvas.width <= 80) cell = Math.min(canvas.width / 4.4, canvas.height / 3.2);
    var w = 0, h = 0;
    var minR = 99, maxR = -1, minC = 99, maxC = -1;
    for (var r = 0; r < n; r++) {
      for (var c = 0; c < m[r].length; c++) {
        if (m[r][c]) {
          if (r < minR) minR = r;
          if (r > maxR) maxR = r;
          if (c < minC) minC = c;
          if (c > maxC) maxC = c;
        }
      }
    }
    w = (maxC - minC + 1) * cell;
    h = (maxR - minR + 1) * cell;
    var ox = (canvas.width - w) / 2 - minC * cell;
    var oy = (canvas.height - h) / 2 - minR * cell;
    for (var r2 = 0; r2 < n; r2++) {
      for (var c2 = 0; c2 < m[r2].length; c2++) {
        if (!m[r2][c2]) continue;
        var px = ox + c2 * cell, py = oy + r2 * cell;
        g.fillStyle = COLORS[type];
        g.fillRect(px + 1, py + 1, cell - 2, cell - 2);
        g.fillStyle = 'rgba(255,255,255,0.35)';
        g.fillRect(px + 1, py + 1, cell - 2, 2);
      }
    }
  }

  function drawSidePanels() {
    drawMini(holdCtx, holdCanvas, heldType);
    if (holdMobileCtx && holdMobile) drawMini(holdMobileCtx, holdMobile, heldType);
    // Desktop shows 3 upcoming; mobile mini shows 1
    nextCtx.clearRect(0, 0, nextCanvas.width, nextCanvas.height);
    var slotH = nextCanvas.height / 3;
    for (var i = 0; i < Math.min(3, nextQueue.length); i++) {
      nextCtx.save();
      nextCtx.beginPath();
      nextCtx.rect(0, i * slotH, nextCanvas.width, slotH);
      nextCtx.clip();
      drawMiniInSlot(nextQueue[i], i * slotH, slotH);
      nextCtx.restore();
    }
    if (nextMobileCtx && nextMobile) drawMini(nextMobileCtx, nextMobile, nextQueue[0] || null);
    updateHoldUI();
  }

  // Hold controls reflect the one-hold-per-piece lock: dimmed/disabled while
  // locked so touch players can see at a glance whether HOLD will do anything.
  // Change-checked so the per-frame call from draw() costs nothing.
  var lastHoldUiKey = null;
  function updateHoldUI() {
    var key = state + ':' + (canHold ? '1' : '0');
    if (key === lastHoldUiKey) return;
    lastHoldUiKey = key;
    var enabled = (state === 'playing' && canHold);
    holdBtn.disabled = !enabled;
    if (tHoldBtn) tHoldBtn.disabled = !enabled;
    if (holdBayMobile) {
      holdBayMobile.classList.toggle('locked', !enabled);
      holdBayMobile.setAttribute('aria-disabled', String(!enabled));
    }
  }

  function drawMiniInSlot(type, yOff, slotH) {
    var m = SHAPES[type];
    var n = m.length;
    var cell = Math.min(nextCanvas.width / 5, slotH / 4.4);
    var minR = 99, maxR = -1, minC = 99, maxC = -1, r, c;
    for (r = 0; r < n; r++) {
      for (c = 0; c < m[r].length; c++) {
        if (m[r][c]) {
          minR = Math.min(minR, r); maxR = Math.max(maxR, r);
          minC = Math.min(minC, c); maxC = Math.max(maxC, c);
        }
      }
    }
    var w = (maxC - minC + 1) * cell;
    var h = (maxR - minR + 1) * cell;
    var ox = (nextCanvas.width - w) / 2 - minC * cell;
    var oy = yOff + (slotH - h) / 2 - minR * cell;
    for (r = 0; r < n; r++) {
      for (c = 0; c < m[r].length; c++) {
        if (!m[r][c]) continue;
        nextCtx.fillStyle = COLORS[type];
        nextCtx.fillRect(ox + c * cell + 1, oy + r * cell + 1, cell - 2, cell - 2);
      }
    }
  }

  function updateHud() {
    elScore.textContent = String(score);
    elLevel.textContent = String(level);
    elLines.textContent = String(lines);
  }

  // ---------- Overlay ----------
  function showOverlay(mode, reason) {
    saveScoreBtn.classList.add('hidden');
    nameRow.classList.add('hidden');
    resumeBtn.classList.add('hidden');
    restartBtn.classList.add('hidden');
    overlayScores.classList.add('hidden');
    overlayScores.innerHTML = '';
    startBtn.classList.remove('hidden');

    if (mode === null) {
      overlay.classList.add('hidden');
      return;
    }
    overlay.classList.remove('hidden');
    if (mode === 'paused') {
      overlayTitle.textContent = 'PAUSED';
      overlayText.textContent = 'Score ' + score + ' — Level ' + level;
      startBtn.classList.add('hidden');
      resumeBtn.classList.remove('hidden');
      restartBtn.classList.remove('hidden');
    } else if (mode === 'ready') {
      overlayTitle.textContent = 'TETRIS';
      overlayText.textContent = 'Press Start to play';
    } else if (mode === 'over') {
      overlayTitle.textContent = 'GAME OVER';
      overlayText.textContent = (reason ? reason + ' ' : '') + 'Score ' + score + ' · Level ' + level + ' · Lines ' + lines;
      startBtn.textContent = 'Play again';
      nameRow.classList.remove('hidden');
      saveScoreBtn.classList.remove('hidden');
      restartBtn.classList.remove('hidden');
      renderOverlayScores();
    } else if (mode === 'stopped') {
      overlayTitle.textContent = 'GAME ENDED';
      overlayText.textContent = 'Score ' + score + ' · Level ' + level + ' · Lines ' + lines;
      startBtn.textContent = 'Play again';
      nameRow.classList.remove('hidden');
      saveScoreBtn.classList.remove('hidden');
      renderOverlayScores();
    }
  }

  // Top-5 in the end overlay: on iPhone the page doesn't scroll (overflow
  // hidden), so this is the mobile player's way to see the leaderboard.
  function renderOverlayScores() {
    var arr = loadScores().slice(0, 5);
    if (!arr.length) return;
    overlayScores.innerHTML = arr.map(function (e, i) {
      return '<li>#' + (i + 1) + ' ' + escapeHtml(e.name) + ' — ' + e.score + '</li>';
    }).join('');
    overlayScores.classList.remove('hidden');
  }

  // ---------- Leaderboard ----------
  function loadScores() {
    try {
      var raw = window.localStorage.getItem(LEADER_KEY);
      if (!raw) return [];
      var arr = JSON.parse(raw);
      return Array.isArray(arr) ? arr : [];
    } catch (e) {
      return [];
    }
  }

  function persistScores(arr) {
    try {
      window.localStorage.setItem(LEADER_KEY, JSON.stringify(arr.slice(0, MAX_SCORES)));
    } catch (e) { /* private mode / quota — game still works */ }
  }

  function addScore(name, s, lv, ln) {
    var arr = loadScores();
    arr.push({ name: (name || 'YOU').toUpperCase().slice(0, 12), score: s, level: lv, lines: ln, date: Date.now() });
    arr.sort(function (a, b) { return b.score - a.score; });
    persistScores(arr);
    renderLeaderboard();
    return arr;
  }

  function renderLeaderboard() {
    var arr = loadScores();
    var html = arr.length
      ? arr.map(function (e, i) {
          return '<li><strong>#' + (i + 1) + '</strong> ' + escapeHtml(e.name) +
            ' — ' + e.score + ' <small>(Lv ' + e.level + ')</small></li>';
        }).join('')
      : '<li class="empty">No scores yet — be the first!</li>';
    boardList.innerHTML = html;
    if (boardListMobile) boardListMobile.innerHTML = html;
  }

  function escapeHtml(s) {
    return String(s).replace(/[&<>"']/g, function (ch) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[ch];
    });
  }

  // ---------- Sound (tiny WebAudio blips, off by default) ----------
  var audioCtx = null;
  function beep(freq, dur) {
    if (!soundOn) return;
    try {
      var AC = window.AudioContext || window.webkitAudioContext;
      if (!AC) return;
      if (!audioCtx) audioCtx = new AC();
      if (audioCtx.state === 'suspended') audioCtx.resume();
      var o = audioCtx.createOscillator();
      var g = audioCtx.createGain();
      o.type = 'square';
      o.frequency.value = freq;
      g.gain.value = 0.04;
      o.connect(g); g.connect(audioCtx.destination);
      o.start();
      o.stop(audioCtx.currentTime + dur);
    } catch (e) { /* audio is decorative */ }
  }

  // ---------- Input: keyboard ----------
  document.addEventListener('keydown', function (e) {
    var k = e.key;
    // Prevent page scroll for game keys (space/arrows) in all browsers
    if ([' ', 'ArrowLeft', 'ArrowRight', 'ArrowDown', 'ArrowUp'].indexOf(k) >= 0) e.preventDefault();
    if (k === 'p' || k === 'P' || k === 'Escape') {
      if (state === 'playing' || state === 'paused') togglePause();
      return;
    }
    if (state !== 'playing') {
      if (k === 'Enter' && !overlay.classList.contains('hidden')) {
        if (state === 'ready' || state === 'over') startGame();
        else if (state === 'paused') resumeGame();
      }
      return;
    }
    switch (k) {
      case 'ArrowLeft': move(-1, 0); break;
      case 'ArrowRight': move(1, 0); break;
      case 'ArrowDown': softDrop(); break;
      case 'ArrowUp':
      case 'x':
      case 'X': rotate(1); break;
      case 'z':
      case 'Z': rotate(-1); break;
      case ' ':
        // Avoid repeat-triggered multi drops when holding space
        if (!e.repeat) hardDrop();
        break;
      case 'c':
      case 'C':
      case 'Shift': holdPiece(); break;
      default: break;
    }
  });

  // ---------- Input: touch buttons (with auto-repeat for held direction) ----------
  function bindHoldRepeat(el, fn, initialDelay, repeatMs) {
    var t1 = 0, t2 = 0;
    function clear() {
      window.clearTimeout(t1); window.clearInterval(t2);
      t1 = 0; t2 = 0;
    }
    function start(e) {
      if (e && e.preventDefault) e.preventDefault();
      fn();
      clear();
      t1 = window.setTimeout(function () {
        t2 = window.setInterval(fn, repeatMs);
      }, initialDelay);
    }
    // touchstart + mousedown cover iOS Safari + desktop; mouseup/leave/touchend stop repeat
    el.addEventListener('touchstart', start, { passive: false });
    el.addEventListener('mousedown', start);
    ['touchend', 'touchcancel', 'mouseup', 'mouseleave'].forEach(function (ev) {
      el.addEventListener(ev, clear);
    });
  }

  function bindTap(el, fn) {
    el.addEventListener('touchstart', function (e) { e.preventDefault(); fn(); }, { passive: false });
    el.addEventListener('click', function (e) { e.preventDefault(); fn(); });
  }

  // ---------- Wire up ----------
  startBtn.addEventListener('click', startGame);
  restartBtn.addEventListener('click', startGame);
  resumeBtn.addEventListener('click', resumeGame);
  startPauseBtn.addEventListener('click', function () {
    if (state === 'playing') pauseGame();
    else if (state === 'paused') resumeGame();
    else startGame();
  });
  stopBtn.addEventListener('click', function () {
    if (state === 'playing' || state === 'paused') {
      if (state === 'playing') cancelLoop();
      state = 'over';
      startPauseBtn.textContent = 'Start';
      stopBtn.disabled = true;
      draw();
      showOverlay('stopped');
    }
  });
  saveScoreBtn.addEventListener('click', function () {
    var nm = (playerName.value || 'YOU').trim() || 'YOU';
    addScore(nm, score, level, lines);
    saveScoreBtn.classList.add('hidden');
    nameRow.classList.add('hidden');
    renderOverlayScores();
    overlayText.textContent += ' — saved!';
  });
  clearScoresBtn.addEventListener('click', function () {
    persistScores([]);
    renderLeaderboard();
  });
  muteBtn.addEventListener('click', function () {
    soundOn = !soundOn;
    muteBtn.textContent = soundOn ? 'Sound: On' : 'Sound: Off';
  });
  holdBtn.addEventListener('click', holdPiece);

  bindHoldRepeat($('tLeft'), function () { move(-1, 0); }, 220, 70);
  bindHoldRepeat($('tRight'), function () { move(1, 0); }, 220, 70);
  bindHoldRepeat($('tDown'), function () { softDrop(); }, 180, 60);
  bindTap($('tRotate'), function () { rotate(1); });
  bindTap($('tDrop'), function () { hardDrop(); });
  bindTap($('tHold'), function () { holdPiece(); });
  // The Hold bay itself is a big touch target (easier to discover than the button)
  if (holdBayMobile) {
    bindTap(holdBayMobile, function () { holdPiece(); });
    holdBayMobile.addEventListener('keydown', function (e) {
      if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); holdPiece(); }
    });
  }

  // Touch gestures on the board.
  // Disambiguation rules (tap vs. swipe), all measured from the touch ORIGIN:
  // - Tap (rotate): lifts within TAP_SLOP px of origin, no drag ever exceeded slop.
  // - Drag: finger travels -> horizontal steps move the piece, vertical steps soft-drop.
  // - Flick down (hard drop): fast, mostly-downward motion, decided at touchend by
  //   total displacement + duration, so it works even when iOS delivers almost no
  //   touchmove events for a quick flick (the old code rotated the piece instead).
  // Buttons remain the primary control; gestures are a convenience.
  (function enableSwipe() {
    var TAP_SLOP = 14;   // px from origin still counted as "not a swipe"
    var STEP = 26;       // px of drag per move / soft-drop step
    var FLICK_MS = 350;  // max duration for a lift to count as a flick
    var FLICK_DY = 28;   // min downward travel for a flick hard-drop
    var sx = 0, sy = 0, lastX = 0, lastDownY = 0, t0 = 0;
    var tracking = false, moved = false;
    boardCanvas.addEventListener('touchstart', function (e) {
      var t = e.changedTouches[0];
      sx = t.clientX; sy = t.clientY;
      lastX = sx; lastDownY = sy;
      t0 = Date.now();
      tracking = true; moved = false;
    }, { passive: true });
    boardCanvas.addEventListener('touchmove', function (e) {
      if (!tracking || state !== 'playing') return;
      var t = e.changedTouches[0];
      var dxT = t.clientX - sx, dyT = t.clientY - sy;
      if (Math.abs(dxT) > TAP_SLOP || Math.abs(dyT) > TAP_SLOP) moved = true;
      // Horizontal drag: one cell per STEP px (uses a running cursor so repeats work)
      while (t.clientX - lastX > STEP) { if (!move(1, 0)) break; lastX += STEP; }
      while (lastX - t.clientX > STEP) { if (!move(-1, 0)) break; lastX += STEP; }
      // Vertical drag: soft-drop steps only — dragging never hard-drops by accident
      while (t.clientY - lastDownY > STEP) {
        var before = current;
        softDrop();
        if (state !== 'playing') { tracking = false; return; }
        lastDownY += STEP;
        if (current !== before) { lastX = t.clientX; } // fresh piece: re-anchor
      }
      if (e.cancelable) e.preventDefault();
    }, { passive: false });
    function end(e) {
      if (!tracking) return;
      tracking = false;
      if (state !== 'playing') return;
      var t = e.changedTouches[0];
      var dxT = t.clientX - sx, dyT = t.clientY - sy;
      var dt = Date.now() - t0;
      if (!moved && Math.abs(dxT) < TAP_SLOP && Math.abs(dyT) < TAP_SLOP) {
        rotate(1); // clean tap
      } else if (dyT > FLICK_DY && Math.abs(dyT) > Math.abs(dxT) && dt < FLICK_MS) {
        hardDrop(); // downward flick
      }
    }
    boardCanvas.addEventListener('touchend', end);
    boardCanvas.addEventListener('touchcancel', function () { tracking = false; });
  })();

  // Pause when tab hidden (prevents unfair top-outs)
  document.addEventListener('visibilitychange', function () {
    if (document.hidden && state === 'playing') pauseGame();
  });

  // ---------- Init ----------
  resetState();
  state = 'ready';
  renderLeaderboard();
  draw();
  drawSidePanels();
  showOverlay('ready');

  // Expose a small API for manual / automated testing (see TEST_PLAN.md)
  window.Tetris = {
    state: function () { return state; },
    score: function () { return { score: score, level: level, lines: lines }; },
    grid: function () { return grid; },
    current: function () { return current; },
    next: function () { return nextQueue.slice(); },
    held: function () { return heldType; },
    randomPiece: randomPiece,
    start: startGame,
    pause: pauseGame,
    resume: resumeGame,
    end: endGame,
    move: move,
    rotate: rotate,
    hold: holdPiece,
    hardDrop: hardDrop,
    addScore: addScore,
    leaderboard: loadScores
  };
})();
