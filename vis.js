// Curiosity Modeling visualizer for Sterling/Forge.
// Uses ES5-style JS for compatibility with Sterling's script engine.

function toStr(atom) {
  if (atom == null) return "";
  return atom.toString();
}

function tuplesOf(rel) {
  try {
    if (rel && rel.tuples) return rel.tuples();
  } catch (e) {}
  return [];
}

function getUnaryAtoms(rel) {
  var ts = tuplesOf(rel);
  var out = [];
  for (var i = 0; i < ts.length; i++) {
    var t = ts[i];
    if (t._atoms && t._atoms.length === 1) {
      out.push(toStr(t._atoms[0]));
    }
  }
  return out;
}

function mapBinary(rel) {
  var ts = tuplesOf(rel);
  var out = {};
  for (var i = 0; i < ts.length; i++) {
    var t = ts[i];
    if (t._atoms && t._atoms.length === 2) {
      out[toStr(t._atoms[0])] = toStr(t._atoms[1]);
    }
  }
  return out;
}

function pieceTypeFromAtomName(name) {
  if (!name) return "";
  // Forge atoms may look like `T_1 or T_1.
  var s = name;
  var tick = s.lastIndexOf("`");
  if (tick >= 0 && tick < s.length - 1) s = s.substring(tick + 1);
  for (var i = 0; i < s.length; i++) {
    var ch = s.charAt(i);
    if (ch >= "A" && ch <= "Z") return ch;
  }
  return s;
}

function pieceCells(pieceType) {
  if (pieceType === "I") return [[0,1],[1,1],[2,1],[3,1]];
  if (pieceType === "O") return [[1,0],[2,0],[1,1],[2,1]];
  if (pieceType === "T") return [[1,0],[0,1],[1,1],[2,1]];
  if (pieceType === "L") return [[2,0],[0,1],[1,1],[2,1]];
  if (pieceType === "J") return [[0,0],[0,1],[1,1],[2,1]];
  if (pieceType === "S") return [[1,0],[2,0],[0,1],[1,1]];
  if (pieceType === "Z") return [[0,0],[1,0],[1,1],[2,1]];
  return [];
}

function pieceColor(pieceType) {
  if (pieceType === "I") return "#22d3ee";
  if (pieceType === "O") return "#facc15";
  if (pieceType === "T") return "#a78bfa";
  if (pieceType === "L") return "#fb923c";
  if (pieceType === "J") return "#60a5fa";
  if (pieceType === "S") return "#4ade80";
  if (pieceType === "Z") return "#f87171";
  return "#cbd5e1";
}

function makePieceIcon(pieceType) {
  var box = document.createElement("div");
  box.className = "cm-nextpiece";

  var label = document.createElement("div");
  label.className = "cm-nextlabel";
  label.textContent = "next";
  box.appendChild(label);

  var icon = document.createElement("div");
  icon.className = "cm-pieceicon";
  box.appendChild(icon);

  var color = pieceColor(pieceType);
  var fill = {};
  var cells = pieceCells(pieceType);
  for (var i = 0; i < cells.length; i++) {
    fill[cells[i][0] + "|" + cells[i][1]] = true;
  }

  for (var y = 0; y < 2; y++) {
    var row = document.createElement("div");
    row.className = "cm-prow";
    for (var x = 0; x < 4; x++) {
      var p = document.createElement("div");
      p.className = "cm-pcell";
      if (fill[x + "|" + y]) {
        p.style.background = color;
        p.style.borderColor = "#334155";
      }
      row.appendChild(p);
    }
    icon.appendChild(row);
  }

  return box;
}

function isTrueAtomName(name) {
  // Avoid String.endsWith for older engines.
  return name.indexOf("True", name.length - 4) !== -1;
}

function setFromBoardTrue(boardRel) {
  var occ = {};
  // Preferred path: relationally filter cells where board = True.
  // board.join(True) should yield State -> Int -> Int.
  try {
    var jt = tuplesOf(boardRel.join(True));
    var states = getUnaryAtoms(State);
    for (var j = 0; j < jt.length; j++) {
      var tj = jt[j];
      if (!tj._atoms) continue;
      if (tj._atoms.length === 3) {
        var s3 = toStr(tj._atoms[0]);
        var x3 = toStr(tj._atoms[1]);
        var y3 = toStr(tj._atoms[2]);
        occ[s3 + "|" + x3 + "|" + y3] = true;
      } else if (tj._atoms.length === 2) {
        // Projected state: join(True) becomes Int -> Int.
        var x2 = toStr(tj._atoms[0]);
        var y2 = toStr(tj._atoms[1]);
        for (var si = 0; si < states.length; si++) {
          occ[states[si] + "|" + x2 + "|" + y2] = true;
        }
      }
    }
    if (jt.length > 0) return occ;
  } catch (e) {}

  // Fallback: inspect raw board tuples (State, Int, Int, Boolean).
  var ts = tuplesOf(boardRel);
  for (var i = 0; i < ts.length; i++) {
    var t = ts[i];
    if (!t._atoms || t._atoms.length !== 4) continue;
    var s = toStr(t._atoms[0]);
    var x = toStr(t._atoms[1]);
    var y = toStr(t._atoms[2]);
    var b = toStr(t._atoms[3]);
    if (isTrueAtomName(b)) {
      occ[s + "|" + x + "|" + y] = true;
    }
  }
  return occ;
}

function orderStates(states, nextMap) {
  var hasPred = {};
  for (var k in nextMap) {
    if (Object.prototype.hasOwnProperty.call(nextMap, k)) {
      hasPred[nextMap[k]] = true;
    }
  }

  var start = states.length > 0 ? states[0] : null;
  for (var i = 0; i < states.length; i++) {
    if (!hasPred[states[i]]) {
      start = states[i];
      break;
    }
  }

  var ordered = [];
  var seen = {};
  var cur = start;

  while (cur && !seen[cur]) {
    ordered.push(cur);
    seen[cur] = true;
    cur = nextMap[cur];
  }

  for (var j = 0; j < states.length; j++) {
    if (!seen[states[j]]) ordered.push(states[j]);
  }

  return ordered;
}

function injectStyle() {
  if (document.getElementById("curiosity-vis-style")) return;

  var style = document.createElement("style");
  style.id = "curiosity-vis-style";
  style.textContent = ""
    + ".cm-wrap{font-family:Arial,sans-serif;padding:12px;color:#1f2937;}"
    + ".cm-title{font-size:18px;font-weight:700;margin-bottom:10px;}"
    + ".cm-flow{display:flex;gap:14px;align-items:flex-start;overflow-x:auto;padding-bottom:8px;}"
    + ".cm-card{min-width:180px;background:#f8fafc;border:1px solid #cbd5e1;border-radius:10px;padding:10px;}"
    + ".cm-h{display:flex;justify-content:space-between;align-items:flex-start;gap:8px;font-size:13px;margin-bottom:8px;}"
    + ".cm-nextpiece{display:inline-block;min-width:58px;}"
    + ".cm-nextlabel{font-size:11px;color:#475569;text-transform:uppercase;letter-spacing:0.03em;}"
    + ".cm-pieceicon{display:inline-block;margin-top:2px;}"
    + ".cm-prow{height:12px;white-space:nowrap;}"
    + ".cm-pcell{display:inline-block;width:11px;height:11px;border:1px solid #cbd5e1;background:#ffffff;box-sizing:border-box;margin-right:1px;vertical-align:top;}"
    + ".cm-prow .cm-pcell:last-child{margin-right:0;}"
    + ".cm-grid{display:grid;grid-template-columns:repeat(4,24px);grid-template-rows:repeat(4,24px);gap:3px;}"
    + ".cm-cell{width:24px;height:24px;border:1px solid #94a3b8;background:#ffffff;}"
    + ".cm-cell.on{background:#111827;}"
    + ".cm-next{margin-top:8px;font-size:12px;color:#334155;}"
    + ".cm-arrow{display:inline-block;align-self:center;min-width:26px;text-align:center;font-size:18px;color:#64748b;padding-top:30px;white-space:nowrap;line-height:1;font-family:monospace;}";

  document.head.appendChild(style);
}

function renderCuriosityModel() {
  div.innerHTML = "";
  div.style.overflow = "auto";

  injectStyle();

  var states = getUnaryAtoms(State);
  var nextMap = mapBinary(nexts);
  var pieceMap = mapBinary(nextp);
  var occ = setFromBoardTrue(board);
  var ordered = orderStates(states, nextMap);

  var wrap = document.createElement("div");
  wrap.className = "cm-wrap";

  var title = document.createElement("div");
  title.className = "cm-title";
  title.textContent = "Curiosity Modeling: 4-Wide State Chain";
  wrap.appendChild(title);

  var flow = document.createElement("div");
  flow.className = "cm-flow";

  for (var i = 0; i < ordered.length; i++) {
    var s = ordered[i];

    var card = document.createElement("div");
    card.className = "cm-card";

    var h = document.createElement("div");
    h.className = "cm-h";

    var left = document.createElement("span");
    left.textContent = s;

    var right = document.createElement("div");
    if (pieceMap[s]) {
      right.appendChild(makePieceIcon(pieceTypeFromAtomName(pieceMap[s])));
    } else {
      right.textContent = "terminal";
    }

    h.appendChild(left);
    h.appendChild(right);
    card.appendChild(h);

    var grid = document.createElement("div");
    grid.className = "cm-grid";

    for (var y = 3; y >= 0; y--) {
      for (var x = 0; x <= 3; x++) {
        var cell = document.createElement("div");
        cell.className = "cm-cell";
        if (occ[s + "|" + x + "|" + y]) {
          cell.className += " on";
        }
        cell.title = "(" + x + "," + y + ")";
        grid.appendChild(cell);
      }
    }

    card.appendChild(grid);

    var nextText = document.createElement("div");
    nextText.className = "cm-next";
    nextText.textContent = nextMap[s] ? ("next state: " + nextMap[s]) : "next state: none";
    card.appendChild(nextText);

    flow.appendChild(card);

    if (i < ordered.length - 1) {
      var arrow = document.createElement("div");
      arrow.className = "cm-arrow";
      arrow.textContent = "->";
      flow.appendChild(arrow);
    }
  }

  wrap.appendChild(flow);
  div.appendChild(wrap);
}

renderCuriosityModel();
