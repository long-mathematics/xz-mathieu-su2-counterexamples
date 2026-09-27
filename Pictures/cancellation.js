import * as React from 'react';
const e = React.createElement;

const SERIF = "'CMU Serif', 'Latin Modern Roman', 'STIX Two Text', Georgia, serif";
const MONO = "ui-monospace, 'SF Mono', Menlo, monospace";
const PURE = '#3f9d5f';
const MARK = '#e0822c';
const SUP = { '-': '⁻', 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹' };
const sup = n => String(n).split('').map(c => SUP[c]).join('');
const zpow = p => p === 0 ? '1' : p === 1 ? 'z' : 'z' + sup(p);
const frac = ([p, q]) => q === 1 ? String(p) : `${p}/${q}`;
const signed = v => (v < 0 ? '− ' : '+ ') + Math.abs(v);

// props.rows[n-1] = { n, coeffs: [(-1)^j C(n,j)], pure: [p,q], marked: [p,q] }, all computed in Lean.
export default function Cancellation(props) {
  const [n, setN] = React.useState(3);
  const [mode, setMode] = React.useState('pure');
  const row = props.rows[n - 1];
  const shift = mode === 'pure' ? 0 : 1;
  const hot = mode === 'pure' ? PURE : MARK;
  const on = (j, k) => k === j + shift;

  const cell = 46, left = 92, top = 34;
  const size = n + 1;
  const W = left + size * cell + 16, H = top + size * cell + 12;
  const kids = [];
  for (let k = 0; k < size; k++)
    kids.push(e('text', { key: `h${k}`, x: left + k * cell + cell / 2, y: top - 12, textAnchor: 'middle',
      fontFamily: SERIF, fontSize: 17, fill: 'currentColor', opacity: 0.8 }, zpow(k)));
  for (let j = 0; j < size; j++) {
    const c = row.coeffs[j];
    kids.push(e('text', { key: `r${j}`, x: left - 10, y: top + j * cell + cell / 2 + 6, textAnchor: 'end',
      fontFamily: SERIF, fontSize: 17, fill: 'currentColor', opacity: 0.8 },
      j === 0 ? String(c) : `${c < 0 ? '−' : ''}${Math.abs(c) === 1 ? '' : Math.abs(c) + '·'}${zpow(-j)}`));
    for (let k = 0; k < size; k++) {
      const x = left + k * cell, y = top + j * cell, lit = on(j, k);
      kids.push(e('g', { key: `c${j}_${k}` },
        e('rect', { x: x + 2, y: y + 2, width: cell - 4, height: cell - 4, rx: 7,
          fill: lit ? hot : 'currentColor', fillOpacity: lit ? 0.9 : 0.06 }),
        e('text', { x: x + cell / 2, y: y + cell / 2 + 5, textAnchor: 'middle', fontFamily: SERIF,
          fontSize: 14, fill: lit ? '#fff' : 'currentColor', opacity: lit ? 1 : 0.45 },
          zpow(k - j - shift))));
    }
  }

  const lit = [];
  for (let j = 0; j < size; j++) if (j + shift <= n) lit.push(row.coeffs[j]);
  const sum = lit.reduce((a, b) => a + b, 0);
  const total = mode === 'pure' ? row.pure : row.marked;
  const terms = lit.map((c, i) => i === 0 ? String(c) : signed(c)).join(' ');

  // Mathieu's conjecture predicts ∫FⁿG = 0 for all large n. The bars are the actual values.
  const bw = 44, bx = 20, by = 84, scale = 120;
  const bars = props.rows.map((r, i) => {
    const v = r.marked[0] / r.marked[1], h = v * scale;
    const cx = bx + i * bw + bw / 2;
    return e('g', { key: `b${i}`, onClick: () => { setN(i + 1); setMode('marked'); }, style: { cursor: 'pointer' } },
      e('rect', { x: bx + i * bw + 8, y: h > 0 ? by - h : by, width: bw - 16, height: Math.abs(h), rx: 3,
        fill: MARK, fillOpacity: i + 1 === n && mode === 'marked' ? 1 : 0.55 }),
      e('text', { x: cx, y: h > 0 ? by - h - 5 : by - h + 14, textAnchor: 'middle', fontFamily: SERIF,
        fontSize: 12, fill: 'currentColor', opacity: 0.85 }, frac(r.marked)),
      e('text', { x: cx, y: h > 0 ? by + 15 : by - 7, textAnchor: 'middle', fontFamily: SERIF,
        fontSize: 11, fill: 'currentColor', opacity: 0.55 }, `n=${r.n}`));
  });

  const btn = (m, label, color) => e('button', {
    onClick: () => setMode(m),
    style: { font: `15px ${SERIF}`, padding: '5px 12px', marginRight: 8, borderRadius: 8, cursor: 'pointer',
      border: `1.5px solid ${color}`, background: mode === m ? color : 'transparent',
      color: mode === m ? '#fff' : 'inherit' } }, label);

  return e('div', { style: { fontFamily: SERIF, lineHeight: 1.35, maxWidth: 760 } },
    e('div', { style: { fontSize: 20, marginBottom: 2 } }, 'Mathieu’s conjecture fails for SU(2)'),
    e('div', { style: { fontSize: 15, opacity: 0.75, marginBottom: 10 } },
      'F = (1 + c)(ad + b),  G = −c  on  g = [a c; b d] ∈ SU(2).  Under Müger–Tuset’s β, F becomes (1 − z⁻¹)((1 − x) + xz) and G becomes z⁻¹.'),
    e('div', { style: { marginBottom: 8 } },
      btn('pure', '∫ Fⁿ dg', PURE), btn('marked', '∫ Fⁿ·G dg', MARK),
      e('label', { style: { fontSize: 15, marginLeft: 8 } }, 'n = ',
        e('input', { type: 'range', min: 1, max: props.rows.length, value: n,
          onChange: ev => setN(Number(ev.target.value)), style: { verticalAlign: 'middle', width: 140 } }),
        ` ${n}`)),
    e('div', { style: { fontSize: 14, opacity: 0.7, margin: '4px 0 0' } },
      `Rows: (1 − z⁻¹)ⁿ.  Columns: ∫₀¹((1 − x) + xz)ⁿ dx, where every power zᵏ gets the same weight 1/${n + 1}.`),
    e('svg', { width: W, height: H, viewBox: `0 0 ${W} ${H}`, style: { display: 'block' } }, kids),
    e('div', { style: { fontSize: 16, margin: '6px 0 2px' } },
      mode === 'pure' ? 'Constant term = the diagonal: ' : 'Times z⁻¹ shifts it one step: ',
      e('span', { style: { fontFamily: MONO, fontSize: 14 } }, `(${terms}) / ${n + 1}`),
      ' = ',
      e('b', { style: { color: hot } }, frac(total)),
      mode === 'pure' ? '   (the full row of (1 − 1)ⁿ)' : '   (the row minus its last term)'),
    e('div', { style: { fontSize: 14, opacity: 0.75, margin: '12px 0 0' } },
      'Mathieu predicts ∫FⁿG dg = 0 for every large n. It is never 0:'),
    e('svg', { width: bx * 2 + bw * props.rows.length, height: 162, style: { display: 'block' } },
      e('line', { x1: bx, x2: bx + bw * props.rows.length, y1: by, y2: by, stroke: 'currentColor', strokeOpacity: 0.4 }),
      bars),
    e('div', { style: { fontSize: 13, opacity: 0.65, marginTop: 6, fontFamily: MONO } },
      props.proved.map((s, i) => e('div', { key: i }, s))));
}
