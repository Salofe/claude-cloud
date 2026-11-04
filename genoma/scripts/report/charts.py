"""Funciones SVG para el reporte (sin dependencias). Colores vía variables CSS del tema."""
CHRLEN = {1:249250621,2:243199373,3:198022430,4:191154276,5:180915260,6:171115067,7:159138663,8:146364022,9:141213431,10:135534747,
          11:135006516,12:133851895,13:115169878,14:107349540,15:102531392,16:90354753,17:81195210,18:78077248,19:59128983,20:63025520,
          21:48129895,22:51304566,'X':155270560}
CEN = {1:125.0,2:93.3,3:91.0,4:50.4,5:48.4,6:61.0,7:59.9,8:45.6,9:49.0,10:40.2,11:53.7,12:35.8,13:17.9,14:17.6,15:19.0,16:36.6,17:24.0,
       18:17.2,19:26.5,20:27.5,21:13.2,22:14.7,'X':60.6}
COL = {'EUR':'var(--eur)','NAT':'var(--nat)','AFR':'var(--afr)','UNK':'var(--unk)'}

def ideogram(segs, title='Ideograma'):
    """segs: lista de (chr, start, end, hap(0/1), anc). Dibuja 22 autosomas (2 haplotipos) + X (1)."""
    chrs = list(range(1, 23)) + ['X']
    colw, barw, gap = 42, 11, 3
    H, top = 300, 30
    W = colw * len(chrs) + 20
    scale = H / CHRLEN[1]
    out = [f'<svg viewBox="0 0 {W} {top+H+40}" width="100%" role="img" aria-label="{title}" xmlns="http://www.w3.org/2000/svg" style="min-width:760px">']
    for i, c in enumerate(chrs):
        x0 = 10 + i * colw + (colw - (2*barw+gap)) / 2
        L = CHRLEN[c] * scale
        nh = 1 if c == 'X' else 2
        for h in range(nh):
            x = x0 + h * (barw + gap) + (barw/2+gap/2 if nh == 1 else 0)
            out.append(f'<rect x="{x:.1f}" y="{top}" width="{barw}" height="{L:.1f}" rx="5" fill="var(--unk)"/>')
            for (sc, s, e, hp, a) in segs:
                if sc != c or hp != h: continue
                y = top + s * scale; hh = max((e - s) * scale, 0.6)
                out.append(f'<rect x="{x:.1f}" y="{y:.1f}" width="{barw}" height="{hh:.1f}" fill="{COL.get(a, COL["UNK"])}"/>')
            out.append(f'<rect x="{x:.1f}" y="{top}" width="{barw}" height="{L:.1f}" rx="5" fill="none" stroke="var(--rule)" stroke-width="1"/>')
        cy = top + CEN[c] * 1e6 * scale
        out.append(f'<line x1="{x0-2:.1f}" x2="{x0+2*barw+gap+2:.1f}" y1="{cy:.1f}" y2="{cy:.1f}" stroke="var(--bg)" stroke-width="2"/>')
        out.append(f'<text x="{x0+barw+gap/2:.1f}" y="{top-10}" text-anchor="middle" font-size="12">{c}</text>')
    out.append(f'<text x="10" y="{top+H+28}" font-size="11" class="muted">Cada par de barras = tus dos copias de ese cromosoma (X: una sola). Escala: cromosoma 1 = 249 Mb. Gris = sin llamada.</text>')
    out.append('</svg>')
    return '\n'.join(out)

def stacked_bar(parts):
    """parts: lista (etiqueta, fracción, clave color)."""
    spans = ''.join(f'<span style="width:{100*f:.2f}%;background:{COL.get(k, k)}" title="{l} {100*f:.1f}%"></span>' for l, f, k in parts if f > 0)
    return f'<div class="bar" role="img" aria-label="{", ".join(f"{l} {100*f:.1f}%" for l, f, k in parts)}">{spans}</div>'

def pgs_dots(rows, width=760):
    """rows: lista dict(label, pct, lo, hi, note). Percentil 0-100 en eje x, con banda de incertidumbre."""
    rh, left, right, top = 34, 250, 30, 30
    W = width; H = top + rh * len(rows) + 40
    X = lambda p: left + (W - left - right) * p / 100
    o = [f'<svg viewBox="0 0 {W} {H}" width="100%" role="img" aria-label="Percentiles de scores poligénicos" xmlns="http://www.w3.org/2000/svg" style="min-width:600px">']
    for p in (0, 25, 50, 75, 100):
        o.append(f'<line x1="{X(p):.1f}" x2="{X(p):.1f}" y1="{top-8}" y2="{H-30}" stroke="var(--rule)" stroke-width="1" {"" if p!=50 else "stroke-dasharray=\'4 3\'"}/>')
        o.append(f'<text x="{X(p):.1f}" y="{H-12}" font-size="11" text-anchor="middle" class="muted">{p}</text>')
    o.append(f'<text x="{X(50):.1f}" y="{top-14}" font-size="11" text-anchor="middle" class="muted">percentil (50 = promedio de tu ancestría)</text>')
    for i, r in enumerate(rows):
        y = top + i * rh + rh / 2
        o.append(f'<text x="{left-12}" y="{y+4:.1f}" font-size="12.5" text-anchor="end">{r["label"]}</text>')
        o.append(f'<rect x="{X(r["lo"]):.1f}" y="{y-5:.1f}" width="{max(X(r["hi"])-X(r["lo"]),2):.1f}" height="10" rx="5" fill="var(--accent-soft)" stroke="var(--accent)" stroke-width=".6"/>')
        o.append(f'<circle cx="{X(r["pct"]):.1f}" cy="{y:.1f}" r="5.5" fill="var(--accent)"/>')
        o.append(f'<text x="{min(X(r["pct"])+10, W-right-30):.1f}" y="{y-8:.1f}" font-size="11" class="muted">{r["pct"]:.0f}</text>')
    o.append('</svg>')
    return '\n'.join(o)
