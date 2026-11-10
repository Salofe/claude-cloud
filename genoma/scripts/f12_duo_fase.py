"""Faseo madre-hijo. Entrada: VCF de 2 muestras (HIJO, MADRE) faseado estadísticamente por Beagle + genotipos MEDIDOS de ambos.
Corrige la fase con herencia mendeliana:
  hijo  -> hap0 = alelo MATERNO, hap1 = alelo PATERNO
  madre -> hap0 = alelo TRANSMITIDO al hijo, hap1 = NO transmitido
Sitios informativos del hijo: hijo heterocigoto y madre homocigota (medidos). Los doble-heterocigotos toman la orientación
del sitio informativo más cercano dentro de la fase local de Beagle; los cambios puntuales aislados no se propagan.
Uso: f12_duo_fase.py <beagle_faseado.vcf.gz> <medido_duo.vcf.gz> <salida.vcf> <HIJO> <MADRE>"""
import sys, gzip, bisect, collections
ph, meas, out, KID, MOM = sys.argv[1:6]
def op(f): return gzip.open(f, 'rt') if f.endswith('gz') else open(f)
mg = {}   # (pos, ref, alt) -> (g_hijo, g_madre) medidos; None si falta
for l in op(meas):
    if l.startswith('##'): continue
    x = l.rstrip('\n').split('\t')
    if l[0] == '#': ik, im = x.index(KID), x.index(MOM); continue
    def g(s):
        a = s.split(':')[0].replace('|', '/').split('/')
        return None if '.' in a or len(a) != 2 else int(a[0]) + int(a[1])
    mg[(int(x[1]), x[3], x[4])] = (g(x[ik]), g(x[im]))
hdr = []; rows = []
for l in op(ph):
    if l.startswith('##'): hdr.append(l); continue
    x = l.rstrip('\n').split('\t')
    if l[0] == '#': ik, im = x.index(KID), x.index(MOM); hdr.append(l); continue
    c = [int(a) for a in x[ik].split(':')[0].split('|')]; m = [int(a) for a in x[im].split(':')[0].split('|')]
    rows.append([x, int(x[1]), c, m, mg.get((int(x[1]), x[3], x[4]), (None, None))])
st = collections.Counter()
def orient(inf):
    """inf: lista ordenada de (pos, o). Devuelve función pos -> (o, distancia) ignorando cambios puntuales aislados."""
    keep = []
    for i, (p, o) in enumerate(inf):
        l = inf[i - 1][1] if i > 0 else None; r = inf[i + 1][1] if i + 1 < len(inf) else None
        if l is not None and r is not None and l == r != o: st['flip_puntual'] += 1; continue
        keep.append((p, o))
    ps = [p for p, _ in keep]
    st['cambios_de_fase'] += sum(1 for a, b in zip(keep, keep[1:]) if a[1] != b[1])
    def f(pos):
        if not keep: return (0, 10 ** 12)
        i = bisect.bisect_left(ps, pos)
        cands = [keep[j] for j in (i - 1, i) if 0 <= j < len(keep)]
        p, o = min(cands, key=lambda t: abs(t[0] - pos))
        return (o, abs(p - pos))
    return f
# hijo: orientación = índice del haplotipo de Beagle que lleva el alelo materno
inf_k = {}; inf_m = {}
for x, pos, c, m, (gk, gm) in rows:
    if c[0] != c[1] and gk == 1 and gm in (0, 2):
        inf_k[pos] = 0 if c[0] == gm // 2 else 1
    if m[0] != m[1] and gm == 1 and gk in (0, 2):
        inf_m[pos] = 0 if m[0] == gk // 2 else 1      # índice del haplotipo materno (Beagle) transmitido
    if gk is not None and gm is not None and {gk, gm} == {0, 2}: st['error_mendeliano'] += 1
fk = orient(sorted(inf_k.items())); st['cambios_hijo'] = st.pop('cambios_de_fase', 0); st['flips_hijo'] = st.pop('flip_puntual', 0)
fm = orient(sorted(inf_m.items())); st['cambios_madre'] = st.pop('cambios_de_fase', 0); st['flips_madre'] = st.pop('flip_puntual', 0)
st['informativos_hijo'] = len(inf_k); st['informativos_madre'] = len(inf_m)
with open(out, 'w') as o:
    for l in hdr: o.write(l)
    for x, pos, c, m, (gk, gm) in rows:
        khet = c[0] != c[1]; mhet = m[0] != m[1]
        if khet and mhet:      # doble heterocigoto: una sola decisión coherente para los dos
            if pos in inf_k: mat = c[inf_k[pos]]
            else:
                ok, dk = fk(pos); om, dm = fm(pos)
                mat = c[ok] if dk <= dm else m[om]
                st['doble_het'] += 1
                if c[ok] != m[om]: st['doble_het_discrepa'] += 1
            kid = (mat, 1 - mat); mom = (mat, 1 - mat)
        elif khet:             # madre homocigota (según Beagle/medido)
            mat = m[0]; kid = (mat, 1 - mat); mom = (m[0], m[1])
        elif mhet:             # hijo homocigoto: transmitió ese alelo
            kid = (c[0], c[1]); mom = (c[0], 1 - c[0])
        else:
            kid = (c[0], c[1]); mom = (m[0], m[1])
        x[ik] = f'{kid[0]}|{kid[1]}'; x[im] = f'{mom[0]}|{mom[1]}'; x[8] = 'GT'
        o.write('\t'.join(x) + '\n')
print(len(rows), dict(st))
