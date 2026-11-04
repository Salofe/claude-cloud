"""Corre qpAdm (ADMIXTOOLS clásico) para una lista de modelos y extrae pesos, SE y p-valor.
Uso: f7_qpadm.py <prefijo eigenstrat> <salida.tsv> ; modelos definidos abajo."""
import sys, subprocess, os, re, itertools
pref, out = sys.argv[1], sys.argv[2]
W = os.path.dirname(out) + '/qpadm_runs'; os.makedirs(W, exist_ok=True)
RIGHT_BASE = ['Mbuti', 'Russia_Kostenki_UP', 'Israel_Natufian', 'Iran_GanjDareh_N', 'Russia_Samara_EBA_Yamnaya',
              'Serbia_IronGates_Mesolithic', 'Han', 'Papuan', 'Georgia_KotiasKlde_Mesolithic', 'Morocco_Iberomaurusian', 'Turkey_N']
MODELS = {
 # Santiago completo
 'S_IA_Rom_Moro_Mixe_Yor': (['Santiago', 'Spain_IA', 'Italy_Lazio_ImperialRoman_Roman', 'Morocco_LN', 'Mixe', 'Yoruba'], RIGHT_BASE + ['Karitiana']),
 'S_IA_Rom_Mixe_Yor': (['Santiago', 'Spain_IA', 'Italy_Lazio_ImperialRoman_Roman', 'Mixe', 'Yoruba'], RIGHT_BASE + ['Karitiana']),
 'S_IA_Mixe_Yor': (['Santiago', 'Spain_IA', 'Mixe', 'Yoruba'], RIGHT_BASE + ['Karitiana']),
 'S_LateAnt_Mixe_Yor': (['Santiago', 'Spain_LateAntiquity', 'Mixe', 'Yoruba'], RIGHT_BASE + ['Karitiana']),
 'S_Spanish_Mixe_Yor': (['Santiago', 'Spanish', 'Mixe', 'Yoruba'], RIGHT_BASE + ['Karitiana']),
 'S_Spanish_Mixe': (['Santiago', 'Spanish', 'Mixe'], RIGHT_BASE + ['Karitiana', 'Yoruba']),
 'S_Spanish_Pima_Yor': (['Santiago', 'Spanish', 'Pima', 'Yoruba'], RIGHT_BASE + ['Karitiana']),
 'S_Spanish_Mayan_Yor': (['Santiago', 'Spanish', 'Mayan', 'Yoruba'], RIGHT_BASE + ['Karitiana']),
 'S_IA_Rom_Moz_Mixe_Yor': (['Santiago', 'Spain_IA', 'Italy_Lazio_ImperialRoman_Roman', 'Mozabite', 'Mixe', 'Yoruba'], RIGHT_BASE + ['Karitiana']),
 # control: españoles modernos (Olalde 2019)
 'Spanish_IA_Rom': (['Spanish', 'Spain_IA', 'Italy_Lazio_ImperialRoman_Roman'], RIGHT_BASE + ['Karitiana', 'Yoruba']),
 'Spanish_IA_Rom_Moro': (['Spanish', 'Spain_IA', 'Italy_Lazio_ImperialRoman_Roman', 'Morocco_LN'], RIGHT_BASE + ['Karitiana', 'Yoruba']),
 'Spanish_IA': (['Spanish', 'Spain_IA'], RIGHT_BASE + ['Karitiana', 'Yoruba']),
}
sel = sys.argv[3].split(',') if len(sys.argv) > 3 else list(MODELS)
rows = []
for name in sel:
    left, right = MODELS[name]
    open(f'{W}/{name}.left', 'w').write('\n'.join(left) + '\n')
    open(f'{W}/{name}.right', 'w').write('\n'.join(right) + '\n')
    par = f"""genotypename: {pref}.geno
snpname: {pref}.snp
indivname: {pref}.ind
popleft: {W}/{name}.left
popright: {W}/{name}.right
details: YES
allsnps: YES
inbreed: NO
"""
    open(f'{W}/{name}.par', 'w').write(par)
    r = subprocess.run(['nice', '-n', '5', '/opt/mm/gen/bin/qpAdm', '-p', f'{W}/{name}.par'], capture_output=True, text=True, env={**os.environ, 'PATH': '/opt/mm/gen/bin:' + os.environ['PATH']})
    txt = r.stdout; open(f'{W}/{name}.log', 'w').write(txt + r.stderr)
    m = re.search(r'best coefficients:\s+([-\d.\s]+)\n', txt)
    se = re.search(r'std\. errors:\s+([-\d.\s]+)\n', txt)
    # p-valor del modelo completo: fila de la tabla "fixed pat" con todos ceros
    p = None
    for line in txt.splitlines():
        if re.match(r'\s*0+\s+\d+\s+[-\d.]+\s+[-\d.e+]+\s+[-\d.e+]+', line):
            f = line.split(); p = f[4]; break
    nsnp = re.search(r'numsnps used:\s+(\d+)', txt) or re.search(r'nsnps used:\s+(\d+)', txt)
    coef = m.group(1).split() if m else []
    ses = se.group(1).split() if se else []
    rows.append((name, ','.join(left[1:]), ' '.join(coef), ' '.join(ses), p, nsnp.group(1) if nsnp else ''))
    print(name, '|', ' '.join(f'{s}={c}±{e}' for s, c, e in zip(left[1:], coef, ses)), '| p =', p, '| snps', nsnp.group(1) if nsnp else '?', flush=True)
with open(out, 'w') as o:
    o.write('modelo\tfuentes\tpesos\tSE\tp\tsnps\n')
    for r in rows: o.write('\t'.join(map(str, r)) + '\n')
