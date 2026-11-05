"""Extrae del AADR v66 compatibility_HO los grupos indígenas mexicanos antiguos y modernos (+ Mbuti, Han, sudamericanos),
reetiqueta por sitio arqueológico, filtra cobertura y añade las columnas enmascaradas de Santiago (m_mask) -> anc/mx/mx.{geno,snp,ind}."""
import csv, subprocess, os, collections
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
A = S + '/ref/aadr'; O = S + '/anc/mx'; os.makedirs(O, exist_ok=True)
MIN_SNPS = 20000
site = {  # (grupo AADR, fragmento de localidad) -> etiqueta
    ('Mexico_Tayopa_1000BP', ''): 'Sonora_Tayopa_1000aP',
    ('Mexico_600BP_TradicionTrincheras', ''): 'Sonora_Trincheras_600aP',
    ('Mexico_900BP_TradicionTrincheras', ''): 'Sonora_Trincheras_otros',
    ('Mexico_1100BP_TradicionTrincheras', ''): 'Sonora_Trincheras_otros',
    ('Mexico_1900BP_TradicionTrincheras', ''): 'Sonora_Trincheras_otros',
    ('Mexico_2500BP_TradicionTrincheras', ''): 'Sonora_Trincheras_otros',
    ('Mexico_2800BP_TradicionTrincheras', ''): 'Sonora_Trincheras_otros',
    ('Mexico_1100BP', ''): 'Durango_RioZape_1100aP',
    ('Mexico_950BP', ''): 'Coahuila_950aP',
    ('Mexico_Medieval', 'Toluquilla'): 'Queretaro_Toluquilla',
    ('Mexico_Medieval', 'Virgen'): 'Guanajuato_CanadaVirgen',
    ('Mexico_Medieval', 'Ventana'): 'Chihuahua_Tarahumara_antiguo',
    ('Mexico_PreColumbian_Medio', ''): 'Chihuahua_Paquime',
    ('Mexico_LateClassic', ''): 'Yucatan_ChichenItza',
    ('Mexico_Colonial_Maya', ''): 'Campeche_Maya_colonial',
    ('Mexico_Pericues_Unknown', ''): 'BajaCalifornia_Pericu',
}
modern = {'Mbuti', 'Han', 'Pima', 'Mixe', 'Mayan', 'Zapotec', 'Mixtec', 'Nahua', 'Huichol', 'Karitiana', 'Surui', 'Quechua', 'Yoruba', 'Spanish'}
rows = list(csv.reader(open(A + '/v66.HO.anno'), delimiter='\t'))
hdr = rows[0]
lab = {}
for r in rows[1:]:
    gid, grp, loc = r[0], r[14], r[15]
    try: nsnp = int(float(r[29]))
    except ValueError: nsnp = 0
    if grp in modern:
        lab[gid] = grp
        continue
    for (g, frag), l in site.items():
        if grp == g and frag in loc and nsnp >= MIN_SNPS:
            lab[gid] = l; break
ind_in = [l.split() for l in open(A + '/v66.HO.ind')]
with open(O + '/all.ind', 'w') as f:
    for iid, sex, pop in ind_in:
        f.write(f'{iid} {sex} {lab.get(iid, "Ignore_" + pop)}\n')
pops = sorted(set(lab.values()))
open(O + '/pops.txt', 'w').write('\n'.join(pops) + '\n')
par = f"""genotypename: {S}/ref/aadr_c/comp.geno
snpname: {A}/v66.HO.snp
indivname: {O}/all.ind
outputformat: EIGENSTRAT
genotypeoutname: {O}/sub.geno
snpoutname: {O}/sub.snp
indivoutname: {O}/sub.ind
poplistname: {O}/pops.txt
"""
open(O + '/cf.par', 'w').write(par)
env = dict(os.environ, PATH='/opt/mm/gen/bin:' + os.environ['PATH'])
subprocess.run(f'convertf -p {O}/cf.par > {O}/cf.log 2>&1', shell=True, check=True, env=env)
# añadir columnas de Santiago (últimas 3 de m_mask: SANTIAGO, SANTIAGO_NAT, SANTIAGO_EUR); mismas SNPs y orden
mi = [l.split() for l in open(S + '/anc/m_mask.ind')]
idx = [i for i, x in enumerate(mi) if x[0].startswith('SANTIAGO')]
assert open(S + '/anc/m_mask.snp').read() == open(O + '/sub.snp').read()
with open(S + '/anc/m_mask.geno') as fm, open(O + '/sub.geno') as fs, open(O + '/mx.geno', 'w') as fo:
    for a, b in zip(fs, fm):
        b = b.rstrip('\n'); fo.write(a.rstrip('\n') + ''.join(b[i] for i in idx) + '\n')
os.replace(O + '/sub.snp', O + '/mx.snp')
with open(O + '/mx.ind', 'w') as f:
    f.write(open(O + '/sub.ind').read())
    for i in idx: f.write(' '.join(mi[i]) + '\n')
c = collections.Counter(l.split()[2] for l in open(O + '/mx.ind'))
for k, v in sorted(c.items()): print(k, v)
