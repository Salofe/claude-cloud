"""Fase 8: suma por cromosoma los alelos 'neandertales' (Vindija homocigota, ausentes en África) y compara con 1000G."""
import glob, collections, json, os
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'; N = S + '/nea'
pop = {}; sup = {}
for l in open(S + '/ref/integrated_call_samples_v3.20130502.ALL.panel'):
    f = l.split()
    if f[0] != 'sample': pop[f[0]] = f[1]; sup[f[0]] = f[2]
done = sorted(int(os.path.basename(f)[7:-5]) for f in glob.glob(N + '/vin_chr*.done'))
kg = collections.Counter(); kgn = collections.Counter(); s = 0; sn = 0; sites = 0
for c in done:
    for l in open(f'{N}/nkg_{c}.sscore').read().splitlines()[1:]:
        f = l.split(); kg[f[0]] += float(f[1]); kgn[f[0]] += 1
    for l in open(f'{N}/nsant_{c}.tsv'):
        x = l.rstrip('\n').split('\t'); s += int(x[3]); sn += 1
    sites += int(open(f'{N}/vin_chr{c}.done').read().split()[2])
def stats(ids):
    v = sorted(kg[i] for i in ids); n = len(v)
    return dict(n=n, media=round(sum(v)/n, 1), pct_santiago=round(100*sum(x < s for x in v)/n, 1))
res = dict(cromosomas=done, sitios_informativos=sites, sitios_con_genotipo=sn, alelos_santiago=s, por_superpob={}, por_pob={})
for sp in ('AFR', 'EUR', 'AMR', 'EAS', 'SAS'):
    res['por_superpob'][sp] = stats([i for i in kg if sup.get(i) == sp])
for p in ('YRI', 'IBS', 'TSI', 'CEU', 'GBR', 'FIN', 'MXL', 'PEL', 'CLM', 'PUR', 'CHB', 'JPT'):
    res['por_pob'][p] = stats([i for i in kg if pop.get(i) == p])
eur = res['por_superpob']['EUR']['media']
res['fraccion_relativa_a_EUR'] = round(s / eur, 2)
json.dump(res, open(N + '/resumen.json', 'w'), indent=1)
print(json.dumps(res, indent=1))
