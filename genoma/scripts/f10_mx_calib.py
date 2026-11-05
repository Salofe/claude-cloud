"""Calibración: individuos de referencia convertidos en pseudohaploides y enmascarados con el MISMO patrón de SNPs
faltantes que SantiagoNAT; se quitan de su grupo de referencia y se prueban como si fueran Santiago."""
import random, sys
O = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad/anc/mx'
random.seed(11)
ind = [l.split() for l in open(O + '/mx.ind')]
col = {x[2]: [] for x in ind}
for i, x in enumerate(ind): col[x[2]].append(i)
sn = col['SantiagoNAT'][0]
pick = {}
for pop, k in [('Pima', 4), ('Mixe', 4), ('Yucatan_ChichenItza', 4), ('Sonora_Tayopa_1000aP', 3), ('Queretaro_Toluquilla', 2), ('Zapotec', 3)]:
    for j, i in enumerate(random.sample(col[pop], k)): pick[i] = f'T_{pop}_{j+1}'
order = sorted(pick)
with open(O + '/mx.geno') as f, open(O + '/cal.geno', 'w') as fo:
    for l in f:
        l = l.rstrip('\n'); extra = []
        for i in order:
            g = l[i]
            if l[sn] == '9' or g == '9': extra.append('9')
            elif g == '1': extra.append(random.choice('02'))
            else: extra.append(g)
        fo.write(l + ''.join(extra) + '\n')
with open(O + '/cal.ind', 'w') as fo:
    for i, x in enumerate(ind):
        fo.write(f'{x[0]} {x[1]} {"Ignore_" + x[2] if i in pick else x[2]}\n')
    for i in order: fo.write(f'{ind[i][0]}_T {ind[i][1]} {pick[i]}\n')
print('\n'.join(pick[i] for i in order))
