"""Genotipos enmascarados por ancestría local: SantiagoNAT y SantiagoEUR (pseudohaploides) en los SNPs del AADR.
Para cada SNP, toma el alelo del haplotipo faseado (Beagle) cuya ancestría (RFMix) es la buscada; si ambos lo son, uno al azar.
Solo usa dosis seguras (|DS-entero|<=0.1)."""
import subprocess, collections, random, sys
random.seed(42)
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
A = S + '/anc'; R = A + '/rfmix'; BT = '/opt/mm/bt/bin/bcftools'
snps = [l.split() for l in open(A + '/aadr_sub.snp')]
segs = collections.defaultdict(list)
for c in range(1, 23):
    for l in open(f'{R}/out_{c}.msp.tsv').read().splitlines()[2:]:
        f = l.split('\t'); segs[c].append((int(f[1]), int(f[2]), {'0': 'AFR', '1': 'EUR', '2': 'NAT'}[f[6]], {'0': 'AFR', '1': 'EUR', '2': 'NAT'}[f[7]]))
out = {'NAT': ['9'] * len(snps), 'EUR': ['9'] * len(snps)}
byc = collections.defaultdict(dict)
for i, s in enumerate(snps): byc[int(s[1])][int(s[3])] = i
n = collections.Counter()
for c in range(1, 23):
    reg = A + '/_mreg.txt'
    open(reg, 'w').write(''.join(f'{c}\t{p}\n' for p in sorted(byc[c])))
    q = subprocess.run([BT, 'query', '-R', reg, '-i', 'TYPE="snp"', '-f', '%POS\t%REF\t%ALT\t[%GT]\t[%DS]\n', f'{S}/imp/imp_chr{c}.vcf.gz'], capture_output=True, text=True).stdout
    sg = segs[c]
    for line in q.splitlines():
        p, r, a, g, ds = line.split('\t'); p = int(p)
        i = byc[c].get(p)
        if i is None or '|' not in g or abs(float(ds) - round(float(ds))) > 0.1: continue
        h = [r if x == '0' else a for x in g.split('|')]
        anc = None
        for (s0, e0, a0, a1) in sg:
            if s0 <= p < e0: anc = (a0, a1); break
        if not anc: continue
        a1, a2 = snps[i][4], snps[i][5]
        for target in ('NAT', 'EUR'):
            ks = [k for k in (0, 1) if anc[k] == target]
            if not ks: continue
            al = h[random.choice(ks)]
            if al not in (a1, a2): continue
            out[target][i] = '2' if al == a1 else '0'; n[target] += 1
for t in ('NAT', 'EUR'):
    open(f'{A}/sant_{t}.geno', 'w').write('\n'.join(out[t]) + '\n')
print(dict(n))
