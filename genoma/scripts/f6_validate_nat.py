"""Valida los tramos de RFMix: en sitios diagnósticos (|p_NAT - p_IBS| >= 0.5) cuenta, por haplotipo y ancestría llamada,
qué fracción de tus alelos es el alelo más frecuente en nativos. Tramos NAT reales -> fracción alta; EUR -> baja."""
import subprocess, glob, os, collections, sys
S = '/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad'
R = S + '/anc/rfmix'; BT = '/opt/mm/bt/bin/bcftools'
pops = R + '/valpops.txt'
with open(pops, 'w') as o:
    for l in open(R + '/samplemap.txt'):
        s, p = l.split(); o.write(f'{s}\t{p}\n')
stat = collections.defaultdict(lambda: [0, 0])
for f in sorted(glob.glob(R + '/out_*.msp.tsv')):
    c = os.path.basename(f)[4:-8]
    if c == 'X': continue
    segs = [l.split('\t') for l in open(f).read().splitlines()[2:]]
    q = R + f'/q_{c}.vcf.gz'
    posf = R + f'/pos_{c}.txt'
    fr = subprocess.run(f"{BT} view -S <(cut -f1 {pops}) -R {posf} -v snps -m2 -M2 {S}/ref/1kg/chr{c}.vcf.gz -Ou | {BT} +fill-tags -Ou -- -S {pops} -t AF | {BT} query -f '%POS\\t%INFO/AF_EUR\\t%INFO/AF_NAT\\n'",
                        shell=True, capture_output=True, text=True, executable='/bin/bash').stdout
    diag = {}
    for line in fr.splitlines():
        p, fe, fn = line.split('\t'); fe = float(fe); fn = float(fn)
        if abs(fn - fe) >= 0.5: diag[int(p)] = 1 if fn > fe else 0   # alelo "nativo": 1=ALT, 0=REF
    gq = subprocess.run([BT, 'query', '-f', '%POS\t[%GT]\n', q], capture_output=True, text=True).stdout
    for line in gq.splitlines():
        p, g = line.split('\t'); p = int(p)
        if p not in diag or '|' not in g: continue
        h = g.split('|')
        for s in segs:
            if int(s[1]) <= p < int(s[2]):
                for k in (0, 1):
                    anc = {'0': 'AFR', '1': 'EUR', '2': 'NAT'}[s[6 + k]]
                    stat[anc][0] += (int(h[k]) == diag[p]); stat[anc][1] += 1
                break
for a, (m, n) in sorted(stat.items()):
    print(f'Tramos llamados {a}: {n} alelos en sitios diagnósticos; fracción = alelo nativo: {m/n:.3f}')
