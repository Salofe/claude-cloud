"""Fase 0b: recalcula cada genotipo de genotipos_clave.tsv desde el archivo crudo."""
import sys, csv
genome, tsv = sys.argv[1], sys.argv[2]
want = {}
with open(tsv) as f:
    r = csv.DictReader(f, delimiter='\t')
    rows = list(r)
ids = {row['rsid'] for row in rows}
raw = {}
with open(genome) as f:
    for line in f:
        if line.startswith('#'): continue
        p = line.rstrip('\n').split('\t')
        if p[0] in ids: raw[p[0]] = p
bad = 0
for row in rows:
    g = raw.get(row['rsid'])
    if g is None:
        print('NO_EN_CRUDO', row['rsid']); bad += 1; continue
    msgs = []
    if g[1] != row['cromosoma']: msgs.append(f"chr {g[1]}!={row['cromosoma']}")
    if g[2] != row['posicion_GRCh37']: msgs.append(f"pos {g[2]}!={row['posicion_GRCh37']}")
    if g[3] != row['genotipo']: msgs.append(f"gt {g[3]}!={row['genotipo']}")
    if msgs: print('DIFIERE', row['rsid'], row['gen'], '; '.join(msgs)); bad += 1
print(f'{len(rows)} filas, {bad} discrepancias')
