"""Provenance check: how much of a proof file appears verbatim in downloaded third-party Lean code.

Usage: python3 -I overlap_check.py <proof.lean>
Prints the share of substantive lines (>= 35 chars after whitespace normalisation) that occur
verbatim in third-party files on disk (scratchpad dirs ext, triage54, dl_plby, oai, excluding any
Mathlib copies), the files contributing most matches, and shared top-level declaration names.
Exit code 0 if the share is below 10% and no single third-party file contributes more than 8
matching lines; exit code 1 otherwise (treat as suspicious: do not submit).
"""
import collections
import glob
import re
import sys

SP = '/tmp/claude-0/-home-user-claude-cloud/bd3d433e-a40c-5862-83a1-d99ab03e0074/scratchpad'
DECL = re.compile(r'^(?:private )?(?:theorem|lemma|def|noncomputable def)\s+(\S+)', re.M)


def norm(line):
    return re.sub(r'\s+', ' ', line.strip())


ours = open(sys.argv[1]).read()
our_lines = [norm(l) for l in ours.split('\n') if len(norm(l)) >= 35 and not norm(l).startswith('--')]
where = collections.defaultdict(set)
names = collections.defaultdict(set)
for d in ('ext', 'triage54', 'dl_plby', 'oai'):
    for f in glob.glob(f'{SP}/{d}/**/*.lean', recursive=True):
        if 'mathlib' in f.lower() or '.lake' in f:
            continue
        try:
            t = open(f, errors='ignore').read()
        except OSError:
            continue
        short = f.split('scratchpad/')[1]
        for l in set(norm(x) for x in t.split('\n') if len(norm(x)) >= 35):
            where[l].add(short)
        for n in DECL.findall(t):
            names[n].add(short)
same = [l for l in our_lines if l in where]
per_file = collections.Counter(f for l in same for f in where[l])
share = 100 * len(same) / max(1, len(our_lines))
shared_names = sorted(n for n in set(DECL.findall(ours)) if n in names)
print(f'identical lines: {len(same)} of {len(our_lines)} ({share:.1f}%)')
print('top contributing files:', per_file.most_common(3))
print('shared declaration names:', shared_names[:15])
bad = share >= 10 or (per_file and per_file.most_common(1)[0][1] > 8)
print('VERDICT:', 'SUSPICIOUS' if bad else 'OK')
sys.exit(1 if bad else 0)
