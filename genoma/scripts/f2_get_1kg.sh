#!/bin/bash
# Descarga 1000 Genomes phase 3 (GRCh37, mirror NCBI) y deja solo variantes bialélicas con MAC>=2 y GT. Reanudable.
S=/tmp/claude-0/-home-user-claude-cloud/a79c4d0a-93d9-512a-8620-3273e0be7d84/scratchpad
export PATH=/opt/mm/gen/bin:$PATH
B=https://ftp-trace.ncbi.nih.gov/1000genomes/ftp/release/20130502
mkdir -p $S/ref/1kg $S/ref/1kg_raw
one() {
  c=$1
  if [ "$c" = X ]; then f=ALL.chrX.phase3_shapeit2_mvncall_integrated_v1b.20130502.genotypes.vcf.gz
  else f=ALL.chr$c.phase3_shapeit2_mvncall_integrated_v5a.20130502.genotypes.vcf.gz; fi
  out=$S/ref/1kg/chr$c.vcf.gz
  [ -s $out.tbi ] && return
  raw=$S/ref/1kg_raw/$f
  len=$(curl -sI $B/$f | awk 'tolower($1)=="content-length:"{print $2}' | tr -d '\r' | tail -1)
  if [ ! -s $raw ] || [ "$(stat -c %s $raw)" != "$len" ]; then
    curl -sS --retry 5 -C - -o $raw $B/$f || { echo "FAIL dl $c"; return; }
  fi
  bcftools view -m2 -M2 --min-ac 2:minor $raw -Ou | bcftools annotate -x INFO,^FORMAT/GT -Oz -o $out.tmp && mv $out.tmp $out && tabix -p vcf $out && echo "OK $c $(date +%T)" && rm -f $raw
}
export -f one; export S B
printf "%s\n" 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 X | xargs -P 3 -I{} bash -c 'one {}'
echo ALLDONE
