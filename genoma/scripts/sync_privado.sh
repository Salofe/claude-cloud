#!/bin/bash
# Copia el análisis completo (código + resultados + reportes; NUNCA genotipos) al repo privado y lo empuja.
P=/home/user/genome-analisis; G=/home/user/claude-cloud/genoma
mkdir -p $P
find $P -mindepth 1 -maxdepth 1 ! -name .git -exec rm -rf {} +
tar -C $G --exclude='.gitignore' --exclude='__pycache__' --exclude='*.txt' --exclude='*.vcf' --exclude='*.vcf.gz' --exclude='*.bcf' \
  --exclude='*.bed' --exclude='*.bim' --exclude='*.fam' --exclude='*.pgen' --exclude='*.pvar' --exclude='*.psam' --exclude='*.tbi' --exclude='*.csi' -cf - . | tar -C $P -xf -
cat > $P/.gitignore <<'GI'
# Nunca versionar genotipos completos ni el archivo crudo
*.txt
*.vcf
*.vcf.gz
*.bcf
*.bed
*.bim
*.fam
*.pgen
*.pvar
*.psam
*.tbi
*.csi
__pycache__/
GI
cd $P && git add -A && git -c user.name="Claude" -c user.email="noreply@anthropic.com" commit -qm "${1:-Actualiza análisis}

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01AHP11hgardECTU2kJgvdFN" && for i in 1 2 3 4; do git push -q -u origin HEAD:main && break || sleep $((2**i)); done
git -C $P log --oneline | head -3
