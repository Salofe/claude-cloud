#!/bin/bash
cd "$(dirname "$0")"
mkdir -p logs
ls jobs/j*.json | xargs -P ${PAR:-4} -I{} sh -c 'n=$(basename {} .json); node capture.mjs {} 1920 1080 shots >> logs/$n.log 2>&1; echo "finished $n"'
echo ALLDONE
