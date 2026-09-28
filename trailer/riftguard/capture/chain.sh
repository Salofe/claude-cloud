#!/bin/bash
cd "$(dirname "$0")"

ls jobs2/j*.json | xargs -P 3 -I{} sh -c 'n=$(basename {} .json); node capture.mjs {} 1920 1080 shots >> logs/$n.log 2>&1; echo "finished $n"' >> runall.log
echo CHAINDONE >> runall.log
