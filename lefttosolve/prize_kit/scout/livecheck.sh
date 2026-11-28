#!/bin/bash
# usage: livecheck.sh ids.txt out.tsv
: > "$2"
while IFS= read -r id; do
  lid="$(printf '%s' "$id" | tr 'A-Z' 'a-z')"
  for try in 1 2 3 4; do
    out="$(gh api -X GET search/issues -f q="repo:GuillaumeBAUD-coder/open-math-agents is:pr is:open in:title $id" --jq ".items[] | select(.title | ascii_downcase | endswith(\"$lid\")) | \"\(.number):\(.user.login)\"" 2>/tmp/lc_err_$$)" && break
    sleep 25
  done
  printf '%s\t%s\n' "$id" "$(printf '%s' "$out" | tr '\n' ' ')" >> "$2"
  sleep 2.2
done < "$1"
echo DONE >> "$2"
