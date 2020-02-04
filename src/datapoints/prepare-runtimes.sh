#! /bin/bash
set -euo pipefail

if [[ $# -eq 0 ]]; then
  echo "No files to be prepared!"
  exit 1
fi

aux=$(tempfile --prefix="RT-")

for f in $@; do
  if [[ ! -f "$f" ]]; then
    echo "file '$f' does not exist; aborting"
    exit 1
  fi

  cat "$f" | grep "time(s)" | cut -d' ' -f4,5 | sed 's/\(time(s)\|n+m\)://g' >> $aux
done

echo "$aux"
