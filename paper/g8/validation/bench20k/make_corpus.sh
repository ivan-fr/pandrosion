#!/bin/sh
# make_corpus.sh DIR : writes the 20 000 polynomials (DIR/cases/*.poly), DIR/corpus.json and DIR/list.txt.
# The three generators write next to themselves, so they are copied to DIR and run there, in this order.
set -e
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$1/cases"
cp "$here/../bench10k/add_extended_cases.py" "$here/../bench10k/gen10k.py" "$here/gen20k.py" "$1/"
cd "$1"
echo '{"cases": []}' > corpus.json
python3 add_extended_cases.py
python3 gen10k.py
python3 gen20k.py
python3 -c "
import json, os
open('list.txt', 'w').write(''.join(os.path.abspath(c['path']) + '\n' for c in json.load(open('corpus.json'))['cases']))"
