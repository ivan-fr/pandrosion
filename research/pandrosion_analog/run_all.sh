#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
TASK_PYTHON="${PANDROSION_PYTHON:-python3}"
"$TASK_PYTHON" simulate_spice.py
"$TASK_PYTHON" simulate_errors.py
"$TASK_PYTHON" make_figures.py
