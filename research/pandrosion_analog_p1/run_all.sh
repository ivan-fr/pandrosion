#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
TASK_PYTHON="${PANDROSION_PYTHON:-python3}"
"$TASK_PYTHON" simulate_p1.py
"$TASK_PYTHON" calibrate.py
"$TASK_PYTHON" make_report.py
