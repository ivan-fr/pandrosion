#!/usr/bin/env bash
# Retry interrupted cache transfers, reusing files already downloaded by Lake.
# A persistent failure still blocks the job before any project build or audit.
set -euo pipefail

readonly cache_attempts=3
for ((cache_attempt=1; cache_attempt<=cache_attempts; cache_attempt++)); do
  echo "Mathlib cache download: attempt $cache_attempt/$cache_attempts"
  if lake exe cache get; then
    exit 0
  else
    cache_status=$?
  fi

  if ((cache_attempt == cache_attempts)); then
    echo "Mathlib cache download failed after $cache_attempts attempts." >&2
    exit "$cache_status"
  fi

  cache_delay=$((10 * cache_attempt))
  echo "Retrying incomplete cache download in $cache_delay seconds." >&2
  sleep "$cache_delay"
done
