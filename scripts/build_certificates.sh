#!/usr/bin/env bash
set -e
LABELS=("11a1" "14a1" "37a1" "43a1")
for L in "${LABELS[@]}"; do
  sage -python finitud_espectral.py --curve "$L" --certificate
done
echo "Certificados generados en certificados/"
