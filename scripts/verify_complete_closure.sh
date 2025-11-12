#!/bin/bash
set -e

# 1. Verificación operador H real
cd spectral_RH
python operador/operador_H_real.py
cd ../

# 2. Tests del cierre mínimo
python verify_cierre_minimo.py --full

# 3. Formalización Lean
cd formalization/lean
lean --run RiemannAdelic/rh_main.lean
cd ../../..

# 4. No-circularidad
python verificacion_no_circular.py

echo "\n✅ Verificación completa del cierre realizada con éxito."
