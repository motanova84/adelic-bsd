#!/bin/bash
# Script para encontrar pruebas incompletas (sorry) en Lean 4

echo "🔍 Buscando pruebas incompletas (sorry) en Lean 4..."
echo ""

LEAN_DIR="formalization/lean"

if [ ! -d "$LEAN_DIR" ]; then
    echo "⚠️  Directorio $LEAN_DIR no encontrado"
    exit 1
fi

# Buscar todos los sorry
echo "📋 Archivos con 'sorry' encontrados:"
echo ""

TOTAL=0
while IFS= read -r line; do
    echo "⚠️  $line"
    ((TOTAL++))
done < <(grep -rn "sorry" "$LEAN_DIR" --include="*.lean")

echo ""
echo "📊 Total de 'sorry' encontrados: $TOTAL"

if [ $TOTAL -eq 0 ]; then
    echo ""
    echo "✅ ¡No hay pruebas incompletas! Todas las formalizaciones están completas."
    exit 0
else
    echo ""
    echo "💡 Recomendación: Completar las pruebas marcadas con 'sorry'"
    echo "   Ver: scripts/complete_lean_proofs.py para guía de completación"
    exit 0
fi
