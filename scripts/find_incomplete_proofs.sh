#!/bin/bash

# Script para encontrar pruebas incompletas en archivos Lean
# Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
# Date: November 2025

echo "╔════════════════════════════════════════════════════════╗"
echo "║  BUSCANDO PRUEBAS INCOMPLETAS EN LEAN 4                ║"
echo "║  Framework Espectral Adelico                           ║"
echo "╚════════════════════════════════════════════════════════╝"
echo ""

LEAN_DIR="formalization/lean"

if [ ! -d "$LEAN_DIR" ]; then
    echo "⚠️  Directorio $LEAN_DIR no encontrado"
    exit 1
fi

echo "🔍 Buscando archivos .lean en $LEAN_DIR..."
echo ""

# Contar total de sorries
TOTAL_SORRIES=$(find "$LEAN_DIR" -name "*.lean" -exec grep -c "sorry" {} + 2>/dev/null | awk '{s+=$1} END {print s}')

if [ -z "$TOTAL_SORRIES" ] || [ "$TOTAL_SORRIES" -eq 0 ]; then
    echo "✅ No se encontraron pruebas incompletas (sorry)"
    exit 0
fi

echo "📊 Total de 'sorry' encontrados: $TOTAL_SORRIES"
echo ""
echo "════════════════════════════════════════════════════════"
echo "PRUEBAS INCOMPLETAS POR ARCHIVO:"
echo "════════════════════════════════════════════════════════"

# Listar sorries por archivo
find "$LEAN_DIR" -name "*.lean" | while read -r file; do
    SORRY_COUNT=$(grep -c "sorry" "$file" 2>/dev/null || echo 0)
    
    if [ "$SORRY_COUNT" -gt 0 ]; then
        echo ""
        echo "📄 $(basename "$file"): $SORRY_COUNT prueba(s) pendiente(s)"
        
        # Mostrar líneas con sorry
        grep -n "sorry" "$file" | while IFS=: read -r line_num line_content; do
            echo "   Línea $line_num: ${line_content:0:60}..."
        done
    fi
done

echo ""
echo "════════════════════════════════════════════════════════"
echo "💡 Para mapeo detallado, ejecuta:"
echo "   python3 scripts/complete_lean_proofs.py"
echo "════════════════════════════════════════════════════════"
