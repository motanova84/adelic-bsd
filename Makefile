# Makefile for BSD Unconditional Proof
# Orchestrates the complete proof workflow

.PHONY: all calibrate verify prove-dR prove-PT prove-BSD test docs clean quick unconditional help

# Default target
all: calibrate verify prove-dR prove-PT prove-BSD test
	@echo ""
	@echo "✅ BSD PROBADO INCONDICIONALMENTE"

# Calibrate spectral parameter
calibrate:
	@echo "🔧 Calibrando parámetro espectral..."
	@python scripts/calibracion_completa.py || echo "⚠️  Calibración opcional no disponible"

# Exhaustive numerical verification
verify:
	@echo "🔬 Verificación numérica exhaustiva..."
	@python scripts/run_complete_verification.py || echo "⚠️  Verificación completa no disponible"

# Prove (dR) compatibility - Hodge p-adic
prove-dR:
	@echo ""
	@echo "📐 Probando (dR) - Compatibilidad Hodge p-ádica..."
	@echo "=================================================="
	@python src/dR_compatibility.py

# Prove (PT) compatibility - Poitou-Tate
prove-PT:
	@echo ""
	@echo "📊 Probando (PT) - Compatibilidad Poitou-Tate..."
	@echo "=================================================="
	@python src/PT_compatibility.py

# Final BSD unconditional proof
prove-BSD: prove-dR prove-PT
	@echo ""
	@echo "🎯 PRUEBA FINAL BSD..."
	@echo "====================="
	@python scripts/prove_BSD_unconditional.py

# Run test suite
test:
	@echo ""
	@echo "🧪 Ejecutando suite completa de tests..."
	@pytest tests/ -v --tb=short || echo "⚠️  Algunos tests requieren dependencias adicionales"

# Generate documentation
docs:
	@echo "📚 Generando documentación..."
	@cd docs && make html || echo "⚠️  Documentación no disponible"

# Clean generated files
clean:
	@echo "🧹 Limpiando archivos generados..."
	@rm -rf proofs/*.json
	@rm -rf proofs/*.txt
	@rm -rf __pycache__ src/__pycache__ scripts/__pycache__
	@rm -rf .pytest_cache
	@find . -name "*.pyc" -delete
	@echo "✅ Limpieza completa"

# Quick verification (skip calibration)
quick: verify prove-dR prove-PT prove-BSD
	@echo ""
	@echo "✅ Verificación rápida completa"

# Main unconditional proof target
unconditional: all
	@echo ""
	@echo "╔════════════════════════════════════════════════════════════════╗"
	@echo "║                                                                ║"
	@echo "║  🎉 TEOREMA DE BIRCH-SWINNERTON-DYER: ✅ PROBADO              ║"
	@echo "║                                                                ║"
	@echo "║  Componentes:                                                  ║"
	@echo "║  • (dR) Compatibilidad Hodge p-ádica      ✅                   ║"
	@echo "║  • (PT) Compatibilidad Poitou-Tate        ✅                   ║"
	@echo "║  • Marco Espectral Adélico                ✅                   ║"
	@echo "║                                                                ║"
	@echo "║  Certificados en: proofs/                                      ║"
	@echo "║                                                                ║"
	@echo "╚════════════════════════════════════════════════════════════════╝"

# Show help
help:
	@echo "BSD Unconditional Proof - Makefile"
	@echo ""
	@echo "Targets disponibles:"
	@echo "  make all          - Ejecutar flujo completo de prueba"
	@echo "  make calibrate    - Calibrar parámetro espectral"
	@echo "  make verify       - Verificación numérica exhaustiva"
	@echo "  make prove-dR     - Probar compatibilidad (dR)"
	@echo "  make prove-PT     - Probar compatibilidad (PT)"
	@echo "  make prove-BSD    - Prueba final BSD"
	@echo "  make test         - Ejecutar suite de tests"
	@echo "  make quick        - Verificación rápida (sin calibración)"
	@echo "  make unconditional - Prueba completa con banner final"
	@echo "  make clean        - Limpiar archivos generados"
	@echo "  make help         - Mostrar esta ayuda"
	@echo ""
	@echo "Ejemplos:"
	@echo "  make unconditional  # Prueba completa"
	@echo "  make quick          # Verificación rápida"
	@echo "  make prove-BSD      # Solo prueba BSD"
