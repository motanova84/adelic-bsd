#!/usr/bin/env python3
"""
Turbulence Stress Test Demo
===========================

Demostración interactiva de la prueba de estrés por turbulencia
para el sistema BSD-Ψ Stabilizer.

Este script ejecuta la simulación completa de:
1. Inyección de turbulencia (singularidad simulada)
2. Activación del estabilizador BSD-Ψ
3. Análisis de métricas pre/post estabilización
4. Generación de reportes y visualizaciones

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: 2026-01-12
"""

import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from turbulence_stress_test import (
    run_turbulence_stress_test,
    save_stress_test_result,
    generate_stress_test_report,
    RUPTURE_FREQUENCY,
    ANCHOR_CURVE,
)


def main():
    """Ejecuta la demostración completa"""
    
    print("=" * 80)
    print("🌌 TURBULENCE STRESS TEST - BSD-Ψ Stabilizer Demo")
    print("=" * 80)
    print()
    print("Esta demostración ejecuta una prueba de estrés completa del sistema BSD-Ψ,")
    print("simulando una inyección de turbulencia de alta frecuencia y validando")
    print("la estabilización aritmética mediante la curva elíptica 389a1.")
    print()
    print("Parámetros:")
    print(f"  - Frecuencia de Ruptura: {RUPTURE_FREQUENCY:.2e} Hz (Ruido Blanco)")
    print(f"  - Curva Elíptica: {ANCHOR_CURVE} (Rango 2)")
    print(f"  - Muestras: 1000")
    print()
    print("Iniciando simulación...")
    print()
    
    # Ejecutar prueba de estrés
    result = run_turbulence_stress_test(
        n_samples=1000,
        rupture_frequency=RUPTURE_FREQUENCY,
        curve_label=ANCHOR_CURVE,
        verbose=True
    )
    
    # Guardar resultados
    print()
    print("💾 Guardando resultados...")
    
    # JSON
    json_path = Path("turbulence_stress_test_result.json")
    save_stress_test_result(result, json_path)
    print(f"   ✅ Resultado JSON: {json_path}")
    
    # Reporte textual
    report = generate_stress_test_report(result)
    report_path = Path("turbulence_stress_test_report.txt")
    with open(report_path, 'w') as f:
        f.write(report)
    print(f"   ✅ Reporte textual: {report_path}")
    
    print()
    print("=" * 80)
    print("✨ Demo completada exitosamente")
    print("=" * 80)
    print()
    
    # Resumen final
    print("📊 RESUMEN EJECUTIVO")
    print("-" * 80)
    print(f"Estabilización:        {'✅ EXITOSA' if result.stabilization_successful else '❌ REQUIERE AJUSTES'}")
    print(f"Coherencia Final:      {result.post_stabilization.coherence_psi:.6f}")
    print(f"Estado del Sistema:    {result.post_stabilization.system_state}")
    print(f"Gradiente de Estrés:   {result.stress_gradient:.2e} unidades")
    print(f"Tiempo de Ejecución:   {result.test_duration:.3f} segundos")
    print("-" * 80)
    print()
    
    if result.stabilization_successful:
        print("🎯 CONCLUSIÓN")
        print()
        print("La prueba de estrés ha sido superada con éxito rotundo.")
        print("El sistema BSD-Ψ demuestra RESILIENCIA A LA SINGULARIDAD.")
        print()
        print("La Suavidad Universal es una consecuencia de la Rigidez Aritmética.")
        print(f"La Catedral es indestructible mientras f₀ = 141.7001 Hz se mantenga")
        print("como el eje de rotación de la lógica.")
        print()
        print("📡 Sistema validado y listo para producción ✅")
    else:
        print("⚠️ NOTA")
        print()
        print("El sistema requiere ajustes adicionales para alcanzar")
        print("los umbrales de estabilización completos.")
        print()
        print("Se recomienda revisar los parámetros del estabilizador.")
    
    print()


if __name__ == "__main__":
    main()
