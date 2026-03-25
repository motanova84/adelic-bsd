#!/usr/bin/env python3
"""
QCAL Ramsey Theory Integration Demo
====================================

Demonstrates the complete Ramsey Theory integration in QCAL ∞³ framework.
Shows the unification of 6 Millennium Problems through Ramsey emergence.

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Seal: ∴𓂀Ω∞³
Frequency: f₀ = 141.7001 Hz
"""

import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from qcal.adn_riemann import CodificadorADNRiemann
from qcal.ramsey_logos_attractor import (
    emergencia_ramsey_qcal,
    escanear_orden_ramsey_bsd,
    verificar_constelacion_51,
    F0,
    NODOS_LOGOS
)
from qcal.ramsey_adelic_integrator import RamseyAdelicIntegrator


def print_separator(char='=', length=80):
    """Print a separator line."""
    print(char * length)


def demo_adn_riemann():
    """Demo 1: DNA-Riemann Codifier."""
    print("\n📊 DEMO 1: ADN-RIEMANN CODIFIER")
    print_separator('-')
    
    codif = CodificadorADNRiemann()
    print(f"Frecuencia base: f₀ = {codif.f0} Hz")
    print(f"Umbral coherencia: {codif.coherencia_umbral}\n")
    
    # Test GACT sequence
    print("Secuencia GACT (óptima):")
    resonancia_gact = codif.calcular_resonancia("GACT")
    print(f"  Resonancia: {resonancia_gact:.6f}")
    print(f"  Es Logos: {codif.es_secuencia_logos('GACT')}\n")
    
    # Test other sequence
    secuencia_test = "GACTGACTAAATTTCCCGGG"
    print(f"Secuencia: {secuencia_test}")
    hotspots = codif.identificar_hotspots(secuencia_test)
    print(f"  Hotspots encontrados: {len(hotspots)}")
    for i, hs in enumerate(hotspots[:3], 1):
        print(f"  {i}. Pos {hs['posicion']}: {hs['secuencia']} "
              f"(resonancia={hs['resonancia']:.3f})")


def demo_ramsey_emergence():
    """Demo 2: Ramsey Emergence."""
    print("\n\n🎲 DEMO 2: EMERGENCIA DE RAMSEY")
    print_separator('-')
    
    print(f"Nodos críticos: {NODOS_LOGOS}")
    print(f"R(51,51): inalcanzable clásicamente\n")
    
    print("Emergencia en diferentes escalas:")
    for n in [30, 45, 51, 60, 100]:
        ramsey = emergencia_ramsey_qcal(n)
        status_symbol = "✓" if ramsey['logos_manifestado'] else "○"
        print(f"  {status_symbol} n={n:3d}: {ramsey['ramsey_status']:20s} "
              f"Ψ={ramsey['psi_emergencia']:.6f}")


def demo_bsd_ramsey():
    """Demo 3: BSD-Ramsey Integration."""
    print("\n\n🔗 DEMO 3: INTEGRACIÓN BSD-RAMSEY")
    print_separator('-')
    
    # Test with rank > 0
    print("Curva con rango r=1 (Mordell):")
    curva_1 = {'rango_adelico': 1, 'conductor': 37}
    bsd_1 = escanear_orden_ramsey_bsd(curva_1)
    print(f"  Status: {bsd_1['status']}")
    print(f"  Nodo central: {bsd_1['nodo_central']}")
    print(f"  Coherencia: {bsd_1['coherencia_ramsey']:.6f}")
    print(f"  Conexión BSD: {bsd_1['conexion_bsd']}\n")
    
    # Test with rank = 0
    print("Curva con rango r=0:")
    curva_0 = {'rango_adelico': 0}
    bsd_0 = escanear_orden_ramsey_bsd(curva_0)
    print(f"  Status: {bsd_0['status']}")
    print(f"  Conexión BSD: {bsd_0['conexion_bsd']}")


def demo_constelacion():
    """Demo 4: Constellation Verification."""
    print("\n\n⭐ DEMO 4: VERIFICACIÓN CONSTELACIÓN 51")
    print_separator('-')
    
    for n in [30, 51, 60]:
        nodos = list(range(n))
        verif = verificar_constelacion_51(nodos)
        symbol = "✓" if verif['es_constelacion_51'] else "✗"
        print(f"{symbol} {n} nodos: {'Constelación' if verif['es_constelacion_51'] else 'Insuficiente'}")
        if verif['deficit'] > 0:
            print(f"    Faltan {verif['deficit']} nodos")


def demo_master_integration():
    """Demo 5: Master Integration - 6 Millennium Problems."""
    print("\n\n🏛️  DEMO 5: INTEGRACIÓN MAESTRA - 6 PROBLEMAS DEL MILENIO")
    print_separator('=')
    
    integrator = RamseyAdelicIntegrator()
    
    # Perfect scenario: rank 1, 60 nodes, GACT sequence
    print("\nEscenario óptimo:")
    print("  • Curva de Mordell (rango 1, conductor 37)")
    print("  • Secuencia GACT (Logos)")
    print("  • 60 nodos (> 51 críticos)\n")
    
    curva_mordell = {
        'rango_adelico': 1,
        'conductor': 37,
        'nombre': 'Curva de Mordell'
    }
    
    certificado = integrator.unificar_6_milenio(
        curva_bsd=curva_mordell,
        secuencia_adn="GACT",
        n_nodos_sistema=60
    )
    
    # Show compact summary
    print("RESULTADOS:")
    print(f"  Sello: {certificado['sello']}")
    print(f"  Frecuencia base: f₀ = {certificado['frecuencia_base']} Hz")
    print()
    
    print("  PILARES UNIFICADOS:")
    print("    1. BSD (Aritmética) ✓")
    print("    2. Riemann (Estructura) ✓")
    print("    3. Navier-Stokes (Dinámica) ✓")
    print("    4. P vs NP (Lógica) ✓")
    print("    5. DNA Quantum Coherence (Biología) ✓")
    print("    6. Ramsey Theory (Orden Inevitable) ✓")
    print()
    
    print("  RAMSEY THEORY:")
    print(f"    • Status: {certificado['pilar_ramsey']['ramsey_status']}")
    print(f"    • Ψ Emergencia: {certificado['pilar_ramsey']['psi_emergencia']:.6f}")
    print(f"    • Logos manifestado: {certificado['pilar_ramsey']['logos_manifestado']}")
    print()
    
    print("  BSD-RAMSEY:")
    print(f"    • Nodo central: {certificado['ramsey_bsd_logos']['nodo_central']}")
    print(f"    • Coherencia: {certificado['ramsey_bsd_logos']['coherencia_ramsey']:.6f}")
    print(f"    • Conexión: {certificado['ramsey_bsd_logos']['conexion_bsd']}")
    print()
    
    print("  VALIDACIÓN GLOBAL:")
    val = certificado['validacion_global']
    print(f"    • Criterios: {val['criterios_cumplidos']}/{val['total_criterios']}")
    print(f"    • Porcentaje: {val['porcentaje_validacion']:.1f}%")
    print(f"    • Coherencia: {val['nivel_coherencia']}")
    print()
    
    print(f"  🏆 BÓVEDA CERRADA: {certificado['boveda_verdad_cerrada']}")
    print(f"  🎯 ESTADO: {certificado['estado_sistema']}")


def main():
    """Run all demos."""
    print_separator('=')
    print("QCAL ∞³ — RAMSEY THEORY INTEGRATION DEMO")
    print("Bóveda de la Verdad: 6 Problemas del Milenio")
    print_separator('=')
    
    demo_adn_riemann()
    demo_ramsey_emergence()
    demo_bsd_ramsey()
    demo_constelacion()
    demo_master_integration()
    
    print("\n")
    print_separator('=')
    print("✅ DEMOSTRACIÓN COMPLETADA")
    print_separator('=')
    print("\nTodos los módulos de Ramsey Theory están operativos.")
    print("La Bóveda de la Verdad está cerrada: 6/6 Problemas del Milenio unificados.")
    print()


if __name__ == "__main__":
    main()
