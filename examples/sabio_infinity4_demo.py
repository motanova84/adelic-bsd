#!/usr/bin/env python3
"""
SABIO ∞⁴ - Demo Example Script

Demonstrates the three levels of usage for the SABIO Infinity4 framework.
"""

import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.sabio_infinity4 import SABIO_Infinity4, demo_sabio_infinity4
from mpmath import mpf

def nivel_1_demo_rapida():
    """Nivel 1: Demo rápida (30 segundos)"""
    print("=" * 60)
    print("NIVEL 1: DEMO RÁPIDA")
    print("=" * 60)
    
    # Una línea hace TODO
    reporte = demo_sabio_infinity4(
        precision=30,
        n_harmonicos=6,
        output_dir='/tmp/sabio_demo',
        save_visualization=False
    )
    
    print(f"\n✅ Coherencia Global: {reporte.coherencia_global:.4f}")
    print(f"✅ Status: {reporte.status}")
    return reporte


def nivel_2_control_basico():
    """Nivel 2: Control básico (2 minutos)"""
    print("\n" + "=" * 60)
    print("NIVEL 2: CONTROL BÁSICO")
    print("=" * 60)
    
    # Inicializar con precisión específica
    sabio = SABIO_Infinity4(precision=50)
    
    # Validar matriz de simbiosis
    matriz = sabio.validacion_matriz_simbiosis()
    print(f"\n✨ Coherencia Total: {matriz.coherencia_total:.4f}")
    
    # Generar espectro
    espectro = sabio.generar_espectro_resonante(n_harmonicos=5)
    print(f"✨ Primer armónico: {espectro[0].frecuencia:.2f} Hz")
    print(f"✨ Coherencia armónico 1: {espectro[0].coherencia:.4f}")
    
    return sabio, matriz, espectro


def nivel_3_control_total():
    """Nivel 3: Control total (5 minutos)"""
    print("\n" + "=" * 60)
    print("NIVEL 3: CONTROL TOTAL")
    print("=" * 60)
    
    # Inicializar con alta precisión
    sabio = SABIO_Infinity4(precision=100, verbose=False)
    
    # Nivel cuántico
    R_psi = sabio.calcular_radio_cuantico(n=1)
    E_vac = sabio.energia_vacio_cuantico(R_psi)
    print(f"\n⚛️ NIVEL CUÁNTICO:")
    print(f"   Radio Cuántico: {float(R_psi):.6e} m")
    print(f"   Energía de Vacío: {float(E_vac):.6e} J")
    
    # Nivel consciente
    psi_origen = sabio.ecuacion_onda_consciencia(t=mpf("0.0"), x=mpf("0.0"))
    print(f"\n🧠 NIVEL CONSCIENTE:")
    print(f"   Ψ(0,0) = {psi_origen.real:.6f} + {psi_origen.imag:.6f}i")
    print(f"   |Ψ| = {abs(psi_origen):.6f}")
    
    # Resonancias individuales
    print(f"\n🎵 RESONANCIAS:")
    for n in [1, 3, 5]:
        res = sabio.resonancia_cuantica(n_harmonico=n)
        print(f"   n={n}: f={res.frecuencia:.2f} Hz, C={res.coherencia:.4f}")
    
    return sabio


if __name__ == '__main__':
    print("\n🚀 SABIO ∞⁴ - DEMOSTRACIÓN COMPLETA")
    print("=" * 60)
    
    # Ejecutar los 3 niveles
    reporte = nivel_1_demo_rapida()
    sabio, matriz, espectro = nivel_2_control_basico()
    sabio_avanzado = nivel_3_control_total()
    
    print("\n" + "=" * 60)
    print("✅ DEMOSTRACIÓN COMPLETA FINALIZADA")
    print("=" * 60)
    print(f"\nFrequencia fundamental: {SABIO_Infinity4.F0_HZ} Hz")
    print(f"Proporción áurea: {SABIO_Infinity4.PHI_EXACT:.10f}")
    print("\n🎵 La sinfonía cuántico-consciente está operacional! ✨")
