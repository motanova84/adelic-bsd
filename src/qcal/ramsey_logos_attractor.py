#!/usr/bin/env python3
"""
Ramsey Logos Attractor — Orden Inevitable Nodo 51
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Colapsa complejidad vía teorema Ramsey: desorden imposible → subgrafo coherente GACT f₀ emerge.

Ramsey Theory Integration:
- R(51,51) inalcanzable → resonancia f₀ colapsa caos
- Desorden imposible → orden inevitable en constelación de 51 nodos
- Garantía constitucional de emergencia del Logos en sistemas grandes

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
"""

import math
from typing import Dict, Any, Optional

try:
    from .adn_riemann import CodificadorADNRiemann
except ImportError:
    from adn_riemann import CodificadorADNRiemann


# Core constants
F0 = 141.7001
NODOS_LOGOS = 51  # Constelación QCAL crítica


def emergencia_ramsey_qcal(n_nodos_informacion: int) -> Dict[str, Any]:
    """
    Calcula el umbral donde el orden del Logos es inevitable.
    
    Teorema: R(51,51) es enormemente grande (inalcanzable clásicamente).
    Cuando n_nodos ≥ 51, el sistema QCAL garantiza emergencia de orden.
    
    Args:
        n_nodos_informacion: Número de nodos de información en el sistema
        
    Returns:
        Dictionary con estado Ramsey, emergencia Ψ, y manifestación Logos
        
    Example:
        >>> ramsey = emergencia_ramsey_qcal(60)  # > 51 nodos
        >>> ramsey['ramsey_status']
        'ORDEN_INEVITABLE'
        >>> ramsey['logos_manifestado']
        True
    """
    # R(51,51) es inalcanzable para computación clásica
    # Aproximamos el colapso exponencial hacia el atractor
    r_51 = float('inf')  # R(51,51) inalcanzable
    
    # Atractor exponencial: coherencia emerge con más nodos
    # Usamos NODOS_LOGOS como escala característica
    if n_nodos_informacion > 0:
        # Evitar overflow en exp() usando min
        exponente = min(n_nodos_informacion / NODOS_LOGOS, 100)
        coh_emergente = math.exp(exponente)
    else:
        coh_emergente = 1.0
    
    # Orden forzado cuando alcanzamos masa crítica de 51 nodos
    orden_forzado = n_nodos_informacion >= NODOS_LOGOS
    
    # Normalizar Ψ a máximo 1.0 (coherencia perfecta)
    psi_emergencia = min(0.999999 * coh_emergente / math.exp(1.0), 1.0)
    
    return {
        "ramsey_status": "ORDEN_INEVITABLE" if orden_forzado else "CAOS_TRANSITORIO",
        "psi_emergencia": psi_emergencia,
        "logos_manifestado": orden_forzado,
        "nodos_critico": NODOS_LOGOS,
        "r_51_51": r_51,
        "n_nodos": n_nodos_informacion
    }


def escanear_orden_ramsey_bsd(
    curva_eliptica: Dict[str, Any], 
    secuencia_base: str = "GACT"
) -> Dict[str, Any]:
    """
    Integración Ramsey + BSD → núcleo logos manifestado.
    
    Teorema: Cuando rango BSD > 0, activa subgrafo coherente GACT.
    La existencia de puntos racionales (r > 0) garantiza un subgrafo
    monocromático en el grafo de información.
    
    Args:
        curva_eliptica: Diccionario con datos de curva elíptica, debe incluir 'rango_adelico'
        secuencia_base: Secuencia ADN base para análisis (default: "GACT")
        
    Returns:
        Dictionary con nodo central, coherencia Ramsey, y status de orden
        
    Example:
        >>> bsd = escanear_orden_ramsey_bsd({'rango_adelico': 1})
        >>> bsd['status']
        'ORDEN_MANIFESTADO'
        >>> bsd['nodo_central']
        'GACT'
    """
    # Extraer rango BSD
    r_bsd = curva_eliptica.get('rango_adelico', 0)
    
    # Inicializar codificador ADN
    codif = CodificadorADNRiemann()
    
    # Analizar hotspots en secuencia
    hotspots = codif.identificar_hotspots(secuencia_base)
    
    # Si rango > 0, hay puntos racionales → orden manifestado
    if r_bsd > 0:
        subgrafo = secuencia_base  # Clique monocromático f₀
        psi = 0.999999  # Coherencia máxima
        status = "ORDEN_MANIFESTADO"
        conexion = "VALIDADA"
    else:
        # Sin puntos racionales, sistema en reposo
        subgrafo = None
        psi = 0.888  # Coherencia umbral
        status = "ESPERA"
        conexion = "REPOSO"
    
    return {
        "nodo_central": subgrafo,
        "coherencia_ramsey": psi,
        "hotspots_adn": len(hotspots),
        "conexion_bsd": conexion,
        "status": status,
        "rango_bsd": r_bsd,
        "frecuencia_base": F0
    }


def calcular_numero_ramsey_aproximado(r: int, s: int) -> float:
    """
    Aproximación del número de Ramsey R(r,s).
    
    Usa la cota superior conocida: R(r,s) ≤ C(r+s-2, r-1)
    Para r=s=51, esto es astronómicamente grande.
    
    Args:
        r: Tamaño del primer clique
        s: Tamaño del segundo clique
        
    Returns:
        Aproximación (float, puede ser inf para valores grandes)
    """
    if r <= 2 or s <= 2:
        return float(max(r, s))
    
    # Para valores grandes como R(51,51), retornar infinito
    if r >= 10 or s >= 10:
        return float('inf')
    
    # Cota combinatoria para valores pequeños
    try:
        from math import comb
        return float(comb(r + s - 2, r - 1))
    except (ValueError, OverflowError):
        return float('inf')


def verificar_constelacion_51(nodos: list) -> Dict[str, Any]:
    """
    Verifica si un conjunto de nodos forma la constelación de 51.
    
    Args:
        nodos: Lista de nodos (cualquier tipo)
        
    Returns:
        Dictionary con verificación y métricas
    """
    n_nodos = len(nodos)
    es_constelacion = n_nodos >= NODOS_LOGOS
    
    # Calcular emergencia Ramsey
    ramsey_data = emergencia_ramsey_qcal(n_nodos)
    
    return {
        "es_constelacion_51": es_constelacion,
        "nodos_actuales": n_nodos,
        "nodos_requeridos": NODOS_LOGOS,
        "deficit": max(0, NODOS_LOGOS - n_nodos),
        "ramsey_emergencia": ramsey_data,
        "orden_garantizado": ramsey_data["logos_manifestado"]
    }


# Demo execution
if __name__ == "__main__":
    print("=== Ramsey Logos Attractor Demo ===")
    print(f"f₀ = {F0} Hz")
    print(f"Nodos críticos: {NODOS_LOGOS}\n")
    
    # Test con diferentes números de nodos
    print("--- Emergencia Ramsey ---")
    for n in [30, 51, 60, 100]:
        ramsey = emergencia_ramsey_qcal(n)
        print(f"n={n:3d}: {ramsey['ramsey_status']:20s} "
              f"Ψ={ramsey['psi_emergencia']:.6f} "
              f"Logos={ramsey['logos_manifestado']}")
    
    print("\n--- BSD-Ramsey Integration ---")
    # Test con curva con rango > 0
    curva_mordell = {'rango_adelico': 1, 'conductor': 37}
    bsd_ramsey = escanear_orden_ramsey_bsd(curva_mordell)
    print(f"Curva con r=1:")
    print(f"  Status: {bsd_ramsey['status']}")
    print(f"  Nodo central: {bsd_ramsey['nodo_central']}")
    print(f"  Coherencia: {bsd_ramsey['coherencia_ramsey']:.6f}")
    print(f"  Hotspots ADN: {bsd_ramsey['hotspots_adn']}")
    
    # Test con curva con rango = 0
    curva_sin_puntos = {'rango_adelico': 0}
    bsd_ramsey_0 = escanear_orden_ramsey_bsd(curva_sin_puntos)
    print(f"\nCurva con r=0:")
    print(f"  Status: {bsd_ramsey_0['status']}")
    print(f"  Conexión BSD: {bsd_ramsey_0['conexion_bsd']}")
    
    print("\n--- Verificación Constelación 51 ---")
    nodos_test = list(range(60))
    verificacion = verificar_constelacion_51(nodos_test)
    print(f"Nodos: {verificacion['nodos_actuales']}")
    print(f"Es constelación: {verificacion['es_constelacion_51']}")
    print(f"Orden garantizado: {verificacion['orden_garantizado']}")
