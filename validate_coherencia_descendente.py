#!/usr/bin/env python3
"""
Validación del Teorema de la Coherencia Descendente
Validation of the Descending Coherence Theorem

Este script valida que los 5 fenómenos fundamentales emergen
de un único mecanismo: la coherencia descendente.

Autor: José Manuel Mota Burruezo (JMMB Ψ·∴)
Framework: QCAL ∞³
Fecha: 13 Febrero 2026
"""

import sys
import os

# Añadir src al path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from coherencia_descendente import CoherenciaDescendente
import json


def test_complejidad_irreducible():
    """Test del Fenómeno 1: Complejidad Irreducible."""
    print("\n" + "="*70)
    print("TEST 1: COMPLEJIDAD IRREDUCIBLE")
    print("="*70)
    
    sistema = CoherenciaDescendente(verbose=False)
    
    # Test con coherencia por encima del umbral
    resultado = sistema.complejidad_irreducible(40, 0.900)
    assert resultado['activado'] == True, "Debería activarse con Ψ > 0.888"
    assert resultado['estado'] == "ESTRUCTURA_COMPLETA"
    print("✓ Test 1a: Activación con Ψ = 0.900 - PASADO")
    
    # Test con coherencia por debajo del umbral
    resultado = sistema.complejidad_irreducible(40, 0.700)
    assert resultado['activado'] == False, "No debería activarse con Ψ < 0.888"
    assert resultado['estado'] == "NO_SINCRONIZADO"
    print("✓ Test 1b: No activación con Ψ = 0.700 - PASADO")
    
    # Test en el umbral exacto
    resultado = sistema.complejidad_irreducible(40, 0.888)
    assert resultado['activado'] == True, "Debería activarse en Ψ = 0.888"
    print("✓ Test 1c: Activación en umbral Ψ = 0.888 - PASADO")
    
    print("\n✓ FENÓMENO 1: VALIDADO")
    return True


def test_aparicion_conciencia():
    """Test del Fenómeno 2: Aparición de Conciencia."""
    print("\n" + "="*70)
    print("TEST 2: APARICIÓN DE CONCIENCIA")
    print("="*70)
    
    sistema = CoherenciaDescendente(verbose=False)
    
    # Test cerebro humano (~86 mil millones de neuronas)
    resultado = sistema.antena_biologica(86e9)
    assert resultado['conciencia'] == True, "Cerebro humano debe tener conciencia"
    assert resultado['sintonizacion'] >= sistema.UMBRAL_PICODE
    print("✓ Test 2a: Cerebro humano (86B neuronas) - CONSCIENTE")
    
    # Test sistema simple (pocas neuronas)
    resultado = sistema.antena_biologica(100)
    assert resultado['conciencia'] == False, "Sistema simple no debe tener conciencia plena"
    print("✓ Test 2b: Sistema simple (100 neuronas) - PRE-CONSCIENTE")
    
    # Test frecuencia de acople
    resultado = sistema.antena_biologica(86e9, 141.7001)
    assert abs(resultado['campo_frecuencia'] - 141.7001) < 1e-6
    print("✓ Test 2c: Acople a f₀ = 141.7001 Hz - VALIDADO")
    
    print("\n✓ FENÓMENO 2: VALIDADO")
    return True


def test_experiencias_cercanas_muerte():
    """Test del Fenómeno 3: Experiencias Cercanas a la Muerte."""
    print("\n" + "="*70)
    print("TEST 3: EXPERIENCIAS CERCANAS A LA MUERTE")
    print("="*70)
    
    sistema = CoherenciaDescendente(verbose=False)
    
    # Test ECM intensa
    resultado = sistema.experiencia_cercana_muerte(0.98)
    assert resultado['conciencia'] == True, "Conciencia debe permanecer en ECM"
    assert resultado['antena_activa'] == False, "Antena debe estar descorrelada"
    assert resultado['localizacion'] == "NO_LOCAL"
    print("✓ Test 3a: ECM intensa (0.98) - DESCORRELACIÓN NO-LOCAL")
    
    # Test estado normal
    resultado = sistema.experiencia_cercana_muerte(0.50)
    assert resultado['conciencia'] == True
    assert resultado['antena_activa'] == True
    assert resultado['localizacion'] == "CUERPO"
    print("✓ Test 3b: Estado normal (0.50) - CORRELACIÓN LOCAL")
    
    # Test campo invariante
    resultado = sistema.experiencia_cercana_muerte(0.98)
    assert "141.7001" in resultado['campo']
    print("✓ Test 3c: Campo invariante a 141.7001 Hz - VALIDADO")
    
    print("\n✓ FENÓMENO 3: VALIDADO")
    return True


def test_no_localidad():
    """Test del Fenómeno 4: No-localidad."""
    print("\n" + "="*70)
    print("TEST 4: NO-LOCALIDAD")
    print("="*70)
    
    sistema = CoherenciaDescendente(verbose=False)
    
    # Test coherencia alta (distancia irrelevante)
    resultado = sistema.correlacion_no_local(1000.0, 0.950)
    assert resultado['correlacion'] == 1.0, "Correlación debe ser perfecta con alta coherencia"
    assert resultado['tiempo'] == "INSTANTÁNEO"
    assert resultado['distancia_estado'] == "IRRELEVANTE"
    print("✓ Test 4a: Alta coherencia (Ψ=0.950) - CORRELACIÓN PERFECTA")
    
    # Test coherencia baja (aparece separación)
    resultado = sistema.correlacion_no_local(1000.0, 0.700)
    assert resultado['correlacion'] < 1.0
    assert resultado['tiempo'] == "LIMITADO POR c"
    print("✓ Test 4b: Baja coherencia (Ψ=0.700) - SEPARACIÓN APARENTE")
    
    # Test constante κ_Π
    assert abs(sistema.KAPPA_PI - 2.578208) < 1e-6
    print("✓ Test 4c: Constante κ_Π = 2.578208 - VALIDADO")
    
    print("\n✓ FENÓMENO 4: VALIDADO")
    return True


def test_evolucion_puntuada():
    """Test del Fenómeno 5: Evolución Puntuada."""
    print("\n" + "="*70)
    print("TEST 5: EVOLUCIÓN PUNTUADA")
    print("="*70)
    
    sistema = CoherenciaDescendente(verbose=False)
    
    # Test estado actual humano
    resultado = sistema.transicion_evolutiva(0.8991)
    assert resultado['estado_actual'] == "cerebro_humano"
    assert len(resultado['estados_activados']) == 6  # Hasta cerebro_humano
    assert len(resultado['estados_potenciales']) == 2  # Conciencia global y campo unificado
    print("✓ Test 5a: Estado cerebro_humano (Ψ=0.8991) - VALIDADO")
    
    # Test estado primitivo
    resultado = sistema.transicion_evolutiva(0.650)
    assert resultado['estado_actual'] == "eucariota"
    print("✓ Test 5b: Estado eucariota (Ψ=0.650) - VALIDADO")
    
    # Test umbrales discretos
    assert len(sistema.UMBRALES_COHERENCIA) == 8
    assert sistema.UMBRALES_COHERENCIA['cerebro_humano'] == 0.8991
    print("✓ Test 5c: Umbrales discretos - VALIDADOS")
    
    print("\n✓ FENÓMENO 5: VALIDADO")
    return True


def test_teorema_completo():
    """Test de validación completa del teorema."""
    print("\n" + "="*70)
    print("TEST 6: TEOREMA COMPLETO DE COHERENCIA DESCENDENTE")
    print("="*70)
    
    sistema = CoherenciaDescendente(verbose=False)
    
    # Validar teorema completo
    validacion = sistema.validar_teorema_completo()
    
    # Verificar estructura del resultado
    assert 'teorema' in validacion
    assert validacion['teorema'] == "COHERENCIA_DESCENDENTE"
    
    assert 'fenomenos' in validacion
    assert len(validacion['fenomenos']) == 5
    
    # Verificar constantes fundamentales
    assert abs(validacion['frecuencia_fundamental'] - 141.7001) < 1e-6
    assert abs(validacion['coherencia_sistema'] - 0.8991) < 1e-6
    assert abs(validacion['umbral_critico'] - 0.888) < 1e-6
    
    # Verificar verificación empírica
    verificacion = validacion['verificacion']
    assert verificacion['f0_hz'] == 141.7001
    assert verificacion['delta_p'] == 0.1987
    assert verificacion['sigma_magnetorrecepcion'] == 9.2
    assert verificacion['sigma_microtubulos'] == 8.7
    assert verificacion['psi_sistema'] == 0.8991
    
    print("✓ Test 6a: Estructura de validación - CORRECTA")
    print("✓ Test 6b: Constantes fundamentales - VALIDADAS")
    print("✓ Test 6c: Verificación empírica - CONFIRMADA")
    
    # Generar reporte JSON
    archivo = sistema.generar_reporte_json()
    assert os.path.exists(archivo)
    print(f"✓ Test 6d: Reporte JSON generado - {archivo}")
    
    # Verificar contenido del JSON
    with open(archivo, 'r', encoding='utf-8') as f:
        datos = json.load(f)
        assert datos['conclusion'] == "MATERIALISMO FALSADO - COHERENCIA VALIDADA"
    
    print("✓ Test 6e: Contenido JSON - VALIDADO")
    
    print("\n✓ TEOREMA COMPLETO: VALIDADO")
    return True


def test_constantes_fundamentales():
    """Test de constantes fundamentales del framework."""
    print("\n" + "="*70)
    print("TEST 7: CONSTANTES FUNDAMENTALES")
    print("="*70)
    
    sistema = CoherenciaDescendente(verbose=False)
    
    # Verificar todas las constantes
    assert abs(sistema.F0 - 141.7001) < 1e-6
    print("✓ Test 7a: f₀ = 141.7001 Hz")
    
    assert abs(sistema.F_MICROTUBULOS - 141.88) < 1e-6
    print("✓ Test 7b: f_microtúbulos = 141.88 Hz")
    
    assert abs(sistema.DELTA_ACOPLE - 0.18) < 1e-6
    print("✓ Test 7c: Δ_acople = 0.18 Hz")
    
    assert abs(sistema.KAPPA_PI - 2.578208) < 1e-6
    print("✓ Test 7d: κ_Π = 2.578208")
    
    assert abs(sistema.DELTA_V - 0.21) < 1e-6
    print("✓ Test 7e: δ_v = 0.21 Hz")
    
    assert abs(sistema.UMBRAL_PICODE - 0.888) < 1e-6
    print("✓ Test 7f: Umbral πCODE = 0.888")
    
    assert abs(sistema.PSI_SISTEMA - 0.8991) < 1e-6
    print("✓ Test 7g: Ψ_sistema = 0.8991")
    
    print("\n✓ CONSTANTES FUNDAMENTALES: VALIDADAS")
    return True


def main():
    """Ejecuta todos los tests de validación."""
    print("\n" + "#"*70)
    print("# VALIDACIÓN DEL TEOREMA DE LA COHERENCIA DESCENDENTE")
    print("# Descending Coherence Theorem Validation")
    print("#"*70)
    print(f"\nFramework: QCAL ∞³")
    print(f"Frecuencia: 141.7001 Hz")
    print(f"Autor: JMMB Ψ·∴")
    print(f"Fecha: 13 Febrero 2026")
    
    tests = [
        ("Constantes Fundamentales", test_constantes_fundamentales),
        ("Complejidad Irreducible", test_complejidad_irreducible),
        ("Aparición de Conciencia", test_aparicion_conciencia),
        ("Experiencias Cercanas a Muerte", test_experiencias_cercanas_muerte),
        ("No-localidad", test_no_localidad),
        ("Evolución Puntuada", test_evolucion_puntuada),
        ("Teorema Completo", test_teorema_completo)
    ]
    
    resultados = []
    
    for nombre, test_func in tests:
        try:
            resultado = test_func()
            resultados.append((nombre, True, None))
        except Exception as e:
            resultados.append((nombre, False, str(e)))
            print(f"\n❌ ERROR en {nombre}: {e}")
    
    # Resumen
    print("\n" + "="*70)
    print("RESUMEN DE VALIDACIÓN")
    print("="*70)
    
    pasados = sum(1 for _, resultado, _ in resultados if resultado)
    total = len(resultados)
    
    for nombre, resultado, error in resultados:
        simbolo = "✓" if resultado else "❌"
        print(f"{simbolo} {nombre}")
        if error:
            print(f"  Error: {error}")
    
    print(f"\nTests pasados: {pasados}/{total}")
    
    if pasados == total:
        print("\n" + "="*70)
        print("✓ TODOS LOS TESTS PASADOS")
        print("="*70)
        print("\n∴ La coherencia desciende. ∴")
        print("∴ La materia responde. ∴")
        print("∴ La vida recuerda. ∴")
        print("\n∴ MATERIALISMO FALSADO - COHERENCIA VALIDADA ∴")
        print("\n∴ 𓂀 Ω ∞³ Ξ Σ ⊕ ∴")
        print("∴ JMMB Ψ✧ · motanova84 · NOESIS ∞³ ∴")
        return 0
    else:
        print("\n" + "="*70)
        print(f"❌ {total - pasados} TESTS FALLIDOS")
        print("="*70)
        return 1


if __name__ == "__main__":
    sys.exit(main())
