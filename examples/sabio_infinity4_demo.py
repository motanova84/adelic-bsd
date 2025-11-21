#!/usr/bin/env python3
"""
Demo de SABIO ∞⁴ - Symbiotic Adelic-Based Infinite-Order Operator
Demostración del sistema cuántico-consciente de orden infinito

Este script muestra las capacidades principales de SABIO ∞⁴:
1. Inicialización del sistema con alta precisión
2. Cálculo de radio cuántico R_Ψ y energía de vacío E_vac
3. Ecuación de onda de consciencia Ψ(x,t)
4. Generación de espectro resonante con escalado áureo
5. Validación simbiótica multi-nivel (6 niveles)
6. Exportación de reportes y visualizaciones
"""

import sys
import os

# Configurar path para importar desde src
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# noqa below to suppress flake8 warnings for imports after path manipulation
from src.sabio_infinity4 import (  # noqa: E402
    SABIO_Infinity4,
    demo_sabio_infinity4
)


def demo_basico():
    """Demo básico de funcionalidades principales"""
    print("="*70)
    print("🌌 SABIO ∞⁴ - DEMO BÁSICO")
    print("="*70)
    print()
    
    # 1. Inicializar sistema
    print("1️⃣  Inicializando sistema SABIO ∞⁴...")
    sabio = SABIO_Infinity4(precision=40)
    print()
    
    # 2. Radio cuántico
    print("2️⃣  Calculando radio cuántico R_Ψ...")
    R_psi = sabio.calcular_radio_cuantico(n=1)
    print(f"   R_Ψ = {float(R_psi):.6e} m")
    print("   (Orden de longitud de Planck × π × √φ)")
    print()
    
    # 3. Energía de vacío
    print("3️⃣  Calculando energía de vacío E_vac(R_Ψ)...")
    E_vac = sabio.energia_vacio_cuantico(R_psi)
    print(f"   E_vac = {float(E_vac):.6e} J")
    print("   Ecuación: E_vac(R_Ψ) = α/R_Ψ⁴ + β·ζ'(1/2)/R_Ψ² + "
          "γ·Λ²·R_Ψ² + δ·sin²(log(R_Ψ)/log(π))")
    print()
    
    # 4. Ecuación de onda de consciencia
    print("4️⃣  Evaluando ecuación de onda de consciencia Ψ(x,t)...")
    from mpmath import mpf
    psi = sabio.ecuacion_onda_consciencia(t=mpf("0.0"), x=mpf("0.0"))
    print(f"   Ψ(0,0) = {float(psi.real):.6f} + {float(psi.imag):.6f}i")
    print(f"   |Ψ| = {float(abs(psi)):.6f}")
    print("   Ecuación: ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·∇²Φ")
    print()
    
    # 5. Resonancia cuántica
    print("5️⃣  Generando resonancia cuántica fundamental...")
    res = sabio.resonancia_cuantica(n_harmonico=1)
    print(f"   Frecuencia: {res.frecuencia:.2f} Hz")
    print(f"   Amplitud: {abs(res.amplitud):.4f}")
    print(f"   Coherencia: {res.coherencia:.4f}")
    print(f"   Entropía: {res.entropia:.4f}")
    print(f"   Firma: {res.firma_vibracional}")
    print()
    
    # 6. Espectro resonante
    print("6️⃣  Generando espectro resonante completo...")
    espectro = sabio.generar_espectro_resonante(n_harmonicos=5)
    print()
    
    # 7. Validación simbiótica
    print("7️⃣  Validación simbiótica multi-nivel...")
    matriz = sabio.validacion_matriz_simbiosis()
    print(f"   Nivel Python (Aritmético):    {matriz.nivel_python:.4f}")
    print(f"   Nivel Lean (Geométrico):      {matriz.nivel_lean:.4f}")
    print(f"   Nivel Sage (Vibracional):     {matriz.nivel_sage:.4f}")
    print(f"   Nivel SABIO (Compilador):     {matriz.nivel_sabio:.4f}")
    print(f"   Nivel Cuántico (E_vac):       {matriz.nivel_cuantico:.4f}")
    print(f"   Nivel Consciente (Ψ):         {matriz.nivel_consciente:.4f}")
    print(f"   🌟 COHERENCIA TOTAL:          {matriz.coherencia_total:.4f}")
    print()
    
    print("="*70)
    print("✨ Demo básico completado con éxito")
    print("="*70)


def demo_avanzado():
    """Demo avanzado con reporte completo y visualizaciones"""
    print("\n")
    print("="*70)
    print("🌌 SABIO ∞⁴ - DEMO AVANZADO")
    print("="*70)
    print()
    
    # Ejecutar demo completo
    reporte = demo_sabio_infinity4()
    
    return reporte


def demo_exploracion_armonicos():
    """Demo de exploración de armónicos con escalado áureo"""
    print("\n")
    print("="*70)
    print("🎵 EXPLORACIÓN DE ARMÓNICOS CON ESCALADO ÁUREO")
    print("="*70)
    print()
    
    sabio = SABIO_Infinity4(precision=30)
    
    print("Generando primeros 10 armónicos:")
    print("-" * 70)
    print(f"{'n':>3} | {'Frecuencia (Hz)':>15} | {'Relación φⁿ':>12} | "
          f"{'Coherencia':>11} | {'Entropía':>9}")
    print("-" * 70)
    
    phi = float(sabio.phi_golden)
    f0 = float(sabio.f0)
    
    for n in range(1, 11):
        res = sabio.resonancia_cuantica(n_harmonico=n)
        ratio = res.frecuencia / f0
        expected_ratio = phi ** n
        
        print(f"{n:>3} | {res.frecuencia:>15.2f} | {ratio:>12.4f} | "
              f"{res.coherencia:>11.4f} | {res.entropia:>9.4f}")
    
    print("-" * 70)
    print(f"\n📐 Razón áurea φ = {phi:.8f}")
    print(f"🎵 Frecuencia base f₀ = {f0} Hz")
    print(f"✨ Relación: f_n = f₀ · φⁿ")
    print()


def demo_comparacion_niveles():
    """Demo de comparación entre diferentes niveles de realidad"""
    print("\n")
    print("="*70)
    print("🔬 COMPARACIÓN DE NIVELES DE REALIDAD")
    print("="*70)
    print()
    
    sabio = SABIO_Infinity4(precision=30)
    
    # Test individual de cada nivel
    niveles_info = [
        ("Aritmético", {'test_aritmetico': True}),
        ("Geométrico", {'test_geometrico': True}),
        ("Vibracional", {'test_vibracional': True}),
        ("Cuántico", {'test_cuantico': True}),
        ("Consciente", {'test_consciente': True}),
    ]
    
    print("Validación individual de cada nivel:")
    print("-" * 70)
    
    for nombre, kwargs in niveles_info:
        # Resetear todos los tests a False
        test_params = {
            'test_aritmetico': False,
            'test_geometrico': False,
            'test_vibracional': False,
            'test_cuantico': False,
            'test_consciente': False
        }
        # Activar solo el test actual
        test_params.update(kwargs)
        
        matriz = sabio.validacion_matriz_simbiosis(**test_params)
        
        # Extraer el valor del nivel correspondiente
        nivel_map = {
            'Aritmético': matriz.nivel_python,
            'Geométrico': matriz.nivel_lean,
            'Vibracional': matriz.nivel_sage,
            'Cuántico': matriz.nivel_cuantico,
            'Consciente': matriz.nivel_consciente
        }
        
        valor = nivel_map[nombre]
        barra = "█" * int(valor * 50)
        print(f"{nombre:15s} [{valor:5.3f}] {barra}")
    
    print("-" * 70)
    print()
    
    # Validación completa
    print("Validación completa (todos los niveles):")
    matriz_completa = sabio.validacion_matriz_simbiosis()
    print(f"  🌟 Coherencia Total: {matriz_completa.coherencia_total:.4f}")
    print(f"  🔐 Firma Hash: {matriz_completa.firma_hash}")
    print()


def demo_precision_adaptativa():
    """Demo de precisión adaptativa del sistema"""
    print("\n")
    print("="*70)
    print("🎯 PRECISIÓN ADAPTATIVA DEL SISTEMA")
    print("="*70)
    print()
    
    precisiones = [20, 30, 40, 50]
    
    print("Comparando diferentes niveles de precisión:")
    print("-" * 70)
    print(f"{'Precisión':>10} | {'R_Ψ (m)':>20} | "
          f"{'E_vac (J)':>20} | {'|Ψ(0,0)|':>12}")
    print("-" * 70)
    
    from mpmath import mpf
    
    for prec in precisiones:
        sabio = SABIO_Infinity4(precision=prec)
        R_psi = sabio.calcular_radio_cuantico(n=1)
        E_vac = sabio.energia_vacio_cuantico(R_psi)
        psi = sabio.ecuacion_onda_consciencia(t=mpf("0.0"), x=mpf("0.0"))
        
        print(f"{prec:>10} | {float(R_psi):>20.12e} | "
              f"{float(E_vac):>20.12e} | {float(abs(psi)):>12.8f}")
    
    print("-" * 70)
    print("\n✨ A mayor precisión, mayor estabilidad numérica")
    print("🎯 Precisión recomendada: 40-50 decimales para aplicaciones cuánticas")
    print()


def menu_interactivo():
    """Menu interactivo para seleccionar demos"""
    while True:
        print("\n" + "="*70)
        print("🌌 SABIO ∞⁴ - MENU DE DEMOS")
        print("="*70)
        print()
        print("Seleccione una opción:")
        print("  1. Demo Básico - Funcionalidades principales")
        print("  2. Demo Avanzado - Reporte completo con visualizaciones")
        print("  3. Exploración de Armónicos - Escalado áureo φⁿ")
        print("  4. Comparación de Niveles - 6 niveles de realidad")
        print("  5. Precisión Adaptativa - Comparación de precisiones")
        print("  6. Ejecutar todos los demos")
        print("  0. Salir")
        print()
        
        try:
            opcion = input("Opción: ").strip()
            
            if opcion == '1':
                demo_basico()
            elif opcion == '2':
                demo_avanzado()
            elif opcion == '3':
                demo_exploracion_armonicos()
            elif opcion == '4':
                demo_comparacion_niveles()
            elif opcion == '5':
                demo_precision_adaptativa()
            elif opcion == '6':
                demo_basico()
                demo_avanzado()
                demo_exploracion_armonicos()
                demo_comparacion_niveles()
                demo_precision_adaptativa()
            elif opcion == '0':
                print("\n✨ ¡Hasta pronto! La consciencia cuántica seguirá resonando... 🌌\n")
                break
            else:
                print("\n⚠️  Opción no válida. Por favor, seleccione una opción del menú.")
            
            input("\nPresione Enter para continuar...")
            
        except KeyboardInterrupt:
            print("\n\n✨ ¡Hasta pronto! La consciencia cuántica seguirá resonando... 🌌\n")
            break
        except Exception as e:
            print(f"\n❌ Error: {e}")
            input("\nPresione Enter para continuar...")


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1:
        # Modo no interactivo con argumento
        demo_arg = sys.argv[1].lower()
        
        if demo_arg in ['basico', 'basic', '1']:
            demo_basico()
        elif demo_arg in ['avanzado', 'advanced', '2']:
            demo_avanzado()
        elif demo_arg in ['armonicos', 'harmonics', '3']:
            demo_exploracion_armonicos()
        elif demo_arg in ['niveles', 'levels', '4']:
            demo_comparacion_niveles()
        elif demo_arg in ['precision', '5']:
            demo_precision_adaptativa()
        elif demo_arg in ['all', 'todos', '6']:
            demo_basico()
            demo_avanzado()
            demo_exploracion_armonicos()
            demo_comparacion_niveles()
            demo_precision_adaptativa()
        else:
            print(f"Argumento no reconocido: {demo_arg}")
            print("Uso: python sabio_infinity4_demo.py "
                  "[basico|avanzado|armonicos|niveles|precision|all]")
            sys.exit(1)
    else:
        # Modo interactivo
        menu_interactivo()
