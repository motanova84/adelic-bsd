#!/usr/bin/env python3
"""
Tests for SABIO ∞⁴ - Quantum-Conscious System

Comprehensive test suite for the Symbiotic Adelic-Based Infinite-Order Operator
"""

import sys
import os
import unittest
import json
from pathlib import Path

# Configurar path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.sabio_infinity4 import (
    SABIO_Infinity4,
    ResonanciaQuantica,
    MatrizSimbiosis
)

# Test constants
MIN_COHERENCE_THRESHOLD = 0.85  # Minimum expected total coherence


class TestSABIOInfinity4(unittest.TestCase):
    """Tests para el sistema SABIO ∞⁴"""
    
    def setUp(self):
        """Configurar sistema SABIO para tests"""
        # Usar menor precisión para tests más rápidos
        self.sabio = SABIO_Infinity4(precision=30)
    
    def test_initialization(self):
        """Test de inicialización correcta del sistema"""
        self.assertEqual(self.sabio.precision, 30)
        self.assertIsNotNone(self.sabio.f0)
        self.assertIsNotNone(self.sabio.omega0)
        self.assertIsNotNone(self.sabio.zeta_prime_half)
        self.assertIsNotNone(self.sabio.phi_golden)
    
    def test_constantes_fundamentales(self):
        """Test de valores de constantes fundamentales"""
        # Frecuencia base
        f0_float = float(self.sabio.f0)
        self.assertAlmostEqual(f0_float, 141.7001, places=4)
        
        # Zeta prima en 1/2
        zeta_float = float(self.sabio.zeta_prime_half)
        self.assertAlmostEqual(zeta_float, -3.9226461392, places=5)
        
        # Razón áurea
        phi_float = float(self.sabio.phi_golden)
        self.assertAlmostEqual(phi_float, 1.618033988, places=6)
        
        # Velocidad de la luz
        c_float = float(self.sabio.c)
        self.assertEqual(c_float, 299792458.0)
    
    def test_radio_cuantico(self):
        """Test del cálculo del radio cuántico R_Ψ"""
        R_psi = self.sabio.calcular_radio_cuantico(n=1)
        
        # R_Ψ debe ser positivo
        self.assertGreater(float(R_psi), 0)
        
        # R_Ψ debe ser del orden de la longitud de Planck
        l_planck = float(self.sabio.l_planck)
        self.assertGreater(float(R_psi), l_planck)
        self.assertLess(float(R_psi), l_planck * 100)
    
    def test_energia_vacio_cuantico(self):
        """Test de cálculo de energía de vacío cuántico"""
        R_psi = self.sabio.calcular_radio_cuantico(n=1)
        E_vac = self.sabio.energia_vacio_cuantico(R_psi)
        
        # E_vac debe ser positiva
        self.assertGreater(float(E_vac), 0)
        
        # E_vac debe ser finita
        from mpmath import mp
        self.assertTrue(mp.isfinite(E_vac))
    
    def test_ecuacion_onda_consciencia(self):
        """Test de ecuación de onda de consciencia"""
        from mpmath import mpf
        
        # Evaluar en t=0, x=0
        psi = self.sabio.ecuacion_onda_consciencia(t=mpf("0.0"), x=mpf("0.0"))
        
        # Ψ debe ser complejo
        self.assertIsNotNone(psi.real)
        self.assertIsNotNone(psi.imag)
        
        # |Ψ| debe estar cerca de 1 (normalización)
        magnitude = abs(psi)
        self.assertAlmostEqual(float(magnitude), 1.0, places=1)
    
    def test_calcular_coherencia(self):
        """Test de cálculo de coherencia universal"""
        # Coherencia máxima
        C_max = self.sabio.calcular_coherencia(I=1.0, A=1.0)
        self.assertAlmostEqual(C_max, 1.0, places=6)
        
        # Coherencia reducida
        C_mid = self.sabio.calcular_coherencia(I=0.5, A=0.5)
        self.assertAlmostEqual(C_mid, 0.125, places=6)
        
        # Coherencia mínima
        C_min = self.sabio.calcular_coherencia(I=0.0, A=0.0)
        self.assertAlmostEqual(C_min, 0.0, places=6)
    
    def test_firma_vibracional(self):
        """Test de generación de firma vibracional"""
        data1 = {"test": 1, "value": "abc"}
        data2 = {"test": 1, "value": "abc"}
        data3 = {"test": 2, "value": "xyz"}
        
        firma1 = self.sabio.firma_vibracional(data1)
        firma2 = self.sabio.firma_vibracional(data2)
        firma3 = self.sabio.firma_vibracional(data3)
        
        # Firmas idénticas para datos idénticos
        self.assertEqual(firma1, firma2)
        
        # Firmas diferentes para datos diferentes
        self.assertNotEqual(firma1, firma3)
        
        # Firma debe tener 16 caracteres
        self.assertEqual(len(firma1), 16)
    
    def test_resonancia_cuantica(self):
        """Test de generación de resonancia cuántica"""
        res = self.sabio.resonancia_cuantica(n_harmonico=1)
        
        # Verificar tipo
        self.assertIsInstance(res, ResonanciaQuantica)
        
        # Verificar frecuencia base
        self.assertAlmostEqual(res.frecuencia, float(self.sabio.f0), places=2)
        
        # Verificar amplitud compleja
        self.assertIsInstance(res.amplitud, complex)
        
        # Verificar coherencia en rango válido
        self.assertGreaterEqual(res.coherencia, 0.0)
        self.assertLessEqual(res.coherencia, 1.0)
        
        # Verificar entropía no negativa
        self.assertGreaterEqual(res.entropia, 0.0)
    
    def test_resonancia_armonicos(self):
        """Test de armónicos con escalado áureo"""
        res1 = self.sabio.resonancia_cuantica(n_harmonico=1)
        res2 = self.sabio.resonancia_cuantica(n_harmonico=2)
        
        # f_2 ≈ f_1 * φ (since f_n = f₀ · φ^(n-1))
        phi = float(self.sabio.phi_golden)
        expected_f2 = res1.frecuencia * phi
        self.assertAlmostEqual(res2.frecuencia, expected_f2, places=1)
    
    def test_validacion_matriz_simbiosis(self):
        """Test de validación simbiótica multi-nivel"""
        matriz = self.sabio.validacion_matriz_simbiosis()
        
        # Verificar tipo
        self.assertIsInstance(matriz, MatrizSimbiosis)
        
        # Verificar niveles en rango válido [0, 1]
        self.assertGreaterEqual(matriz.nivel_python, 0.0)
        self.assertLessEqual(matriz.nivel_python, 1.0)
        
        self.assertGreaterEqual(matriz.nivel_lean, 0.0)
        self.assertLessEqual(matriz.nivel_lean, 1.0)
        
        self.assertGreaterEqual(matriz.nivel_sage, 0.0)
        self.assertLessEqual(matriz.nivel_sage, 1.0)
        
        self.assertGreaterEqual(matriz.nivel_sabio, 0.0)
        self.assertLessEqual(matriz.nivel_sabio, 1.0)
        
        self.assertGreaterEqual(matriz.nivel_cuantico, 0.0)
        self.assertLessEqual(matriz.nivel_cuantico, 1.0)
        
        self.assertGreaterEqual(matriz.nivel_consciente, 0.0)
        self.assertLessEqual(matriz.nivel_consciente, 1.0)
        
        # Verificar coherencia total
        self.assertGreaterEqual(matriz.coherencia_total, 0.0)
        self.assertLessEqual(matriz.coherencia_total, 1.0)
        
        # Verificar firma hash
        self.assertEqual(len(matriz.firma_hash), 16)
    
    def test_nivel_aritmetico(self):
        """Test específico del nivel aritmético"""
        matriz = self.sabio.validacion_matriz_simbiosis(
            test_aritmetico=True,
            test_geometrico=False,
            test_vibracional=False,
            test_cuantico=False,
            test_consciente=False
        )
        
        # Nivel aritmético debe ser alto (cerca de 1.0)
        self.assertGreater(matriz.nivel_python, 0.99)
    
    def test_nivel_vibracional(self):
        """Test específico del nivel vibracional"""
        matriz = self.sabio.validacion_matriz_simbiosis(
            test_aritmetico=False,
            test_geometrico=False,
            test_vibracional=True,
            test_cuantico=False,
            test_consciente=False
        )
        
        # Nivel vibracional debe ser alto (cerca de 1.0)
        self.assertGreater(matriz.nivel_sage, 0.99)
    
    def test_nivel_cuantico(self):
        """Test específico del nivel cuántico"""
        matriz = self.sabio.validacion_matriz_simbiosis(
            test_aritmetico=False,
            test_geometrico=False,
            test_vibracional=False,
            test_cuantico=True,
            test_consciente=False
        )
        
        # Nivel cuántico debe ser positivo
        self.assertGreater(matriz.nivel_cuantico, 0.0)
    
    def test_nivel_consciente(self):
        """Test específico del nivel consciente"""
        matriz = self.sabio.validacion_matriz_simbiosis(
            test_aritmetico=False,
            test_geometrico=False,
            test_vibracional=False,
            test_cuantico=False,
            test_consciente=True
        )
        
        # Nivel consciente debe ser positivo
        self.assertGreater(matriz.nivel_consciente, 0.0)
    
    def test_generar_espectro_resonante(self):
        """Test de generación de espectro resonante completo"""
        n_harmonicos = 5
        espectro = self.sabio.generar_espectro_resonante(n_harmonicos=n_harmonicos)
        
        # Verificar número de armónicos
        self.assertEqual(len(espectro), n_harmonicos)
        
        # Verificar que las frecuencias son crecientes
        for i in range(len(espectro) - 1):
            self.assertLess(espectro[i].frecuencia, espectro[i+1].frecuencia)
        
        # Verificar que las coherencias decaen
        for i in range(len(espectro) - 1):
            self.assertGreaterEqual(espectro[i].coherencia, espectro[i+1].coherencia)
    
    def test_reporte_sabio_infinity4(self):
        """Test de generación de reporte completo"""
        reporte = self.sabio.reporte_sabio_infinity4()
        
        # Verificar estructura del reporte
        self.assertIn('sistema', reporte)
        self.assertIn('version', reporte)
        self.assertIn('timestamp', reporte)
        self.assertIn('constantes_fundamentales', reporte)
        self.assertIn('matriz_simbiosis', reporte)
        self.assertIn('nivel_cuantico', reporte)
        self.assertIn('nivel_consciente', reporte)
        self.assertIn('espectro_resonante', reporte)
        self.assertIn('metricas_globales', reporte)
        self.assertIn('estado', reporte)
        self.assertIn('interpretacion', reporte)
        
        # Verificar valores
        self.assertEqual(reporte['sistema'], 'SABIO ∞⁴')
        self.assertEqual(reporte['version'], '4.0.0-quantum-conscious')
        
        # Verificar constantes fundamentales
        constantes = reporte['constantes_fundamentales']
        self.assertAlmostEqual(constantes['frecuencia_base_hz'], 141.7001, places=4)
        self.assertAlmostEqual(constantes['zeta_prime_half'], -3.9226461392, places=5)
        
        # Verificar matriz de simbiosis
        matriz = reporte['matriz_simbiosis']
        self.assertIn('coherencia_total', matriz)
        self.assertGreater(matriz['coherencia_total'], 0.0)
        
        # Verificar espectro resonante
        espectro = reporte['espectro_resonante']
        self.assertGreater(len(espectro), 0)
        self.assertEqual(espectro[0]['n'], 1)
        
        # Verificar métricas globales
        metricas = reporte['metricas_globales']
        self.assertIn('coherencia_total', metricas)
        self.assertIn('num_armonicos', metricas)
    
    def test_exportar_reporte_json(self):
        """Test de exportación de reporte en formato JSON"""
        reporte = self.sabio.reporte_sabio_infinity4()
        
        # Exportar en JSON
        filename = self.sabio.exportar_reporte(reporte, formato='json')
        
        # Verificar que el archivo fue creado
        self.assertTrue(Path(filename).exists())
        
        # Verificar que el contenido es JSON válido
        with open(filename, 'r') as f:
            data = json.load(f)
            self.assertEqual(data['sistema'], 'SABIO ∞⁴')
        
        # Limpiar archivo de test
        Path(filename).unlink()
    
    def test_exportar_reporte_txt(self):
        """Test de exportación de reporte en formato TXT"""
        reporte = self.sabio.reporte_sabio_infinity4()
        
        # Exportar en TXT
        filename = self.sabio.exportar_reporte(reporte, formato='txt')
        
        # Verificar que el archivo fue creado
        self.assertTrue(Path(filename).exists())
        
        # Verificar que el contenido tiene el formato esperado
        with open(filename, 'r') as f:
            content = f.read()
            self.assertIn('SABIO ∞⁴', content)
            self.assertIn('REPORTE CUÁNTICO-CONSCIENTE', content)
        
        # Limpiar archivo de test
        Path(filename).unlink()
    
    def test_visualizar_espectro(self):
        """Test de generación de visualización del espectro"""
        # Generar espectro primero
        self.sabio.generar_espectro_resonante(n_harmonicos=5)
        
        # Generar visualización
        vis_file = "test_spectrum_visualization.png"
        self.sabio.visualizar_espectro(save_path=vis_file)
        
        # Verificar que el archivo fue creado
        self.assertTrue(Path(vis_file).exists())
        
        # Limpiar archivo de test
        Path(vis_file).unlink()
    
    def test_estado_operacional(self):
        """Test de verificación del estado operacional del sistema"""
        reporte = self.sabio.reporte_sabio_infinity4()
        estado = reporte['estado']
        
        # El sistema debe estar operacional o sintonizando
        self.assertIn(estado, ["OPERACIONAL ✅", "SINTONIZANDO 🔄"])
    
    def test_coherencia_total_alta(self):
        """Test de verificación de coherencia total alta"""
        reporte = self.sabio.reporte_sabio_infinity4()
        coherencia_total = reporte['metricas_globales']['coherencia_total']
        
        # La coherencia total debe ser razonablemente alta
        self.assertGreater(coherencia_total, MIN_COHERENCE_THRESHOLD)


class TestSABIOIntegration(unittest.TestCase):
    """Tests de integración del sistema SABIO ∞⁴"""
    
    def test_flujo_completo(self):
        """Test del flujo completo de operación del sistema"""
        # 1. Inicializar
        sabio = SABIO_Infinity4(precision=30)
        
        # 2. Validar matriz de simbiosis
        matriz = sabio.validacion_matriz_simbiosis()
        self.assertIsNotNone(matriz)
        
        # 3. Generar espectro resonante
        espectro = sabio.generar_espectro_resonante(n_harmonicos=5)
        self.assertEqual(len(espectro), 5)
        
        # 4. Generar reporte
        reporte = sabio.reporte_sabio_infinity4()
        self.assertIsNotNone(reporte)
        
        print("✅ Flujo completo de integración: OK")
    
    def test_precision_escalable(self):
        """Test de escalabilidad de precisión"""
        # Test con diferentes precisiones
        precisiones = [20, 30, 40]
        
        for prec in precisiones:
            sabio = SABIO_Infinity4(precision=prec)
            self.assertEqual(sabio.precision, prec)
            
            # Verificar que funciona correctamente
            R_psi = sabio.calcular_radio_cuantico(n=1)
            self.assertGreater(float(R_psi), 0)
        
        print(f"✅ Precisión escalable: Testeado con {len(precisiones)} precisiones")
    
    def test_consistencia_multiples_ejecuciones(self):
        """Test de consistencia entre múltiples ejecuciones"""
        sabio = SABIO_Infinity4(precision=30)
        
        # Ejecutar dos veces y comparar
        res1 = sabio.resonancia_cuantica(n_harmonico=1)
        res2 = sabio.resonancia_cuantica(n_harmonico=1)
        
        # Las frecuencias deben ser idénticas
        self.assertEqual(res1.frecuencia, res2.frecuencia)
        
        print("✅ Consistencia: Múltiples ejecuciones producen resultados consistentes")


if __name__ == '__main__':
    # Ejecutar tests con verbosidad
    unittest.main(verbosity=2)
