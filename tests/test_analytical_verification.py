#!/usr/bin/env python3
"""
Tests for analytical verification module

Tests the analytical verification of the gap in det(I - M_E(s)) = c(s)/L(E,s)
"""

import sys
import os
import unittest
import numpy as np

# Configurar path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.verification.analytical_verification import (
    VerificadorAnalitico,
    FactorLocal,
    demo_verificacion_analitica
)


class TestFactorLocal(unittest.TestCase):
    """Tests for FactorLocal dataclass"""

    def test_factor_local_creation(self):
        """Test FactorLocal can be created"""
        factor = FactorLocal(
            p=2,
            a_p=1,
            s=2+0j,
            factor_euler=0.75+0j,
            factor_simple=0.5+0j,
            discrepancia=0.25+0j
        )

        self.assertEqual(factor.p, 2)
        self.assertEqual(factor.a_p, 1)
        self.assertEqual(factor.s, 2+0j)
        self.assertEqual(factor.factor_euler, 0.75+0j)
        self.assertEqual(factor.factor_simple, 0.5+0j)
        self.assertEqual(factor.discrepancia, 0.25+0j)


class TestVerificadorAnalitico(unittest.TestCase):
    """Tests for VerificadorAnalitico class"""

    def setUp(self):
        """Set up test fixtures"""
        self.verificador = VerificadorAnalitico(precision=50)
        self.E_params = {
            'A': 0,
            'B': 1,
            'conductor': 11
        }

    def test_initialization(self):
        """Test verificador initialization"""
        self.assertEqual(self.verificador.precision, 50)
        self.assertEqual(len(self.verificador.factores_locales), 0)

    def test_calcular_a_p_hasse_weil(self):
        """Test a_p calculation with Hasse-Weil bound"""
        # Test for small primes
        a_2 = self.verificador.calcular_a_p_hasse_weil(self.E_params, 2)
        self.assertIsInstance(a_2, int)
        self.assertLessEqual(abs(a_2), 2 * np.sqrt(2) + 1)  # Hasse-Weil bound

        a_3 = self.verificador.calcular_a_p_hasse_weil(self.E_params, 3)
        self.assertIsInstance(a_3, int)
        self.assertLessEqual(abs(a_3), 2 * np.sqrt(3) + 1)

        a_5 = self.verificador.calcular_a_p_hasse_weil(self.E_params, 5)
        self.assertIsInstance(a_5, int)
        self.assertLessEqual(abs(a_5), 2 * np.sqrt(5) + 1)

    def test_factor_euler_local(self):
        """Test Euler factor calculation"""
        a_p = 1
        p = 2
        s = 2 + 0j

        factor = self.verificador.factor_euler_local(a_p, p, s)
        self.assertIsInstance(factor, complex)

        # For s=2, p=2, a_p=1: factor = 1 - 1/4 + 1/16 = 0.8125
        expected = 1 - 1/4 + 1/16
        self.assertAlmostEqual(abs(factor - expected), 0, places=5)

    def test_factor_simple_local(self):
        """Test simple diagonal factor calculation"""
        a_p = 1
        p = 2
        s = 2 + 0j

        factor = self.verificador.factor_simple_local(a_p, p, s)
        self.assertIsInstance(factor, complex)

        # For s=2, p=2, a_p=1: factor = 1 - 1/4 = 0.75
        expected = 1 - 1/4
        self.assertAlmostEqual(abs(factor - expected), 0, places=5)

    def test_calcular_discrepancia_local(self):
        """Test local discrepancy calculation"""
        a_p = 1
        p = 2
        s = 2 + 0j

        factor_local = self.verificador.calcular_discrepancia_local(a_p, p, s)

        self.assertIsInstance(factor_local, FactorLocal)
        self.assertEqual(factor_local.p, p)
        self.assertEqual(factor_local.a_p, a_p)
        self.assertEqual(factor_local.s, s)

        # Discrepancy should be approximately p^{1-2s} = 2^{-3} = 1/16
        expected_disc = 1/16
        self.assertAlmostEqual(abs(factor_local.discrepancia - expected_disc), 0, places=5)

    def test_producto_euler_truncado(self):
        """Test truncated Euler product calculation"""
        s = 2 + 0j
        max_p = 20

        prod_euler, prod_simple, ratio = self.verificador.producto_euler_truncado(
            self.E_params, s, max_p
        )

        # Check types
        self.assertIsInstance(prod_euler, complex)
        self.assertIsInstance(prod_simple, complex)
        self.assertIsInstance(ratio, complex)

        # Products should be positive real for Re(s) > 1
        self.assertGreater(prod_euler.real, 0)
        self.assertGreater(prod_simple.real, 0)

        # Ratio should be close to 1 for large Re(s)
        self.assertGreater(ratio.real, 0.5)
        self.assertLess(ratio.real, 2.0)

        # Check that factores_locales was populated
        self.assertGreater(len(self.verificador.factores_locales), 0)

    def test_convergencia_termino_correccion(self):
        """Test convergence of correction term"""
        s = 2 + 0j
        max_p = 50

        conv = self.verificador.convergencia_termino_correccion(s, max_p)

        # Check structure
        self.assertIn('producto_correccion', conv)
        self.assertIn('num_terminos', conv)
        self.assertIn('terminos_muestra', conv)
        self.assertIn('convergencia', conv)

        # Check types
        self.assertIsInstance(conv['producto_correccion'], complex)
        self.assertIsInstance(conv['num_terminos'], int)
        self.assertIsInstance(conv['terminos_muestra'], list)
        self.assertIsInstance(conv['convergencia'], bool)

        # Should converge for Re(s) > 1
        self.assertTrue(conv['convergencia'])
        self.assertGreater(conv['num_terminos'], 0)

    def test_analizar_s_igual_1(self):
        """Test critical analysis at s=1"""
        analisis = self.verificador.analizar_s_igual_1(self.E_params)

        # Check structure
        required_keys = [
            's', 'producto_euler', 'producto_simple', 'ratio',
            'log_ratio', 'suma_discrepancias', 'convergencia_correccion',
            'conclusion'
        ]
        for key in required_keys:
            self.assertIn(key, analisis)

        # Check types
        self.assertEqual(analisis['s'], 1+0j)
        self.assertIsInstance(analisis['producto_euler'], complex)
        self.assertIsInstance(analisis['producto_simple'], complex)
        self.assertIsInstance(analisis['ratio'], complex)
        self.assertIsInstance(analisis['conclusion'], str)

        # Check that conclusion contains expected keywords
        conclusion_lower = analisis['conclusion'].lower()
        self.assertTrue(
            'discrepancia' in conclusion_lower or 'pequeña' in conclusion_lower or
            'moderada' in conclusion_lower or 'grande' in conclusion_lower
        )

    def test_reporte_analitico_completo(self):
        """Test complete analytical report generation"""
        import io
        import sys

        # Capture stdout
        captured_output = io.StringIO()
        sys.stdout = captured_output

        try:
            reporte = self.verificador.reporte_analitico_completo(self.E_params)
        finally:
            sys.stdout = sys.__stdout__

        # Check structure
        required_keys = ['s2', 's32', 's1', 'factores_locales']
        for key in required_keys:
            self.assertIn(key, reporte)

        # Check s2 analysis
        self.assertIn('s', reporte['s2'])
        self.assertIn('ratio', reporte['s2'])

        # Check s32 analysis
        self.assertIn('s', reporte['s32'])
        self.assertIn('ratio', reporte['s32'])

        # Check s1 analysis (most detailed)
        self.assertIsInstance(reporte['s1'], dict)
        self.assertIn('conclusion', reporte['s1'])

        # Check factores_locales
        self.assertIsInstance(reporte['factores_locales'], list)
        if len(reporte['factores_locales']) > 0:
            factor = reporte['factores_locales'][0]
            self.assertIn('p', factor)
            self.assertIn('a_p', factor)
            self.assertIn('discrepancia', factor)

        # Check that output was generated
        output = captured_output.getvalue()
        self.assertIn('VERIFICACIÓN ANALÍTICA', output)
        self.assertIn('CONCLUSIÓN ANALÍTICA', output)


class TestDemoVerificacion(unittest.TestCase):
    """Tests for demo function"""

    def test_demo_verificacion_analitica(self):
        """Test that demo function runs without errors"""
        import io
        import sys

        # Capture stdout
        captured_output = io.StringIO()
        sys.stdout = captured_output

        try:
            reporte = demo_verificacion_analitica()
        finally:
            sys.stdout = sys.__stdout__

        # Check that demo returned a report
        self.assertIsInstance(reporte, dict)
        self.assertIn('s1', reporte)
        self.assertIn('factores_locales', reporte)

        # Check that output was generated
        output = captured_output.getvalue()
        self.assertIn('DEMO', output)
        self.assertIn('VERIFICACIÓN ANALÍTICA', output)
        self.assertIn('completada', output.lower())


class TestEdgeCases(unittest.TestCase):
    """Tests for edge cases and error handling"""

    def setUp(self):
        """Set up test fixtures"""
        self.verificador = VerificadorAnalitico(precision=30)

    def test_large_s_convergence(self):
        """Test convergence for large Re(s)"""
        E_params = {'A': 0, 'B': 1, 'conductor': 11}
        s = 5 + 0j

        prod_euler, prod_simple, ratio = self.verificador.producto_euler_truncado(
            E_params, s, max_p=30
        )

        # For large Re(s), products should converge rapidly
        self.assertTrue(np.isfinite(prod_euler.real))
        self.assertTrue(np.isfinite(prod_simple.real))
        self.assertGreater(prod_euler.real, 0)

    def test_different_precisions(self):
        """Test with different precision settings"""
        for precision in [20, 30, 50]:
            v = VerificadorAnalitico(precision=precision)
            self.assertEqual(v.precision, precision)

            # Test basic calculation works
            a_p = v.calcular_a_p_hasse_weil({'A': 0, 'B': 1}, 2)
            self.assertIsInstance(a_p, int)


if __name__ == '__main__':
    unittest.main()
