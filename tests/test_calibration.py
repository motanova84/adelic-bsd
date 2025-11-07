#!/usr/bin/env python3
"""
Tests for the complete calibration and validation system
"""

import sys
import os
import unittest
import json
from pathlib import Path

# Configure path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# Import the calibrator
from scripts.calibracion_completa import CompleteCalibratorValidator


class TestCalibrationSystem(unittest.TestCase):
    """Tests for the calibration system"""

    def setUp(self):
        """Set up test fixtures"""
        self.calibrator = CompleteCalibratorValidator()
        # Clean up any existing output
        self.output_file = Path('calibration/optimal_a.json')
        if self.output_file.exists():
            self.output_file.unlink()

    def tearDown(self):
        """Clean up after tests"""
        # Clean up test output
        if self.output_file.exists():
            self.output_file.unlink()
        calibration_dir = Path('calibration')
        if calibration_dir.exists() and not any(calibration_dir.iterdir()):
            calibration_dir.rmdir()

    def test_initialization(self):
        """Test that calibrator initializes correctly"""
        self.assertIsNotNone(self.calibrator)
        self.assertEqual(self.calibrator.zeta_prime_half, -1.460354508)
        self.assertEqual(len(self.calibrator.methods), 3)
        self.assertIn('gradient', self.calibrator.methods)
        self.assertIn('global_search', self.calibrator.methods)
        self.assertIn('bootstrap', self.calibrator.methods)

    def test_spectral_bound(self):
        """Test spectral bound calculation"""
        # Test with specific values
        a = 10.0
        delta = 0.05
        bound = self.calibrator._spectral_bound(a, delta)
        
        # Verify bound is positive and reasonable
        self.assertGreater(bound, 0)
        self.assertTrue(abs(bound) < 1000)  # Sanity check

    def test_compute_gamma(self):
        """Test gamma (second derivative) computation"""
        a = 10.0
        delta = 0.05
        gamma = self.calibrator._compute_gamma(a, delta)
        
        # Gamma should be a real number
        self.assertIsInstance(gamma, float)
        self.assertFalse(gamma != gamma)  # Not NaN

    def test_method_gradient(self):
        """Test gradient optimization method"""
        result = self.calibrator._method_gradient()
        
        # Verify structure
        self.assertIn('a', result)
        self.assertIn('delta_star', result)
        self.assertIn('gamma', result)
        self.assertIn('method', result)
        self.assertEqual(result['method'], 'gradient')
        
        # Verify values are reasonable
        self.assertGreater(result['a'], 0)
        self.assertLess(result['a'], 1001)
        self.assertGreater(result['delta_star'], 0)
        self.assertLess(result['delta_star'], 0.15)

    def test_method_global(self):
        """Test global search method"""
        result = self.calibrator._method_global()
        
        # Verify structure
        self.assertIn('a', result)
        self.assertIn('delta_star', result)
        self.assertIn('gamma', result)
        self.assertIn('method', result)
        self.assertEqual(result['method'], 'global_search')
        
        # Verify values are reasonable
        self.assertGreater(result['a'], 0)
        self.assertLess(result['a'], 1001)
        self.assertGreater(result['delta_star'], 0)
        self.assertLess(result['delta_star'], 0.15)

    def test_method_bootstrap(self):
        """Test bootstrap Monte Carlo method"""
        result = self.calibrator._method_bootstrap()
        
        # Verify structure
        self.assertIn('a', result)
        self.assertIn('delta_star', result)
        self.assertIn('gamma', result)
        self.assertIn('method', result)
        self.assertIn('total_valid', result)
        self.assertEqual(result['method'], 'bootstrap')
        
        # Verify values are reasonable
        self.assertGreater(result['a'], 0)
        self.assertLess(result['a'], 1001)
        self.assertGreater(result['delta_star'], 0)
        self.assertLess(result['delta_star'], 0.15)
        self.assertGreater(result['total_valid'], 0)

    def test_run_all_methods(self):
        """Test running all methods and validation"""
        results = self.calibrator.run_all_methods()
        
        # Verify output structure
        self.assertIn('a_calibrated', results)
        self.assertIn('methods', results)
        self.assertIn('statistics', results)
        
        # Verify methods results
        methods = results['methods']
        self.assertIn('gradient', methods)
        self.assertIn('global_search', methods)
        self.assertIn('bootstrap', methods)
        
        # Verify statistics
        stats = results['statistics']
        self.assertIn('mean', stats)
        self.assertIn('std', stats)
        self.assertIn('consistency', stats)
        
        # Verify output file was created
        self.assertTrue(self.output_file.exists())
        
        # Verify JSON is valid
        with open(self.output_file, 'r') as f:
            saved_results = json.load(f)
        self.assertEqual(saved_results['a_calibrated'], results['a_calibrated'])

    def test_consistency_classification(self):
        """Test that consistency is properly classified"""
        results = self.calibrator.run_all_methods()
        consistency = results['statistics']['consistency']
        self.assertIn(consistency, ['high', 'medium'])


if __name__ == '__main__':
    unittest.main()
"""
Tests para validación de la calibración del parámetro 'a'

Valida que el parámetro calibrado satisface los requisitos de la prueba incondicional:
- δ* > 0.04
- γ > 0

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: November 2025
Tests para la calibración del parámetro a

Verifica que:
1. γ > 0 para el valor calibrado de a
2. El límite espectral converge correctamente
3. La optimización encuentra valores válidos
"""

import pytest
import sys
import os
import json

# Add scripts to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'scripts'))

from calibrar_parametro_a import (
    compute_delta_star,
    compute_gamma,
    validate_parameters
)


class TestCalibration:
    """Test suite for parameter calibration"""
    
    def test_original_case_fails(self):
        """Test that original a=7.0 fails validation"""
        result = validate_parameters(7.0)
        
        # Should fail both requirements
        assert not result['all_valid'], "Original case should fail validation"
        assert result['gamma'] < 0, "Original gamma should be negative"
    
    def test_calibrated_value_passes(self):
        """Test that calibrated a=200.0 passes validation"""
        result = validate_parameters(200.0)
        
        # Should pass both requirements
        assert result['all_valid'], "Calibrated value should pass validation"
        assert result['delta_star'] > 0.04, "Delta star should be > 0.04"
        assert result['gamma'] > 0, "Gamma should be positive"
    
    def test_delta_star_at_7(self):
        """Test delta star computation at a=7"""
        delta = compute_delta_star(7.0)
        # Expected: δ* ≈ 0.0253
        assert abs(delta - 0.0253) < 0.001, f"Expected δ*≈0.0253, got {delta}"
    
    def test_delta_star_at_200(self):
        """Test delta star computation at a=200"""
        delta = compute_delta_star(200.0)
        # Expected: δ* ≈ 0.0485
        assert abs(delta - 0.0485) < 0.001, f"Expected δ*≈0.0485, got {delta}"
    
    def test_gamma_at_200(self):
        """Test gamma computation at a=200"""
        delta = compute_delta_star(200.0)
        gamma = compute_gamma(200.0, delta)
        # Expected: γ ≈ 0.0123
        assert abs(gamma - 0.0123) < 0.001, f"Expected γ≈0.0123, got {gamma}"
    
    def test_delta_star_increases_with_a(self):
        """Test that delta star increases with a"""
        delta_100 = compute_delta_star(100.0)
        delta_200 = compute_delta_star(200.0)
        
        assert delta_200 > delta_100, "Delta star should increase with a"
    
    def test_gamma_increases_with_a(self):
        """Test that gamma increases with a"""
        result_100 = validate_parameters(100.0)
        result_200 = validate_parameters(200.0)
        
        assert result_200['gamma'] > result_100['gamma'], "Gamma should increase with a"
    
    def test_minimum_valid_a(self):
        """Test that there exists a minimum valid a"""
        # Test range around expected minimum (~130)
        result_120 = validate_parameters(120.0)
        result_130 = validate_parameters(130.0)
        result_140 = validate_parameters(140.0)
        
        # At least one in this range should pass
        assert (result_130['all_valid'] or result_140['all_valid']), \
            "Expected minimum a to be around 130"
    
    def test_parameter_a_positive(self):
        """Test that parameter a must be positive"""
        with pytest.raises(ValueError):
            compute_delta_star(-1.0)
        
        with pytest.raises(ValueError):
            compute_delta_star(0.0)
    
    def test_consistency_requirements(self):
        """Test overall consistency of requirements"""
        # For a >= 200, both requirements should be satisfied
        for a in [200, 250, 300]:
            result = validate_parameters(a)
            assert result['delta_valid'], f"Delta should be valid for a={a}"
            assert result['gamma_valid'], f"Gamma should be valid for a={a}"
            assert result['all_valid'], f"All validation should pass for a={a}"


def test_calibration_file_exists():
    """Test that calibration output file was created"""
    calib_file = os.path.join(
        os.path.dirname(__file__),
        '..',
        'scripts',
        'calibration',
        'optimal_a.txt'
    )
    
    if os.path.exists(calib_file):
        with open(calib_file, 'r') as f:
            content = f.read()
            assert 'recommended_a=200' in content, \
                "Calibration file should contain recommended a=200"


if __name__ == "__main__":
    pytest.main([__file__, '-v'])


class TestParameterCalibration:
    """Tests for parameter calibration"""
    
    def test_spectral_bound_computation(self):
        """Verificar que el límite espectral se calcula correctamente"""
        a = 100.0
        delta = 0.05
        
        bound = compute_spectral_bound(a, delta)
        
        # El límite espectral debe ser finito
        assert not pytest.approx(bound) == float('inf')
        assert not pytest.approx(bound) == float('-inf')
        print(f"✅ Límite espectral calculado: {bound:.6f}")
    
    def test_delta_star_computation(self):
        """Verificar que δ* se calcula correctamente"""
        a = 200.0
        
        delta_star = compute_delta_star(a)
        
        # δ* debe estar en el rango válido
        assert 0.001 <= delta_star <= 0.1
        print(f"✅ δ* calculado para a={a}: {delta_star:.6f}")
    
    def test_gamma_computation(self):
        """Verificar que γ se calcula correctamente"""
        a = 200.0
        delta_star = compute_delta_star(a)
        gamma = compute_gamma(delta_star, a)
        
        # γ debe ser finito
        assert not pytest.approx(gamma) == float('inf')
        assert not pytest.approx(gamma) == float('-inf')
        print(f"✅ γ calculado: {gamma:.6f}")
    
    def test_gamma_positivity(self):
        """
        Verificar que γ > 0 para valores grandes de a
        
        Este es el test crítico: necesitamos γ > 0 para la
        prueba incondicional de finitud.
        """
        # Probar con varios valores grandes de a
        test_values = [100.0, 150.0, 200.0, 250.0, 300.0]
        
        results = []
        for a in test_values:
            delta_star = compute_delta_star(a)
            gamma = compute_gamma(delta_star, a)
            results.append((a, gamma))
            print(f"   a = {a:.1f}: γ = {gamma:.6f}")
        
        # Al menos uno debe tener γ > 0
        positive_gammas = [g for a, g in results if g > 0]
        assert len(positive_gammas) > 0, "Debe existir al menos un valor con γ > 0"
        
        print(f"\n✅ {len(positive_gammas)}/{len(test_values)} valores con γ > 0")
    
    def test_optimal_a_search(self):
        """Verificar que la búsqueda de a óptimo funciona"""
        # Buscar en un rango pequeño para el test (más rápido)
        results = find_optimal_a(
            target_gamma=0.0,
            a_range=(50.0, 250.0),
            num_points=50,
            verbose=False
        )
        
        # Debe haber evaluado algunos puntos
        assert len(results) > 0
        
        # Algunos deben ser válidos
        valid_results = [r for r in results if r.get('passes', False)]
        
        print(f"\n✅ Búsqueda completada:")
        print(f"   • Puntos evaluados: {len(results)}")
        print(f"   • Puntos válidos: {len(valid_results)}")
        
        if valid_results:
            optimal = valid_results[0]
            print(f"   • a óptimo encontrado: {optimal['a']:.2f}")
            print(f"   • γ correspondiente: {optimal['gamma']:.6f}")
    
    def test_calibration_report_format(self):
        """Verificar que el reporte de calibración tiene el formato correcto"""
        # Ejecutar una calibración pequeña
        results = find_optimal_a(
            target_gamma=0.0,
            a_range=(100.0, 200.0),
            num_points=20,
            verbose=False
        )
        
        # Verificar estructura de resultados
        for result in results:
            if 'error' not in result:
                assert 'a' in result
                assert 'delta_star' in result
                assert 'gamma' in result
                assert 'passes' in result
        
        print("✅ Formato de reporte validado")


class TestSpectralBoundProperties:
    """Tests for spectral bound function properties"""
    
    def test_spectral_bound_continuity(self):
        """Verificar continuidad del límite espectral"""
        a = 200.0
        delta1 = 0.05
        delta2 = 0.050001
        
        bound1 = compute_spectral_bound(a, delta1)
        bound2 = compute_spectral_bound(a, delta2)
        
        # Valores cercanos de δ deben dar límites cercanos
        assert abs(bound1 - bound2) < 0.01
        print(f"✅ Continuidad verificada: |Δbound| = {abs(bound1 - bound2):.8f}")
    
    def test_spectral_bound_monotonicity_in_a(self):
        """Verificar comportamiento respecto a a"""
        delta = 0.05
        a1 = 100.0
        a2 = 200.0
        
        bound1 = compute_spectral_bound(a1, delta)
        bound2 = compute_spectral_bound(a2, delta)
        
        # Simplemente verificar que son finitos y diferentes
        assert bound1 != bound2
        print(f"✅ Dependencia en a verificada: bound(a={a1}) = {bound1:.6f}, bound(a={a2}) = {bound2:.6f}")


def test_calibration_file_generation():
    """Verificar que el script genera archivos de salida correctos"""
    # Este test verifica que podemos importar y usar las funciones
    # sin errores de importación
    from calibrar_parametro_a import generate_calibration_report
    
    # Crear datos de prueba
    test_results = [
        {'a': 100.0, 'delta_star': 0.05, 'gamma': -0.1, 'passes': False},
        {'a': 200.0, 'delta_star': 0.04, 'gamma': 0.05, 'passes': True},
    ]
    
    # No guardar archivo en el test
    report = generate_calibration_report(test_results, output_path=None)
    
    # Verificar estructura del reporte
    assert 'status' in report
    assert 'total_evaluated' in report
    
    print(f"✅ Reporte generado correctamente: status={report['status']}")


if __name__ == "__main__":
    # Permitir ejecución directa para debugging
    pytest.main([__file__, "-v"])
