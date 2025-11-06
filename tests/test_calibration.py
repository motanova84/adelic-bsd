#!/usr/bin/env python3
"""
Tests for the complete calibration and validation system
"""

import sys
import os
import unittest
import json
from pathlib import Path

# Configurar path
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
