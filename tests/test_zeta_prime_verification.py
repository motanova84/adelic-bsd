"""
Tests for the zeta prime verification script.

This module tests the verification script that computes |ζ'(1/2)|
with high precision and verifies bounds used in Lean formalization.
"""

import sys
import os
import unittest
from unittest.mock import patch
import warnings

# Add scripts directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'scripts'))

try:
    from verify_zeta_prime import (
        compute_zeta_prime_half,
        verify_bounds,
        compare_with_known_sources
    )
    SCRIPT_AVAILABLE = True
except ImportError:
    SCRIPT_AVAILABLE = False


@unittest.skipUnless(SCRIPT_AVAILABLE, "verify_zeta_prime script not available")
class TestZetaPrimeVerification(unittest.TestCase):
    """Test suite for zeta prime verification."""
    
    def test_compute_zeta_prime_half_basic(self):
        """Test basic computation of ζ'(1/2)."""
        value_str, abs_value_str = compute_zeta_prime_half(precision=20)
        
        # Check that we got strings
        self.assertIsInstance(value_str, str)
        self.assertIsInstance(abs_value_str, str)
        
        # Check that value is negative
        self.assertTrue(value_str.startswith('-'))
        
        # Check that absolute value is positive
        self.assertFalse(abs_value_str.startswith('-'))
        
        # Check approximate value (first few digits)
        self.assertTrue(abs_value_str.startswith('3.922'))
    
    def test_compute_zeta_prime_half_precision(self):
        """Test that precision parameter affects output length."""
        value_10, abs_value_10 = compute_zeta_prime_half(precision=10)
        value_50, abs_value_50 = compute_zeta_prime_half(precision=50)
        
        # Higher precision should give more digits
        # (accounting for decimal point and possible sign)
        self.assertLessEqual(len(value_10), len(value_50))
    
    def test_verify_bounds_correct(self):
        """Test bound verification with correct bounds."""
        # Known value: |ζ'(1/2)| ≈ 3.9226...
        known_value = "3.92264396712893547"
        
        # These bounds should work
        self.assertTrue(verify_bounds(known_value, 3.92, 3.93))
        self.assertTrue(verify_bounds(known_value, 3.9, 4.0))
        self.assertTrue(verify_bounds(known_value, 0.0, 10.0))
    
    def test_verify_bounds_incorrect(self):
        """Test bound verification with incorrect bounds."""
        # Known value: |ζ'(1/2)| ≈ 3.9226...
        known_value = "3.92264396712893547"
        
        # These bounds should NOT work (from problem statement)
        self.assertFalse(verify_bounds(known_value, 1.45, 1.47))
        
        # Too narrow bounds
        self.assertFalse(verify_bounds(known_value, 3.93, 4.0))
        self.assertFalse(verify_bounds(known_value, 0.0, 3.0))
    
    def test_compare_with_known_sources(self):
        """Test comparison with known sources."""
        sources = compare_with_known_sources()
        
        # Check that we have multiple sources
        self.assertGreater(len(sources), 0)
        
        # Check that OEIS is in sources
        self.assertIn("OEIS_A059750", sources)
        
        # Check that values start with expected digits
        for source_name, value in sources.items():
            self.assertTrue(value.startswith('3.922'), 
                          f"Source {source_name} has unexpected value: {value}")
    
    def test_known_value_matches_python_module(self):
        """Test that verification script matches src/vacuum_energy.py."""
        try:
            from src.vacuum_energy import zeta_prime_half
            
            # Get value from module
            python_value = abs(zeta_prime_half())
            
            # Get value from verification script
            _, abs_value_str = compute_zeta_prime_half(precision=20)
            script_value = float(abs_value_str)
            
            # They should match to reasonable precision
            self.assertAlmostEqual(python_value, script_value, places=10)
            
        except ImportError:
            self.skipTest("vacuum_energy module not available")
    
    def test_value_in_correct_range(self):
        """Test that computed value is in expected range."""
        _, abs_value_str = compute_zeta_prime_half(precision=30)
        value = float(abs_value_str)
        
        # The value should be approximately 3.9226
        self.assertGreater(value, 3.9)
        self.assertLess(value, 4.0)
        
        # More precisely
        self.assertGreater(value, 3.92)
        self.assertLess(value, 3.93)
    
    def test_consistency_across_precisions(self):
        """Test that different precisions give consistent results."""
        _, abs_20 = compute_zeta_prime_half(precision=20)
        _, abs_50 = compute_zeta_prime_half(precision=50)
        
        # First 15 digits should match
        self.assertEqual(abs_20[:15], abs_50[:15])


class TestZetaPrimeIntegration(unittest.TestCase):
    """Integration tests for zeta prime verification."""
    
    @unittest.skipUnless(SCRIPT_AVAILABLE, "Script not available")
    def test_script_runs_without_errors(self):
        """Test that the script can be imported and run."""
        # If we got here, the import worked
        self.assertTrue(SCRIPT_AVAILABLE)
        
        # Try running a basic computation
        try:
            value, abs_value = compute_zeta_prime_half(precision=10)
            self.assertIsNotNone(value)
            self.assertIsNotNone(abs_value)
        except Exception as e:
            self.fail(f"Script raised unexpected exception: {e}")
    
    @unittest.skipUnless(SCRIPT_AVAILABLE, "Script not available")
    def test_bounds_from_lean_formalization(self):
        """Test the bounds used in Lean formalization."""
        _, abs_value = compute_zeta_prime_half(precision=30)
        
        # The Lean formalization uses [3.92, 3.93]
        self.assertTrue(verify_bounds(abs_value, 3.92, 3.93),
                       "Bounds from Lean formalization should be valid")
        
        # The problem statement incorrectly suggests [1.45, 1.47]
        self.assertFalse(verify_bounds(abs_value, 1.45, 1.47),
                        "Incorrect bounds from problem statement should fail")


if __name__ == '__main__':
    unittest.main()
