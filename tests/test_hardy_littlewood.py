#!/usr/bin/env python3
"""
Tests for Hardy-Littlewood singular series (Equation 4)
Tests the corrected Hardy-Littlewood formula with p=2 omitted.
"""

import sys
import os
import unittest
import pytest

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))


@pytest.mark.sage_required
class TestHardyLittlewoodSeries(unittest.TestCase):
    """Test Hardy-Littlewood singular series S(n) computation"""
    
    @classmethod
    def setUpClass(cls):
        """Set up test fixtures"""
        try:
            from src.local_factors import (
                hardy_littlewood_singular_series,
                hardy_littlewood_constant
            )
            cls.S = hardy_littlewood_singular_series
            cls.C2 = hardy_littlewood_constant
        except ImportError as e:
            if 'sage' in str(e).lower():
                pytest.skip("SageMath not available", allow_module_level=True)
            raise
    
    def test_import(self):
        """Test that Hardy-Littlewood functions can be imported"""
        from src.local_factors import (
            hardy_littlewood_singular_series,
            hardy_littlewood_constant
        )
        self.assertIsNotNone(hardy_littlewood_singular_series)
        self.assertIsNotNone(hardy_littlewood_constant)
        print("✅ Hardy-Littlewood functions import: OK")
    
    def test_s_of_1(self):
        """
        Test S(1) = Hardy-Littlewood constant C₂
        
        S(1) should equal the infinite product prod_{p>2} (1 - 1/(p-1)²)
        Known value: approximately 0.6601618158...
        """
        S_1 = self.S(1, max_prime=1000)
        
        # Check it's positive
        self.assertGreater(S_1, 0)
        
        # Check it's less than 1 (each factor is < 1)
        self.assertLess(S_1, 1)
        
        # Check it's close to known value (with some tolerance due to truncation)
        # Actual value is approximately 0.6601618158
        self.assertGreater(S_1, 0.65)
        self.assertLess(S_1, 0.67)
        
        print(f"✅ S(1) = {S_1:.10f} (expected ≈ 0.6601618158)")
    
    def test_hardy_littlewood_constant(self):
        """Test Hardy-Littlewood constant C₂ computation"""
        C2 = self.C2(max_prime=1000)
        
        # Should equal S(1)
        S_1 = self.S(1, max_prime=1000)
        self.assertAlmostEqual(C2, S_1, places=8)
        
        print(f"✅ C₂ (Hardy-Littlewood constant) = {C2:.10f}")
    
    def test_s_increases_with_prime_divisors(self):
        """
        Test that S(n) increases when n has prime divisors > 2
        
        For each prime p > 2 dividing n, we multiply by (p-1)/(p-2) > 1
        So S(n) > S(1) when n has prime divisors > 2
        """
        S_1 = self.S(1, max_prime=500)
        S_3 = self.S(3, max_prime=500)  # 3 | 3, adds factor 2/1 = 2
        S_5 = self.S(5, max_prime=500)  # 5 | 5, adds factor 4/3 ≈ 1.333
        S_15 = self.S(15, max_prime=500)  # 15 = 3·5, adds factors for 3 and 5
        
        # S(3) should be larger than S(1)
        self.assertGreater(S_3, S_1)
        
        # S(5) should be larger than S(1)
        self.assertGreater(S_5, S_1)
        
        # S(15) should be larger than S(3) and S(5)
        self.assertGreater(S_15, S_3)
        self.assertGreater(S_15, S_5)
        
        print(f"✅ S(1)  = {S_1:.6f}")
        print(f"✅ S(3)  = {S_3:.6f} (> S(1))")
        print(f"✅ S(5)  = {S_5:.6f} (> S(1))")
        print(f"✅ S(15) = {S_15:.6f} (> S(3), S(5))")
    
    def test_p_equals_2_omitted(self):
        """
        Test that p=2 factor is correctly omitted
        
        S(2) should equal S(1) since the local factor at p=2 is omitted
        S(6) should equal S(3) since 6 = 2·3 but we ignore p=2
        """
        S_1 = self.S(1, max_prime=500)
        S_2 = self.S(2, max_prime=500)
        
        S_3 = self.S(3, max_prime=500)
        S_6 = self.S(6, max_prime=500)  # 6 = 2·3
        
        # S(2) should equal S(1) (no factor for p=2)
        self.assertAlmostEqual(S_2, S_1, places=10)
        
        # S(6) should equal S(3) (both have only p=3 factor, ignore p=2)
        self.assertAlmostEqual(S_6, S_3, places=10)
        
        print(f"✅ S(2) = S(1) = {S_2:.10f} (p=2 omitted)")
        print(f"✅ S(6) = S(3) = {S_6:.10f} (p=2 omitted)")
    
    def test_correction_factor_formula(self):
        """
        Test the correction factor (p-1)/(p-2) for individual primes
        
        For n = p (prime > 2), we have:
        S(p) = S(1) * (p-1)/(p-2)
        """
        S_1 = self.S(1, max_prime=500)
        
        # Test for p = 3: factor = 2/1 = 2
        S_3 = self.S(3, max_prime=500)
        expected_3 = S_1 * 2.0
        self.assertAlmostEqual(S_3, expected_3, places=8)
        
        # Test for p = 5: factor = 4/3
        S_5 = self.S(5, max_prime=500)
        expected_5 = S_1 * (4.0 / 3.0)
        self.assertAlmostEqual(S_5, expected_5, places=8)
        
        # Test for p = 7: factor = 6/5
        S_7 = self.S(7, max_prime=500)
        expected_7 = S_1 * (6.0 / 5.0)
        self.assertAlmostEqual(S_7, expected_7, places=8)
        
        print(f"✅ S(3) = S(1) * 2/1 = {S_3:.6f}")
        print(f"✅ S(5) = S(1) * 4/3 = {S_5:.6f}")
        print(f"✅ S(7) = S(1) * 6/5 = {S_7:.6f}")
    
    def test_multiple_prime_factors(self):
        """
        Test S(n) for n with multiple prime factors > 2
        
        For n = p·q with p,q > 2 distinct primes:
        S(p·q) = S(1) * (p-1)/(p-2) * (q-1)/(q-2)
        """
        S_1 = self.S(1, max_prime=500)
        
        # n = 15 = 3 * 5
        S_15 = self.S(15, max_prime=500)
        expected_15 = S_1 * (2.0 / 1.0) * (4.0 / 3.0)
        self.assertAlmostEqual(S_15, expected_15, places=8)
        
        # n = 21 = 3 * 7
        S_21 = self.S(21, max_prime=500)
        expected_21 = S_1 * (2.0 / 1.0) * (6.0 / 5.0)
        self.assertAlmostEqual(S_21, expected_21, places=8)
        
        print(f"✅ S(15) = S(1) * (2/1) * (4/3) = {S_15:.6f}")
        print(f"✅ S(21) = S(1) * (2/1) * (6/5) = {S_21:.6f}")
    
    def test_convergence_with_max_prime(self):
        """
        Test that S(1) converges as max_prime increases
        
        The infinite product converges, so increasing max_prime should
        give increasingly accurate approximations.
        """
        S_100 = self.S(1, max_prime=100)
        S_500 = self.S(1, max_prime=500)
        S_1000 = self.S(1, max_prime=1000)
        
        # Values should be close for large max_prime
        self.assertAlmostEqual(S_500, S_1000, places=4)
        
        # S_100 might differ more
        self.assertGreater(abs(S_100 - S_1000), abs(S_500 - S_1000))
        
        print(f"✅ S(1) with max_prime=100:  {S_100:.10f}")
        print(f"✅ S(1) with max_prime=500:  {S_500:.10f}")
        print(f"✅ S(1) with max_prime=1000: {S_1000:.10f}")
    
    def test_invalid_input(self):
        """Test error handling for invalid inputs"""
        with self.assertRaises(ValueError):
            self.S(0)  # n must be positive
        
        with self.assertRaises(ValueError):
            self.S(-5)  # n must be positive
        
        print("✅ Invalid input handling: OK")
    
    def test_precision_parameter(self):
        """Test that precision parameter affects computation accuracy"""
        S_low = self.S(1, max_prime=500, precision=20)
        S_high = self.S(1, max_prime=500, precision=100)
        
        # Both should be close but high precision should allow more accuracy
        self.assertAlmostEqual(S_low, S_high, places=6)
        
        print(f"✅ Precision=20:  {S_low:.15f}")
        print(f"✅ Precision=100: {S_high:.15f}")


@pytest.mark.basic
class TestHardyLittlewoodDocumentation(unittest.TestCase):
    """Test that Hardy-Littlewood functions are documented"""
    
    def test_function_docstrings(self):
        """Test that functions have proper docstrings"""
        try:
            from src.local_factors import (
                hardy_littlewood_singular_series,
                hardy_littlewood_constant
            )
            
            self.assertIsNotNone(hardy_littlewood_singular_series.__doc__)
            self.assertIsNotNone(hardy_littlewood_constant.__doc__)
            
            # Check docstrings contain key information
            doc = hardy_littlewood_singular_series.__doc__
            self.assertIn("Hardy-Littlewood", doc)
            self.assertIn("equation", doc.lower() or "Equation" in doc)
            self.assertIn("p=2", doc or "p>2" in doc)
            self.assertIn("omit", doc.lower())
            
            print("✅ Function documentation: OK")
        except ImportError as e:
            if 'sage' in str(e).lower():
                self.skipTest("SageMath not available")
            raise


if __name__ == '__main__':
    unittest.main()
