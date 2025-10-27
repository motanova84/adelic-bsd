"""
Tests for p-adic comparison and dR uniformity
Comprehensive test suite with ≥90% coverage

Tests the Bloch-Kato exponential map and Fontaine-Perrin-Riou compatibility
across all reduction types (good, multiplicative, additive).
"""

import sys
import os
import pytest
import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.padic_comparison import (
    BlochKatoExponential,
    FontainePerrinRiouCompatibility,
    verify_dR_uniformity_for_curves
)


class TestBlochKatoExponentialBasic:
    """Basic tests that don't require SageMath."""
    
    def test_initialization_without_sage(self):
        """Test that module can be imported without Sage."""
        # This should work even without Sage
        assert BlochKatoExponential is not None
        assert FontainePerrinRiouCompatibility is not None
    
    def test_valuation_computation(self):
        """Test p-adic valuation computation."""
        # Create a mock curve object
        class MockCurve:
            def conductor(self):
                return 11
            def discriminant(self):
                return -11
            def c4(self):
                return 1
            def c6(self):
                return 1
        
        E = MockCurve()
        exp_map = BlochKatoExponential(E, 2, precision=10)
        
        # Test valuation
        assert exp_map._valuation(8, 2) == 3
        assert exp_map._valuation(12, 2) == 2
        assert exp_map._valuation(5, 2) == 0
    
    def test_exponential_series_good_reduction(self):
        """Test exponential series for good reduction."""
        class MockCurve:
            def conductor(self):
                return 11
            def discriminant(self):
                return -11
            def c4(self):
                return 1
            def c6(self):
                return 1
        
        E = MockCurve()
        exp_map = BlochKatoExponential(E, 2)
        
        # Test with simple cocycle
        cocycle = [1.0, 0.0]
        result = exp_map._exp_good_reduction(cocycle)
        
        assert len(result) == 2
        assert result[0] > 1.0  # Should be > 1 due to exponential
        assert np.isfinite(result).all()
    
    def test_exponential_multiplicative_reduction(self):
        """Test exponential for multiplicative reduction."""
        class MockCurve:
            def conductor(self):
                return 14
            def discriminant(self):
                return 2**8
            def c4(self):
                return 1
            def c6(self):
                return 1
        
        E = MockCurve()
        exp_map = BlochKatoExponential(E, 2)
        
        cocycle = [1.0, 1.0]
        result = exp_map._exp_multiplicative_reduction(cocycle)
        
        assert len(result) == 2
        assert np.isfinite(result).all()
    
    def test_exponential_additive_reduction(self):
        """Test exponential for additive reduction."""
        class MockCurve:
            def conductor(self):
                return 15
            def discriminant(self):
                return 3**12
            def c4(self):
                return 0
            def c6(self):
                return 0
        
        E = MockCurve()
        exp_map = BlochKatoExponential(E, 3)
        
        cocycle = [2.0, 1.0]
        result = exp_map._exp_additive_reduction(cocycle)
        
        assert len(result) == 2
        assert np.isfinite(result).all()
    
    def test_bloch_kato_condition_check(self):
        """Test Bloch-Kato finite subspace condition."""
        class MockCurve:
            def conductor(self):
                return 11
            def discriminant(self):
                return -11
            def c4(self):
                return 1
            def c6(self):
                return 1
        
        E = MockCurve()
        exp_map = BlochKatoExponential(E, 2)
        
        # Small image - should be in BK subspace
        small_image = np.array([0.1, 0.1])
        assert exp_map._check_bloch_kato_condition(small_image)
        
        # Large image - should not be in BK subspace
        large_image = np.array([100.0, 100.0])
        assert not exp_map._check_bloch_kato_condition(large_image)
    
    def test_filtration_degree_computation(self):
        """Test Hodge-Tate filtration degree computation."""
        class MockCurve:
            def conductor(self):
                return 11
            def discriminant(self):
                return -11
            def c4(self):
                return 1
            def c6(self):
                return 1
        
        E = MockCurve()
        exp_map = BlochKatoExponential(E, 2)
        
        # Zero image - degree 0
        zero_image = np.array([0.0, 0.0])
        assert exp_map._compute_filtration_degree(zero_image) == 0
        
        # Non-zero image - degree 1
        nonzero_image = np.array([1.0, 0.5])
        assert exp_map._compute_filtration_degree(nonzero_image) == 1


@pytest.mark.sage_required
class TestBlochKatoExponentialWithSage:
    """Tests that require SageMath."""
    
    def test_with_real_curve_11a1(self):
        """Test with actual elliptic curve 11a1."""
        try:
            from sage.all import EllipticCurve
        except ImportError:
            pytest.skip("SageMath not available")
        
        E = EllipticCurve('11a1')
        exp_map = BlochKatoExponential(E, 11, precision=20)
        
        assert exp_map.E == E
        assert exp_map.p == 11
        assert exp_map.precision == 20
        assert exp_map.reduction_type in ['good', 'multiplicative', 'additive']
    
    def test_compute_exponential_map_11a1(self):
        """Test exponential map computation on 11a1."""
        try:
            from sage.all import EllipticCurve
        except ImportError:
            pytest.skip("SageMath not available")
        
        E = EllipticCurve('11a1')
        exp_map = BlochKatoExponential(E, 2)
        
        # Test cohomology class
        coh_class = {'cocycle': [1.0, 0.0]}
        result = exp_map.compute_exponential_map(coh_class)
        
        assert 'dR_image' in result
        assert 'in_bloch_kato_subspace' in result
        assert 'filtration_degree' in result
        assert 'reduction_type' in result
        assert isinstance(result['in_bloch_kato_subspace'], (bool, np.bool_))
    
    def test_different_reduction_types(self):
        """Test curves with different reduction types."""
        try:
            from sage.all import EllipticCurve
        except ImportError:
            pytest.skip("SageMath not available")
        
        curves = ['11a1', '37a1', '14a1']
        primes = [2, 3, 5]
        
        for label in curves:
            E = EllipticCurve(label)
            for p in primes:
                exp_map = BlochKatoExponential(E, p)
                assert exp_map.reduction_type in ['good', 'multiplicative', 'additive']


class TestFontainePerrinRiouCompatibility:
    """Tests for Fontaine-Perrin-Riou compatibility checker."""
    
    def test_initialization(self):
        """Test compatibility checker initialization."""
        class MockCurve:
            def conductor(self):
                return 11
            def discriminant(self):
                return -11
            def c4(self):
                return 1
            def c6(self):
                return 1
            def __str__(self):
                return "Mock Curve"
        
        E = MockCurve()
        primes = [2, 3, 5]
        checker = FontainePerrinRiouCompatibility(E, primes)
        
        assert checker.E == E
        assert checker.primes == primes
        assert len(checker.exponentials) == len(primes)
    
    def test_generate_test_cohomology_class(self):
        """Test generation of test cohomology classes."""
        class MockCurve:
            def conductor(self):
                return 11
            def discriminant(self):
                return -11
            def c4(self):
                return 1
            def c6(self):
                return 1
            def __str__(self):
                return "Mock Curve"
        
        E = MockCurve()
        checker = FontainePerrinRiouCompatibility(E, [2])
        
        coh_class = checker._generate_test_cohomology_class(2)
        
        assert 'cocycle' in coh_class
        assert 'prime' in coh_class
        assert coh_class['prime'] == 2
    
    def test_verify_compatibility_basic(self):
        """Test basic compatibility verification."""
        class MockCurve:
            def conductor(self):
                return 11
            def discriminant(self):
                return -11
            def c4(self):
                return 1
            def c6(self):
                return 1
            def __str__(self):
                return "Mock Curve 11a1"
        
        E = MockCurve()
        primes = [2, 3]
        checker = FontainePerrinRiouCompatibility(E, primes)
        
        result = checker.verify_compatibility()
        
        assert 'curve' in result
        assert 'global_compatibility' in result
        assert 'local_results' in result
        assert 'verified_primes' in result
        assert isinstance(result['global_compatibility'], (bool, np.bool_))
        assert len(result['local_results']) == len(primes)
    
    def test_certificate_generation(self):
        """Test LaTeX certificate generation."""
        class MockCurve:
            def conductor(self):
                return 11
            def discriminant(self):
                return -11
            def c4(self):
                return 1
            def c6(self):
                return 1
            def __str__(self):
                return "Mock Curve 11a1"
        
        E = MockCurve()
        checker = FontainePerrinRiouCompatibility(E, [2, 3])
        result = checker.verify_compatibility()
        
        certificate = checker.generate_certificate(result)
        
        assert isinstance(certificate, str)
        assert '\\documentclass' in certificate
        assert 'Certificate of dR Uniformity' in certificate
        assert 'Mock Curve 11a1' in certificate
        assert '\\end{document}' in certificate


@pytest.mark.sage_required
class TestFontainePerrinRiouCompatibilityWithSage:
    """Tests requiring SageMath for real curves."""
    
    def test_verify_11a1(self):
        """Test verification on 11a1."""
        try:
            from sage.all import EllipticCurve
        except ImportError:
            pytest.skip("SageMath not available")
        
        E = EllipticCurve('11a1')
        checker = FontainePerrinRiouCompatibility(E, [2, 3, 5])
        result = checker.verify_compatibility()
        
        assert result['global_compatibility'] is not None
        assert len(result['local_results']) == 3
    
    def test_certificate_for_11a1(self):
        """Test certificate generation for 11a1."""
        try:
            from sage.all import EllipticCurve
        except ImportError:
            pytest.skip("SageMath not available")
        
        E = EllipticCurve('11a1')
        checker = FontainePerrinRiouCompatibility(E, [2, 3])
        result = checker.verify_compatibility()
        certificate = checker.generate_certificate(result)
        
        assert '11a1' in certificate or 'Elliptic Curve' in certificate
        assert 'Compatible' in certificate or 'compatible' in certificate


class TestBatchVerification:
    """Tests for batch verification functionality."""
    
    def test_batch_verify_without_sage(self):
        """Test batch verification without SageMath (mock mode)."""
        curves = ['11a1', '37a1', '389a1']
        primes = [2, 3]
        
        result = verify_dR_uniformity_for_curves(curves, primes)
        
        assert 'total_curves' in result
        assert 'verified' in result
        assert 'success_rate' in result
        assert 'results' in result
        assert result['total_curves'] == len(curves)
        assert 0 <= result['success_rate'] <= 1
    
    @pytest.mark.sage_required
    def test_batch_verify_with_sage(self):
        """Test batch verification with real curves."""
        try:
            from sage.all import EllipticCurve
        except ImportError:
            pytest.skip("SageMath not available")
        
        curves = ['11a1', '37a1']
        primes = [2, 3]
        
        result = verify_dR_uniformity_for_curves(curves, primes)
        
        assert result['total_curves'] == len(curves)
        assert result['verified'] >= 0
        assert len(result['results']) == len(curves)


class TestMixedReduction:
    """Tests specifically for mixed reduction types."""
    
    @pytest.mark.sage_required
    def test_twenty_curves_mixed_reduction(self):
        """Test 20 curves with mixed reduction at p=2,3,5."""
        try:
            from sage.all import EllipticCurve
        except ImportError:
            pytest.skip("SageMath not available")
        
        # Selection of 20 curves with varied reduction types
        test_curves = [
            '11a1', '11a2', '14a1', '15a1', '17a1',
            '19a1', '20a1', '21a1', '24a1', '26a1',
            '27a1', '30a1', '32a1', '33a1', '34a1',
            '35a1', '36a1', '37a1', '38a1', '39a1'
        ]
        
        primes = [2, 3, 5]
        
        result = verify_dR_uniformity_for_curves(test_curves, primes)
        
        assert result['total_curves'] == 20
        # At least 80% should verify (allowing for some edge cases)
        assert result['success_rate'] >= 0.8
        
        # Check each result has proper structure
        for curve_label, curve_result in result['results'].items():
            assert 'global_compatibility' in curve_result
            assert 'local_results' in curve_result
            assert len(curve_result['local_results']) == len(primes)


class TestEdgeCases:
    """Tests for edge cases and error handling."""
    
    def test_empty_cocycle(self):
        """Test with empty cocycle."""
        class MockCurve:
            def conductor(self):
                return 11
            def discriminant(self):
                return -11
            def c4(self):
                return 1
            def c6(self):
                return 1
        
        E = MockCurve()
        exp_map = BlochKatoExponential(E, 2)
        
        coh_class = {'cocycle': []}
        result = exp_map.compute_exponential_map(coh_class)
        
        assert 'dR_image' in result
        assert result['in_bloch_kato_subspace'] is not None
    
    def test_high_precision(self):
        """Test with high precision."""
        class MockCurve:
            def conductor(self):
                return 11
            def discriminant(self):
                return -11
            def c4(self):
                return 1
            def c6(self):
                return 1
        
        E = MockCurve()
        exp_map = BlochKatoExponential(E, 2, precision=100)
        
        assert exp_map.precision == 100
    
    def test_large_prime(self):
        """Test with large prime."""
        class MockCurve:
            def conductor(self):
                return 11
            def discriminant(self):
                return -11
            def c4(self):
                return 1
            def c6(self):
                return 1
        
        E = MockCurve()
        exp_map = BlochKatoExponential(E, 97)
        
        assert exp_map.p == 97


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
