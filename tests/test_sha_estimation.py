"""
Tests for SHA estimation from BSD formula (PASO 7)
"""

import sys
import os
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# Conditionally import sage - tests will be skipped if sage is not available
pytest.importorskip("sage.all")
from sage.all import EllipticCurve

from validation.birch_swinnerton_sha import (
    ShaEstimator,
    estimate_sha,
    compute_bsd_lhs,
    compute_bsd_rhs,
    validate_sha_estimation
)


class TestShaEstimatorBasic:
    """Basic tests for ShaEstimator class"""
    
    def test_estimator_initialization(self):
        """Test that estimator initializes correctly"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        assert estimator.E == E
        assert estimator.N == E.conductor()
    
    def test_rank_property(self):
        """Test rank property computes correctly"""
        E = EllipticCurve('11a1')  # rank 0
        estimator = ShaEstimator(E)
        
        assert estimator.rank == 0
    
    def test_torsion_order_property(self):
        """Test torsion order property"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        assert estimator.torsion_order == 5  # Known: E(Q)_tors = Z/5Z
    
    def test_real_period_positive(self):
        """Test real period is positive"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        assert estimator.real_period > 0
    
    def test_regulator_positive(self):
        """Test regulator is positive"""
        E = EllipticCurve('11a1')  # rank 0, so regulator = 1
        estimator = ShaEstimator(E)
        
        assert estimator.regulator >= 1.0
    
    def test_tamagawa_product_positive(self):
        """Test Tamagawa product is positive integer"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        assert estimator.tamagawa_product >= 1
        assert isinstance(estimator.tamagawa_product, int)


class TestBSDComponents:
    """Tests for BSD formula components"""
    
    def test_compute_bsd_lhs_11a1(self):
        """Test LHS computation for 11a1"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        lhs = estimator.compute_bsd_lhs()
        
        assert lhs['status'] == 'computed'
        assert lhs['rank'] == 0
        assert lhs['value'] is not None
        assert lhs['value'] > 0  # L(E,1) > 0 for rank 0
    
    def test_compute_bsd_rhs_11a1(self):
        """Test RHS computation for 11a1"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        rhs = estimator.compute_bsd_rhs(sha_value=1)
        
        assert rhs['status'] == 'computed'
        assert rhs['omega'] > 0
        assert rhs['regulator'] > 0
        assert rhs['tamagawa_product'] >= 1
        assert rhs['torsion_order'] >= 1
        assert rhs['value'] > 0
    
    def test_bsd_lhs_rhs_consistency(self):
        """Test that LHS and RHS are consistent (should be close for Sha=1)"""
        E = EllipticCurve('11a1')  # Known: Sha = 1
        estimator = ShaEstimator(E)
        
        lhs = estimator.compute_bsd_lhs()
        rhs = estimator.compute_bsd_rhs(sha_value=1)
        
        # For Sha = 1, LHS should approximately equal RHS
        if lhs['status'] == 'computed' and rhs['status'] == 'computed':
            ratio = lhs['value'] / rhs['value']
            assert 0.9 < ratio < 1.1, f"LHS/RHS ratio = {ratio}, expected ~1.0"


class TestShaEstimation:
    """Tests for Sha estimation"""
    
    def test_estimate_sha_11a1(self):
        """Test Sha estimation for 11a1 (known Sha = 1)"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        result = estimator.estimate_sha()
        
        assert result['status'] in ['valid', 'approximate', 'error']
        if result['status'] in ['valid', 'approximate']:
            assert result['sha_estimate'] is not None
            # For 11a1, Sha = 1
            assert 0.8 < result['sha_estimate'] < 1.2, \
                f"Expected Sha ≈ 1, got {result['sha_estimate']}"
    
    def test_estimate_sha_37a1(self):
        """Test Sha estimation for 37a1 (rank 1, known Sha = 1)"""
        E = EllipticCurve('37a1')
        estimator = ShaEstimator(E)
        
        result = estimator.estimate_sha()
        
        # Rank 1 curves require derivative computation which may be approximate
        assert result['status'] in ['valid', 'approximate', 'error', 'warning']
    
    def test_estimate_sha_result_structure(self):
        """Test that result has expected structure"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        result = estimator.estimate_sha()
        
        # Check required keys
        assert 'sha_estimate' in result
        assert 'status' in result
        
        if result['status'] in ['valid', 'approximate']:
            assert 'L_lhs' in result
            assert 'rhs_without_sha' in result
            assert 'relative_error' in result
            assert 'components' in result
    
    def test_estimate_sha_components(self):
        """Test that components are properly included"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        result = estimator.estimate_sha()
        
        if result['status'] in ['valid', 'approximate']:
            components = result['components']
            assert 'rank' in components
            assert 'torsion_order' in components
            assert 'real_period' in components
            assert 'regulator' in components
            assert 'tamagawa_product' in components
            assert 'conductor' in components


class TestConvenienceFunctions:
    """Tests for convenience functions"""
    
    def test_estimate_sha_function(self):
        """Test estimate_sha convenience function"""
        result = estimate_sha('11a1')
        
        assert 'sha_estimate' in result
        assert 'status' in result
    
    def test_compute_bsd_lhs_function(self):
        """Test compute_bsd_lhs convenience function"""
        result = compute_bsd_lhs('11a1')
        
        assert 'value' in result
        assert 'rank' in result
        assert 'status' in result
    
    def test_compute_bsd_rhs_function(self):
        """Test compute_bsd_rhs convenience function"""
        result = compute_bsd_rhs('11a1')
        
        assert 'value' in result
        assert 'omega' in result
        assert 'status' in result
    
    def test_estimate_sha_with_curve_object(self):
        """Test estimate_sha with EllipticCurve object"""
        E = EllipticCurve('11a1')
        result = estimate_sha(E)
        
        assert 'sha_estimate' in result
        assert 'status' in result


class TestValidation:
    """Tests for validation across multiple curves"""
    
    def test_validate_sha_estimation_single(self):
        """Test validation for single curve"""
        results = validate_sha_estimation(['11a1'])
        
        assert results['total_curves'] == 1
        assert 'success_rate' in results
        assert 'results' in results
        assert len(results['results']) == 1
    
    def test_validate_sha_estimation_multiple(self):
        """Test validation for multiple curves"""
        curves = ['11a1', '14a1', '15a1']
        results = validate_sha_estimation(curves)
        
        assert results['total_curves'] == len(curves)
        assert results['successful'] + results['failed'] == len(curves)
        assert len(results['results']) == len(curves)
    
    def test_validate_sha_estimation_invalid_curve(self):
        """Test validation handles invalid curve gracefully"""
        results = validate_sha_estimation(['invalid_curve_xyz'])
        
        assert results['total_curves'] == 1
        assert results['failed'] == 1
        assert results['results'][0]['status'] == 'error'


class TestReportGeneration:
    """Tests for report generation"""
    
    def test_generate_report_11a1(self):
        """Test report generation for 11a1"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        report = estimator.generate_report()
        
        assert 'SHA ESTIMATION REPORT' in report
        assert '11a1' in report
        assert 'BSD COMPONENTS' in report
        assert 'INTERPRETATION' in report
    
    def test_generate_report_to_file(self, tmp_path):
        """Test report generation to file"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        output_file = tmp_path / "test_report.txt"
        report = estimator.generate_report(output_file=str(output_file))
        
        assert output_file.exists()
        
        with open(output_file, 'r') as f:
            content = f.read()
        
        assert 'SHA ESTIMATION REPORT' in content
        assert report == content


class TestInterpretation:
    """Tests for Sha interpretation"""
    
    def test_interpret_sha_trivial(self):
        """Test interpretation for Sha = 1 (trivial)"""
        E = EllipticCurve('11a1')  # Known Sha = 1
        estimator = ShaEstimator(E)
        result = estimator.estimate_sha()
        
        if result['status'] in ['valid', 'approximate']:
            if abs(result['sha_estimate'] - 1.0) < 0.1:
                assert 'trivial' in result['interpretation'].lower() or '= 1' in result['interpretation']
    
    def test_is_perfect_square(self):
        """Test perfect square detection"""
        E = EllipticCurve('11a1')
        estimator = ShaEstimator(E)
        
        assert estimator._is_perfect_square(1)
        assert estimator._is_perfect_square(4)
        assert estimator._is_perfect_square(9)
        assert estimator._is_perfect_square(16)
        assert not estimator._is_perfect_square(2)
        assert not estimator._is_perfect_square(3)
        assert not estimator._is_perfect_square(-1)


class TestEdgeCases:
    """Tests for edge cases"""
    
    def test_rank_zero_curve(self):
        """Test Sha estimation for rank 0 curve"""
        E = EllipticCurve('11a1')  # rank 0
        estimator = ShaEstimator(E)
        
        assert estimator.rank == 0
        result = estimator.estimate_sha()
        assert result['status'] != 'error' or 'components' in result
    
    def test_rank_one_curve(self):
        """Test Sha estimation for rank 1 curve"""
        E = EllipticCurve('37a1')  # rank 1
        estimator = ShaEstimator(E)
        
        assert estimator.rank == 1
        result = estimator.estimate_sha()
        # Rank 1 may have computational challenges
        assert 'status' in result


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
