"""
Tests for the BSD LHS validation module (birch_swinnerton_lhs.py)

This module tests the PASO 6 implementation:
- L-function derivative computation at s=1
- Division by r!
- Comparison with RHS of BSD formula
"""

import pytest
import sys
import os

# Add paths for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# Check for SageMath availability
sage = pytest.importorskip("sage.all")
from sage.all import EllipticCurve

from validation.birch_swinnerton_lhs import (
    BirchSwinnertonLHS,
    compute_bsd_rhs,
    compute_bsd_lhs_vs_rhs,
    determine_validation_level,
    validate_bsd_comparison,
    BSD_THRESHOLDS,
    NUMERICAL_ZERO_THRESHOLD
)


class TestBirchSwinnertonLHS:
    """Tests for BirchSwinnertonLHS class."""

    def test_init_rank_0(self):
        """Test initialization with rank 0 curve."""
        E = EllipticCurve('11a1')
        lhs = BirchSwinnertonLHS(E)

        assert lhs.E == E
        assert lhs._rank is None  # Not computed yet
        assert lhs._L_derivative is None
        assert lhs._L_lhs is None

    def test_rank_property(self):
        """Test rank property returns correct value."""
        E = EllipticCurve('11a1')
        lhs = BirchSwinnertonLHS(E)

        # 11a1 has rank 0
        assert lhs.rank == 0
        assert lhs._rank == 0  # Should be cached

    def test_rank_property_rank_1(self):
        """Test rank property for rank 1 curve."""
        E = EllipticCurve('37a1')
        lhs = BirchSwinnertonLHS(E)

        # 37a1 has rank 1
        assert lhs.rank == 1

    def test_label_property(self):
        """Test label property."""
        E = EllipticCurve('11a1')
        lhs = BirchSwinnertonLHS(E)

        assert lhs.label == '11a1'

    def test_compute_L_derivative_rank_0(self):
        """Test L-function value for rank 0."""
        E = EllipticCurve('11a1')
        lhs = BirchSwinnertonLHS(E)

        L_deriv = lhs.compute_L_derivative()

        # For rank 0, L(E,1) should be non-zero
        assert L_deriv != 0
        assert L_deriv > 0  # L(E,1) should be positive for this curve

    def test_compute_L_derivative_rank_1(self):
        """Test L'(E,1) for rank 1."""
        E = EllipticCurve('37a1')
        lhs = BirchSwinnertonLHS(E)

        L_deriv = lhs.compute_L_derivative()

        # For rank 1, L'(E,1) should be non-zero
        assert L_deriv is not None

    def test_compute_lhs_rank_0(self):
        """Test LHS = L(E,1)/0! = L(E,1) for rank 0."""
        E = EllipticCurve('11a1')
        lhs = BirchSwinnertonLHS(E)

        L_lhs = lhs.compute_lhs()

        # For rank 0, LHS = L(E,1)/1 = L(E,1)
        assert L_lhs == lhs._L_derivative

    def test_compute_lhs_rank_1(self):
        """Test LHS = L'(E,1)/1! = L'(E,1) for rank 1."""
        E = EllipticCurve('37a1')
        lhs = BirchSwinnertonLHS(E)

        L_lhs = lhs.compute_lhs()

        # For rank 1, LHS = L'(E,1)/1 = L'(E,1)
        assert L_lhs == lhs._L_derivative

    def test_get_summary(self):
        """Test get_summary returns all required fields."""
        E = EllipticCurve('11a1')
        lhs = BirchSwinnertonLHS(E)

        summary = lhs.get_summary()

        assert 'curve' in summary
        assert 'conductor' in summary
        assert 'rank' in summary
        assert 'L_derivative' in summary
        assert 'factorial_r' in summary
        assert 'L_lhs' in summary
        assert 'timestamp' in summary

        assert summary['curve'] == '11a1'
        assert summary['conductor'] == 11
        assert summary['rank'] == 0
        assert summary['factorial_r'] == 1


class TestComputeBSDRHS:
    """Tests for compute_bsd_rhs function."""

    def test_rhs_components_rank_0(self):
        """Test RHS components for rank 0 curve."""
        E = EllipticCurve('11a1')
        rhs_data = compute_bsd_rhs(E)

        assert 'omega' in rhs_data
        assert 'regulator' in rhs_data
        assert 'tamagawa_product' in rhs_data
        assert 'sha_order' in rhs_data
        assert 'torsion_order' in rhs_data
        assert 'rhs' in rhs_data

        # For rank 0, regulator should be 1
        assert rhs_data['regulator'] == 1.0

        # Omega should be positive
        assert rhs_data['omega'] > 0

        # RHS should be positive
        assert rhs_data['rhs'] > 0

    def test_rhs_components_rank_1(self):
        """Test RHS components for rank 1 curve."""
        E = EllipticCurve('37a1')
        rhs_data = compute_bsd_rhs(E)

        # For rank 1, regulator should be computed
        assert 'regulator' in rhs_data
        assert rhs_data['regulator'] > 0

    def test_torsion_order(self):
        """Test torsion order computation."""
        E = EllipticCurve('11a1')
        rhs_data = compute_bsd_rhs(E)

        # 11a1 has torsion order 5
        assert rhs_data['torsion_order'] == 5


class TestDetermineValidationLevel:
    """Tests for validation level determination."""

    def test_almost_perfect(self):
        """Test almost perfect validation."""
        error = 1e-4
        level = determine_validation_level(error)
        assert level == 'almost_perfect'

    def test_good(self):
        """Test good validation."""
        error = 5e-3
        level = determine_validation_level(error)
        assert level == 'good'

    def test_partial(self):
        """Test partial validation."""
        error = 5e-2
        level = determine_validation_level(error)
        assert level == 'partial'

    def test_needs_review(self):
        """Test needs review level."""
        error = 0.5
        level = determine_validation_level(error)
        assert level == 'needs_review'

    def test_boundary_almost_perfect(self):
        """Test boundary at almost_perfect threshold."""
        assert determine_validation_level(0.0009) == 'almost_perfect'
        assert determine_validation_level(0.001) == 'good'

    def test_boundary_good(self):
        """Test boundary at good threshold."""
        assert determine_validation_level(0.009) == 'good'
        assert determine_validation_level(0.01) == 'partial'

    def test_boundary_partial(self):
        """Test boundary at partial threshold."""
        assert determine_validation_level(0.09) == 'partial'
        assert determine_validation_level(0.1) == 'needs_review'


class TestComputeBSDLhsVsRhs:
    """Tests for compute_bsd_lhs_vs_rhs function."""

    def test_comparison_structure(self):
        """Test that comparison returns all required fields."""
        E = EllipticCurve('11a1')
        result = compute_bsd_lhs_vs_rhs(E)

        assert 'curve' in result
        assert 'rank' in result
        assert 'lhs' in result
        assert 'rhs' in result
        assert 'comparison' in result
        assert 'timestamp' in result

        # Check LHS structure
        assert 'L_derivative' in result['lhs']
        assert 'factorial' in result['lhs']
        assert 'value' in result['lhs']

        # Check RHS structure
        assert 'omega' in result['rhs']
        assert 'regulator' in result['rhs']
        assert 'value' in result['rhs']

        # Check comparison structure
        assert 'relative_error' in result['comparison']
        assert 'validation_level' in result['comparison']
        assert 'bsd_compatible' in result['comparison']

    def test_relative_error_computation(self):
        """Test that relative error is computed correctly."""
        E = EllipticCurve('11a1')
        result = compute_bsd_lhs_vs_rhs(E)

        lhs = result['lhs']['value']
        rhs = result['rhs']['value']
        error = result['comparison']['relative_error']

        # Verify relative error formula
        if abs(lhs) > 1e-15:
            expected_error = abs(lhs - rhs) / abs(lhs)
        else:
            expected_error = abs(lhs - rhs) / abs(rhs)

        assert abs(error - expected_error) < 1e-10


class TestValidateBSDComparison:
    """Tests for validate_bsd_comparison function."""

    def test_validation_with_verbose(self, capsys):
        """Test verbose output of validation."""
        E = EllipticCurve('11a1')
        result = validate_bsd_comparison(E, verbose=True)

        captured = capsys.readouterr()

        # Check that output contains expected sections
        assert 'BSD VALIDATION' in captured.out
        assert 'LEFT SIDE' in captured.out
        assert 'RIGHT SIDE' in captured.out
        assert 'COMPARISON' in captured.out

    def test_validation_without_verbose(self, capsys):
        """Test silent mode of validation."""
        E = EllipticCurve('11a1')
        result = validate_bsd_comparison(E, verbose=False)

        captured = capsys.readouterr()

        # Should have no output in silent mode
        assert captured.out == ''

    def test_validation_returns_result(self):
        """Test that validation returns complete result."""
        E = EllipticCurve('11a1')
        result = validate_bsd_comparison(E, verbose=False)

        assert result is not None
        assert 'curve' in result
        assert 'comparison' in result


class TestBSDThresholds:
    """Tests for BSD threshold constants."""

    def test_thresholds_exist(self):
        """Test that all thresholds are defined."""
        assert 'almost_perfect' in BSD_THRESHOLDS
        assert 'good' in BSD_THRESHOLDS
        assert 'partial' in BSD_THRESHOLDS
        assert 'needs_review' in BSD_THRESHOLDS

    def test_thresholds_order(self):
        """Test that thresholds are in correct order."""
        assert BSD_THRESHOLDS['almost_perfect'] < BSD_THRESHOLDS['good']
        assert BSD_THRESHOLDS['good'] < BSD_THRESHOLDS['partial']
        assert BSD_THRESHOLDS['partial'] < BSD_THRESHOLDS['needs_review']

    def test_thresholds_values(self):
        """Test specific threshold values."""
        assert BSD_THRESHOLDS['almost_perfect'] == 1e-3
        assert BSD_THRESHOLDS['good'] == 1e-2
        assert BSD_THRESHOLDS['partial'] == 1e-1

    def test_numerical_zero_threshold(self):
        """Test that numerical zero threshold is defined."""
        assert NUMERICAL_ZERO_THRESHOLD == 1e-15
        assert NUMERICAL_ZERO_THRESHOLD > 0


def run_all_tests():
    """Run all tests for BSD LHS module."""
    print("\n" + "="*70)
    print("RUNNING BSD LHS VALIDATION TESTS")
    print("="*70 + "\n")

    # Run pytest programmatically
    pytest.main([__file__, '-v'])


if __name__ == "__main__":
    run_all_tests()
