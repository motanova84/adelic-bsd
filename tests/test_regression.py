"""
Tests for Regression Testing Framework

Validates the regression testing module against known results.
"""

import pytest
import sys
import os

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from src.regression_tests import (
    RegressionTestSuite,
    validate_against_literature
)


@pytest.mark.basic
def test_regression_suite_initialization():
    """Test that regression suite initializes correctly."""
    suite = RegressionTestSuite()
    
    assert suite.reference_data is not None
    assert 'classical_curves' in suite.reference_data
    assert 'published_results' in suite.reference_data
    assert len(suite.test_results) == 0


@pytest.mark.basic
def test_reference_data_structure():
    """Test that reference data has correct structure."""
    suite = RegressionTestSuite()
    
    # Check known curves are present
    classical_curves = suite.reference_data['classical_curves']
    assert '11a1' in classical_curves
    assert '37a1' in classical_curves
    assert '389a1' in classical_curves
    
    # Check curve data structure
    curve_11a1 = classical_curves['11a1']
    assert 'N' in curve_11a1
    assert 'rank' in curve_11a1
    assert 'sha' in curve_11a1
    
    # Verify known values
    assert curve_11a1['N'] == 11
    assert curve_11a1['sha'] == 1


@pytest.mark.basic
def test_spectral_bound_consistency():
    """Test spectral bound consistency check."""
    suite = RegressionTestSuite()
    
    # Test with valid bound
    result = suite.test_spectral_bound_consistency('11a1', spectral_bound=1)
    assert result['status'] == 'passed'
    assert result['consistent'] is True
    
    # Test with higher bound (should still pass)
    result = suite.test_spectral_bound_consistency('11a1', spectral_bound=11)
    assert result['status'] == 'passed'
    assert result['consistent'] is True
    
    # Test with insufficient bound
    result = suite.test_spectral_bound_consistency('11a1', spectral_bound=0)
    assert result['status'] == 'failed'
    assert result['consistent'] is False


@pytest.mark.basic
def test_conductor_computation():
    """Test conductor computation verification."""
    suite = RegressionTestSuite()
    
    # Test correct conductor
    result = suite.test_conductor_computation('11a1', computed_conductor=11)
    assert result['status'] == 'passed'
    assert result['matches'] is True
    
    # Test incorrect conductor
    result = suite.test_conductor_computation('11a1', computed_conductor=13)
    assert result['status'] == 'failed'
    assert result['matches'] is False


@pytest.mark.basic
def test_rank_prediction():
    """Test rank prediction verification."""
    suite = RegressionTestSuite()
    
    # Test rank 0 curve
    result = suite.test_rank_prediction('11a1', predicted_rank=0)
    assert result['status'] == 'passed'
    assert result['matches'] is True
    
    # Test rank 1 curve
    result = suite.test_rank_prediction('37a1', predicted_rank=1)
    assert result['status'] == 'passed'
    assert result['matches'] is True
    
    # Test rank 2 curve
    result = suite.test_rank_prediction('389a1', predicted_rank=2)
    assert result['status'] == 'passed'
    assert result['matches'] is True
    
    # Test incorrect rank
    result = suite.test_rank_prediction('11a1', predicted_rank=1)
    assert result['status'] == 'failed'
    assert result['matches'] is False


@pytest.mark.basic
def test_unknown_curve_handling():
    """Test handling of curves not in reference data."""
    suite = RegressionTestSuite()
    
    result = suite.test_spectral_bound_consistency('999999a1', spectral_bound=1)
    assert result['status'] == 'skipped'
    assert 'reason' in result


@pytest.mark.basic
def test_regression_report_generation():
    """Test generation of regression report."""
    suite = RegressionTestSuite()
    
    # Add some test results
    suite.test_spectral_bound_consistency('11a1', 1)
    suite.test_conductor_computation('11a1', 11)
    suite.test_rank_prediction('11a1', 0)
    
    # Generate report
    report = suite.generate_regression_report()
    
    assert isinstance(report, str)
    assert 'REGRESSION TEST REPORT' in report
    assert 'REFERENCES' in report
    # Check that summary info is present
    assert 'Total Tests:' in report
    assert 'Passed:' in report


@pytest.mark.basic
def test_full_regression_suite():
    """Test full regression suite execution."""
    suite = RegressionTestSuite()
    
    # Add some tests
    suite.test_spectral_bound_consistency('11a1', 1)
    suite.test_spectral_bound_consistency('37a1', 1)
    
    summary = suite.run_full_regression_suite()
    
    assert 'total_tests' in summary
    assert 'passed' in summary
    assert 'failed' in summary
    assert 'skipped' in summary
    assert summary['total_tests'] > 0


@pytest.mark.basic
def test_validate_against_literature():
    """Test literature validation function."""
    curve_results = {
        '11a1': {
            'spectral_bound': 1,
            'conductor': 11,
            'rank': 0
        },
        '37a1': {
            'spectral_bound': 1,
            'conductor': 37,
            'rank': 1
        }
    }
    
    summary = validate_against_literature(curve_results)
    
    assert 'total_tests' in summary
    assert summary['passed'] > 0


@pytest.mark.sage_required
def test_regression_with_sage():
    """Test regression suite with actual SageMath computations."""
    try:
        from sage.all import EllipticCurve
        from src.spectral_finiteness import SpectralFinitenessProver
    except ImportError:
        pytest.skip("SageMath not available")
    
    suite = RegressionTestSuite()
    
    # Test with actual computation
    E = EllipticCurve('11a1')
    prover = SpectralFinitenessProver(E)
    result = prover.prove_finiteness()
    
    # Validate results
    bound_result = suite.test_spectral_bound_consistency('11a1', result['global_bound'])
    assert bound_result['status'] == 'passed'
    
    conductor = int(E.conductor())
    conductor_result = suite.test_conductor_computation('11a1', conductor)
    assert conductor_result['status'] == 'passed'
    
    rank = E.rank()
    rank_result = suite.test_rank_prediction('11a1', rank)
    assert rank_result['status'] == 'passed'


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
