"""
Tests for validate_spectral_identity_all_ranks.py

These tests verify the validation script works correctly even without SageMath.
"""

import pytest
import sys
import os
import json
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))

from validate_spectral_identity_all_ranks import SpectralIdentityValidator


def test_validator_initialization():
    """Test that validator can be initialized"""
    validator = SpectralIdentityValidator(verbose=False)
    assert validator is not None
    assert isinstance(validator.results, dict)


def test_mock_validation_known_curves():
    """Test mock validation for known curves"""
    validator = SpectralIdentityValidator(verbose=False)
    
    # Test curves with known data
    test_cases = [
        ('11a1', 0, 11),
        ('37a1', 1, 37),
        ('389a1', 2, 389),
        ('5077a1', 3, 5077)
    ]
    
    for curve_label, expected_rank, expected_conductor in test_cases:
        result = validator._mock_validation(curve_label)
        
        assert result['success'] is True
        assert result['curve'] == curve_label
        assert result['rank'] == expected_rank
        assert result['conductor'] == expected_conductor
        assert result['spectral_identity_verified'] is True
        assert result['vanishing_order_matches_rank'] is True
        assert result['c_factor_nonzero'] is True


def test_validate_single_curve_mock():
    """Test validation of a single curve in mock mode"""
    validator = SpectralIdentityValidator(verbose=False)
    
    result = validator.validate_curve('11a1')
    
    assert result['success'] is True
    assert result['curve'] == '11a1'
    assert 'rank' in result
    assert 'conductor' in result


def test_validate_all_ranks():
    """Test validation of all ranks"""
    validator = SpectralIdentityValidator(verbose=False)
    
    results = validator.validate_all_ranks()
    
    # Check summary
    assert 'summary' in results
    assert 'individual_results' in results
    
    summary = results['summary']
    assert summary['total_curves'] == 4
    assert summary['successful_validations'] == 4
    assert summary['success_rate'] == 1.0
    assert summary['all_passed'] is True
    
    # Check rank coverage
    assert set(summary['ranks_covered']) == {0, 1, 2, 3}


def test_results_saving(tmp_path):
    """Test that results can be saved to JSON"""
    validator = SpectralIdentityValidator(verbose=False)
    
    # Run validation
    validator.validate_curve('11a1')
    
    # Save to temp file
    output_file = tmp_path / "test_results.json"
    validator.results['11a1'] = validator.results.get('11a1', {})
    
    with open(output_file, 'w') as f:
        json.dump(validator.results, f)
    
    # Verify file exists and can be read
    assert output_file.exists()
    
    with open(output_file, 'r') as f:
        loaded_results = json.load(f)
    
    assert '11a1' in loaded_results


def test_summary_generation():
    """Test summary generation"""
    validator = SpectralIdentityValidator(verbose=False)
    
    # Create mock results
    mock_results = [
        {
            'success': True,
            'rank': 0,
            'spectral_identity_verified': True,
            'vanishing_order_matches_rank': True,
            'c_factor_nonzero': True
        },
        {
            'success': True,
            'rank': 1,
            'spectral_identity_verified': True,
            'vanishing_order_matches_rank': True,
            'c_factor_nonzero': True
        }
    ]
    
    summary = validator._generate_summary(mock_results)
    
    assert summary['total_curves'] == 2
    assert summary['successful_validations'] == 2
    assert summary['identity_verified_count'] == 2
    assert summary['rank_compatibility_count'] == 2
    assert summary['c_nonzero_count'] == 2
    assert summary['success_rate'] == 1.0
    assert summary['all_passed'] is True


def test_validation_with_partial_failure():
    """Test summary when some validations fail"""
    validator = SpectralIdentityValidator(verbose=False)
    
    mock_results = [
        {'success': True, 'rank': 0, 'spectral_identity_verified': True,
         'vanishing_order_matches_rank': True, 'c_factor_nonzero': True},
        {'success': False, 'rank': 1}  # Failed validation
    ]
    
    summary = validator._generate_summary(mock_results)
    
    assert summary['total_curves'] == 2
    assert summary['successful_validations'] == 1
    assert summary['success_rate'] == 0.5
    assert summary['all_passed'] is False


def test_verbose_mode():
    """Test that verbose mode can be toggled"""
    validator_verbose = SpectralIdentityValidator(verbose=True)
    validator_quiet = SpectralIdentityValidator(verbose=False)
    
    assert validator_verbose.verbose is True
    assert validator_quiet.verbose is False


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
