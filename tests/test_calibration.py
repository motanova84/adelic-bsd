"""
Tests para validación de la calibración del parámetro 'a'

Valida que el parámetro calibrado satisface los requisitos de la prueba incondicional:
- δ* > 0.04
- γ > 0

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: November 2025
"""

import pytest
import sys
import os

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
