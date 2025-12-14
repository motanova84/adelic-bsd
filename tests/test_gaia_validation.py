#!/usr/bin/env python3
"""
Test Suite for GAIA ∞³ Validation Protocol
==========================================

Tests for the GAIA-LIGO validation module.
"""

import pytest
import sys
import os
from pathlib import Path
import numpy as np
import pandas as pd
from scipy import stats

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from scripts.validate_gaia_ligo import GAIALIGOValidator


class TestGAIALIGOValidator:
    """Test suite for GAIA-LIGO validator."""
    
    def setup_method(self):
        """Setup test validator instance."""
        self.validator = GAIALIGOValidator(f0=141.7001, sigma_gaia=0.2)
    
    def test_initialization(self):
        """Test validator initialization."""
        assert self.validator.f0 == 141.7001
        assert self.validator.sigma_gaia == 0.2
        assert self.validator.eventos is None
        assert self.validator.results == {}
    
    def test_load_gwtc3_sample(self):
        """Test loading GWTC-3 sample data."""
        eventos = self.validator.load_gwtc3_sample()
        
        # Check data structure
        assert isinstance(eventos, pd.DataFrame)
        assert len(eventos) == 5
        assert 'Evento' in eventos.columns
        assert 'f_pico' in eventos.columns
        assert 'f_err' in eventos.columns
        assert 'Δf' in eventos.columns
        
        # Check Δf computation
        expected_delta_f = eventos['f_pico'] - self.validator.f0
        np.testing.assert_array_almost_equal(eventos['Δf'].values, expected_delta_f.values)
        
        # Verify data is stored
        assert self.validator.eventos is not None
    
    def test_normality_test(self):
        """Test Shapiro-Wilk normality test."""
        self.validator.load_gwtc3_sample()
        stat, p_value = self.validator.test_normality()
        
        # Check return values
        assert isinstance(stat, float)
        assert isinstance(p_value, float)
        assert 0 <= p_value <= 1
        
        # Check results stored
        assert 'normality_stat' in self.validator.results
        assert 'normality_pvalue' in self.validator.results
    
    def test_normality_without_data_raises_error(self):
        """Test that normality test raises error without data."""
        with pytest.raises(ValueError, match="No data loaded"):
            self.validator.test_normality()
    
    def test_ttest(self):
        """Test one-sample t-test."""
        self.validator.load_gwtc3_sample()
        results = self.validator.perform_ttest()
        
        # Check result structure
        assert 'mean' in results
        assert 'std' in results
        assert 'n' in results
        assert 't_stat' in results
        assert 'p_value' in results
        assert 'ci95_lower' in results
        assert 'ci95_upper' in results
        
        # Verify computation
        assert results['n'] == 5
        assert results['ci95_lower'] < results['mean'] < results['ci95_upper']
        
        # Check stored results
        assert 'mean' in self.validator.results
        assert 'p_value' in self.validator.results
    
    def test_ttest_without_data_raises_error(self):
        """Test that t-test raises error without data."""
        with pytest.raises(ValueError, match="No data loaded"):
            self.validator.perform_ttest()
    
    def test_dynamic_threshold_computation(self):
        """Test dynamic 3σ threshold computation."""
        self.validator.load_gwtc3_sample()
        threshold = self.validator.compute_dynamic_threshold()
        
        # Check threshold is positive
        assert threshold > 0
        
        # Check components stored
        assert 'sigma_ligo' in self.validator.results
        assert 'sigma_combined' in self.validator.results
        assert 'threshold_3sigma' in self.validator.results
        
        # Verify computation
        sigma_ligo = self.validator.results['sigma_ligo']
        sigma_combined = self.validator.results['sigma_combined']
        expected_combined = np.sqrt(sigma_ligo**2 + self.validator.sigma_gaia**2)
        np.testing.assert_almost_equal(sigma_combined, expected_combined)
        np.testing.assert_almost_equal(threshold, 3 * expected_combined)
    
    def test_threshold_without_data_raises_error(self):
        """Test that threshold computation raises error without data."""
        with pytest.raises(ValueError, match="No data loaded"):
            self.validator.compute_dynamic_threshold()
    
    def test_count_coincidences(self):
        """Test coincidence counting."""
        self.validator.load_gwtc3_sample()
        threshold = 1.0  # Use fixed threshold for testing
        
        results = self.validator.count_coincidences(threshold)
        
        # Check result structure
        assert 'n_coincidencias' in results
        assert 'porcentaje' in results
        
        # Verify counts
        n_coincidencias = results['n_coincidencias']
        assert 0 <= n_coincidencias <= len(self.validator.eventos)
        assert 0 <= results['porcentaje'] <= 100
        
        # Check stored results
        assert 'n_coincidencias' in self.validator.results
        assert 'porcentaje_coincidencias' in self.validator.results
    
    def test_coincidences_without_data_raises_error(self):
        """Test that coincidence counting raises error without data."""
        with pytest.raises(ValueError, match="No data loaded"):
            self.validator.count_coincidences(1.0)
    
    def test_generate_summary(self):
        """Test summary generation."""
        # Run necessary computations first
        self.validator.load_gwtc3_sample()
        self.validator.test_normality()
        self.validator.perform_ttest()
        threshold = self.validator.compute_dynamic_threshold()
        self.validator.count_coincidences(threshold)
        
        summary = self.validator.generate_summary()
        
        # Check summary structure
        assert isinstance(summary, pd.DataFrame)
        assert 'Estadístico' in summary.columns
        assert 'Valor' in summary.columns
        assert len(summary) == 12  # Expected number of rows
    
    def test_validate_criteria(self):
        """Test validation criteria checking."""
        # Run necessary computations first
        self.validator.load_gwtc3_sample()
        self.validator.test_normality()
        self.validator.perform_ttest()
        threshold = self.validator.compute_dynamic_threshold()
        self.validator.count_coincidences(threshold)
        
        criteria = self.validator.validate_criteria()
        
        # Check criteria structure
        assert 'p_value_significant' in criteria
        assert 'ci95_excludes_zero' in criteria
        assert 'normality_valid' in criteria
        assert 'coincidence_high' in criteria
        
        # All should be boolean
        assert all(isinstance(v, (bool, np.bool_)) for v in criteria.values())
        
        # Check stored in results
        assert 'validation_criteria' in self.validator.results
    
    def test_export_results(self, tmp_path):
        """Test results export to files."""
        # Run complete validation
        self.validator.load_gwtc3_sample()
        self.validator.test_normality()
        self.validator.perform_ttest()
        threshold = self.validator.compute_dynamic_threshold()
        self.validator.count_coincidences(threshold)
        self.validator.validate_criteria()
        
        # Export to temporary directory
        self.validator.export_results(str(tmp_path))
        
        # Check files exist
        assert (tmp_path / "delta_f_eventos_gaia_inf3.csv").exists()
        assert (tmp_path / "resumen_validacion_gaia_inf3.csv").exists()
        assert (tmp_path / "validation_results_gaia_inf3.json").exists()
        
        # Verify CSV can be read
        eventos_df = pd.read_csv(tmp_path / "delta_f_eventos_gaia_inf3.csv")
        assert len(eventos_df) == 5
        
        resumen_df = pd.read_csv(tmp_path / "resumen_validacion_gaia_inf3.csv")
        assert len(resumen_df) == 12
    
    def test_complete_validation_pipeline(self, tmp_path):
        """Test complete validation pipeline."""
        results = self.validator.run_complete_validation(
            output_dir=str(tmp_path),
            plot=False  # Skip plotting in tests
        )
        
        # Check results structure
        assert isinstance(results, dict)
        assert 'mean' in results
        assert 'p_value' in results
        assert 'normality_pvalue' in results
        assert 'threshold_3sigma' in results
        assert 'porcentaje_coincidencias' in results
        assert 'validation_criteria' in results
        
        # Check files were created
        assert (tmp_path / "delta_f_eventos_gaia_inf3.csv").exists()
        assert (tmp_path / "resumen_validacion_gaia_inf3.csv").exists()
        assert (tmp_path / "validation_results_gaia_inf3.json").exists()
    
    def test_f0_value_consistency(self):
        """Test that f₀ = 141.7001 Hz is used consistently."""
        validator1 = GAIALIGOValidator(f0=141.7001)
        validator2 = GAIALIGOValidator(f0=142.0)
        
        validator1.load_gwtc3_sample()
        validator2.load_gwtc3_sample()
        
        # Different f0 should give different Δf
        assert not np.allclose(validator1.eventos['Δf'].values, 
                               validator2.eventos['Δf'].values)
    
    def test_statistical_properties(self):
        """Test that statistical computations are mathematically correct."""
        self.validator.load_gwtc3_sample()
        
        # Manual computation
        delta_f = self.validator.eventos['Δf'].values
        manual_mean = np.mean(delta_f)
        manual_std = np.std(delta_f, ddof=1)
        
        # From validator
        self.validator.perform_ttest()
        
        # Compare
        np.testing.assert_almost_equal(self.validator.results['mean'], manual_mean)
        np.testing.assert_almost_equal(self.validator.results['std'], manual_std)
    
    def test_threshold_increases_with_uncertainty(self):
        """Test that threshold increases with uncertainty."""
        validator_low_sigma = GAIALIGOValidator(f0=141.7001, sigma_gaia=0.1)
        validator_high_sigma = GAIALIGOValidator(f0=141.7001, sigma_gaia=0.5)
        
        validator_low_sigma.load_gwtc3_sample()
        validator_high_sigma.load_gwtc3_sample()
        
        threshold_low = validator_low_sigma.compute_dynamic_threshold()
        threshold_high = validator_high_sigma.compute_dynamic_threshold()
        
        # Higher sigma should give higher threshold
        assert threshold_high > threshold_low


class TestIntegrationWithExistingFramework:
    """Test integration with existing adelic-BSD framework."""
    
    def test_f0_matches_framework_value(self):
        """Test that f₀ matches the value in the framework."""
        # The framework defines f₀ = 141.7001 Hz
        validator = GAIALIGOValidator()
        assert validator.f0 == 141.7001
    
    def test_output_directory_structure(self, tmp_path):
        """Test that output structure is compatible with existing scripts."""
        validator = GAIALIGOValidator()
        validator.run_complete_validation(
            output_dir=str(tmp_path),
            plot=False
        )
        
        # Check standard output format
        expected_files = [
            "delta_f_eventos_gaia_inf3.csv",
            "resumen_validacion_gaia_inf3.csv",
            "validation_results_gaia_inf3.json"
        ]
        
        for filename in expected_files:
            assert (tmp_path / filename).exists()


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
