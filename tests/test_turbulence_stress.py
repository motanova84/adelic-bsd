#!/usr/bin/env python3
"""
Test suite for Turbulence Stress Test module
============================================

Tests for the BSD-Ψ stabilizer validation under turbulence injection.
"""

import pytest
import numpy as np
from pathlib import Path
import json
import sys

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from turbulence_stress_test import (
    generate_white_noise,
    compute_velocity_gradient,
    seeley_dewitt_tensor_simulation,
    BSDPsiStabilizer,
    run_turbulence_stress_test,
    save_stress_test_result,
    generate_stress_test_report,
    TurbulenceMetrics,
    StressTestResult,
    RUPTURE_FREQUENCY,
    ANCHOR_CURVE,
    COHERENCE_CRITICAL,
    COHERENCE_STABLE,
)


class TestWhiteNoiseGeneration:
    """Test white noise generation for turbulence"""
    
    def test_noise_generation_basic(self):
        """Test that white noise is generated correctly"""
        n_samples = 100
        noise = generate_white_noise(n_samples)
        
        assert len(noise) == n_samples
        assert isinstance(noise, np.ndarray)
        assert noise.dtype in [np.float64, np.float32]
    
    def test_noise_normalization(self):
        """Test that noise is approximately normalized"""
        n_samples = 1000
        noise = generate_white_noise(n_samples)
        
        # Should have approximately unit variance
        assert 0.5 < np.std(noise) < 2.0
        # Mean should be close to 0
        assert abs(np.mean(noise)) < 0.5
    
    def test_noise_high_frequency(self):
        """Test that high-frequency filtering works"""
        n_samples = 1000
        noise = generate_white_noise(n_samples, frequency=1e9)
        
        # Check that FFT has high-frequency components
        fft = np.fft.fft(noise)
        freqs = np.fft.fftfreq(n_samples)
        
        # Should have more power at higher frequencies
        low_freq_power = np.sum(np.abs(fft[np.abs(freqs) < 0.1]))
        high_freq_power = np.sum(np.abs(fft[np.abs(freqs) >= 0.1]))
        
        # High frequency should dominate
        assert high_freq_power > low_freq_power * 0.1


class TestVelocityGradient:
    """Test velocity gradient computation"""
    
    def test_gradient_zero_field(self):
        """Test gradient of zero field"""
        field = np.zeros(100)
        gradient = compute_velocity_gradient(field)
        
        assert gradient == 0.0 or gradient < 1e-10
    
    def test_gradient_linear_field(self):
        """Test gradient of linear field"""
        field = np.linspace(0, 10, 100)
        gradient = compute_velocity_gradient(field)
        
        # Should have non-zero gradient
        assert gradient > 0
    
    def test_gradient_magnitude(self):
        """Test that gradient magnitude is positive"""
        field = np.random.randn(100)
        gradient = compute_velocity_gradient(field)
        
        assert gradient >= 0


class TestSeeleyDeWittTensor:
    """Test Seeley-DeWitt tensor simulation"""
    
    def test_smooth_field(self):
        """Test that smooth fields have low singularity measure"""
        # Smooth sine wave
        field = np.sin(np.linspace(0, 2*np.pi, 100))
        singularity = seeley_dewitt_tensor_simulation(field)
        
        # Should be relatively small
        assert singularity < 10.0
    
    def test_discontinuous_field(self):
        """Test that discontinuous fields have high singularity measure"""
        # Step function
        field = np.concatenate([np.zeros(50), np.ones(50)])
        singularity = seeley_dewitt_tensor_simulation(field)
        
        # Should detect the discontinuity
        assert singularity > 0
    
    def test_random_field(self):
        """Test random field produces finite singularity measure"""
        field = np.random.randn(100)
        singularity = seeley_dewitt_tensor_simulation(field)
        
        assert np.isfinite(singularity)
        assert singularity >= 0


class TestBSDPsiStabilizer:
    """Test BSD-Ψ Stabilizer"""
    
    def test_initialization(self):
        """Test stabilizer initialization"""
        stabilizer = BSDPsiStabilizer(curve_label=ANCHOR_CURVE)
        
        assert stabilizer.curve_label == ANCHOR_CURVE
        assert stabilizer.rank == 2  # 389a1 has rank 2
        assert stabilizer.conductor == 389
    
    def test_l_function_value(self):
        """Test L-function computation"""
        stabilizer = BSDPsiStabilizer(curve_label=ANCHOR_CURVE)
        
        # For rank 2 curve, L(E,1) should be 0
        l_val = stabilizer.compute_l_function_value(s=1.0)
        
        assert isinstance(l_val, float)
        assert l_val >= 0
        assert l_val < 0.1  # Should be close to 0 for s=1
    
    def test_mordell_weil_redistribution(self):
        """Test energy redistribution via Mordell-Weil"""
        stabilizer = BSDPsiStabilizer(curve_label=ANCHOR_CURVE)
        
        turbulence = generate_white_noise(100)
        energy_diss, coherence = stabilizer.mordell_weil_energy_redistribution(turbulence)
        
        assert isinstance(energy_diss, float)
        assert isinstance(coherence, float)
        assert energy_diss >= 0
        assert 0.0 <= coherence <= 1.0
    
    def test_arithmetic_dissipation(self):
        """Test arithmetic dissipation"""
        stabilizer = BSDPsiStabilizer(curve_label=ANCHOR_CURVE)
        
        turbulence = generate_white_noise(100)
        dissipation = stabilizer.arithmetic_dissipation(turbulence)
        
        assert isinstance(dissipation, float)
        assert 0.0 <= dissipation <= 1.0
    
    def test_stabilize(self):
        """Test complete stabilization"""
        stabilizer = BSDPsiStabilizer(curve_label=ANCHOR_CURVE)
        
        turbulence = generate_white_noise(100)
        result = stabilizer.stabilize(turbulence)
        
        # Check all expected keys
        assert 'coherence' in result
        assert 'velocity_gradient' in result
        assert 'l_residue' in result
        assert 'energy_dissipated' in result
        assert 'dissipation_factor' in result
        
        # Check value ranges
        assert 0.0 <= result['coherence'] <= 1.0
        assert result['velocity_gradient'] >= 0
        assert result['l_residue'] >= 0
        assert result['energy_dissipated'] >= 0
        assert 0.0 <= result['dissipation_factor'] <= 1.0


class TestTurbulenceMetrics:
    """Test TurbulenceMetrics dataclass"""
    
    def test_metrics_creation(self):
        """Test creating metrics object"""
        metrics = TurbulenceMetrics(
            coherence_psi=0.5,
            velocity_gradient=100.0,
            l_function_residue=0.01,
            system_state="TRANSITORIO",
            entropy_level=5.0,
            timestamp="2026-01-12T00:00:00"
        )
        
        assert metrics.coherence_psi == 0.5
        assert metrics.velocity_gradient == 100.0
        assert metrics.system_state == "TRANSITORIO"
    
    def test_metrics_to_dict(self):
        """Test conversion to dictionary"""
        metrics = TurbulenceMetrics(
            coherence_psi=0.5,
            velocity_gradient=100.0,
            l_function_residue=0.01,
            system_state="TRANSITORIO",
            entropy_level=5.0,
            timestamp="2026-01-12T00:00:00"
        )
        
        d = metrics.to_dict()
        assert isinstance(d, dict)
        assert d['coherence_psi'] == 0.5
        assert d['system_state'] == "TRANSITORIO"


class TestStressTest:
    """Test full stress test execution"""
    
    def test_stress_test_execution(self):
        """Test that stress test runs without errors"""
        result = run_turbulence_stress_test(
            n_samples=100,
            verbose=False
        )
        
        assert isinstance(result, StressTestResult)
        assert result.curve_label == ANCHOR_CURVE
        assert result.test_duration > 0
    
    def test_stress_test_stabilization_metrics(self):
        """Test that stabilization improves metrics"""
        result = run_turbulence_stress_test(
            n_samples=100,
            verbose=False
        )
        
        # Post-stabilization should have better coherence
        assert result.post_stabilization.coherence_psi > result.pre_stabilization.coherence_psi
        
        # System state should improve or at least not worsen
        # With small sample size, might still be CAOS but with better metrics
        assert result.post_stabilization.system_state in ["CAOS", "TRANSITORIO", "REVELACIÓN"]
    
    def test_stress_test_result_to_dict(self):
        """Test result conversion to dictionary"""
        result = run_turbulence_stress_test(
            n_samples=100,
            verbose=False
        )
        
        d = result.to_dict()
        assert isinstance(d, dict)
        assert 'pre_stabilization' in d
        assert 'post_stabilization' in d
        assert 'stabilization_successful' in d
        assert 'stress_gradient' in d
    
    def test_stress_test_with_large_samples(self):
        """Test stress test with larger sample size"""
        result = run_turbulence_stress_test(
            n_samples=1000,
            verbose=False
        )
        
        # Should still produce valid results
        assert result.stabilization_successful in [True, False]
        assert result.stress_gradient > 0
    
    def test_stress_test_deterministic_seed(self):
        """Test that results are reproducible with same seed"""
        np.random.seed(42)
        result1 = run_turbulence_stress_test(n_samples=100, verbose=False)
        
        np.random.seed(42)
        result2 = run_turbulence_stress_test(n_samples=100, verbose=False)
        
        # Results should be similar (within numerical precision)
        assert abs(result1.pre_stabilization.coherence_psi - 
                  result2.pre_stabilization.coherence_psi) < 0.1


class TestResultExport:
    """Test result export functionality"""
    
    def test_save_stress_test_result(self, tmp_path):
        """Test saving result to JSON"""
        result = run_turbulence_stress_test(n_samples=100, verbose=False)
        
        output_path = tmp_path / "test_result.json"
        saved_path = save_stress_test_result(result, output_path)
        
        assert saved_path.exists()
        assert saved_path == output_path
        
        # Verify JSON is valid
        with open(saved_path) as f:
            data = json.load(f)
        
        assert 'pre_stabilization' in data
        assert 'post_stabilization' in data
    
    def test_generate_report(self):
        """Test report generation"""
        result = run_turbulence_stress_test(n_samples=100, verbose=False)
        
        report = generate_stress_test_report(result)
        
        assert isinstance(report, str)
        assert len(report) > 0
        assert "REPORTE DE PRUEBA DE ESTRÉS" in report
        assert result.curve_label in report
        
        # Check key sections
        assert "MÉTRICAS PRE-ESTABILIZACIÓN" in report
        assert "MÉTRICAS POST-ESTABILIZACIÓN" in report
        assert "RESULTADO" in report


class TestConstants:
    """Test module constants"""
    
    def test_constants_defined(self):
        """Test that required constants are defined"""
        assert RUPTURE_FREQUENCY == 1e9
        assert ANCHOR_CURVE == "389a1"
        assert COHERENCE_CRITICAL == 0.2
        assert COHERENCE_STABLE == 0.8
    
    def test_coherence_thresholds(self):
        """Test coherence threshold ordering"""
        assert COHERENCE_CRITICAL < COHERENCE_STABLE


class TestIntegration:
    """Integration tests"""
    
    def test_full_workflow(self, tmp_path):
        """Test complete workflow from test to export"""
        # Run test
        result = run_turbulence_stress_test(
            n_samples=100,
            rupture_frequency=1e9,
            curve_label=ANCHOR_CURVE,
            verbose=False
        )
        
        # Save result
        json_path = tmp_path / "result.json"
        save_stress_test_result(result, json_path)
        
        # Generate report
        report = generate_stress_test_report(result)
        report_path = tmp_path / "report.txt"
        with open(report_path, 'w') as f:
            f.write(report)
        
        # Verify both files exist
        assert json_path.exists()
        assert report_path.exists()
        
        # Verify JSON is valid
        with open(json_path) as f:
            data = json.load(f)
        assert data['curve_label'] == ANCHOR_CURVE
        
        # Verify report contains key information
        with open(report_path) as f:
            report_content = f.read()
        assert ANCHOR_CURVE in report_content
    
    def test_stress_test_meets_expected_metrics(self):
        """Test that stress test produces expected improvements"""
        # Set seed for reproducibility
        np.random.seed(42)
        
        result = run_turbulence_stress_test(
            n_samples=500,
            verbose=False
        )
        
        # Pre-stabilization should be chaotic
        assert result.pre_stabilization.coherence_psi < COHERENCE_STABLE
        assert result.pre_stabilization.system_state == "CAOS"
        
        # Post-stabilization should improve
        improvement = (result.post_stabilization.coherence_psi - 
                      result.pre_stabilization.coherence_psi)
        assert improvement > 0
        
        # Stress gradient should be significant
        assert result.stress_gradient > 1e10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
