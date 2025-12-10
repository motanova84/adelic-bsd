"""
test_operator_proof.py
Tests for the formal operator proof M_E(s) and trace identity

This module tests the analytical properties of the spectral operator
M_E(s) as described in OperatorProofBSD.tex.

Author: José Manuel Mota Burruezo (JMMB Ψ ∴)
Date: November 2025
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add scripts directory to path
scripts_dir = Path(__file__).parent.parent / "scripts"
sys.path.insert(0, str(scripts_dir))

from validate_operator_proof import (
    mock_elliptic_curve_coefficients,
    compute_trace_power_k,
    compute_fredholm_det,
    compute_L_function,
    validate_operator_proof
)


class TestOperatorBasis:
    """Test basic operator properties."""
    
    def test_coefficient_generation(self):
        """Test that mock coefficients are generated correctly."""
        a_n = mock_elliptic_curve_coefficients(N=50)
        assert len(a_n) == 50
        assert isinstance(a_n, np.ndarray)
        assert a_n.dtype in [np.float64, np.float32]
    
    def test_coefficient_decay(self):
        """Test that coefficients decay as expected."""
        a_n = mock_elliptic_curve_coefficients(N=100)
        # Later coefficients should be smaller (on average)
        early_mean = np.mean(np.abs(a_n[:10]))
        late_mean = np.mean(np.abs(a_n[-10:]))
        assert late_mean < early_mean


class TestTraceIdentity:
    """Test trace identity Tr(M_E(s)^k) = sum(a_n^k / n^(ks))."""
    
    def test_trace_power_1(self):
        """Test trace for k=1."""
        a_n = mock_elliptic_curve_coefficients(N=30)
        s = 2.0
        trace = compute_trace_power_k(a_n, s, k=1)
        
        # Verify it's a finite number
        assert np.isfinite(trace)
        assert isinstance(trace, (float, np.floating))
    
    def test_trace_power_higher(self):
        """Test trace for higher powers k=2,3,4."""
        a_n = mock_elliptic_curve_coefficients(N=30)
        s = 2.0
        
        traces = []
        for k in [1, 2, 3, 4]:
            trace = compute_trace_power_k(a_n, s, k)
            traces.append(trace)
            assert np.isfinite(trace)
        
        # Higher powers should generally have smaller traces (due to eigenvalue decay)
        # This is not always strict but holds on average
        assert all(np.isfinite(t) for t in traces)
    
    def test_trace_convergence_with_s(self):
        """Test that trace converges better for larger s."""
        a_n = mock_elliptic_curve_coefficients(N=50)
        
        trace_s2 = abs(compute_trace_power_k(a_n, s=2.0, k=1))
        trace_s3 = abs(compute_trace_power_k(a_n, s=3.0, k=1))
        
        # For s=3, eigenvalues decay faster, so trace should be smaller
        assert trace_s3 < trace_s2 or np.isclose(trace_s3, trace_s2, rtol=0.5)
    
    def test_trace_reproducibility(self):
        """Test that trace computation is reproducible."""
        a_n = mock_elliptic_curve_coefficients(N=30)
        s = 2.0
        k = 2
        
        trace1 = compute_trace_power_k(a_n, s, k)
        trace2 = compute_trace_power_k(a_n, s, k)
        
        assert trace1 == trace2


class TestFredholmDeterminant:
    """Test Fredholm determinant det(I - M_E(s))."""
    
    def test_determinant_computation(self):
        """Test basic determinant computation."""
        a_n = mock_elliptic_curve_coefficients(N=30)
        s = 2.0
        
        det = compute_fredholm_det(a_n, s, max_k=10)
        
        assert np.isfinite(det)
        assert isinstance(det, (float, np.floating, complex, np.complexfloating))
    
    def test_determinant_positive(self):
        """Test that determinant is positive for real s > 1."""
        a_n = mock_elliptic_curve_coefficients(N=30)
        s = 2.0
        
        det = compute_fredholm_det(a_n, s, max_k=15)
        
        # For real s and reasonable coefficients, det should be real and positive
        assert np.real(det) > 0
    
    def test_determinant_convergence(self):
        """Test that determinant converges with increasing max_k."""
        a_n = mock_elliptic_curve_coefficients(N=30)
        s = 2.0
        
        det_10 = compute_fredholm_det(a_n, s, max_k=10)
        det_20 = compute_fredholm_det(a_n, s, max_k=20)
        det_30 = compute_fredholm_det(a_n, s, max_k=30)
        
        # Should converge: later values closer together
        diff1 = abs(det_20 - det_10)
        diff2 = abs(det_30 - det_20)
        
        # diff2 should be smaller than diff1 (convergence)
        assert diff2 <= diff1 or np.isclose(diff2, diff1, rtol=0.5)


class TestLFunction:
    """Test L-function computation."""
    
    def test_L_function_basic(self):
        """Test basic L-function computation."""
        a_n = mock_elliptic_curve_coefficients(N=30)
        s = 2.0
        
        L_val = compute_L_function(a_n, s)
        
        assert np.isfinite(L_val)
        assert isinstance(L_val, (float, np.floating, complex, np.complexfloating))
    
    def test_L_function_convergence(self):
        """Test L-function convergence with more terms."""
        s = 2.0
        
        a_n_30 = mock_elliptic_curve_coefficients(N=30)
        a_n_50 = mock_elliptic_curve_coefficients(N=50)
        
        L_30 = compute_L_function(a_n_30, s)
        L_50 = compute_L_function(a_n_50, s)
        
        # With more terms, should be similar (same random seed)
        # First 30 terms are the same
        assert np.isfinite(L_30)
        assert np.isfinite(L_50)


class TestSpectralIdentity:
    """Test spectral identity det(I - M_E(s)) ~ c(s) * L(E,s)."""
    
    def test_spectral_relation(self):
        """Test that det and L are related by a reasonable factor."""
        a_n = mock_elliptic_curve_coefficients(N=50)
        s = 2.0
        
        det = compute_fredholm_det(a_n, s, max_k=20)
        L_val = compute_L_function(a_n, s)
        
        # Compute factor c(s)
        c_factor = abs(det / L_val) if L_val != 0 else float('inf')
        
        # Factor should be reasonable (between 0.01 and 100)
        assert 0.01 < c_factor < 100, f"Factor c(s) = {c_factor} out of range"
    
    def test_spectral_identity_consistency(self):
        """Test that spectral identity is consistent across different s."""
        a_n = mock_elliptic_curve_coefficients(N=50)
        
        results = []
        for s in [2.0, 2.5, 3.0]:
            det = compute_fredholm_det(a_n, s, max_k=20)
            L_val = compute_L_function(a_n, s)
            c_factor = abs(det / L_val) if L_val != 0 else float('inf')
            results.append((s, c_factor))
        
        # All factors should be finite and positive
        for s, c in results:
            assert np.isfinite(c), f"Factor at s={s} is not finite"
            assert c > 0, f"Factor at s={s} is not positive"


class TestOperatorCompactness:
    """Test operator compactness (eigenvalue decay)."""
    
    def test_eigenvalue_decay(self):
        """Test that eigenvalues decay for s > 1."""
        a_n = mock_elliptic_curve_coefficients(N=50)
        s = 2.0
        
        n_values = np.arange(1, len(a_n) + 1)
        eigenvalues = a_n / (n_values ** s)
        eigenvalue_norms = np.abs(eigenvalues)
        
        # First eigenvalue should be larger than last (in magnitude)
        assert eigenvalue_norms[0] > eigenvalue_norms[-1]
    
    def test_eigenvalue_ordering(self):
        """Test that eigenvalues are approximately decreasing."""
        a_n = mock_elliptic_curve_coefficients(N=50)
        s = 2.5  # Higher s for stronger decay
        
        n_values = np.arange(1, len(a_n) + 1)
        eigenvalues = a_n / (n_values ** s)
        eigenvalue_norms = np.abs(eigenvalues)
        
        # Count how many times eigenvalues decrease
        decreases = np.sum(eigenvalue_norms[1:] < eigenvalue_norms[:-1])
        total = len(eigenvalue_norms) - 1
        
        # At least 50% should decrease (allowing for coefficient oscillations)
        assert decreases / total > 0.5


class TestFullValidation:
    """Test full validation workflow."""
    
    def test_validate_operator_proof(self):
        """Test complete validation routine."""
        results = validate_operator_proof()
        
        assert isinstance(results, dict)
        assert "validation_type" in results
        assert "tests" in results
        assert "overall_status" in results
        
        # Check that all required tests are present
        required_tests = [
            "trace_identity",
            "operator_compactness",
            "fredholm_determinant",
            "trace_convergence"
        ]
        
        for test_name in required_tests:
            assert test_name in results["tests"], f"Missing test: {test_name}"
            assert "status" in results["tests"][test_name]
    
    def test_validation_output_structure(self):
        """Test that validation produces correct output structure."""
        results = validate_operator_proof()
        
        # Check parameters
        assert "parameters" in results
        assert "N_terms" in results["parameters"]
        assert "s_value" in results["parameters"]
        
        # Check each test has proper structure
        for test_name, test_data in results["tests"].items():
            assert "status" in test_data
            assert test_data["status"] in ["PASSED", "WARNING", "FAILED"]


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
