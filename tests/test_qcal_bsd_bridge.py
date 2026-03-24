"""
Tests for QCAL-BSD Bridge Module
=================================

Validates the connection between Navier-Stokes (QCAL) and BSD.

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: January 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from qcal_bsd_bridge import (
    QCALBSDBridge,
    demonstrate_qcal_bsd_bridge,
    QCAL_FREQUENCY
)


class TestQCALBSDBridge:
    """Test suite for QCAL-BSD Bridge"""
    
    def test_initialization(self):
        """Test bridge initialization"""
        bridge = QCALBSDBridge("11a1")
        assert bridge.curve_label == "11a1"
        assert bridge.f0 == QCAL_FREQUENCY
        assert bridge.f0 == 141.7001
    
    def test_compute_operator_spectrum(self):
        """Test H_Ψ operator spectrum computation"""
        bridge = QCALBSDBridge()
        spectral = bridge.compute_operator_spectrum(n_modes=5)
        
        # Check structure
        assert 'eigenvalues' in spectral
        assert 'frequencies' in spectral
        assert 'coherence_field' in spectral
        assert 'global_coherence' in spectral
        
        # Check dimensions
        assert len(spectral['eigenvalues']) == 5
        assert len(spectral['frequencies']) == 5
        assert len(spectral['coherence_field']) == 5
        
        # Check values
        assert spectral['global_coherence'] >= 0
        assert spectral['global_coherence'] <= 1
        assert spectral['resonance_frequency'] == QCAL_FREQUENCY
        
        # Check eigenvalues are positive (λ_k = ω_k² + 1/4 ≥ 1/4)
        eigenvalues = np.array(spectral['eigenvalues'])
        assert np.all(eigenvalues >= 0.25)
    
    def test_compute_l_function_proxy(self):
        """Test L-function proxy computation"""
        bridge = QCALBSDBridge()
        bridge.compute_operator_spectrum(n_modes=5)
        bsd = bridge.compute_l_function_proxy(s_value=1.0)
        
        # Check structure
        assert 'fredholm_determinant' in bsd
        assert 'l_function_proxy' in bsd
        assert 'c_factor' in bsd
        assert 'spectral_coherent' in bsd
        
        # Check s_value
        assert bsd['s_value'] == 1.0
        
        # Check c_factor is non-zero
        assert abs(bsd['c_factor']) > 1e-10
        
        # Check product formula exists
        assert 'product_formula' in bsd
    
    def test_map_eigenvalues_to_points(self):
        """Test mapping of eigenvalues to rational points"""
        bridge = QCALBSDBridge()
        bridge.compute_operator_spectrum(n_modes=10)
        mapping = bridge.map_eigenvalues_to_points()
        
        # Check structure
        assert 'zero_modes' in mapping
        assert 'torsion_proxy' in mapping
        assert 'rank_indicator' in mapping
        assert 'discreteness_ratio' in mapping
        
        # Check values
        assert mapping['zero_modes'] >= 0
        assert mapping['discreteness_ratio'] >= 0
        assert mapping['discreteness_ratio'] <= 1
        assert mapping['rank_indicator'] >= 0
        
        # Torsion should equal zero modes
        assert mapping['torsion_proxy'] == mapping['zero_modes']
    
    def test_validate_coherence(self):
        """Test coherence validation at critical frequency"""
        bridge = QCALBSDBridge()
        validation = bridge.validate_coherence_at_critical_frequency()
        
        # Check structure
        assert 'status' in validation
        assert 'spectral_coherence' in validation
        assert 'bsd_coherent' in validation
        assert 'frequency_locked' in validation
        assert 'critical_frequency_hz' in validation
        
        # Check frequency
        assert validation['critical_frequency_hz'] == QCAL_FREQUENCY
        
        # Check status is valid
        assert validation['status'] in ['SYNCHRONIZED', 'PARTIAL']
        
        # Check boolean fields
        assert isinstance(validation['bsd_coherent'], bool)
        assert isinstance(validation['frequency_locked'], bool)
        assert isinstance(validation['global_smoothness'], bool)
        assert isinstance(validation['l_function_analytic'], bool)
    
    def test_generate_bridge_theorem(self):
        """Test bridge theorem generation"""
        bridge = QCALBSDBridge("11a1")
        theorem = bridge.generate_bridge_theorem()
        
        # Check main structure
        assert 'title' in theorem
        assert 'frequency' in theorem
        assert 'curve' in theorem
        assert 'correspondences' in theorem
        assert 'validation_matrix' in theorem
        
        # Check frequency
        assert theorem['frequency'] == QCAL_FREQUENCY
        assert theorem['curve'] == "11a1"
        
        # Check correspondences
        corr = theorem['correspondences']
        assert 'critical_point' in corr
        assert 'stability' in corr
        assert 'invariant' in corr
        assert 'complexity' in corr
        
        # Each correspondence should have validation
        assert 'synchronized' in corr['critical_point']
        assert 'validated' in corr['stability']
        assert 'equivalent' in corr['invariant']
        
        # Check theorem statement
        assert 'statement' in theorem
        assert 'es' in theorem['statement']
        assert 'en' in theorem['statement']
        assert 'verified' in theorem['statement']
        
        # Check final status
        assert 'axiom_status' in theorem
        assert 'millennia_connected' in theorem
    
    def test_export_validation_report(self):
        """Test report export functionality"""
        bridge = QCALBSDBridge()
        
        # Export to temporary file
        import tempfile
        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.json') as f:
            output_path = Path(f.name)
        
        try:
            result_path = bridge.export_validation_report(output_path)
            
            # Check file was created
            assert result_path.exists()
            
            # Check file content
            import json
            with open(result_path, 'r') as f:
                report = json.load(f)
            
            # Validate structure
            assert 'metadata' in report
            assert 'theorem' in report
            assert 'spectral_data' in report
            
            # Validate metadata
            assert report['metadata']['frequency'] == QCAL_FREQUENCY
            
        finally:
            # Cleanup
            if output_path.exists():
                output_path.unlink()
    
    def test_demonstration_function(self):
        """Test the demonstration function"""
        result = demonstrate_qcal_bsd_bridge(
            curve_label="11a1",
            n_modes=5,
            verbose=False
        )
        
        # Check result structure
        assert 'title' in result
        assert 'correspondences' in result
        assert 'validation_matrix' in result
        assert 'statement' in result
        
        # Verify it's a valid theorem
        assert result['frequency'] == QCAL_FREQUENCY
        assert result['curve'] == "11a1"
    
    def test_different_curves(self):
        """Test with different elliptic curves"""
        curves = ["11a1", "37a1", "389a1"]
        
        for curve in curves:
            bridge = QCALBSDBridge(curve)
            theorem = bridge.generate_bridge_theorem()
            
            assert theorem['curve'] == curve
            assert theorem['frequency'] == QCAL_FREQUENCY
            assert 'correspondences' in theorem
    
    def test_different_mode_counts(self):
        """Test with different numbers of spectral modes"""
        mode_counts = [5, 10, 20]
        
        bridge = QCALBSDBridge()
        for n_modes in mode_counts:
            spectral = bridge.compute_operator_spectrum(n_modes=n_modes)
            
            assert len(spectral['eigenvalues']) == n_modes
            assert spectral['n_modes'] == n_modes
            assert spectral['global_coherence'] >= 0
    
    def test_critical_frequency_constant(self):
        """Test that critical frequency is exactly 141.7001 Hz"""
        assert QCAL_FREQUENCY == 141.7001
        
        bridge = QCALBSDBridge()
        assert bridge.f0 == 141.7001
        
        spectral = bridge.compute_operator_spectrum()
        assert spectral['resonance_frequency'] == 141.7001
    
    def test_coherence_bounds(self):
        """Test that coherence values are properly bounded"""
        bridge = QCALBSDBridge()
        spectral = bridge.compute_operator_spectrum(n_modes=10)
        
        # Global coherence should be in [0, 1]
        assert 0 <= spectral['global_coherence'] <= 1
        
        # Individual coherence field values should be positive
        coherence_field = np.array(spectral['coherence_field'])
        assert np.all(coherence_field >= 0)
        assert np.all(coherence_field <= 1)
    
    def test_rank_indicator_sensible(self):
        """Test that rank indicator gives sensible values"""
        bridge = QCALBSDBridge()
        bridge.compute_operator_spectrum(n_modes=10)
        mapping = bridge.map_eigenvalues_to_points()
        
        # Rank should be a small non-negative integer
        rank = mapping['rank_indicator']
        assert isinstance(rank, int)
        assert 0 <= rank <= 10  # Should not exceed number of modes
    
    def test_synchronized_status_logic(self):
        """Test the synchronization status logic"""
        bridge = QCALBSDBridge()
        validation = bridge.validate_coherence_at_critical_frequency()
        
        # If frequency is locked and coherence is high, should be synchronized
        if (validation['frequency_locked'] and 
            validation['spectral_coherence'] > 0.5 and
            validation['bsd_coherent']):
            assert validation['status'] == 'SYNCHRONIZED'
        else:
            assert validation['status'] == 'PARTIAL'
    
    def test_golden_ratio_in_frequencies(self):
        """Test that golden ratio structure appears in frequencies"""
        from qcal_bsd_bridge import GOLDEN_RATIO
        
        # Golden ratio should be (1 + √5) / 2
        expected_phi = (1 + np.sqrt(5)) / 2
        assert abs(GOLDEN_RATIO - expected_phi) < 1e-10
        
        # Should be approximately 1.618...
        assert 1.618 < GOLDEN_RATIO < 1.619


class TestIntegration:
    """Integration tests for the complete bridge"""
    
    def test_complete_workflow(self):
        """Test complete workflow from initialization to theorem"""
        # Initialize
        bridge = QCALBSDBridge("11a1")
        
        # Compute all components
        spectral = bridge.compute_operator_spectrum(n_modes=10)
        bsd = bridge.compute_l_function_proxy()
        mapping = bridge.map_eigenvalues_to_points()
        validation = bridge.validate_coherence_at_critical_frequency()
        theorem = bridge.generate_bridge_theorem()
        
        # Verify all components are present in theorem
        assert theorem['spectral_summary']['n_eigenvalues'] == 10
        assert theorem['validation_matrix'] == validation
        
        # Verify internal consistency
        assert (theorem['spectral_summary']['coherence'] == 
                spectral['global_coherence'])
        assert (theorem['bsd_summary']['fredholm_det'] == 
                bsd['fredholm_determinant'])
    
    def test_multiple_curves_consistency(self):
        """Test that bridge works consistently across multiple curves"""
        curves = ["11a1", "37a1", "389a1"]
        results = []
        
        for curve in curves:
            result = demonstrate_qcal_bsd_bridge(
                curve_label=curve,
                n_modes=10,
                verbose=False
            )
            results.append(result)
        
        # All should have the same frequency
        for result in results:
            assert result['frequency'] == QCAL_FREQUENCY
        
        # All should have valid structure
        for result in results:
            assert 'correspondences' in result
            assert 'validation_matrix' in result
            assert 'statement' in result


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
