"""
Tests for BSD-Yang-Mills Integration Module
"""

import pytest
import numpy as np
from pathlib import Path

from src.yang_mills_bsd import (
    YangMillsOperator,
    BSD_YangMills_System,
    activate_BSD_YM,
    QCAL_FREQUENCY
)


class TestYangMillsOperator:
    """Test suite for YangMillsOperator class"""
    
    def test_operator_initialization(self):
        """Test basic operator initialization"""
        operator = YangMillsOperator("11a1", frequency=141.7001)
        
        assert operator.curve_id == "11a1"
        assert operator.frequency == 141.7001
        assert operator.gauge_group == "SU(2)"
        
    def test_operator_construction(self):
        """Test operator construction from curve"""
        operator = YangMillsOperator("11a1")
        operator.construct_from_curve(n_modes=50)
        
        assert operator.eigenvalues is not None
        assert len(operator.eigenvalues) == 50
        assert all(operator.eigenvalues > 0)  # Eigenvalues should be positive
        
    def test_trace_computation(self):
        """Test trace computation"""
        operator = YangMillsOperator("11a1")
        operator.construct_from_curve(n_modes=100)
        
        # Compute trace at s=1
        trace_value = operator.trace(s=1.0, k=1)
        
        assert trace_value is not None
        assert isinstance(trace_value, complex)
        assert trace_value.real > 0  # Trace should be positive for k=1
        
    def test_trace_caching(self):
        """Test that trace values are cached"""
        operator = YangMillsOperator("11a1")
        operator.construct_from_curve(n_modes=50)
        
        # First call
        trace1 = operator.trace(s=1.0, k=1)
        
        # Second call should use cache
        trace2 = operator.trace(s=1.0, k=1)
        
        assert trace1 == trace2
        assert (1.0, 1) in operator.trace_cache
        
    def test_l_function_coefficients(self):
        """Test L-function coefficient retrieval"""
        operator = YangMillsOperator("11a1")
        
        # Test known coefficients for 11a1
        a1 = operator.get_l_function_coefficient(1)
        a2 = operator.get_l_function_coefficient(2)
        
        assert a1 == 1  # a_1 is always 1
        assert a2 == -2  # Known value for 11a1
        
    def test_trace_identity_verification(self):
        """Test trace identity verification"""
        operator = YangMillsOperator("11a1")
        operator.construct_from_curve(n_modes=100)
        
        verification = operator.verify_trace_identity(s=1.0, k=1, n_terms=50)
        
        assert 'trace_value' in verification
        assert 'l_function_value' in verification
        assert 'relative_error' in verification
        assert 'identity_satisfied' in verification
        
        # Error should be reasonable
        assert verification['relative_error'] < 1.0
        
    def test_frequency_spectrum(self):
        """Test frequency spectrum extraction"""
        operator = YangMillsOperator("11a1", frequency=QCAL_FREQUENCY)
        operator.construct_from_curve(n_modes=50)
        
        spectrum = operator.frequency_spectrum()
        
        assert spectrum is not None
        assert len(spectrum) == 50
        assert all(spectrum >= 0)  # Frequencies should be non-negative
        
    def test_operator_serialization(self):
        """Test operator serialization to dict"""
        operator = YangMillsOperator("11a1")
        operator.construct_from_curve(n_modes=30)
        
        data = operator.to_dict()
        
        assert data['curve_id'] == "11a1"
        assert data['frequency'] == QCAL_FREQUENCY
        assert data['gauge_group'] == "SU(2)"
        assert data['n_eigenvalues'] == 30


class TestBSDYangMillsSystem:
    """Test suite for BSD_YangMills_System class"""
    
    def test_system_initialization(self):
        """Test system initialization"""
        system = BSD_YangMills_System("11a1", frequency=141.7001)
        
        assert system.curve_id == "11a1"
        assert system.frequency == 141.7001
        assert system.operator is not None
        assert system.qcal_bridge_instance is not None
        
    def test_trace_identity_verification(self):
        """Test trace identity verification in system"""
        system = BSD_YangMills_System("11a1")
        
        result = system.verify_trace_identity(s=1.0)
        
        assert isinstance(result, bool)
        # Should pass verification (at least partially)
        
    def test_qcal_bridge_verification(self):
        """Test QCAL bridge verification"""
        system = BSD_YangMills_System("11a1")
        
        result = system.verify_qcal_bridge()
        
        assert isinstance(result, bool)
        
    def test_system_activation(self):
        """Test complete system activation"""
        system = BSD_YangMills_System("11a1")
        
        report = system.activate()
        
        assert 'curve_id' in report
        assert 'frequency' in report
        assert 'system_active' in report
        assert 'trace_identity_verified' in report
        assert 'qcal_bridge_verified' in report
        
        assert report['curve_id'] == "11a1"
        assert report['frequency'] == QCAL_FREQUENCY
        
    def test_theorem_generation(self):
        """Test theorem statement generation"""
        system = BSD_YangMills_System("11a1")
        
        theorem = system.generate_theorem_statement()
        
        assert 'title' in theorem
        assert 'statement' in theorem
        assert 'curve' in theorem
        assert 'frequency' in theorem
        assert 'correspondences' in theorem
        
        assert theorem['curve'] == "11a1"
        assert theorem['frequency'] == QCAL_FREQUENCY
        assert 'en' in theorem['statement']
        assert 'es' in theorem['statement']
        
    def test_report_export(self, tmp_path):
        """Test report export functionality"""
        system = BSD_YangMills_System("11a1")
        
        output_path = tmp_path / "test_report.json"
        result_path = system.export_report(output_path)
        
        assert result_path.exists()
        
        # Verify JSON is valid
        import json
        with open(result_path) as f:
            data = json.load(f)
        
        assert 'metadata' in data
        assert 'system' in data
        assert 'theorem' in data
        assert 'operator' in data
        

class TestActivationFunction:
    """Test suite for activation functions"""
    
    def test_activate_bsd_ym(self):
        """Test activate_BSD_YM function"""
        system = activate_BSD_YM("11a1")
        
        assert isinstance(system, BSD_YangMills_System)
        assert system.curve_id == "11a1"
        assert system.frequency == QCAL_FREQUENCY
        
    def test_multiple_curves(self):
        """Test activation with different curves"""
        curves = ["11a1", "37a1", "389a1"]
        
        for curve_id in curves:
            system = activate_BSD_YM(curve_id)
            assert system.curve_id == curve_id
            assert system.operator is not None


class TestIntegrationWithQCAL:
    """Test integration with existing QCAL framework"""
    
    def test_qcal_frequency_consistency(self):
        """Test that QCAL frequency is consistent"""
        from src.qcal_bsd_bridge import QCAL_FREQUENCY as QCAL_FREQ_ORIGINAL
        
        system = BSD_YangMills_System("11a1")
        
        assert system.frequency == QCAL_FREQ_ORIGINAL
        assert system.frequency == 141.7001
        
    def test_qcal_bridge_integration(self):
        """Test integration with QCALBSDBridge"""
        system = BSD_YangMills_System("11a1")
        
        # Both should use the same curve
        assert system.curve_id == system.qcal_bridge_instance.curve_label
        
        # Both should use the same frequency
        assert system.frequency == system.qcal_bridge_instance.f0


class TestMathematicalProperties:
    """Test mathematical properties of the Yang-Mills operator"""
    
    def test_eigenvalue_positivity(self):
        """Test that eigenvalues are positive"""
        operator = YangMillsOperator("11a1")
        operator.construct_from_curve(n_modes=100)
        
        assert all(operator.eigenvalues > 0)
        
    def test_eigenvalue_growth(self):
        """Test that eigenvalues grow appropriately"""
        operator = YangMillsOperator("11a1")
        operator.construct_from_curve(n_modes=100)
        
        # Eigenvalues should generally increase
        # (though not strictly monotonic due to gauge corrections)
        mean_first_half = np.mean(operator.eigenvalues[:50])
        mean_second_half = np.mean(operator.eigenvalues[50:])
        
        assert mean_second_half >= mean_first_half
        
    def test_trace_convergence(self):
        """Test that trace values are finite and reasonable"""
        operator = YangMillsOperator("11a1")
        operator.construct_from_curve(n_modes=100)
        
        for k in [1, 2, 3]:
            trace_value = operator.trace(s=1.5, k=k)
            
            assert np.isfinite(trace_value)
            assert abs(trace_value) < 1e10  # Should not blow up


class TestEdgeCases:
    """Test edge cases and error handling"""
    
    def test_small_n_modes(self):
        """Test with small number of modes"""
        operator = YangMillsOperator("11a1")
        operator.construct_from_curve(n_modes=5)
        
        assert len(operator.eigenvalues) == 5
        trace_value = operator.trace(s=1.0, k=1)
        assert trace_value is not None
        
    def test_large_n_modes(self):
        """Test with large number of modes"""
        operator = YangMillsOperator("11a1")
        operator.construct_from_curve(n_modes=500)
        
        assert len(operator.eigenvalues) == 500
        
    def test_different_s_values(self):
        """Test trace computation at different s values"""
        operator = YangMillsOperator("11a1")
        operator.construct_from_curve(n_modes=50)
        
        s_values = [1.0, 1.5, 2.0, 1.0 + 0.5j]
        
        for s in s_values:
            trace_value = operator.trace(s, k=1)
            assert trace_value is not None
            assert np.isfinite(trace_value)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
