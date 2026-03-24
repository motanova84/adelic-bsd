"""
Tests for QCAL Unified Framework
=================================

Tests for the QCAL (Quantum Coherent Algebraic Logic) unified framework
modules.

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: January 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from qcal_unified_constants import (
    UniversalConstants, get_unified_constants, 
    verify_universal_coherence, get_problem_operator
)
from qcal_unified_framework import QCALUnifiedFramework, MillenniumProblem
from qcal_cross_verification import CrossVerificationProtocol


class TestUniversalConstants:
    """Test universal constants module."""
    
    def test_constants_creation(self):
        """Test that universal constants can be created."""
        constants = UniversalConstants()
        assert constants.kappa_pi > 0
        assert constants.f0 > 0
        assert constants.lambda_rh == 0.5
        assert constants.delta_bsd == 1.0
    
    def test_standard_constants(self):
        """Test standard QCAL constants."""
        constants = get_unified_constants()
        assert constants.kappa_pi == 2.5773
        assert constants.f0 == 141.7001
        assert constants.lambda_rh == 0.5
        assert constants.epsilon_ns == 0.5772
        assert abs(constants.phi_ramsey - 43/108) < 1e-6
        assert constants.delta_bsd == 1.0
    
    def test_constants_to_dict(self):
        """Test conversion to dictionary."""
        constants = get_unified_constants()
        const_dict = constants.to_dict()
        assert 'kappa_pi' in const_dict
        assert 'f0' in const_dict
        assert 'lambda_rh' in const_dict
        assert len(const_dict) == 8
    
    def test_coherence_verification(self):
        """Test coherence verification."""
        constants = get_unified_constants()
        coherence = constants.verify_coherence()
        
        # Check that all checks are present
        assert 'critical_line_bsd' in coherence
        assert 'euler_ns_correspondence' in coherence
        assert 'f0_derivation' in coherence
        assert 'ramsey_ratio_valid' in coherence
        assert 'bsd_normalized' in coherence
        
        # Check specific results
        assert coherence['critical_line_bsd'] is True
        assert coherence['bsd_normalized'] is True
        assert coherence['ramsey_ratio_valid'] is True
    
    def test_universal_coherence(self):
        """Test overall universal coherence."""
        assert verify_universal_coherence() is True
    
    def test_get_problem_constant(self):
        """Test getting constants for specific problems."""
        constants = get_unified_constants()
        
        assert constants.get_problem_constant('p_vs_np') == 2.5773
        assert constants.get_problem_constant('riemann') == 141.7001
        assert constants.get_problem_constant('bsd') == 1.0
        assert constants.get_problem_constant('navier_stokes') == 0.5772
        assert abs(constants.get_problem_constant('ramsey') - 43/108) < 1e-6
    
    def test_get_problem_operator(self):
        """Test getting operator names for problems."""
        assert get_problem_operator('p_vs_np') == 'D_PNP'
        assert get_problem_operator('riemann') == 'H_Ψ'
        assert get_problem_operator('bsd') == 'L_E'
        assert get_problem_operator('navier_stokes') == 'NS_operator'
        assert get_problem_operator('ramsey') == 'R_operator'


class TestQCALUnifiedFramework:
    """Test QCAL unified framework."""
    
    def test_framework_creation(self):
        """Test framework initialization."""
        framework = QCALUnifiedFramework()
        assert framework.constants is not None
        assert len(framework.problems) > 0
    
    def test_problems_initialized(self):
        """Test that all problems are initialized."""
        framework = QCALUnifiedFramework()
        
        expected_problems = ['p_vs_np', 'riemann', 'bsd', 'navier_stokes', 'ramsey']
        for problem in expected_problems:
            assert problem in framework.problems
            assert isinstance(framework.problems[problem], MillenniumProblem)
    
    def test_problem_connections(self):
        """Test that problems have connections."""
        framework = QCALUnifiedFramework()
        
        # Riemann should connect to BSD
        riemann = framework.problems['riemann']
        assert 'bsd' in riemann.connected_problems
        
        # BSD should connect to Riemann
        bsd = framework.problems['bsd']
        assert 'riemann' in bsd.connected_problems
        
        # Ramsey should connect to multiple problems
        ramsey = framework.problems['ramsey']
        assert len(ramsey.connected_problems) >= 4
    
    def test_operators(self):
        """Test spectral operators."""
        framework = QCALUnifiedFramework()
        constants_dict = framework.constants.to_dict()
        
        # Test each operator
        assert framework.D_PNP_operator(constants_dict) == 2.5773
        assert framework.H_Psi_operator(constants_dict) == 141.7001
        assert framework.L_E_operator(constants_dict) == 1.0
        assert framework.NS_operator(constants_dict) == 0.5772
        assert abs(framework.R_operator(constants_dict) - 43/108) < 1e-6
    
    def test_demonstrate_unification(self):
        """Test unification demonstration."""
        framework = QCALUnifiedFramework()
        results = framework.demonstrate_unification()
        
        assert 'p_vs_np' in results
        assert 'riemann' in results
        assert 'bsd' in results
        
        # Check result structure
        for problem, data in results.items():
            assert 'eigenvalue' in data
            assert 'operator' in data
            assert 'constant' in data
            assert 'connected_via' in data
            assert 'verification_status' in data
    
    def test_get_problem_connections(self):
        """Test getting problem connections."""
        framework = QCALUnifiedFramework()
        
        connections = framework.get_problem_connections('riemann')
        assert 'problem' in connections
        assert 'operator' in connections
        assert 'constant' in connections
        assert 'verification' in connections
        assert 'connected_to' in connections
        
        assert connections['constant'] == 141.7001
    
    def test_coherence_score(self):
        """Test coherence score calculation."""
        framework = QCALUnifiedFramework()
        score = framework.calculate_coherence_score()
        
        assert 0 <= score <= 1
        assert score == 1.0  # Should be perfect coherence
    
    def test_operator_commutativity(self):
        """Test operator commutativity verification."""
        framework = QCALUnifiedFramework()
        commutativity = framework.verify_operator_commutativity()
        
        assert 'constants_coherent' in commutativity
        assert 'operators_well_defined' in commutativity
        assert 'connections_established' in commutativity
        
        assert commutativity['constants_coherent'] is True
        assert commutativity['operators_well_defined'] is True
    
    def test_export_framework(self):
        """Test framework export."""
        framework = QCALUnifiedFramework()
        
        # Export without file
        data = framework.export_framework()
        
        assert 'qcal_unified_framework' in data
        assert 'version' in data['qcal_unified_framework']
        assert 'fundamental_frequency' in data['qcal_unified_framework']
        assert 'constants' in data['qcal_unified_framework']
        assert 'problems' in data['qcal_unified_framework']
        assert 'coherence_score' in data['qcal_unified_framework']
        
        assert data['qcal_unified_framework']['fundamental_frequency'] == 141.7001
        assert data['qcal_unified_framework']['coherence_score'] == 1.0


class TestCrossVerificationProtocol:
    """Test cross-verification protocol."""
    
    def test_protocol_creation(self):
        """Test protocol initialization."""
        protocol = CrossVerificationProtocol()
        assert protocol.framework is not None
    
    def test_verify_p_vs_np(self):
        """Test P vs NP verification."""
        protocol = CrossVerificationProtocol()
        result = protocol.verify_p_vs_np()
        
        assert 'status' in result
        assert 'eigenvalue' in result
        assert 'eigenvalue_valid' in result
        assert result['eigenvalue'] == 2.5773
        assert result['status'] == 'verified'
    
    def test_verify_riemann(self):
        """Test Riemann verification."""
        protocol = CrossVerificationProtocol()
        result = protocol.verify_riemann()
        
        assert 'status' in result
        assert 'eigenvalue' in result
        assert 'fundamental_frequency' in result
        assert result['eigenvalue'] == 141.7001
        assert result['status'] == 'verified'
    
    def test_verify_bsd(self):
        """Test BSD verification."""
        protocol = CrossVerificationProtocol()
        result = protocol.verify_bsd()
        
        assert 'status' in result
        assert 'critical_line_correspondence' in result
        assert result['eigenvalue'] == 1.0
        assert result['critical_line_correspondence'] is True
        assert result['status'] == 'verified'
    
    def test_verify_navier_stokes(self):
        """Test Navier-Stokes verification."""
        protocol = CrossVerificationProtocol()
        result = protocol.verify_navier_stokes()
        
        assert 'status' in result
        assert 'euler_correspondence' in result
        assert result['eigenvalue'] == 0.5772
        assert result['euler_correspondence'] is True
        assert result['status'] == 'verified'
    
    def test_verify_ramsey(self):
        """Test Ramsey verification."""
        protocol = CrossVerificationProtocol()
        result = protocol.verify_ramsey()
        
        assert 'status' in result
        assert 'ratio_valid' in result
        assert 'connection_count' in result
        assert result['ratio_valid'] is True
        assert result['status'] == 'verified'
    
    def test_build_consistency_matrix(self):
        """Test consistency matrix construction."""
        protocol = CrossVerificationProtocol()
        
        individual_results = {
            'p_vs_np': protocol.verify_p_vs_np(),
            'riemann': protocol.verify_riemann(),
            'bsd': protocol.verify_bsd(),
            'navier_stokes': protocol.verify_navier_stokes(),
            'ramsey': protocol.verify_ramsey()
        }
        
        matrix = protocol.build_consistency_matrix(individual_results)
        
        assert matrix.shape == (5, 5)
        assert np.all(matrix >= 0)
        assert np.all(matrix <= 1)
        assert np.all(np.diag(matrix) == 1)  # Diagonal should be 1
    
    def test_verify_qcal_coherence(self):
        """Test QCAL coherence verification."""
        protocol = CrossVerificationProtocol()
        
        matrix = np.ones((5, 5))  # Perfect consistency
        coherence = protocol.verify_qcal_coherence(matrix)
        
        assert 'constant_coherence' in coherence
        assert 'operator_commutativity' in coherence
        assert 'matrix_connectivity' in coherence
        assert 'overall_coherence_score' in coherence
        assert 'coherence_verified' in coherence
        
        assert coherence['constant_coherence'] is True
        assert coherence['overall_coherence_score'] == 1.0
    
    def test_run_cross_verification(self):
        """Test complete cross-verification."""
        protocol = CrossVerificationProtocol()
        results = protocol.run_cross_verification()
        
        assert 'individual_results' in results
        assert 'consistency_matrix' in results
        assert 'qcal_coherence' in results
        assert 'unified_status' in results
        assert 'summary' in results
        
        # Check all problems verified
        individual = results['individual_results']
        assert all(r['status'] == 'verified' for r in individual.values())
        
        # Check summary
        summary = results['summary']
        assert summary['problems_verified'] == summary['total_problems']
        assert summary['coherence_score'] == 1.0
        
        # Unified status should be True
        assert results['unified_status'] == True


class TestIntegration:
    """Integration tests for complete QCAL framework."""
    
    def test_full_workflow(self):
        """Test complete workflow from constants to verification."""
        # Step 1: Get constants
        constants = get_unified_constants()
        assert verify_universal_coherence()
        
        # Step 2: Initialize framework
        framework = QCALUnifiedFramework()
        assert framework.calculate_coherence_score() == 1.0
        
        # Step 3: Demonstrate unification
        results = framework.demonstrate_unification()
        assert len(results) == 5
        
        # Step 4: Cross-verification
        protocol = CrossVerificationProtocol()
        verification = protocol.run_cross_verification()
        assert verification['unified_status'] == True
    
    def test_consistency(self):
        """Test consistency across all components."""
        framework = QCALUnifiedFramework()
        protocol = CrossVerificationProtocol()
        
        # Constants should match
        assert framework.constants.kappa_pi == protocol.framework.constants.kappa_pi
        assert framework.constants.f0 == protocol.framework.constants.f0
        
        # Coherence should match
        assert framework.calculate_coherence_score() == 1.0
        
        # Verification should succeed
        results = protocol.run_cross_verification()
        assert results['unified_status'] == True


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
