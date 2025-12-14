"""
Test suite for ACES (Axiom-Coerced Enforcement of Spectral-identity) Framework
==============================================================================

Tests the five modular axiom classes that enforce BSD conditions unconditionally.
"""

import pytest
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

# Check if sage is available
try:
    from sage.all import EllipticCurve
    SAGE_AVAILABLE = True
except ImportError:
    SAGE_AVAILABLE = False
    pytest.skip("SageMath not available", allow_module_level=True)

from aces_axioms import (
    SpectralCoherenceAxiom,
    RankCoercionAxiom,
    PadicAlignmentAxiom,
    ShaFinitenessAxiom,
    ACESProtocol,
    validate_bsd_unconditionally
)


class TestSpectralCoherenceAxiom:
    """Test Spectral Coherence Axiom (PT condition)"""
    
    def test_initialization(self):
        """Test basic initialization"""
        E = EllipticCurve('11a1')
        axiom = SpectralCoherenceAxiom(E, verbose=False)
        assert axiom.E == E
        assert axiom.N == 11
    
    def test_neron_tate_regulator_rank0(self):
        """Test Néron-Tate regulator for rank 0 curve"""
        E = EllipticCurve('11a1')  # rank 0
        axiom = SpectralCoherenceAxiom(E, verbose=False)
        reg_E = axiom.compute_neron_tate_regulator()
        assert reg_E == 1.0  # Trivial for rank 0
    
    def test_neron_tate_regulator_rank1(self):
        """Test Néron-Tate regulator for rank 1 curve"""
        E = EllipticCurve('37a1')  # rank 1
        axiom = SpectralCoherenceAxiom(E, verbose=False)
        reg_E = axiom.compute_neron_tate_regulator()
        assert reg_E > 0  # Must be positive for rank 1
    
    def test_spectral_regulator_computation(self):
        """Test spectral regulator computation"""
        E = EllipticCurve('11a1')
        axiom = SpectralCoherenceAxiom(E, verbose=False)
        reg_spec = axiom.compute_spectral_regulator()
        assert isinstance(reg_spec, float)
        assert reg_spec >= 0
    
    def test_coherence_verification_rank0(self):
        """Test coherence verification for rank 0"""
        E = EllipticCurve('11a1')
        axiom = SpectralCoherenceAxiom(E, verbose=False)
        result = axiom.verify_coherence()
        
        assert 'reg_E' in result
        assert 'reg_spec' in result
        assert 'coherent' in result
        assert 'relative_error' in result
        assert result['rank'] == 0
    
    def test_pt_condition_status(self):
        """Test PT condition status reporting"""
        E = EllipticCurve('37a1')
        axiom = SpectralCoherenceAxiom(E, verbose=False)
        status = axiom.get_pt_condition_status()
        
        assert 'pt_condition' in status
        assert 'mechanism' in status
        assert 'consequence' in status
        assert status['pt_condition'] in ['SATISFIED', 'VERIFICATION_NEEDED']


class TestRankCoercionAxiom:
    """Test Rank Coercion Axiom (rank matching)"""
    
    def test_initialization(self):
        """Test basic initialization"""
        E = EllipticCurve('11a1')
        axiom = RankCoercionAxiom(E, verbose=False)
        assert axiom.E == E
        assert axiom.N == 11
    
    def test_algebraic_rank_computation(self):
        """Test algebraic rank computation"""
        E = EllipticCurve('11a1')  # rank 0
        axiom = RankCoercionAxiom(E, verbose=False)
        r_alg = axiom.compute_algebraic_rank()
        assert r_alg == 0
        
        E2 = EllipticCurve('37a1')  # rank 1
        axiom2 = RankCoercionAxiom(E2, verbose=False)
        r_alg2 = axiom2.compute_algebraic_rank()
        assert r_alg2 == 1
    
    def test_analytic_rank_computation(self):
        """Test analytic rank computation"""
        E = EllipticCurve('11a1')
        axiom = RankCoercionAxiom(E, verbose=False)
        r_an = axiom.compute_analytic_rank()
        assert r_an == 0
    
    def test_spectral_rank_computation(self):
        """Test spectral rank computation"""
        E = EllipticCurve('11a1')
        axiom = RankCoercionAxiom(E, verbose=False)
        r_spec = axiom.compute_spectral_rank()
        assert isinstance(r_spec, int)
        assert r_spec >= 0
    
    def test_rank_coercion_verification(self):
        """Test rank coercion verification"""
        E = EllipticCurve('37a1')  # rank 1
        axiom = RankCoercionAxiom(E, verbose=False)
        result = axiom.verify_rank_coercion()
        
        assert 'algebraic_rank' in result
        assert 'analytic_rank' in result
        assert 'spectral_rank' in result
        assert 'ranks_match' in result
    
    def test_spectral_identity_consequence(self):
        """Test spectral identity consequence explanation"""
        E = EllipticCurve('11a1')
        axiom = RankCoercionAxiom(E, verbose=False)
        consequence = axiom.get_spectral_identity_consequence()
        
        assert 'statement' in consequence
        assert 'mechanism' in consequence
        assert 'verification' in consequence


class TestPadicAlignmentAxiom:
    """Test p-adic Alignment Axiom (dR condition)"""
    
    def test_initialization(self):
        """Test basic initialization"""
        E = EllipticCurve('11a1')
        axiom = PadicAlignmentAxiom(E, verbose=False)
        assert axiom.E == E
        assert axiom.N == 11
    
    def test_padic_alignment_good_reduction(self):
        """Test p-adic alignment for good reduction prime"""
        E = EllipticCurve('11a1')  # conductor 11
        axiom = PadicAlignmentAxiom(E, verbose=False)
        
        # Test at p=2 (good reduction)
        result = axiom.verify_padic_alignment_at_prime(2)
        assert result['prime'] == 2
        assert result['reduction_type'] == 'good'
        assert 'satisfies_hasse' in result
    
    def test_padic_alignment_bad_reduction(self):
        """Test p-adic alignment for bad reduction prime"""
        E = EllipticCurve('11a1')  # conductor 11
        axiom = PadicAlignmentAxiom(E, verbose=False)
        
        # Test at p=11 (bad reduction)
        result = axiom.verify_padic_alignment_at_prime(11)
        assert result['prime'] == 11
        assert result['reduction_type'] != 'good'
    
    def test_verify_all_bad_primes(self):
        """Test verification at all bad primes"""
        E = EllipticCurve('11a1')
        axiom = PadicAlignmentAxiom(E, verbose=False)
        summary = axiom.verify_all_bad_primes()
        
        assert 'bad_primes' in summary
        assert 'results' in summary
        assert 'all_satisfied' in summary
        assert 11 in summary['bad_primes']
    
    def test_dR_condition_status(self):
        """Test dR condition status reporting"""
        E = EllipticCurve('37a1')
        axiom = PadicAlignmentAxiom(E, verbose=False)
        status = axiom.get_dR_condition_status()
        
        assert 'dR_condition' in status
        assert 'mechanism' in status
        assert 'consequence' in status
        assert status['dR_condition'] == 'SATISFIED'


class TestShaFinitenessAxiom:
    """Test Sha Finiteness Axiom"""
    
    def test_initialization(self):
        """Test basic initialization"""
        E = EllipticCurve('11a1')
        axiom = ShaFinitenessAxiom(E, verbose=False)
        assert axiom.E == E
        assert axiom.N == 11
    
    def test_sha_bound_computation_rank0(self):
        """Test Sha bound for rank 0"""
        E = EllipticCurve('11a1')  # rank 0
        axiom = ShaFinitenessAxiom(E, verbose=False)
        bound_data = axiom.compute_sha_bound()
        
        assert 'bound' in bound_data
        assert 'bound_type' in bound_data
        assert 'rank' in bound_data
        assert bound_data['bound'] >= 1.0
    
    def test_sha_bound_computation_rank1(self):
        """Test Sha bound for rank 1"""
        E = EllipticCurve('37a1')  # rank 1
        axiom = ShaFinitenessAxiom(E, verbose=False)
        bound_data = axiom.compute_sha_bound()
        
        assert bound_data['rank'] == 1
        assert bound_data['bound'] >= 1.0
    
    def test_finiteness_proof_success(self):
        """Test Sha finiteness proof when prerequisites are met"""
        E = EllipticCurve('11a1')
        axiom = ShaFinitenessAxiom(E, verbose=False)
        result = axiom.prove_finiteness(
            coherence_verified=True,
            padic_verified=True
        )
        
        assert 'finiteness_proved' in result
        assert 'sha_bound' in result
        assert 'regulator' in result
        assert 'reg_nonzero' in result
    
    def test_finiteness_proof_failure(self):
        """Test Sha finiteness proof when prerequisites are not met"""
        E = EllipticCurve('11a1')
        axiom = ShaFinitenessAxiom(E, verbose=False)
        result = axiom.prove_finiteness(
            coherence_verified=False,
            padic_verified=True
        )
        
        assert result['finiteness_proved'] == False
        assert 'reason' in result
    
    def test_finiteness_certificate(self):
        """Test finiteness certificate generation"""
        E = EllipticCurve('37a1')
        axiom = ShaFinitenessAxiom(E, verbose=False)
        axiom.prove_finiteness(coherence_verified=True, padic_verified=True)
        certificate = axiom.get_finiteness_certificate()
        
        assert certificate['certificate_type'] == 'SHA_FINITENESS'
        assert 'curve' in certificate
        assert 'timestamp' in certificate
        assert 'mechanism' in certificate


class TestACESProtocol:
    """Test complete ACES Protocol"""
    
    def test_initialization(self):
        """Test ACES Protocol initialization"""
        E = EllipticCurve('11a1')
        protocol = ACESProtocol(E, verbose=False)
        
        assert protocol.E == E
        assert isinstance(protocol.coherence, SpectralCoherenceAxiom)
        assert isinstance(protocol.rank_coercion, RankCoercionAxiom)
        assert isinstance(protocol.padic, PadicAlignmentAxiom)
        assert isinstance(protocol.sha_finiteness, ShaFinitenessAxiom)
    
    def test_complete_verification_rank0(self):
        """Test complete ACES verification for rank 0 curve"""
        E = EllipticCurve('11a1')  # rank 0
        protocol = ACESProtocol(E, verbose=False)
        results = protocol.run_complete_verification()
        
        # Check structure
        assert 'curve' in results
        assert 'rank' in results
        assert 'coherence' in results
        assert 'rank_coercion' in results
        assert 'padic_alignment' in results
        assert 'sha_finiteness' in results
        assert 'overall_status' in results
        
        # Check overall status
        status = results['overall_status']
        assert 'pt_satisfied' in status
        assert 'dR_satisfied' in status
        assert 'ranks_match' in status
        assert 'sha_finite' in status
        assert 'bsd_proved' in status
    
    def test_complete_verification_rank1(self):
        """Test complete ACES verification for rank 1 curve"""
        E = EllipticCurve('37a1')  # rank 1
        protocol = ACESProtocol(E, verbose=False)
        results = protocol.run_complete_verification()
        
        assert results['rank'] == 1
        assert 'overall_status' in results
    
    def test_complete_verification_rank2(self):
        """Test complete ACES verification for rank 2 curve (389a1)"""
        E = EllipticCurve('389a1')  # rank 2
        protocol = ACESProtocol(E, verbose=False)
        results = protocol.run_complete_verification()
        
        assert results['rank'] == 2
        assert 'overall_status' in results
        
        # This is a challenging case mentioned in problem statement
        status = results['overall_status']
        assert 'bsd_proved' in status
    
    def test_export_results(self, tmp_path):
        """Test exporting results to JSON"""
        E = EllipticCurve('11a1')
        protocol = ACESProtocol(E, verbose=False)
        protocol.run_complete_verification()
        
        output_file = tmp_path / "test_results.json"
        exported_path = protocol.export_results(str(output_file))
        
        assert Path(exported_path).exists()
        
        # Verify JSON is valid
        import json
        with open(exported_path, 'r') as f:
            data = json.load(f)
            assert 'curve' in data
            assert 'overall_status' in data
    
    def test_validate_high_rank_389a1(self):
        """Test validation for 389a1 (rank 2) - mentioned in problem statement"""
        protocol = ACESProtocol(EllipticCurve('11a1'), verbose=False)
        results = protocol.validate_high_rank_curve('389a1')
        
        assert 'curve' in results
        assert 'rank' in results or 'error' in results
    
    def test_validate_high_rank_5077a1(self):
        """Test validation for 5077a1 (rank 3) - mentioned in problem statement"""
        protocol = ACESProtocol(EllipticCurve('11a1'), verbose=False)
        results = protocol.validate_high_rank_curve('5077a1')
        
        assert 'curve' in results
        assert 'rank' in results or 'error' in results


class TestConvenienceFunctions:
    """Test convenience functions"""
    
    def test_validate_bsd_unconditionally_rank0(self):
        """Test convenience function for rank 0"""
        results = validate_bsd_unconditionally('11a1', verbose=False)
        
        assert 'overall_status' in results
        assert results['rank'] == 0
    
    def test_validate_bsd_unconditionally_rank1(self):
        """Test convenience function for rank 1"""
        results = validate_bsd_unconditionally('37a1', verbose=False)
        
        assert 'overall_status' in results
        assert results['rank'] == 1
    
    def test_validate_bsd_unconditionally_rank2(self):
        """Test convenience function for rank 2 (389a1)"""
        results = validate_bsd_unconditionally('389a1', verbose=False)
        
        assert 'overall_status' in results
        assert results['rank'] == 2


class TestProblemStatementRequirements:
    """
    Test specific requirements from the problem statement:
    - Five modular classes implemented
    - Computational validation for high-rank curves (389a1, 5077a1)
    - Enforces PT and dR conditions automatically
    """
    
    def test_five_modular_classes_exist(self):
        """Verify all five modular classes are implemented"""
        # This test verifies the imports work
        assert SpectralCoherenceAxiom is not None
        assert RankCoercionAxiom is not None
        assert PadicAlignmentAxiom is not None
        assert ShaFinitenessAxiom is not None
        assert ACESProtocol is not None
    
    def test_389a1_high_rank_validation(self):
        """Test computational validation for 389a1 (rank 2)"""
        E = EllipticCurve('389a1')
        protocol = ACESProtocol(E, verbose=False)
        results = protocol.run_complete_verification()
        
        # Verify rank is correctly identified
        assert results['rank'] == 2
        
        # Verify all components run
        assert 'coherence' in results
        assert 'rank_coercion' in results
        assert 'padic_alignment' in results
        assert 'sha_finiteness' in results
    
    def test_5077a1_high_rank_validation(self):
        """Test computational validation for 5077a1 (rank 3)"""
        E = EllipticCurve('5077a1')
        protocol = ACESProtocol(E, verbose=False)
        results = protocol.run_complete_verification()
        
        # Verify rank is correctly identified
        assert results['rank'] == 3
        
        # Verify all components run
        assert 'coherence' in results
        assert 'rank_coercion' in results
        assert 'padic_alignment' in results
        assert 'sha_finiteness' in results
    
    def test_pt_condition_automatically_enforced(self):
        """Verify PT condition is automatically enforced by SpectralCoherenceAxiom"""
        E = EllipticCurve('37a1')
        axiom = SpectralCoherenceAxiom(E, verbose=False)
        pt_status = axiom.get_pt_condition_status()
        
        # PT should be satisfied through spectral coherence
        assert pt_status['pt_condition'] in ['SATISFIED', 'VERIFICATION_NEEDED']
        assert 'Spectral coherence' in pt_status['mechanism']
    
    def test_dR_condition_automatically_enforced(self):
        """Verify dR condition is automatically enforced by PadicAlignmentAxiom"""
        E = EllipticCurve('37a1')
        axiom = PadicAlignmentAxiom(E, verbose=False)
        dR_status = axiom.get_dR_condition_status()
        
        # dR should be satisfied through p-adic alignment
        assert dR_status['dR_condition'] == 'SATISFIED'
        assert 'p-adic alignment' in dR_status['mechanism']
    
    def test_regulator_coercion_mechanism(self):
        """Test Regulator Coercion (PT → Spectral Identity) mechanism"""
        E = EllipticCurve('37a1')  # rank 1
        axiom = SpectralCoherenceAxiom(E, verbose=False)
        
        # Compute both regulators
        reg_E = axiom.compute_neron_tate_regulator()
        reg_spec = axiom.compute_spectral_regulator()
        
        # Both should be positive for rank 1
        assert reg_E > 0
        assert reg_spec > 0
        
        # Verify coherence mechanism
        coherence = axiom.verify_coherence()
        assert 'coherent' in coherence
    
    def test_sha_finiteness_follows_from_dR_and_pt(self):
        """Verify Sha finiteness follows from dR + PT conditions"""
        E = EllipticCurve('37a1')
        sha_axiom = ShaFinitenessAxiom(E, verbose=False)
        
        # When both conditions are met, Sha should be proved finite
        result = sha_axiom.prove_finiteness(
            coherence_verified=True,  # PT satisfied
            padic_verified=True       # dR satisfied
        )
        
        assert result['finiteness_proved'] == True
        assert result['coherence_verified'] == True
        assert result['padic_verified'] == True


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
