"""
Tests for BSD–Yang–Mills–QCAL ∞³ expansion module.

Validates all components of the expansion:
- Spectral trace validation
- NFT/ERC721A contract generation
- DAO signature module
- Correspondence seal issuance

Author: Adelic-BSD Framework
Date: February 2026
"""

import pytest
import json
from pathlib import Path
import sys

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from bsd_yang_mills_expansion import (
    SpectralTraceValidator,
    CurveNFTContract,
    DAOSignatureModule,
    CorrespondenceSeal,
    EXPANSION_CURVES,
    QCAL_FREQUENCY,
)


class TestSpectralTraceValidator:
    """Tests for spectral trace validation."""
    
    def test_validator_initialization(self):
        """Test validator can be initialized."""
        curve = EXPANSION_CURVES[0]
        validator = SpectralTraceValidator(curve)
        assert validator.label == curve['label']
        assert validator.curve == curve
    
    def test_compute_spectral_trace(self):
        """Test spectral trace computation."""
        curve = EXPANSION_CURVES[0]
        validator = SpectralTraceValidator(curve)
        trace = validator.compute_spectral_trace(n_modes=10)
        assert isinstance(trace, float)
        assert trace > 0  # Trace should be positive
    
    def test_compute_l_function_inverse(self):
        """Test L-function inverse computation."""
        curve = EXPANSION_CURVES[0]
        validator = SpectralTraceValidator(curve)
        l_inv = validator.compute_l_function_inverse()
        assert isinstance(l_inv, float)
        assert l_inv > 0 or l_inv == float('inf')
    
    def test_validate_trace_identity(self):
        """Test trace identity validation."""
        curve = EXPANSION_CURVES[0]
        validator = SpectralTraceValidator(curve)
        result = validator.validate_trace_identity(tolerance=0.5)
        
        assert 'curve_label' in result
        assert 'spectral_trace' in result
        assert 'l_function_inverse' in result
        assert 'relative_error' in result
        assert 'validated' in result
        assert 'status' in result
        
        assert result['curve_label'] == curve['label']
        assert isinstance(result['validated'], bool)
    
    def test_all_expansion_curves(self):
        """Test validation works for all expansion curves."""
        for curve in EXPANSION_CURVES:
            validator = SpectralTraceValidator(curve)
            result = validator.validate_trace_identity(tolerance=0.5)
            assert result['status'] in ['VALIDATED', 'MISMATCH']


class TestCurveNFTContract:
    """Tests for NFT contract generation."""
    
    def test_contract_initialization(self):
        """Test contract can be initialized."""
        curve = EXPANSION_CURVES[0]
        contract = CurveNFTContract(curve)
        assert contract.label == curve['label']
        assert contract.security_level == 256
        assert contract.contract_private_key is not None
        assert contract.contract_public_key is not None
    
    def test_mint_curve_nft(self):
        """Test NFT minting."""
        curve = EXPANSION_CURVES[0]
        contract = CurveNFTContract(curve)
        
        # Create owner keypair
        from postquantum_blockchain import PostQuantumSignature
        pq_sig = PostQuantumSignature()
        _, owner_public = pq_sig.generate_keypair()
        
        # Mint NFT
        nft = contract.mint_curve_nft(owner_public)
        
        assert 'nft_hash' in nft
        assert 'metadata' in nft
        assert 'transaction' in nft
        assert 'contract_address' in nft
        assert nft['minted'] is True
        
        # Check metadata
        metadata = nft['metadata']
        assert metadata['name'] == f'BSD Curve {curve["label"]}'
        assert metadata['standard'] == 'ERC721A-Compatible'
        assert metadata['quantum_resistant'] is True
    
    def test_generate_contract_abi(self):
        """Test ABI generation."""
        curve = EXPANSION_CURVES[0]
        contract = CurveNFTContract(curve)
        abi = contract.generate_contract_abi()
        
        assert abi['contract_name'] == f'BSDCurve{curve["label"]}'
        assert abi['standard'] == 'ERC721A'
        assert abi['quantum_resistant'] is True
        assert 'methods' in abi
        assert len(abi['methods']) >= 2  # mint and validate
        assert 'curve_metadata' in abi


class TestDAOSignatureModule:
    """Tests for DAO signature module."""
    
    def test_dao_initialization(self):
        """Test DAO module initialization."""
        dao = DAOSignatureModule(EXPANSION_CURVES)
        assert len(dao.curves) == 3
        assert dao.security_level == 256
        assert dao.dao_private_key is not None
        assert dao.dao_public_key is not None
    
    def test_compute_global_coherence(self):
        """Test global coherence computation."""
        dao = DAOSignatureModule(EXPANSION_CURVES)
        coherence = dao.compute_global_coherence()
        
        assert isinstance(coherence, float)
        assert 0.0 <= coherence <= 1.0
        # Should be average of all resonances
        expected = sum(c['qcal_resonance'] for c in EXPANSION_CURVES) / len(EXPANSION_CURVES)
        assert abs(coherence - expected) < 1e-6
    
    def test_validate_dao_requirements(self):
        """Test DAO requirements validation."""
        dao = DAOSignatureModule(EXPANSION_CURVES)
        validation = dao.validate_dao_requirements()
        
        assert 'coherence' in validation
        assert 'coherence_threshold' in validation
        assert 'coherence_valid' in validation
        assert 'frequency' in validation
        assert 'frequency_target' in validation
        assert 'frequency_valid' in validation
        assert 'all_requirements_met' in validation
        
        # Check coherence threshold
        assert validation['coherence_threshold'] == 0.888
        assert validation['frequency_target'] == 141.7001
        
        # With our selected curves, coherence should be >= 0.888
        assert validation['coherence'] >= 0.888
        assert validation['coherence_valid'] is True
    
    def test_sign_module(self):
        """Test module signing."""
        dao = DAOSignatureModule(EXPANSION_CURVES)
        signature = dao.sign_module()
        
        assert 'payload' in signature
        assert 'signature' in signature
        assert 'public_key' in signature
        assert signature['signed'] is True
        assert signature['dao_identifier'] == '∴DAO-QCAL-∞³'
        
        # Check payload
        payload = signature['payload']
        assert payload['module'] == 'BSD-Yang-Mills-QCAL-∞³'
        assert len(payload['curves']) == 3
        assert payload['frequency_hz'] == QCAL_FREQUENCY


class TestCorrespondenceSeal:
    """Tests for correspondence seal."""
    
    def test_seal_initialization(self):
        """Test seal initialization."""
        test_data = {'test': 'data'}
        seal_gen = CorrespondenceSeal(test_data)
        assert seal_gen.data == test_data
    
    def test_generate_seal(self):
        """Test seal generation."""
        # Create minimal expansion data
        expansion_data = {
            'curves': EXPANSION_CURVES,
            'trace_validations': [
                {'validated': True},
                {'validated': True},
                {'validated': True},
            ],
            'nft_contracts': [1, 2, 3],
            'dao_signature': {'signed': True},
        }
        
        seal_gen = CorrespondenceSeal(expansion_data)
        seal = seal_gen.generate_seal()
        
        assert 'title' in seal
        assert seal['title'] == 'BSD/QCAL ∞³ Correspondence Seal'
        assert 'version' in seal
        assert 'timestamp' in seal
        assert 'seal_hash' in seal
        assert 'signature' in seal
        assert 'frequency_hz' in seal
        assert seal['frequency_hz'] == QCAL_FREQUENCY
        
        # Check expansion summary
        summary = seal['expansion_summary']
        assert summary['curves_added'] == 3
        assert summary['all_traces_validated'] is True
        assert summary['nfts_minted'] == 3
        assert summary['dao_signed'] is True
    
    def test_export_seal(self, tmp_path):
        """Test seal export."""
        expansion_data = {
            'curves': EXPANSION_CURVES,
            'trace_validations': [],
            'nft_contracts': [],
            'dao_signature': {'signed': True},
        }
        
        seal_gen = CorrespondenceSeal(expansion_data)
        output_path = tmp_path / 'test_seal.json'
        result_path = seal_gen.export_seal(output_path)
        
        assert result_path == output_path
        assert output_path.exists()
        
        # Verify file contents
        with open(output_path) as f:
            seal = json.load(f)
        assert 'seal_hash' in seal
        assert 'signature' in seal


class TestExpansionCurves:
    """Tests for expansion curve selection."""
    
    def test_expansion_curves_count(self):
        """Test we have exactly 3 curves."""
        assert len(EXPANSION_CURVES) == 3
    
    def test_curve_properties(self):
        """Test all curves have required properties."""
        required_fields = [
            'label', 'conductor', 'rank', 'j_invariant',
            'discriminant', 'variety', 'qcal_resonance',
            'torsion_order', 'regulator', 'omega_plus'
        ]
        
        for curve in EXPANSION_CURVES:
            for field in required_fields:
                assert field in curve, f"Curve {curve.get('label')} missing {field}"
    
    def test_low_conductor(self):
        """Test all curves have low conductor (< 10000)."""
        for curve in EXPANSION_CURVES:
            assert curve['conductor'] < 10000
    
    def test_qcal_resonance(self):
        """Test all curves have QCAL resonance >= 0.888."""
        for curve in EXPANSION_CURVES:
            assert curve['qcal_resonance'] >= 0.888
    
    def test_arithmetic_variety(self):
        """Test all curves have prime discriminant variety."""
        for curve in EXPANSION_CURVES:
            assert curve['variety'] == 'prime_discriminant'
    
    def test_rank_diversity(self):
        """Test curves have diverse ranks."""
        ranks = [curve['rank'] for curve in EXPANSION_CURVES]
        assert len(set(ranks)) >= 2  # At least 2 different ranks


class TestFrequencyConstant:
    """Tests for frequency constant."""
    
    def test_qcal_frequency_value(self):
        """Test QCAL frequency is correct."""
        assert QCAL_FREQUENCY == 141.7001
    
    def test_frequency_in_all_components(self):
        """Test frequency is used consistently."""
        # Create validator
        validator = SpectralTraceValidator(EXPANSION_CURVES[0])
        
        # Create DAO module
        dao = DAOSignatureModule(EXPANSION_CURVES)
        validation = dao.validate_dao_requirements()
        
        assert validation['frequency'] == QCAL_FREQUENCY
        assert validation['frequency_target'] == 141.7001


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
