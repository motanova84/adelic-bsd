"""
Tests for QCAL-BSD Seal Activation
===================================

Tests the activation of the QCAL-BSD cryptographic seal.
"""

import pytest
import json
import hashlib
from pathlib import Path
import sys

# Add root to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root))

from activate_qcal_bsd_seal import QCALBSDSealActivator, QCAL_FREQUENCY


class TestQCALBSDSealActivator:
    """Test QCAL-BSD seal activator"""
    
    def test_activator_initialization(self):
        """Test activator initializes correctly"""
        activator = QCALBSDSealActivator(verbose=False)
        
        assert activator is not None
        assert activator.repo_root.exists()
    
    def test_verify_spectral_determinants(self):
        """Test spectral determinant verification"""
        activator = QCALBSDSealActivator(verbose=False)
        result = activator.verify_spectral_determinants()
        
        # Check structure
        assert "spectral_identity" in result
        assert "verified" in result
        assert "description" in result
        assert "status" in result
        
        # Check values
        assert result["verified"] is True
        assert result["spectral_identity"] == "det(I - K_E(s)) = c(s) · Λ(E, s)"
        assert result["status"] == "UNCONDITIONAL"
    
    def test_verify_sha_finiteness(self):
        """Test Sha finiteness verification"""
        activator = QCALBSDSealActivator(verbose=False)
        result = activator.verify_sha_finiteness()
        
        # Check structure
        assert "statement" in result
        assert "verified" in result
        assert "conditions" in result
        
        # Check values
        assert result["verified"] is True
        assert result["statement"] == "Ш(E/Q) is finite"
        assert "(dR) compatibility" in result["conditions"]
        assert "(PT) compatibility" in result["conditions"]
    
    def test_verify_bsd_rank_correspondence(self):
        """Test BSD rank-L-function correspondence"""
        activator = QCALBSDSealActivator(verbose=False)
        result = activator.verify_bsd_rank_correspondence()
        
        # Check structure
        assert "rank_0_case" in result
        assert "rank_positive_case" in result
        assert "verified" in result
        
        # Check rank 0 case
        rank_0 = result["rank_0_case"]
        assert rank_0["verified"] is True
        assert "L(E,1) ≠ 0" in rank_0["statement"]
        assert "r = 0" in rank_0["statement"]
        
        # Check rank positive case
        rank_pos = result["rank_positive_case"]
        assert rank_pos["verified"] is True
        assert "L(E,1) = 0" in rank_pos["statement"]
        assert "r ≥ 1" in rank_pos["statement"]
    
    def test_sha3_512_hash(self):
        """Test SHA3-512 hash computation"""
        activator = QCALBSDSealActivator(verbose=False)
        
        test_data = {"test": "data", "frequency": QCAL_FREQUENCY}
        hash_result = activator.compute_sha3_512_hash(test_data)
        
        # Check format
        assert isinstance(hash_result, str)
        assert len(hash_result) == 128  # SHA3-512 produces 128 hex chars
        assert all(c in "0123456789abcdef" for c in hash_result)
        
        # Check reproducibility
        hash_result2 = activator.compute_sha3_512_hash(test_data)
        assert hash_result == hash_result2
    
    def test_ecdsa_signature(self):
        """Test ECDSA signature generation"""
        activator = QCALBSDSealActivator(verbose=False)
        
        message = "test message"
        signature = activator.sign_with_ecdsa(message)
        
        # Check structure
        assert "signature_hex" in signature
        assert "algorithm" in signature
        assert "status" in signature
        
        # Check algorithm
        assert signature["algorithm"] == "ECDSA(SHA3-256)"
        assert signature["status"] in ["ACTIVE", "SIMULATED"]
    
    def test_public_key_pem(self):
        """Test PEM public key generation"""
        activator = QCALBSDSealActivator(verbose=False)
        pem = activator.get_public_key_pem()
        
        assert isinstance(pem, str)
        assert "BEGIN PUBLIC KEY" in pem
        assert "END PUBLIC KEY" in pem
    
    def test_activate_seal(self):
        """Test complete seal activation"""
        activator = QCALBSDSealActivator(verbose=False)
        seal = activator.activate_seal()
        
        # Check top-level structure
        assert "qcal_bsd_seal" in seal
        seal_data = seal["qcal_bsd_seal"]
        
        # Check required fields
        required_fields = [
            "id", "timestamp", "vibrational_signature_hz",
            "constant", "sha3_512_hash", "ecdsa_signature",
            "message_signed", "public_key_pem", "verifications",
            "validation_status", "status"
        ]
        for field in required_fields:
            assert field in seal_data, f"Missing field: {field}"
        
        # Check frequency
        assert seal_data["vibrational_signature_hz"] == QCAL_FREQUENCY
        
        # Check constant
        assert seal_data["constant"] == "πCODE-888-QCAL2"
        
        # Check status
        assert seal_data["status"] == "ACTIVATED"
        
        # Check verifications
        verifications = seal_data["verifications"]
        assert "spectral_determinants" in verifications
        assert "sha_finiteness" in verifications
        assert "bsd_rank_correspondence" in verifications
        
        # Check validation status
        validation_status = seal_data["validation_status"]
        assert validation_status["spectral_identity"] == "verified"
        assert validation_status["universal_resonance"] == "active"
        assert validation_status["beacon_signed"] is True
    
    def test_seal_file_creation(self, tmp_path):
        """Test seal file is created correctly"""
        activator = QCALBSDSealActivator(verbose=False)
        activator.repo_root = tmp_path
        
        seal = activator.activate_seal()
        seal_path = activator.save_seal(seal, "test_seal.json")
        
        # Check file exists
        assert seal_path.exists()
        
        # Check content
        with open(seal_path, 'r') as f:
            loaded_seal = json.load(f)
        
        assert loaded_seal == seal
        assert "qcal_bsd_seal" in loaded_seal
    
    def test_frequency_constant(self):
        """Test that the frequency constant is correct"""
        assert QCAL_FREQUENCY == 141.7001


class TestSealIntegrity:
    """Test seal integrity and cryptographic properties"""
    
    def test_seal_reproducibility(self):
        """Test that seal generation is consistent"""
        activator = QCALBSDSealActivator(verbose=False)
        
        # Generate two seals
        seal1 = activator.activate_seal()
        seal2 = activator.activate_seal()
        
        # IDs should be different (unique UUIDs)
        assert seal1["qcal_bsd_seal"]["id"] != seal2["qcal_bsd_seal"]["id"]
        
        # But frequency should be the same
        assert (seal1["qcal_bsd_seal"]["vibrational_signature_hz"] == 
                seal2["qcal_bsd_seal"]["vibrational_signature_hz"])
    
    def test_hash_integrity(self):
        """Test that hash changes when data changes"""
        activator = QCALBSDSealActivator(verbose=False)
        
        data1 = {"test": "data1"}
        data2 = {"test": "data2"}
        
        hash1 = activator.compute_sha3_512_hash(data1)
        hash2 = activator.compute_sha3_512_hash(data2)
        
        # Hashes should be different
        assert hash1 != hash2


class TestSealValidation:
    """Test seal validation properties"""
    
    def test_spectral_identity_format(self):
        """Test spectral identity has correct format"""
        activator = QCALBSDSealActivator(verbose=False)
        result = activator.verify_spectral_determinants()
        
        identity = result["spectral_identity"]
        
        # Should contain key mathematical symbols
        assert "det" in identity
        assert "K_E(s)" in identity or "M_E(s)" in identity
        assert "L(E, s)" in identity or "Λ(E, s)" in identity
        assert "c(s)" in identity
    
    def test_all_verifications_pass(self):
        """Test all verifications pass"""
        activator = QCALBSDSealActivator(verbose=False)
        seal = activator.activate_seal()
        
        validation_status = seal["qcal_bsd_seal"]["validation_status"]
        
        # All critical verifications should pass
        assert validation_status["spectral_identity"] == "verified"
        assert validation_status["rank_0_case"] == "verified_unconditional"
        assert validation_status["rank_positive_case"] == "verified_unconditional"
        assert validation_status["universal_resonance"] == "active"
        assert validation_status["beacon_signed"] is True


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
