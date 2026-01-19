"""
Tests for Cryptographic Validation Module
==========================================

Tests the crypto_validation module including:
- CryptoValidator functionality
- EdDSA signature verification
- Elliptic curve security validation
"""

import pytest
import sys
from pathlib import Path

# Add src to path
src_path = Path(__file__).parent.parent / "src"
if str(src_path) not in sys.path:
    sys.path.insert(0, str(src_path))

from crypto_validation import (
    CryptoValidator,
    EdDSAValidator,
    validate_elliptic_curve_for_crypto
)


class TestCryptoValidator:
    """Test CryptoValidator class"""
    
    def test_initialization(self):
        """Test CryptoValidator initialization"""
        validator = CryptoValidator()
        assert validator is not None
        assert len(validator.STANDARD_CURVES) > 0
        assert 'secp256r1' in validator.STANDARD_CURVES
    
    def test_validate_curve_security_high(self):
        """Test security validation for high-security curve"""
        validator = CryptoValidator()
        
        curve_params = {
            'field_size': 256,
            'order': 2**256 - 2**32 - 977,
            'cofactor': 1,
            'discriminant': 123456
        }
        
        result = validator.validate_curve_security(curve_params)
        
        assert result['is_secure'] is True
        assert result['security_level'] > 0
        assert 'security_rating' in result
        assert 'warnings' in result
        assert 'recommendations' in result
    
    def test_validate_curve_security_low(self):
        """Test security validation for low-security curve"""
        validator = CryptoValidator()
        
        curve_params = {
            'field_size': 128,
            'order': 2**128,
            'cofactor': 1,
            'discriminant': 123
        }
        
        result = validator.validate_curve_security(curve_params)
        
        # Low field size should trigger warnings
        assert len(result['warnings']) > 0
    
    def test_generate_key_pair(self):
        """Test ECDSA key pair generation"""
        validator = CryptoValidator()
        
        private_key, public_key = validator.generate_key_pair('secp256r1')
        
        assert private_key is not None
        assert public_key is not None
    
    def test_sign_and_verify_message(self):
        """Test message signing and verification"""
        validator = CryptoValidator()
        
        # Generate key pair
        private_key, public_key = validator.generate_key_pair('secp256r1')
        
        # Sign message
        message = "Test message for cryptographic validation"
        signature_data = validator.sign_message(message, private_key)
        
        assert 'signature' in signature_data
        assert 'algorithm' in signature_data
        assert signature_data['algorithm'] == 'ECDSA-SHA256'
        
        # Verify signature
        is_valid = validator.verify_signature(
            message,
            signature_data['signature'],
            public_key
        )
        
        assert is_valid is True
    
    def test_verify_invalid_signature(self):
        """Test verification of invalid signature"""
        validator = CryptoValidator()
        
        private_key, public_key = validator.generate_key_pair('secp256r1')
        
        message = "Original message"
        signature_data = validator.sign_message(message, private_key)
        
        # Try to verify with different message
        is_valid = validator.verify_signature(
            "Different message",
            signature_data['signature'],
            public_key
        )
        
        assert is_valid is False
    
    def test_export_public_key(self):
        """Test public key export"""
        validator = CryptoValidator()
        
        _, public_key = validator.generate_key_pair('secp256r1')
        
        pem = validator.export_public_key(public_key, 'pem')
        
        assert pem is not None
        assert '-----BEGIN PUBLIC KEY-----' in pem
        assert '-----END PUBLIC KEY-----' in pem
    
    def test_generate_curve_fingerprint(self):
        """Test curve fingerprint generation"""
        validator = CryptoValidator()
        
        curve_data = {
            'conductor': 11,
            'discriminant': -11,
            'j_invariant': -122023936/161051
        }
        
        fingerprint = validator.generate_curve_fingerprint(curve_data)
        
        assert len(fingerprint) == 64  # SHA-256 hex
        assert all(c in '0123456789abcdef' for c in fingerprint)
    
    def test_fingerprint_consistency(self):
        """Test that fingerprints are consistent"""
        validator = CryptoValidator()
        
        curve_data = {
            'conductor': 37,
            'rank': 1
        }
        
        fp1 = validator.generate_curve_fingerprint(curve_data)
        fp2 = validator.generate_curve_fingerprint(curve_data)
        
        assert fp1 == fp2


class TestEdDSAValidator:
    """Test EdDSAValidator class"""
    
    def test_initialization(self):
        """Test EdDSAValidator initialization"""
        validator = EdDSAValidator()
        assert validator is not None
    
    def test_generate_key_pair(self):
        """Test Ed25519 key pair generation"""
        validator = EdDSAValidator()
        
        private_key, public_key = validator.generate_key_pair()
        
        assert private_key is not None
        assert public_key is not None
    
    def test_sign_and_verify_message(self):
        """Test Ed25519 message signing and verification"""
        validator = EdDSAValidator()
        
        # Generate key pair
        private_key, public_key = validator.generate_key_pair()
        
        # Sign message
        message = "Test message for Ed25519"
        signature_data = validator.sign_message(message, private_key)
        
        assert 'signature' in signature_data
        assert 'algorithm' in signature_data
        assert signature_data['algorithm'] == 'Ed25519'
        
        # Verify signature
        is_valid = validator.verify_signature(
            message,
            signature_data['signature'],
            public_key
        )
        
        assert is_valid is True
    
    def test_verify_invalid_signature(self):
        """Test verification of invalid Ed25519 signature"""
        validator = EdDSAValidator()
        
        private_key, public_key = validator.generate_key_pair()
        
        message = "Original message"
        signature_data = validator.sign_message(message, private_key)
        
        # Try to verify with different message
        is_valid = validator.verify_signature(
            "Different message",
            signature_data['signature'],
            public_key
        )
        
        assert is_valid is False


@pytest.mark.sage_required
class TestValidateEllipticCurveForCrypto:
    """Test elliptic curve validation for cryptographic use"""
    
    def test_validate_curve_11a1(self):
        """Test validation of curve 11a1"""
        result = validate_elliptic_curve_for_crypto('11a1')
        
        # Skip if SageMath not available
        if result['status'] == 'error' and 'SageMath not available' in result.get('message', ''):
            pytest.skip('SageMath not available')
        
        assert result['status'] == 'success'
        assert result['curve_label'] == '11a1'
        assert 'validation' in result
        assert 'curve_params' in result
    
    def test_validate_curve_37a1(self):
        """Test validation of curve 37a1"""
        result = validate_elliptic_curve_for_crypto('37a1')
        
        # Skip if SageMath not available
        if result['status'] == 'error' and 'SageMath not available' in result.get('message', ''):
            pytest.skip('SageMath not available')
        
        assert result['status'] == 'success'
        assert 'validation' in result
        assert 'is_secure' in result['validation']


class TestCryptoIntegration:
    """Integration tests for crypto validation"""
    
    def test_multiple_signatures(self):
        """Test signing multiple messages"""
        validator = CryptoValidator()
        
        private_key, public_key = validator.generate_key_pair('secp256r1')
        
        messages = [
            "Message 1",
            "Message 2",
            "Message 3"
        ]
        
        signatures = []
        for msg in messages:
            sig_data = validator.sign_message(msg, private_key)
            signatures.append(sig_data)
        
        # Verify all signatures
        for i, msg in enumerate(messages):
            is_valid = validator.verify_signature(
                msg,
                signatures[i]['signature'],
                public_key
            )
            assert is_valid is True
    
    def test_cross_validation_fails(self):
        """Test that signatures don't cross-validate"""
        validator = CryptoValidator()
        
        # Generate two key pairs
        priv1, pub1 = validator.generate_key_pair('secp256r1')
        priv2, pub2 = validator.generate_key_pair('secp256r1')
        
        message = "Test message"
        
        # Sign with first key
        sig1 = validator.sign_message(message, priv1)
        
        # Try to verify with second key (should fail)
        is_valid = validator.verify_signature(
            message,
            sig1['signature'],
            pub2
        )
        
        assert is_valid is False


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
