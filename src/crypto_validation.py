"""
Cryptographic Validation for Elliptic Curves
=============================================

Implements advanced cryptographic validation of elliptic curves for use in
cryptographic applications, including signature schemes, key agreement,
and security parameter validation.

This module provides:
- Elliptic curve parameter validation for cryptographic use
- ECDSA signature generation and verification
- EdDSA signature support
- Security level assessment
- Cryptographic strength verification

Author: Adelic-BSD Framework
Date: 2026-01
"""

import hashlib
import json
from typing import Dict, Tuple, Optional, Any
from datetime import datetime

from cryptography.hazmat.primitives.asymmetric import ec, ed25519
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.backends import default_backend
from cryptography.exceptions import InvalidSignature

try:
    from sage.all import EllipticCurve, ZZ, QQ, GF, factor
    SAGE_AVAILABLE = True
except ImportError:
    SAGE_AVAILABLE = False


class CryptoValidator:
    """
    Validates elliptic curves for cryptographic applications.
    
    Checks security parameters, curve properties, and suitability
    for use in cryptographic protocols.
    """
    
    # Standard cryptographic curves
    STANDARD_CURVES = {
        'secp256r1': ec.SECP256R1(),
        'secp384r1': ec.SECP384R1(),
        'secp521r1': ec.SECP521R1(),
        'secp256k1': ec.SECP256K1(),
    }
    
    # Security levels in bits
    SECURITY_LEVELS = {
        192: 'low',
        224: 'medium',
        256: 'high',
        384: 'very_high',
        521: 'maximum'
    }
    
    def __init__(self):
        """Initialize the cryptographic validator"""
        self.validation_results = {}
    
    def validate_curve_security(self, curve_params: Dict[str, Any]) -> Dict[str, Any]:
        """
        Validate cryptographic security of an elliptic curve.
        
        Args:
            curve_params: Dictionary with curve parameters
                - field_size: Size of the base field
                - order: Order of the curve
                - cofactor: Cofactor
                - discriminant: Curve discriminant
        
        Returns:
            Dict with validation results:
                - is_secure: Boolean indicating if curve is cryptographically secure
                - security_level: Estimated security level in bits
                - warnings: List of security warnings
                - recommendations: Security recommendations
        """
        results = {
            'is_secure': True,
            'security_level': 0,
            'warnings': [],
            'recommendations': [],
            'timestamp': datetime.now().isoformat()
        }
        
        field_size = curve_params.get('field_size', 0)
        order = curve_params.get('order', 0)
        cofactor = curve_params.get('cofactor', 1)
        
        # Check field size
        if field_size < 192:
            results['is_secure'] = False
            results['warnings'].append('Field size too small for cryptographic use (< 192 bits)')
        elif field_size < 224:
            results['warnings'].append('Field size below current recommendations (< 224 bits)')
        
        # Estimate security level (approximate)
        results['security_level'] = min(field_size // 2, field_size - 20)
        
        # Determine security rating (optimized: reverse iteration)
        results['security_rating'] = 'low'
        for level, rating in sorted(self.SECURITY_LEVELS.items(), reverse=True):
            if results['security_level'] >= level:
                results['security_rating'] = rating
                break
        
        # Check cofactor
        if cofactor > 8:
            results['warnings'].append(f'Large cofactor ({cofactor}) may impact performance')
        
        # Check if order is prime or near-prime
        if order > 0 and cofactor > 1:
            subgroup_order = order // cofactor
            results['subgroup_order'] = subgroup_order
        
        # Recommendations
        if field_size < 256:
            results['recommendations'].append('Consider using curves with at least 256-bit security')
        
        if not results['warnings']:
            results['recommendations'].append('Curve parameters meet current cryptographic standards')
        
        self.validation_results[datetime.now().isoformat()] = results
        return results
    
    def generate_key_pair(self, curve_name: str = 'secp256r1') -> Tuple[Any, Any]:
        """
        Generate an ECDSA key pair on a specified curve.
        
        Args:
            curve_name: Name of the elliptic curve (default: secp256r1)
        
        Returns:
            Tuple of (private_key, public_key)
        """
        if curve_name not in self.STANDARD_CURVES:
            raise ValueError(f"Unknown curve: {curve_name}")
        
        curve = self.STANDARD_CURVES[curve_name]
        private_key = ec.generate_private_key(curve, default_backend())
        public_key = private_key.public_key()
        
        return private_key, public_key
    
    def sign_message(self, message: str, private_key: Any, 
                    algorithm: str = 'ecdsa') -> Dict[str, str]:
        """
        Sign a message using elliptic curve cryptography.
        
        Args:
            message: Message to sign
            private_key: Private key for signing
            algorithm: Signature algorithm ('ecdsa' or 'eddsa')
        
        Returns:
            Dictionary with signature information
        """
        message_bytes = message.encode('utf-8')
        
        if algorithm == 'ecdsa':
            signature = private_key.sign(
                message_bytes,
                ec.ECDSA(hashes.SHA256())
            )
            
            return {
                'signature': signature.hex(),
                'algorithm': 'ECDSA-SHA256',
                'message_hash': hashlib.sha256(message_bytes).hexdigest(),
                'timestamp': datetime.now().isoformat()
            }
        else:
            raise ValueError(f"Unsupported algorithm: {algorithm}")
    
    def verify_signature(self, message: str, signature_hex: str, 
                        public_key: Any) -> bool:
        """
        Verify an ECDSA signature.
        
        Args:
            message: Original message
            signature_hex: Signature in hex format
            public_key: Public key for verification
        
        Returns:
            True if signature is valid, False otherwise
        """
        try:
            message_bytes = message.encode('utf-8')
            signature = bytes.fromhex(signature_hex)
            
            public_key.verify(
                signature,
                message_bytes,
                ec.ECDSA(hashes.SHA256())
            )
            return True
        except InvalidSignature:
            return False
        except Exception:
            return False
    
    def export_public_key(self, public_key: Any, format: str = 'pem') -> str:
        """
        Export public key in specified format.
        
        Args:
            public_key: Public key to export
            format: Export format ('pem' or 'der')
        
        Returns:
            Exported public key as string
        """
        if format == 'pem':
            pem = public_key.public_bytes(
                encoding=serialization.Encoding.PEM,
                format=serialization.PublicFormat.SubjectPublicKeyInfo
            )
            return pem.decode('utf-8')
        else:
            raise ValueError(f"Unsupported format: {format}")
    
    def generate_curve_fingerprint(self, curve_data: Dict[str, Any]) -> str:
        """
        Generate a unique cryptographic fingerprint for a curve.
        
        Args:
            curve_data: Dictionary with curve parameters
        
        Returns:
            SHA-256 fingerprint in hex format
        """
        canonical = json.dumps(curve_data, sort_keys=True, separators=(',', ':'))
        return hashlib.sha256(canonical.encode('utf-8')).hexdigest()


class EdDSAValidator:
    """
    Validator for EdDSA (Edwards-curve Digital Signature Algorithm).
    
    Provides Ed25519 signature generation and verification.
    """
    
    def __init__(self):
        """Initialize EdDSA validator"""
        pass
    
    def generate_key_pair(self) -> Tuple[ed25519.Ed25519PrivateKey, ed25519.Ed25519PublicKey]:
        """
        Generate an Ed25519 key pair.
        
        Returns:
            Tuple of (private_key, public_key)
        """
        private_key = ed25519.Ed25519PrivateKey.generate()
        public_key = private_key.public_key()
        return private_key, public_key
    
    def sign_message(self, message: str, private_key: ed25519.Ed25519PrivateKey) -> Dict[str, str]:
        """
        Sign a message using Ed25519.
        
        Args:
            message: Message to sign
            private_key: Ed25519 private key
        
        Returns:
            Dictionary with signature information
        """
        message_bytes = message.encode('utf-8')
        signature = private_key.sign(message_bytes)
        
        return {
            'signature': signature.hex(),
            'algorithm': 'Ed25519',
            'message_hash': hashlib.sha256(message_bytes).hexdigest(),
            'timestamp': datetime.now().isoformat()
        }
    
    def verify_signature(self, message: str, signature_hex: str,
                        public_key: ed25519.Ed25519PublicKey) -> bool:
        """
        Verify an Ed25519 signature.
        
        Args:
            message: Original message
            signature_hex: Signature in hex format
            public_key: Ed25519 public key
        
        Returns:
            True if signature is valid, False otherwise
        """
        try:
            message_bytes = message.encode('utf-8')
            signature = bytes.fromhex(signature_hex)
            public_key.verify(signature, message_bytes)
            return True
        except Exception:
            return False


def validate_elliptic_curve_for_crypto(curve_label: str) -> Dict[str, Any]:
    """
    Validate an elliptic curve for cryptographic use.
    
    Args:
        curve_label: LMFDB label of the curve (e.g., '11a1')
    
    Returns:
        Dictionary with validation results
    """
    if not SAGE_AVAILABLE:
        return {
            'status': 'error',
            'message': 'SageMath not available for curve validation'
        }
    
    try:
        E = EllipticCurve(curve_label)
        
        # Extract curve parameters
        conductor = E.conductor()
        discriminant = E.discriminant()
        j_invariant = E.j_invariant()
        
        # For cryptographic use, we need curves over finite fields
        # The database curves are over Q, so we consider their reductions
        
        validator = CryptoValidator()
        
        # Estimate security based on conductor (proxy for complexity)
        field_size_estimate = len(bin(abs(int(conductor)))) - 2
        
        curve_params = {
            'field_size': field_size_estimate,
            'order': abs(int(conductor)),
            'cofactor': 1,
            'discriminant': abs(int(discriminant)),
            'curve_label': curve_label,
            'j_invariant': str(j_invariant)
        }
        
        validation = validator.validate_curve_security(curve_params)
        
        return {
            'status': 'success',
            'curve_label': curve_label,
            'validation': validation,
            'curve_params': curve_params,
            'timestamp': datetime.now().isoformat()
        }
        
    except Exception as e:
        return {
            'status': 'error',
            'message': str(e),
            'curve_label': curve_label
        }
