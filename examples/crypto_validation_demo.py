#!/usr/bin/env python3
"""
Cryptographic Validation Demo
==============================

Demonstrates the cryptographic validation capabilities of the Adelic-BSD framework.

This script shows:
1. Elliptic curve security validation
2. ECDSA signature generation and verification
3. EdDSA (Ed25519) signatures
4. Curve fingerprinting
5. Multi-signature workflows

Usage:
    python examples/crypto_validation_demo.py
"""

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


def demo_curve_validation():
    """Demonstrate elliptic curve security validation"""
    print("\n" + "=" * 70)
    print("DEMO 1: Elliptic Curve Security Validation")
    print("=" * 70)
    
    validator = CryptoValidator()
    
    # Test different security levels
    test_curves = [
        {
            'name': 'High Security (256-bit)',
            'params': {
                'field_size': 256,
                'order': 2**256 - 2**32 - 977,
                'cofactor': 1,
                'discriminant': 123456
            }
        },
        {
            'name': 'Medium Security (192-bit)',
            'params': {
                'field_size': 192,
                'order': 2**192,
                'cofactor': 1,
                'discriminant': 789
            }
        },
        {
            'name': 'Low Security (128-bit)',
            'params': {
                'field_size': 128,
                'order': 2**128,
                'cofactor': 1,
                'discriminant': 456
            }
        }
    ]
    
    for curve_info in test_curves:
        print(f"\n{curve_info['name']}:")
        result = validator.validate_curve_security(curve_info['params'])
        print(f"  Is Secure: {result['is_secure']}")
        print(f"  Security Level: {result['security_level']} bits")
        print(f"  Security Rating: {result['security_rating']}")
        if result['warnings']:
            print(f"  Warnings: {', '.join(result['warnings'])}")
        if result['recommendations']:
            print(f"  Recommendations: {result['recommendations'][0]}")


def demo_ecdsa_signatures():
    """Demonstrate ECDSA signature generation and verification"""
    print("\n" + "=" * 70)
    print("DEMO 2: ECDSA Signature Generation and Verification")
    print("=" * 70)
    
    validator = CryptoValidator()
    
    # Generate key pair
    print("\nGenerating ECDSA key pair (secp256r1)...")
    private_key, public_key = validator.generate_key_pair('secp256r1')
    
    # Export public key
    public_key_pem = validator.export_public_key(public_key, 'pem')
    print(f"Public Key:\n{public_key_pem}")
    
    # Sign messages
    messages = [
        "Transaction: Alice pays Bob 100 BTC",
        "Transaction: Bob pays Charlie 50 BTC",
        "Transaction: Charlie pays Alice 25 BTC"
    ]
    
    print(f"\nSigning {len(messages)} messages...")
    signatures = []
    
    for i, message in enumerate(messages):
        sig_data = validator.sign_message(message, private_key)
        signatures.append(sig_data)
        print(f"\nMessage {i+1}: {message}")
        print(f"  Signature: {sig_data['signature'][:32]}...")
        print(f"  Algorithm: {sig_data['algorithm']}")
        print(f"  Message Hash: {sig_data['message_hash'][:32]}...")
    
    # Verify signatures
    print("\n\nVerifying signatures...")
    for i, message in enumerate(messages):
        is_valid = validator.verify_signature(
            message,
            signatures[i]['signature'],
            public_key
        )
        status = "✓ VALID" if is_valid else "✗ INVALID"
        print(f"  Message {i+1}: {status}")
    
    # Test invalid signature
    print("\nTesting invalid signature (wrong message)...")
    is_valid = validator.verify_signature(
        "Wrong message",
        signatures[0]['signature'],
        public_key
    )
    status = "✓ VALID" if is_valid else "✗ INVALID (expected)"
    print(f"  Result: {status}")


def demo_eddsa_signatures():
    """Demonstrate EdDSA (Ed25519) signatures"""
    print("\n" + "=" * 70)
    print("DEMO 3: EdDSA (Ed25519) Signatures")
    print("=" * 70)
    
    validator = EdDSAValidator()
    
    # Generate Ed25519 key pair
    print("\nGenerating Ed25519 key pair...")
    private_key, public_key = validator.generate_key_pair()
    
    # Sign message
    message = "Post-quantum secure blockchain transaction"
    print(f"\nMessage: {message}")
    
    sig_data = validator.sign_message(message, private_key)
    print(f"\nSignature Data:")
    print(f"  Algorithm: {sig_data['algorithm']}")
    print(f"  Signature: {sig_data['signature'][:32]}...")
    print(f"  Message Hash: {sig_data['message_hash'][:32]}...")
    
    # Verify signature
    is_valid = validator.verify_signature(
        message,
        sig_data['signature'],
        public_key
    )
    status = "✓ VALID" if is_valid else "✗ INVALID"
    print(f"\nVerification: {status}")


def demo_curve_fingerprinting():
    """Demonstrate curve fingerprinting"""
    print("\n" + "=" * 70)
    print("DEMO 4: Curve Fingerprinting")
    print("=" * 70)
    
    validator = CryptoValidator()
    
    curves = [
        {'name': '11a1', 'conductor': 11, 'rank': 0},
        {'name': '37a1', 'conductor': 37, 'rank': 1},
        {'name': '389a1', 'conductor': 389, 'rank': 2}
    ]
    
    print("\nGenerating cryptographic fingerprints for elliptic curves:")
    
    for curve in curves:
        fingerprint = validator.generate_curve_fingerprint(curve)
        print(f"\nCurve {curve['name']}:")
        print(f"  Conductor: {curve['conductor']}")
        print(f"  Rank: {curve['rank']}")
        print(f"  Fingerprint: {fingerprint}")
    
    # Verify consistency
    print("\n\nVerifying fingerprint consistency...")
    curve_data = curves[0]
    fp1 = validator.generate_curve_fingerprint(curve_data)
    fp2 = validator.generate_curve_fingerprint(curve_data)
    print(f"  First generation:  {fp1}")
    print(f"  Second generation: {fp2}")
    print(f"  Match: {fp1 == fp2} ✓")


def demo_sage_integration():
    """Demonstrate SageMath integration"""
    print("\n" + "=" * 70)
    print("DEMO 5: SageMath Integration (Curve Validation)")
    print("=" * 70)
    
    curves_to_test = ['11a1', '37a1', '389a1']
    
    print("\nValidating elliptic curves for cryptographic use:")
    
    for curve_label in curves_to_test:
        print(f"\n{curve_label}:")
        result = validate_elliptic_curve_for_crypto(curve_label)
        
        if result['status'] == 'success':
            validation = result['validation']
            print(f"  Status: ✓ Success")
            print(f"  Security Level: {validation['security_level']} bits")
            print(f"  Is Secure: {validation['is_secure']}")
            print(f"  Security Rating: {validation['security_rating']}")
        elif 'SageMath not available' in result.get('message', ''):
            print(f"  Status: ⊘ SageMath not available (skipped)")
        else:
            print(f"  Status: ✗ Error - {result.get('message', 'Unknown error')}")


def main():
    """Run all demonstrations"""
    print("\n" + "=" * 70)
    print("CRYPTOGRAPHIC VALIDATION DEMONSTRATION")
    print("Adelic-BSD Framework")
    print("=" * 70)
    
    try:
        demo_curve_validation()
        demo_ecdsa_signatures()
        demo_eddsa_signatures()
        demo_curve_fingerprinting()
        demo_sage_integration()
        
        print("\n" + "=" * 70)
        print("DEMONSTRATION COMPLETE")
        print("=" * 70)
        print("\nAll cryptographic validation features demonstrated successfully!")
        print("See docs/CRYPTO_BLOCKCHAIN_DOCUMENTATION.md for detailed usage.\n")
        
    except Exception as e:
        print(f"\n✗ Error during demonstration: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
