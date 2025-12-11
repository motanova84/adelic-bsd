"""
Tests for AIK (Activo Inmutable de Conocimiento) Beacon functionality

This module tests the Immutable Knowledge Asset features:
- Integrity Hash generation and validation
- ECDSA signature generation and verification
- Complete AIK beacon structure
- SageMath integration for BSD verification
"""

import sys
import os
import pytest
import json

# Add paths for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../sage_plugin'))

# Import sage if available
pytest.importorskip("sage.all")
from sage.all import EllipticCurve


def test_integrity_hash_generation():
    """Test that integrity hash is generated correctly"""
    from adelic_bsd.verify import generate_integrity_hash
    
    # Test data
    curve_data = {
        'curve_label': '11a1',
        'conductor': 11,
        'discriminant': -161051,
        'j_invariant': '-122023936/161051',
        'analytic_rank': 0
    }
    l_value = 0.2538418608559107
    params = {'s': 1, 'timestamp': '2025-01-15T00:00:00Z'}
    
    hash1 = generate_integrity_hash(curve_data, l_value, params)
    
    # Hash should be 64 characters (SHA-256 in hex)
    assert len(hash1) == 64
    assert isinstance(hash1, str)
    assert all(c in '0123456789abcdef' for c in hash1)
    
    # Same input should produce same hash (deterministic)
    hash2 = generate_integrity_hash(curve_data, l_value, params)
    assert hash1 == hash2
    
    # Different input should produce different hash
    params_different = {'s': 2, 'timestamp': '2025-01-15T00:00:00Z'}
    hash3 = generate_integrity_hash(curve_data, l_value, params_different)
    assert hash1 != hash3
    
    print("✓ Integrity hash generation works correctly")


def test_ecdsa_signature_generation():
    """Test ECDSA signature generation"""
    from adelic_bsd.verify import generate_ecdsa_signature
    
    test_hash = "1234567890abcdef" * 4  # 64 char hash
    
    sig_data = generate_ecdsa_signature(test_hash)
    
    # Check signature structure
    assert 'signature' in sig_data
    assert 'public_key' in sig_data
    assert 'algorithm' in sig_data
    assert 'curve' in sig_data
    
    # Check values
    assert sig_data['algorithm'] == 'ECDSA-SECP256R1-SHA256'
    assert sig_data['curve'] == 'SECP256R1'
    assert isinstance(sig_data['signature'], str)
    assert isinstance(sig_data['public_key'], str)
    
    # Public key should be in PEM format
    assert '-----BEGIN PUBLIC KEY-----' in sig_data['public_key']
    assert '-----END PUBLIC KEY-----' in sig_data['public_key']
    
    print("✓ ECDSA signature generation works correctly")


def test_ecdsa_signature_verification():
    """Test ECDSA signature verification"""
    from adelic_bsd.verify import generate_ecdsa_signature, verify_ecdsa_signature
    
    test_hash = "1234567890abcdef" * 4
    
    # Generate signature
    sig_data = generate_ecdsa_signature(test_hash)
    
    # Verify signature
    is_valid = verify_ecdsa_signature(test_hash, sig_data)
    assert is_valid, "Valid signature should verify"
    
    # Try with wrong hash (should fail)
    wrong_hash = "fedcba0987654321" * 4
    is_invalid = verify_ecdsa_signature(wrong_hash, sig_data)
    assert not is_invalid, "Invalid signature should not verify"
    
    print("✓ ECDSA signature verification works correctly")


def test_verify_bsd_basic_functionality():
    """Test that enhanced verify_bsd maintains backward compatibility"""
    from adelic_bsd.verify import verify_bsd
    
    # Test with curve label
    result = verify_bsd('11a1', generate_aik_beacon=False)
    
    # Check basic fields (backward compatibility)
    assert 'curve_label' in result
    assert 'conductor' in result
    assert 'L(s)' in result
    assert 's' in result
    assert 'analytic_rank' in result
    assert 'hash_sha256' in result
    
    assert result['curve_label'] == '11a1'
    assert result['s'] == 1
    
    print("✓ Basic verify_bsd functionality preserved")


def test_verify_bsd_with_aik_beacon():
    """Test verify_bsd with AIK beacon generation"""
    from adelic_bsd.verify import verify_bsd
    
    result = verify_bsd('11a1', generate_aik_beacon=True)
    
    # Check basic fields
    assert 'curve_label' in result
    assert 'L(s)' in result
    
    # Check AIK beacon
    assert 'aik_beacon' in result
    beacon = result['aik_beacon']
    
    # Check beacon structure
    assert 'integrity_hash' in beacon
    assert 'signature' in beacon
    assert 'timestamp' in beacon
    assert 'beacon_type' in beacon
    assert 'noesis_protocol' in beacon
    assert 'framework' in beacon
    assert 'verification_standard' in beacon
    assert 'verification_info' in beacon
    
    # Check beacon values
    assert beacon['beacon_type'] == 'BSD_VERIFICATION'
    assert beacon['noesis_protocol'] == '∞³'
    assert beacon['framework'] == 'adelic-spectral'
    assert beacon['verification_standard'] == 'AIK-v1.0'
    
    # Check integrity hash
    assert len(beacon['integrity_hash']) == 64
    
    # Check signature
    sig = beacon['signature']
    assert 'signature' in sig
    assert 'public_key' in sig
    assert 'algorithm' in sig
    
    # Check verification info
    info = beacon['verification_info']
    assert 'description' in info
    assert 'properties' in info
    assert 'scientific_claim' in info
    
    print("✓ AIK beacon generation works correctly")


def test_aik_beacon_integrity_validation():
    """Test that AIK beacon integrity hash can detect tampering"""
    from adelic_bsd.verify import verify_bsd, verify_ecdsa_signature
    
    result = verify_bsd('11a1', generate_aik_beacon=True)
    
    beacon = result['aik_beacon']
    integrity_hash = beacon['integrity_hash']
    signature_data = beacon['signature']
    
    # Original signature should verify
    assert verify_ecdsa_signature(integrity_hash, signature_data)
    
    # Modified hash should not verify
    tampered_hash = "0" * 64
    assert not verify_ecdsa_signature(tampered_hash, signature_data)
    
    print("✓ AIK beacon integrity validation works correctly")


def test_aik_beacon_with_different_curves():
    """Test AIK beacon generation for multiple curves"""
    from adelic_bsd.verify import verify_bsd, verify_ecdsa_signature
    
    curves = ['11a1', '14a1', '15a1']
    hashes = []
    
    for label in curves:
        result = verify_bsd(label, generate_aik_beacon=True)
        beacon = result['aik_beacon']
        
        # Check beacon exists
        assert 'integrity_hash' in beacon
        assert 'signature' in beacon
        
        # Store hash
        hashes.append(beacon['integrity_hash'])
        
        # Verify signature
        assert verify_ecdsa_signature(
            beacon['integrity_hash'],
            beacon['signature']
        )
    
    # All hashes should be unique
    assert len(set(hashes)) == len(hashes)
    
    print(f"✓ AIK beacon works for {len(curves)} different curves")


def test_aik_beacon_properties():
    """Test AIK beacon properties structure"""
    from adelic_bsd.verify import verify_bsd
    
    result = verify_bsd('11a1', generate_aik_beacon=True)
    beacon = result['aik_beacon']
    
    properties = beacon['verification_info']['properties']
    
    # Check all expected properties
    expected_properties = ['integrity', 'immutability', 'verifiability', 'integration']
    for prop in expected_properties:
        assert prop in properties
        assert isinstance(properties[prop], str)
        assert len(properties[prop]) > 0
    
    print("✓ AIK beacon properties structure is correct")


def test_aik_beacon_scientific_claim():
    """Test that scientific claim is correctly formatted"""
    from adelic_bsd.verify import verify_bsd
    
    result = verify_bsd('11a1', generate_aik_beacon=True)
    beacon = result['aik_beacon']
    
    claim = beacon['verification_info']['scientific_claim']
    
    # Should contain curve label
    assert '11a1' in claim
    
    # Should contain rank information
    assert 'analytic_rank' in claim
    
    # Should contain L-function value
    assert 'L(' in claim
    
    print(f"✓ Scientific claim: {claim}")


def test_verify_bsd_with_elliptic_curve_object():
    """Test verify_bsd with EllipticCurve object instead of label"""
    from adelic_bsd.verify import verify_bsd
    
    E = EllipticCurve('11a1')
    result = verify_bsd(E, generate_aik_beacon=True)
    
    # Should work the same
    assert 'aik_beacon' in result
    assert result['curve_label'] == '11a1'
    
    print("✓ verify_bsd works with EllipticCurve objects")


def test_aik_beacon_timestamp_format():
    """Test that timestamp is in ISO 8601 format with UTC"""
    from adelic_bsd.verify import verify_bsd
    from datetime import datetime
    
    result = verify_bsd('11a1', generate_aik_beacon=True)
    timestamp = result['aik_beacon']['timestamp']
    
    # Should end with Z (UTC)
    assert timestamp.endswith('Z')
    
    # Should be parseable as ISO format
    timestamp_without_z = timestamp[:-1]
    dt = datetime.fromisoformat(timestamp_without_z)
    assert dt is not None
    
    print(f"✓ Timestamp format correct: {timestamp}")


def test_aik_beacon_json_serializable():
    """Test that AIK beacon can be serialized to JSON"""
    from adelic_bsd.verify import verify_bsd
    
    result = verify_bsd('11a1', generate_aik_beacon=True)
    
    # Remove non-serializable sage objects for this test
    result_copy = {
        'curve_label': result['curve_label'],
        'conductor': int(result['conductor']),
        's': result['s'],
        'analytic_rank': result['analytic_rank'],
        'hash_sha256': result['hash_sha256'],
        'L(s)': float(result['L(s)']),
        'aik_beacon': result['aik_beacon']
    }
    
    # Should be serializable to JSON
    json_str = json.dumps(result_copy, indent=2)
    assert len(json_str) > 0
    
    # Should be deserializable
    parsed = json.loads(json_str)
    assert parsed['aik_beacon']['beacon_type'] == 'BSD_VERIFICATION'
    
    print("✓ AIK beacon is JSON serializable")


def run_all_tests():
    """Run all AIK beacon tests"""
    print("\n" + "="*70)
    print("RUNNING AIK BEACON TESTS")
    print("="*70 + "\n")
    
    test_integrity_hash_generation()
    test_ecdsa_signature_generation()
    test_ecdsa_signature_verification()
    test_verify_bsd_basic_functionality()
    test_verify_bsd_with_aik_beacon()
    test_aik_beacon_integrity_validation()
    test_aik_beacon_with_different_curves()
    test_aik_beacon_properties()
    test_aik_beacon_scientific_claim()
    test_verify_bsd_with_elliptic_curve_object()
    test_aik_beacon_timestamp_format()
    test_aik_beacon_json_serializable()
    
    print("\n" + "="*70)
    print("🎉 ALL AIK BEACON TESTS PASSED!")
    print("="*70 + "\n")


if __name__ == "__main__":
    run_all_tests()
