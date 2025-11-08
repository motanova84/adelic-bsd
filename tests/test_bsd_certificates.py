"""
Tests for BSD certificate generation module in sagemath_integration

This tests the new certificates.py module that provides cryptographically-signed
certificates for BSD proofs with independent verification.
"""

import sys
import os
import pytest
import json
import tempfile

# Add paths for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../sagemath_integration'))

# Import sage if available
pytest.importorskip("sage.all")
from sage.all import EllipticCurve


def test_certificate_import():
    """Test that the certificate module can be imported"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import (
        BSDCertificate,
        generate_bsd_certificate,
        verify_certificate
    )
    
    assert BSDCertificate is not None
    assert generate_bsd_certificate is not None
    assert verify_certificate is not None
    
    print("✓ Certificate module imports successfully")


def test_bsd_certificate_creation():
    """Test that BSDCertificate can be created"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    assert cert is not None
    assert cert._E == E
    assert not cert._finalized
    assert cert.status() == 'UNFINALIZED'
    
    print("✓ BSDCertificate creation works")


def test_curve_hash():
    """Test cryptographic hash computation"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    hash1 = cert.curve_hash()
    hash2 = cert.curve_hash()
    
    # Hash should be consistent
    assert hash1 == hash2
    
    # Hash should be 64 characters (SHA-256 in hex)
    assert len(hash1) == 64
    assert isinstance(hash1, str)
    
    # Different curves should have different hashes
    E2 = EllipticCurve('37a1')
    cert2 = BSDCertificate(E2)
    assert cert.curve_hash() != cert2.curve_hash()
    
    print("✓ Curve hash computation works correctly")


def test_add_spectral_proof():
    """Test adding spectral proof to certificate"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    cert.add_spectral_proof(a=200.84)
    
    assert 'spectral' in cert._proofs
    assert cert._proofs['spectral']['status'] == 'computed'
    assert 'finiteness_proved' in cert._proofs['spectral']
    assert 'gamma' in cert._proofs['spectral']
    assert 'spectral_parameter' in cert._proofs['spectral']
    assert cert._proofs['spectral']['spectral_parameter'] == 200.84
    
    print("✓ Spectral proof addition works")


def test_add_dR_verification():
    """Test adding (dR) verification to certificate"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    cert.add_dR_verification([2, 3, 5])
    
    assert 'dR' in cert._proofs
    assert cert._proofs['dR']['status'] == 'computed'
    assert 'all_compatible' in cert._proofs['dR']
    assert 'verifications' in cert._proofs['dR']
    assert 'primes_tested' in cert._proofs['dR']
    
    print("✓ (dR) verification addition works")


def test_add_PT_verification():
    """Test adding (PT) verification to certificate"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    cert.add_PT_verification()
    
    assert 'PT' in cert._proofs
    assert cert._proofs['PT']['status'] == 'computed'
    assert 'compatible' in cert._proofs['PT']
    assert 'rank' in cert._proofs['PT']
    assert 'method' in cert._proofs['PT']
    
    print("✓ (PT) verification addition works")


def test_certificate_finalize():
    """Test certificate finalization"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    cert.add_spectral_proof()
    cert.add_dR_verification()
    cert.add_PT_verification()
    cert.finalize()
    
    assert cert._finalized
    assert cert.status() in ['PROVED', 'PARTIAL', 'INCOMPLETE']
    
    # Should not be able to finalize twice
    with pytest.raises(ValueError):
        cert.finalize()
    
    print(f"✓ Certificate finalization works (status: {cert.status()})")


def test_certificate_status():
    """Test certificate status tracking"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    # Initially unfinalized
    assert cert.status() == 'UNFINALIZED'
    
    # Add all proofs
    cert.add_spectral_proof()
    cert.add_dR_verification()
    cert.add_PT_verification()
    cert.finalize()
    
    # Should be proved or partial
    status = cert.status()
    assert status in ['PROVED', 'PARTIAL']
    
    print(f"✓ Certificate status tracking works (final status: {status})")


def test_confidence_level():
    """Test confidence level computation"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    # Unfinalized certificate has 0 confidence
    assert cert.confidence_level() == 0.0
    
    # Add all proofs and finalize
    cert.add_spectral_proof()
    cert.add_dR_verification()
    cert.add_PT_verification()
    cert.finalize()
    
    conf = cert.confidence_level()
    
    # Confidence should be between 0 and 1
    assert 0.0 <= conf <= 1.0
    
    # For a complete proof, should be high confidence
    if cert.status() == 'PROVED':
        assert conf > 0.9
    
    print(f"✓ Confidence level computation works (confidence: {conf:.4f})")


def test_export_json():
    """Test JSON export"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    cert.add_spectral_proof()
    cert.add_dR_verification()
    cert.add_PT_verification()
    cert.finalize()
    
    json_str = cert.export_json()
    
    # Should be valid JSON
    data = json.loads(json_str)
    
    assert 'metadata' in data
    assert 'curve' in data
    assert 'proofs' in data
    assert 'status' in data
    assert 'confidence' in data
    assert 'curve_hash' in data['metadata']
    
    print("✓ JSON export works correctly")


def test_export_latex():
    """Test LaTeX export"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    cert.add_spectral_proof()
    cert.add_dR_verification()
    cert.add_PT_verification()
    cert.finalize()
    
    latex_str = cert.export_latex()
    
    # Should contain LaTeX elements
    assert '\\begin{theorem}' in latex_str
    assert '\\end{theorem}' in latex_str
    assert '\\Sha' in latex_str or 'Tate-Shafarevich' in latex_str
    assert '11a1' in latex_str or str(E.conductor()) in latex_str
    
    print("✓ LaTeX export works correctly")


def test_certificate_verify():
    """Test certificate verification"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    # Unfinalized certificate should not verify
    assert not cert.verify()
    
    cert.add_spectral_proof()
    cert.add_dR_verification()
    cert.add_PT_verification()
    cert.finalize()
    
    # Finalized certificate should verify
    assert cert.verify()
    
    print("✓ Certificate verification works")


def test_generate_bsd_certificate():
    """Test convenience function for certificate generation"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import generate_bsd_certificate
    
    E = EllipticCurve('11a1')
    cert = generate_bsd_certificate(E)
    
    # Should be finalized
    assert cert._finalized
    assert cert.status() != 'UNFINALIZED'
    
    # Should have all proofs
    assert 'spectral' in cert._proofs
    assert 'dR' in cert._proofs
    assert 'PT' in cert._proofs
    
    # Should verify
    assert cert.verify()
    
    print(f"✓ generate_bsd_certificate works (status: {cert.status()})")


def test_generate_bsd_certificate_custom_params():
    """Test certificate generation with custom parameters"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import generate_bsd_certificate
    
    E = EllipticCurve('37a1')
    cert = generate_bsd_certificate(E, a=200.84, primes=[2, 3], finalize=False)
    
    # Should not be finalized
    assert not cert._finalized
    assert cert.status() == 'UNFINALIZED'
    
    # Should have custom parameters
    assert cert._proofs['spectral']['spectral_parameter'] == 200.84
    assert cert._proofs['dR']['primes_tested'] == [2, 3]
    
    print("✓ Custom parameters work correctly")


def test_verify_certificate_function():
    """Test standalone verify_certificate function"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import (
        generate_bsd_certificate,
        verify_certificate
    )
    
    E = EllipticCurve('11a1')
    cert = generate_bsd_certificate(E)
    
    # Should verify
    assert verify_certificate(cert)
    
    # Should raise TypeError for non-certificate
    with pytest.raises(TypeError):
        verify_certificate("not a certificate")
    
    print("✓ verify_certificate function works")


def test_multiple_curves():
    """Test certificate generation for multiple curves"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import generate_bsd_certificate
    
    curve_labels = ['11a1', '14a1', '15a1', '37a1']
    
    for label in curve_labels:
        E = EllipticCurve(label)
        cert = generate_bsd_certificate(E)
        
        assert cert._finalized
        assert cert.verify()
        assert cert.confidence_level() > 0.0
    
    print(f"✓ Certificate generation works for {len(curve_labels)} curves")


def test_certificate_repr():
    """Test string representation of certificate"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    repr_str = cert._repr_()
    
    assert 'BSD Certificate' in repr_str
    assert 'UNFINALIZED' in repr_str
    
    cert.add_spectral_proof()
    cert.add_dR_verification()
    cert.add_PT_verification()
    cert.finalize()
    
    repr_str = cert._repr_()
    assert 'BSD Certificate' in repr_str
    assert cert.status() in repr_str
    
    print(f"✓ Certificate representation works: {repr_str}")


def test_incomplete_certificate():
    """Test handling of incomplete certificates"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    # Only add spectral proof
    cert.add_spectral_proof()
    cert.finalize()
    
    # Should be incomplete
    assert cert.status() == 'INCOMPLETE'
    assert cert.confidence_level() == 0.0
    
    print("✓ Incomplete certificate handling works")


def test_export_before_finalize():
    """Test that export fails before finalization"""
    from sagemath_integration.sage.schemes.elliptic_curves.bsd_spectral.certificates import BSDCertificate
    
    E = EllipticCurve('11a1')
    cert = BSDCertificate(E)
    
    cert.add_spectral_proof()
    
    # Should raise ValueError
    with pytest.raises(ValueError):
        cert.export_json()
    
    with pytest.raises(ValueError):
        cert.export_latex()
    
    print("✓ Export validation works correctly")


def run_all_tests():
    """Run all certificate tests"""
    print("\n" + "="*70)
    print("RUNNING BSD CERTIFICATE MODULE TESTS")
    print("="*70 + "\n")
    
    test_certificate_import()
    test_bsd_certificate_creation()
    test_curve_hash()
    test_add_spectral_proof()
    test_add_dR_verification()
    test_add_PT_verification()
    test_certificate_finalize()
    test_certificate_status()
    test_confidence_level()
    test_export_json()
    test_export_latex()
    test_certificate_verify()
    test_generate_bsd_certificate()
    test_generate_bsd_certificate_custom_params()
    test_verify_certificate_function()
    test_multiple_curves()
    test_certificate_repr()
    test_incomplete_certificate()
    test_export_before_finalize()
    
    print("\n" + "="*70)
    print("🎉 ALL BSD CERTIFICATE TESTS PASSED!")
    print("="*70 + "\n")


if __name__ == "__main__":
    run_all_tests()
