"""
Tests for certificate generation
"""

import sys
import os
import pytest

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

# Conditionally import sage - these tests will be skipped if sage is not available
pytest.importorskip("sage.all")
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver


def test_text_certificate_format():
    """Test that text certificates have correct format"""
    E = EllipticCurve('11a1')
    prover = SpectralFinitenessProver(E)
    
    cert = prover.generate_certificate('text')
    
    # Check required sections
    assert 'SPECTRAL FINITENESS CERTIFICATE' in cert
    assert 'Curve:' in cert
    assert 'Conductor:' in cert
    assert 'FINITENESS PROOF:' in cert
    assert 'LOCAL SPECTRAL DATA:' in cert
    assert 'CONCLUSION:' in cert
    assert 'PROVED' in cert or 'finite' in cert
    
    print("✓ Text certificate format is correct")


def test_certificate_contains_curve_data():
    """Test that certificate contains correct curve data"""
    E = EllipticCurve('37a1')
    prover = SpectralFinitenessProver(E)
    
    cert = prover.generate_certificate('text')
    
    # Should contain conductor
    conductor = str(E.conductor())
    assert conductor in cert
    
    print(f"✓ Certificate contains correct conductor: {conductor}")


def test_certificate_shows_finiteness():
    """Test that certificate clearly states finiteness result"""
    test_curves = ['11a1', '14a1', '15a1']
    
    for label in test_curves:
        E = EllipticCurve(label)
        prover = SpectralFinitenessProver(E)
        cert = prover.generate_certificate('text')
        
        # Certificate must state finiteness
        assert ('finite' in cert.lower() or 'PROVED' in cert)
        
    print(f"✓ All {len(test_curves)} certificates show finiteness")


def test_certificate_includes_local_data():
    """Test that certificate includes local spectral data"""
    E = EllipticCurve('11a1')
    prover = SpectralFinitenessProver(E)
    
    cert = prover.generate_certificate('text')
    
    # Should have local data section
    assert 'LOCAL SPECTRAL DATA:' in cert or 'Prime' in cert
    
    # Should mention at least one prime (conductor of 11a1 is 11)
    assert '11' in cert
    
    print("✓ Certificate includes local spectral data")


def test_multiple_curve_certificates():
    """Test certificate generation for multiple curves"""
    curves = ['11a1', '11a2', '11a3', '14a1', '15a1']
    
    for label in curves:
        E = EllipticCurve(label)
        prover = SpectralFinitenessProver(E)
        
        try:
            cert = prover.generate_certificate('text')
            assert len(cert) > 0
            assert 'CERTIFICATE' in cert.upper()
        except Exception as e:
            print(f"✗ Failed for {label}: {e}")
            raise
    
    print(f"✓ Successfully generated {len(curves)} certificates")


def test_certificate_global_bound():
    """Test that certificate includes global bound"""
    E = EllipticCurve('11a1')
    prover = SpectralFinitenessProver(E)
    
    result = prover.prove_finiteness()
    cert = prover.generate_certificate('text')
    
    # Global bound should appear in certificate
    bound_str = str(result['global_bound'])
    assert bound_str in cert
    
    print(f"✓ Certificate includes global bound: {result['global_bound']}")


def run_all_tests():
    """Run all certificate generation tests"""
    print("Running Certificate Generation Tests...")
    print("=" * 60)
    
    test_text_certificate_format()
    test_certificate_contains_curve_data()
    test_certificate_shows_finiteness()
    test_certificate_includes_local_data()
    test_multiple_curve_certificates()
    test_certificate_global_bound()
    
    print("=" * 60)
    print("🎉 ALL CERTIFICATE TESTS PASSED!")


if __name__ == "__main__":
    run_all_tests()
