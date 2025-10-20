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

    # New tests for BSD verification framework
    test_bsd_certificate_generator_alias()
    test_save_text_certificate_method()
    test_print_final_summary()
    test_generate_certificates_from_results_signature()

    print("=" * 60)
    print("🎉 ALL CERTIFICATE TESTS PASSED!")


def test_bsd_certificate_generator_alias():
    """Test that BSDCertificateGenerator alias exists"""
    from scripts.generate_final_certificates import BSDCertificateGenerator
    from src.verification.certificate_generator import CertificateGenerator

    # Check that the alias points to the correct class
    assert BSDCertificateGenerator is CertificateGenerator

    print("✓ BSDCertificateGenerator alias is correctly defined")


def test_save_text_certificate_method():
    """Test that save_text_certificate method exists and works"""
    from src.verification.certificate_generator import CertificateGenerator
    import tempfile
    import os

    # Create a temporary directory for testing
    with tempfile.TemporaryDirectory() as tmpdir:
        generator = CertificateGenerator(output_dir=tmpdir)

        # Create a mock certificate
        mock_certificate = {
            'curve_data': {'label': '11a1', 'conductor': 11},
            'verification': {'bsd_proven': True},
            'certificate_hash': 'test_hash'
        }

        # Test that the method exists and returns a path
        filepath = generator.save_text_certificate(mock_certificate)

        assert filepath is not None
        assert os.path.exists(filepath)
        assert filepath.endswith('.text')

        print("✓ save_text_certificate method works correctly")


def test_print_final_summary():
    """Test that print_final_summary function works"""
    from scripts.generate_final_certificates import print_final_summary
    import io
    import sys

    # Capture output
    old_stdout = sys.stdout
    sys.stdout = io.StringIO()

    try:
        # Test with mock statistics
        stats = {
            'total': 10,
            'verified': 8,
            'certificates_generated': 8,
            'certificates_failed': 2
        }

        print_final_summary(stats)

        output = sys.stdout.getvalue()

        # Check that output contains expected elements
        assert 'CERTIFICATE GENERATION SUMMARY' in output
        assert 'Total curves processed: 10' in output
        assert 'Certificates generated: 8' in output
        assert 'success rate: 80' in output.lower()

        print("✓ print_final_summary produces correct output", file=old_stdout)

    finally:
        sys.stdout = old_stdout


def test_generate_certificates_from_results_signature():
    """Test that generate_certificates_from_results function exists with correct signature"""
    from scripts.generate_final_certificates import generate_certificates_from_results
    import inspect

    # Check function signature
    sig = inspect.signature(generate_certificates_from_results)
    params = list(sig.parameters.keys())

    assert 'results' in params
    assert 'output_dir' in params

    # Check default value for output_dir
    assert sig.parameters['output_dir'].default == 'certificates'

    print("✓ generate_certificates_from_results has correct signature")


if __name__ == "__main__":
    run_all_tests()
