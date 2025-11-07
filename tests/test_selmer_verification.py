"""
Tests for Selmer Verification Module
Tests the integration of Selmer map verification with formal proof system
"""

import sys
import os
import pytest

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

# Conditionally import sage - these tests will be skipped if sage is not available
pytest.importorskip("sage.all")
from sage.all import EllipticCurve


def test_selmer_verification_import():
    """Test that SelmerVerification can be imported"""
    try:
        from src.verification import SelmerVerification
        print("✓ SelmerVerification imported successfully")
        return True
    except Exception as e:
        print(f"✗ Import failed: {e}")
        return False


def test_selmer_verification_initialization():
    """Test SelmerVerification initialization"""
    try:
        from src.verification import SelmerVerification

        E = EllipticCurve('11a1')
        verifier = SelmerVerification(E, primes=[2, 3], precision=20)

        assert verifier.E == E
        assert verifier.primes == [2, 3]
        assert verifier.precision == 20

        print("✓ SelmerVerification initialized correctly")
        return True
    except Exception as e:
        print(f"✗ Initialization failed: {e}")
        return False


def test_verify_selmer_maps_function():
    """Test verify_selmer_maps convenience function"""
    try:
        from src.verification import verify_selmer_maps

        E = EllipticCurve('11a1')
        certificate = verify_selmer_maps(E, primes=[2], precision=20)

        assert 'curve' in certificate
        assert 'verification_passed' in certificate
        assert 'verification_steps' in certificate
        assert 'primes_verified' in certificate

        print("✓ verify_selmer_maps works")
        print(f"  Verification passed: {certificate['verification_passed']}")
        return True
    except Exception as e:
        print(f"✗ verify_selmer_maps failed: {e}")
        return False


def test_selmer_verification_map_initialization():
    """Test Selmer map initialization verification step"""
    try:
        from src.verification import SelmerVerification

        E = EllipticCurve('11a1')
        verifier = SelmerVerification(E, primes=[2, 3])

        init_results = verifier._verify_map_initialization()

        assert 'primes_tested' in init_results
        assert 'initialization_status' in init_results
        assert 'all_initialized' in init_results

        print("✓ Map initialization verification works")
        print(f"  All initialized: {init_results['all_initialized']}")
        return True
    except Exception as e:
        print(f"✗ Map initialization test failed: {e}")
        return False


def test_selmer_verification_bloch_kato():
    """Test Bloch-Kato conditions verification"""
    try:
        from src.verification import SelmerVerification

        E = EllipticCurve('11a1')
        verifier = SelmerVerification(E, primes=[2])

        bk_results = verifier._verify_bloch_kato_conditions()

        assert 'primes_tested' in bk_results
        assert 'bloch_kato_status' in bk_results
        assert 'all_verified' in bk_results

        print("✓ Bloch-Kato verification works")
        print(f"  All verified: {bk_results['all_verified']}")
        return True
    except Exception as e:
        print(f"✗ Bloch-Kato verification failed: {e}")
        return False


def test_complete_verification():
    """Test complete Selmer verification pipeline"""
    try:
        from src.verification import SelmerVerification

        E = EllipticCurve('11a1')
        verifier = SelmerVerification(E, primes=[2, 3])

        certificate = verifier.verify_all()

        assert 'curve' in certificate
        assert 'verification_passed' in certificate
        assert 'verification_steps' in certificate

        # Check all verification steps present
        steps = certificate['verification_steps']
        assert 'initialization' in steps
        assert 'bloch_kato' in steps
        assert 'spectral_compatibility' in steps
        assert 'local_global' in steps

        print("✓ Complete verification works")
        print(f"  Verification passed: {certificate['verification_passed']}")
        print(f"  Steps completed: {list(steps.keys())}")
        return True
    except Exception as e:
        print(f"✗ Complete verification failed: {e}")
        return False


def test_certificate_generation():
    """Test Selmer verification certificate generation"""
    try:
        from src.verification import SelmerVerification

        E = EllipticCurve('37a1')
        verifier = SelmerVerification(E, primes=[2])

        certificate = verifier.generate_certificate(save=False)

        assert 'certificate_type' in certificate
        assert certificate['certificate_type'] == 'selmer_map_verification'
        assert 'certificate_hash' in certificate
        assert 'verification_passed' in certificate

        print("✓ Certificate generation works")
        print(f"  Certificate type: {certificate['certificate_type']}")
        return True
    except Exception as e:
        print(f"✗ Certificate generation failed: {e}")
        return False


def test_batch_verification():
    """Test batch Selmer map verification"""
    try:
        from src.verification import batch_verify_selmer_maps

        curve_labels = ['11a1', '37a1']
        results = batch_verify_selmer_maps(curve_labels, primes=[2], precision=20)

        assert 'total_curves' in results
        assert 'passed' in results
        assert 'results' in results
        assert results['total_curves'] == 2

        print("✓ Batch verification works")
        print(f"  Total curves: {results['total_curves']}")
        print(f"  Passed: {results['passed']}")
        print(f"  Success rate: {results['success_rate']}")
        return True
    except Exception as e:
        print(f"✗ Batch verification failed: {e}")
        return False


def test_verification_report_generation():
    """Test verification report generation"""
    try:
        from src.verification import verify_selmer_maps, generate_selmer_verification_report

        E = EllipticCurve('11a1')
        certificate = verify_selmer_maps(E, primes=[2])

        report = generate_selmer_verification_report(certificate)

        assert isinstance(report, str)
        assert 'SELMER MAP VERIFICATION REPORT' in report
        assert '11a1' in report

        print("✓ Report generation works")
        print("  Report preview:")
        print(report[:200])
        return True
    except Exception as e:
        print(f"✗ Report generation failed: {e}")
        return False


def test_integration_with_formal_prover():
    """Test integration with FormalBSDProver"""
    try:
        from src.verification import verify_selmer_maps, FormalBSDProver

        E = EllipticCurve('11a1')

        # Verify Selmer maps
        selmer_cert = verify_selmer_maps(E, primes=[2])

        # Verify that formal prover can also work with same curve
        prover = FormalBSDProver(E, proof_level="basic")

        # Both should work on same curve
        assert selmer_cert['curve'] == prover.E.cremona_label()

        print("✓ Integration with FormalBSDProver works")
        return True
    except Exception as e:
        print(f"✗ Integration test failed: {e}")
        return False


def run_all_tests():
    """Run all Selmer verification tests"""
    print("\n" + "="*70)
    print("SELMER VERIFICATION MODULE TESTS")
    print("="*70 + "\n")

    tests = [
        ("Import SelmerVerification", test_selmer_verification_import),
        ("Initialize SelmerVerification", test_selmer_verification_initialization),
        ("verify_selmer_maps function", test_verify_selmer_maps_function),
        ("Map initialization verification", test_selmer_verification_map_initialization),
        ("Bloch-Kato verification", test_selmer_verification_bloch_kato),
        ("Complete verification", test_complete_verification),
        ("Certificate generation", test_certificate_generation),
        ("Batch verification", test_batch_verification),
        ("Report generation", test_verification_report_generation),
        ("Integration with FormalBSDProver", test_integration_with_formal_prover),
    ]

    results = []
    for name, test_func in tests:
        print(f"\nTest: {name}")
        print("-" * 70)
        result = test_func()
        results.append((name, result))

    # Summary
    print("\n" + "="*70)
    print("TEST SUMMARY")
    print("="*70)

    passed = sum(1 for _, r in results if r)
    total = len(results)

    for name, result in results:
        status = "✓ PASS" if result else "✗ FAIL"
        print(f"{status}: {name}")

    print(f"\nTotal: {passed}/{total} tests passed")
    print("="*70 + "\n")

    return passed == total


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
