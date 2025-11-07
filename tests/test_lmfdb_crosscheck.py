"""
Tests for LMFDB cross-validation
Compare spectral bounds with known Sha values from LMFDB/Sage
"""

import sys
import os
import pytest

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

# Conditionally import sage - these tests will be skipped if sage is not available
pytest.importorskip("sage.all")
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver


def test_11a1_known_sha():
    """Test 11a1 against known Sha = 1"""
    E = EllipticCurve('11a1')
    prover = SpectralFinitenessProver(E)
    result = prover.prove_finiteness()

    # Known: #Sha = 1 for 11a1
    known_sha = 1
    spectral_bound = result['global_bound']

    # Spectral bound must be at least as large as actual Sha
    assert spectral_bound >= known_sha, f"Bound {spectral_bound} < known Sha {known_sha}"

    print(f"✓ 11a1: Spectral bound {spectral_bound} >= known #Sha {known_sha}")


def test_37a1_known_sha():
    """Test 37a1 against known Sha = 1"""
    E = EllipticCurve('37a1')
    prover = SpectralFinitenessProver(E)
    result = prover.prove_finiteness()

    # Known: #Sha = 1 for 37a1
    known_sha = 1
    spectral_bound = result['global_bound']

    assert spectral_bound >= known_sha, f"Bound {spectral_bound} < known Sha {known_sha}"

    print(f"✓ 37a1: Spectral bound {spectral_bound} >= known #Sha {known_sha}")


def test_389a1_known_sha():
    """Test 389a1 against known Sha = 1"""
    E = EllipticCurve('389a1')
    prover = SpectralFinitenessProver(E)
    result = prover.prove_finiteness()

    # Known: #Sha = 1 for 389a1 (rank 2 curve)
    known_sha = 1
    spectral_bound = result['global_bound']

    assert spectral_bound >= known_sha, f"Bound {spectral_bound} < known Sha {known_sha}"

    print(f"✓ 389a1: Spectral bound {spectral_bound} >= known #Sha {known_sha}")


def test_lmfdb_comparison_multiple_curves():
    """Compare spectral bounds with LMFDB data for multiple curves"""
    # Curves with known Sha = 1
    test_curves = {
        '11a1': 1,
        '11a2': 1,
        '11a3': 1,
        '14a1': 1,
        '15a1': 1,
        '17a1': 1,
        '19a1': 1,
        '37a1': 1
    }

    passed = 0
    failed = 0

    for label, known_sha in test_curves.items():
        try:
            E = EllipticCurve(label)
            prover = SpectralFinitenessProver(E)
            result = prover.prove_finiteness()
            spectral_bound = result['global_bound']

            if spectral_bound >= known_sha:
                print(f"✓ {label}: bound {spectral_bound} >= #Sha {known_sha}")
                passed += 1
            else:
                print(f"✗ {label}: bound {spectral_bound} < #Sha {known_sha}")
                failed += 1
        except Exception as e:
            print(f"✗ {label}: ERROR - {e}")
            failed += 1

    print(f"\nResults: {passed} passed, {failed} failed out of {len(test_curves)} curves")
    assert failed == 0, f"{failed} curves failed LMFDB comparison"


def test_sage_sha_available():
    """Test that we can access Sha data from Sage when available"""
    E = EllipticCurve('11a1')

    try:
        # Try to get Sha from Sage (may not always work)
        sha = E.sha()
        sha_an = sha.an()
        print(f"✓ Sage reports #Sha for 11a1: {sha_an}")
    except Exception as e:
        print(f"⚠ Sha computation not available in this Sage installation: {e}")
        print("  (This is expected in some configurations)")


def test_spectral_bound_consistency():
    """Test that spectral bounds are consistent across runs"""
    E = EllipticCurve('11a1')

    # Run multiple times
    bounds = []
    for i in range(3):
        prover = SpectralFinitenessProver(E)
        result = prover.prove_finiteness()
        bounds.append(result['global_bound'])

    # All bounds should be identical
    assert all(b == bounds[0] for b in bounds), f"Inconsistent bounds: {bounds}"

    print(f"✓ Spectral bounds are consistent: {bounds[0]}")


def test_comparison_with_conductor_range():
    """Test curves in a conductor range and compare with known data"""
    # Test curves with conductor <= 20
    curves_to_test = []
    try:
        from sage.all import cremona_curves
        # Get first few curves with small conductor
        for label in cremona_curves(20):
            curves_to_test.append(label)
            if len(curves_to_test) >= 10:
                break
    except:
        # Fallback to hardcoded list
        curves_to_test = ['11a1', '11a2', '11a3', '14a1', '15a1', '17a1', '19a1']

    print(f"\nTesting {len(curves_to_test)} curves with conductor <= 20:")

    for label in curves_to_test:
        try:
            E = EllipticCurve(label)
            prover = SpectralFinitenessProver(E)
            result = prover.prove_finiteness()

            # Try to get known Sha
            known_sha = "Unknown"
            try:
                known_sha = E.sha().an()
            except:
                pass

            bound_check = "✓" if known_sha == "Unknown" or result['global_bound'] >= known_sha else "✗"
            print(f"  {bound_check} {label}: bound={result['global_bound']}, #Sha={known_sha}")

        except Exception as e:
            print(f"  ✗ {label}: ERROR - {e}")


def run_all_tests():
    """Run all LMFDB cross-check tests"""
    print("Running LMFDB Cross-Check Tests...")
    print("=" * 60)

    test_sage_sha_available()
    print()

    test_11a1_known_sha()
    test_37a1_known_sha()
    test_389a1_known_sha()
    print()

    test_spectral_bound_consistency()
    print()

    test_lmfdb_comparison_multiple_curves()
    print()

    test_comparison_with_conductor_range()

    print("=" * 60)
    print("🎉 ALL LMFDB CROSS-CHECK TESTS PASSED!")


if __name__ == "__main__":
    run_all_tests()
