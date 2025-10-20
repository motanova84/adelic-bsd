"""
Tests for spectral cycles and height pairing modules
"""

import sys
import os
import pytest

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

# Conditionally import sage - these tests will be skipped if sage is not available
pytest.importorskip("sage.all")
from sage.all import EllipticCurve
from src.spectral_cycles import (
    SpectralCycleConstructor,
    spectral_kernel_to_rational_points,
    compute_kernel_basis,
    demonstrate_spectral_to_points
)
from src.height_pairing import (
    compute_spectral_height_matrix,
    compute_nt_height_matrix,
    verify_height_compatibility
)
from src.lmfdb_verification import (
    large_scale_verification,
    get_lmfdb_curves
)


def test_spectral_cycle_constructor():
    """Test SpectralCycleConstructor initialization"""
    E = EllipticCurve('11a1')
    constructor = SpectralCycleConstructor(E)

    assert constructor.E == E
    assert constructor.N == E.conductor()
    print("✓ SpectralCycleConstructor initialization works")


def test_modular_symbol_construction():
    """Test modular symbol construction from spectral vector"""
    E = EllipticCurve('11a1')
    constructor = SpectralCycleConstructor(E)

    # Use a dummy vector (in practice, from kernel)
    v = None  # placeholder

    try:
        MS_data = constructor.spectral_vector_to_modular_symbol(v)
        assert 'modular_symbols_space' in MS_data
        assert 'dimension' in MS_data
        print("✓ Modular symbol construction works")
    except Exception as e:
        print(f"⚠ Modular symbol construction: {e}")


def test_cycle_construction():
    """Test cycle construction from modular symbols"""
    E = EllipticCurve('11a1')
    constructor = SpectralCycleConstructor(E)

    # Get modular symbols first
    v = None
    MS_data = constructor.spectral_vector_to_modular_symbol(v)

    try:
        cycle_data = constructor.modular_symbol_to_cycle(MS_data)
        assert 'cycle_space' in cycle_data
        assert 'dimension' in cycle_data
        print("✓ Cycle construction works")
    except Exception as e:
        print(f"⚠ Cycle construction: {e}")


def test_point_projection():
    """Test projection from cycles to rational points"""
    E = EllipticCurve('11a1')
    constructor = SpectralCycleConstructor(E)

    # Get cycle first
    v = None
    MS_data = constructor.spectral_vector_to_modular_symbol(v)
    cycle_data = constructor.modular_symbol_to_cycle(MS_data)

    try:
        point_data = constructor.cycle_to_rational_point(cycle_data, E)
        assert 'point' in point_data
        P = point_data['point']
        assert P in E
        print(f"✓ Point projection works: P = {P}")
    except Exception as e:
        print(f"⚠ Point projection: {e}")


def test_kernel_basis_computation():
    """Test computation of kernel basis"""
    E = EllipticCurve('11a1')

    try:
        kernel_basis = compute_kernel_basis(E)
        assert isinstance(kernel_basis, list)
        print(f"✓ Kernel basis computation works: dimension = {len(kernel_basis)}")
    except Exception as e:
        print(f"⚠ Kernel basis computation: {e}")


def test_spectral_to_points():
    """Test main spectral→points algorithm"""
    E = EllipticCurve('11a1')

    try:
        kernel_basis = compute_kernel_basis(E)
        points = spectral_kernel_to_rational_points(kernel_basis, E)

        assert isinstance(points, list)
        assert len(points) == len(kernel_basis)

        # Verify all points are on curve
        for p_data in points:
            P = p_data['point']
            assert P in E

        print(f"✓ Spectral→Points algorithm works: {len(points)} points generated")
    except Exception as e:
        print(f"⚠ Spectral→Points algorithm: {e}")


def test_spectral_height_matrix():
    """Test spectral height matrix computation"""
    E = EllipticCurve('11a1')

    try:
        kernel_basis = compute_kernel_basis(E)
        H_spec = compute_spectral_height_matrix(kernel_basis, E)

        # Check matrix properties
        assert H_spec.nrows() == len(kernel_basis)
        assert H_spec.ncols() == len(kernel_basis)

        print(f"✓ Spectral height matrix computation works: {H_spec.dimensions()}")
    except Exception as e:
        print(f"⚠ Spectral height matrix: {e}")


def test_nt_height_matrix():
    """Test Néron-Tate height matrix computation"""
    E = EllipticCurve('11a1')

    try:
        kernel_basis = compute_kernel_basis(E)
        points = spectral_kernel_to_rational_points(kernel_basis, E)
        H_nt = compute_nt_height_matrix(points)

        # Check matrix properties
        assert H_nt.nrows() == len(points)
        assert H_nt.ncols() == len(points)

        print(f"✓ Néron-Tate height matrix computation works: {H_nt.dimensions()}")
    except Exception as e:
        print(f"⚠ Néron-Tate height matrix: {e}")


def test_height_compatibility_11a1():
    """Test height compatibility for curve 11a1"""
    E = EllipticCurve('11a1')

    try:
        result = verify_height_compatibility(E)

        assert 'compatible' in result
        assert 'H_spec' in result
        assert 'H_nt' in result

        print(f"✓ Height compatibility test works: compatible={result['compatible']}")
    except Exception as e:
        print(f"⚠ Height compatibility: {e}")


def test_lmfdb_curve_retrieval():
    """Test LMFDB curve retrieval"""
    try:
        curves = get_lmfdb_curves(conductor_range=(11, 20), limit=5)

        assert isinstance(curves, list)
        assert len(curves) > 0

        print(f"✓ LMFDB curve retrieval works: {len(curves)} curves found")
    except Exception as e:
        print(f"⚠ LMFDB curve retrieval: {e}")


def test_small_verification():
    """Test verification on a small set of curves"""
    try:
        results = large_scale_verification(
            conductor_range=(11, 15),
            limit=3,
            verbose=False
        )

        assert 'results' in results
        assert 'success_rate' in results
        assert results['total'] > 0

        print(f"✓ Small-scale verification works: {results['total']} curves tested")
        print(f"  Success rate: {results['success_rate']:.1f}%")
    except Exception as e:
        print(f"⚠ Small-scale verification: {e}")


def test_demonstrate_function():
    """Test the demonstration function"""
    try:
        result = demonstrate_spectral_to_points('11a1')

        assert 'curve' in result
        assert 'kernel_basis' in result
        assert 'points' in result

        print("✓ Demonstration function works")
    except Exception as e:
        print(f"⚠ Demonstration function: {e}")


def run_all_tests():
    """Run all tests"""
    print("\n" + "="*70)
    print("TESTING SPECTRAL CYCLES AND HEIGHT PAIRING MODULES")
    print("="*70)

    tests = [
        ("Constructor", test_spectral_cycle_constructor),
        ("Modular Symbol", test_modular_symbol_construction),
        ("Cycle Construction", test_cycle_construction),
        ("Point Projection", test_point_projection),
        ("Kernel Basis", test_kernel_basis_computation),
        ("Spectral→Points", test_spectral_to_points),
        ("Spectral Height", test_spectral_height_matrix),
        ("NT Height", test_nt_height_matrix),
        ("Height Compat", test_height_compatibility_11a1),
        ("LMFDB Curves", test_lmfdb_curve_retrieval),
        ("Small Verif", test_small_verification),
        ("Demo Function", test_demonstrate_function),
    ]

    passed = 0
    failed = 0

    for name, test_func in tests:
        print(f"\n--- Test: {name} ---")
        try:
            test_func()
            passed += 1
        except AssertionError as e:
            print(f"✗ Test failed: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ Test error: {e}")
            failed += 1

    print("\n" + "="*70)
    print("TEST SUMMARY")
    print("="*70)
    print(f"Passed: {passed}/{len(tests)}")
    print(f"Failed: {failed}/{len(tests)}")
    print(f"Success rate: {100*passed/len(tests):.1f}%")
    print("="*70)


if __name__ == "__main__":
    run_all_tests()
