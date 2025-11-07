"""
Tests for Spectral Selmer Map
Tests the spectral Selmer map implementation and related functionality
Comprehensive tests for the Selmer map implementation
"""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from sage.all import EllipticCurve


def test_spectral_selmer_map_initialization():
    """Test SpectralSelmerMap initialization"""
    from src.cohomology.spectral_selmer_map import SpectralSelmerMap
    
    E = EllipticCurve('11a1')
    p = 5
    
    selmer_map = SpectralSelmerMap(E, p)
    
    assert selmer_map.E == E
    assert selmer_map.p == p
    assert selmer_map.precision == 20
    assert selmer_map.reduction_type in ['good', 'multiplicative', 'additive']
    
    print("✓ SpectralSelmerMap initialization works")


def test_phi_global_map():
    """Test the global spectral Selmer map"""
    from src.cohomology.spectral_selmer_map import SpectralSelmerMap
    
    E = EllipticCurve('11a1')
    p = 5
    
    selmer_map = SpectralSelmerMap(E, p)
    
    # Create test vector
    v = [1, 0, 0, 0]
    
    # Apply the map
    cocycle = selmer_map.phi_global(v)
    
    assert 'cocycle' in cocycle
    assert 'in_h1f' in cocycle
    assert 'prime' in cocycle
    assert cocycle['prime'] == p
    
    print("✓ phi_global map works")


def test_reduction_type_detection():
    """Test reduction type detection for different curves"""
    from src.cohomology.spectral_selmer_map import SpectralSelmerMap
    
    # Good reduction at 5
    E1 = EllipticCurve('11a1')
    map1 = SpectralSelmerMap(E1, 5)
    assert map1.reduction_type == 'good'
    
    # Bad reduction
    E2 = EllipticCurve('11a1')
    map2 = SpectralSelmerMap(E2, 11)
    assert map2.reduction_type in ['multiplicative', 'additive']
    
    print("✓ Reduction type detection works")


def test_p_adic_integration():
    """Test p-adic integration module"""
    from src.cohomology.p_adic_integration import PAdicIntegrator
    
    E = EllipticCurve('11a1')
    p = 5
    
    integrator = PAdicIntegrator(E, p)
    
    # Test modular symbol integration
    modular_symbol = {'cusps': (0, 'oo')}
    integral = integrator.integrate_modular_symbol(modular_symbol, None)
    
    assert integral is not None
    
    print("✓ p-adic integration works")


def test_bloch_kato_conditions():
    """Test Bloch-Kato condition verification"""
    from src.cohomology.bloch_kato_conditions import BlochKatoVerifier
    
    E = EllipticCurve('11a1')
    p = 5
    
    verifier = BlochKatoVerifier(E)
    
    # Test with a simple cocycle
    cocycle = {'prime': p, 'reduction_type': 'good'}
    results = verifier.verify_global_conditions(cocycle, p)
    
    assert 'local_conditions' in results
    assert 'all_satisfied' in results
    
    print("✓ Bloch-Kato verification works")


def test_integration_spectral_to_selmer():
    """Test integration between spectral vectors and Selmer map"""
    from src.cohomology.spectral_selmer_map import SpectralSelmerMap
    from src.cohomology.bloch_kato_conditions import BlochKatoVerifier
    
    E = EllipticCurve('37a1')  # Rank 1 curve
    p = 5
    
    # Create Selmer map
    selmer_map = SpectralSelmerMap(E, p)
    
    # Create test spectral vector
    v = [1, 0]
    
    # Apply map
    cocycle = selmer_map.phi_global(v)
    
    # Verify conditions
    verifier = BlochKatoVerifier(E)
    is_valid = verifier.verify_selmer_class(cocycle, p)
    
    # Should work without errors
    assert isinstance(is_valid, bool)
    
    print("✓ Spectral to Selmer integration works")


def run_all_tests():
    """Run all tests"""
    print("\n" + "="*60)
    print("TESTING SPECTRAL SELMER MAP MODULE")
    print("="*60)
    print()
    
    tests = [
        test_spectral_selmer_map_initialization,
        test_phi_global_map,
        test_reduction_type_detection,
        test_p_adic_integration,
        test_bloch_kato_conditions,
        test_integration_spectral_to_selmer
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except Exception as e:
            print(f"✗ {test.__name__} failed: {e}")
            import traceback
            traceback.print_exc()
            failed += 1
    
    print()
    print("="*60)
    print(f"Tests passed: {passed}/{len(tests)}")
    if failed > 0:
        print(f"Tests failed: {failed}")
    print("="*60)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
