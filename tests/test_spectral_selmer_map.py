"""
Tests for Spectral Selmer Map
Comprehensive tests for the Selmer map implementation
"""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from sage.all import EllipticCurve


def test_spectral_selmer_map_import():
    """Test that SpectralSelmerMap can be imported"""
    try:
        from src.cohomology.spectral_selmer_map import SpectralSelmerMap
        print("✓ SpectralSelmerMap imported successfully")
        return True
    except Exception as e:
        print(f"✗ Import failed: {e}")
        return False


def test_spectral_selmer_map_initialization():
    """Test SpectralSelmerMap initialization"""
    try:
        from src.cohomology.spectral_selmer_map import SpectralSelmerMap
        
        E = EllipticCurve('11a1')
        p = 2
        
        selmer = SpectralSelmerMap(E, p, precision=20)
        
        assert selmer.E == E
        assert selmer.p == p
        assert selmer.precision == 20
        
        print("✓ SpectralSelmerMap initialized correctly")
        return True
    except Exception as e:
        print(f"✗ Initialization failed: {e}")
        return False


def test_compute_selmer_map():
    """Test compute_selmer_map convenience function"""
    try:
        from src.cohomology.spectral_selmer_map import compute_selmer_map
        
        E = EllipticCurve('11a1')
        p = 2
        
        result = compute_selmer_map(E, p)
        
        assert result['map_initialized'] == True
        assert result['prime'] == p
        assert 'reduction_type' in result
        
        print("✓ compute_selmer_map works correctly")
        print(f"  Reduction type: {result['reduction_type']}")
        return True
    except Exception as e:
        print(f"✗ compute_selmer_map failed: {e}")
        return False


def test_verify_selmer_compatibility():
    """Test verify_selmer_compatibility function"""
    try:
        from src.cohomology.spectral_selmer_map import verify_selmer_compatibility
        
        E = EllipticCurve('37a1')
        p = 3
        
        result = verify_selmer_compatibility(E, p)
        
        assert 'map_well_defined' in result
        assert result['prime'] == p
        assert 'reduction_type' in result
        
        print("✓ verify_selmer_compatibility works")
        print(f"  Map well-defined: {result['map_well_defined']}")
        return True
    except Exception as e:
        print(f"✗ verify_selmer_compatibility failed: {e}")
        return False


def test_construct_global_selmer_group():
    """Test construct_global_selmer_group function"""
    try:
        from src.cohomology.spectral_selmer_map import construct_global_selmer_group
        
        E = EllipticCurve('11a1')
        
        result = construct_global_selmer_group(E)
        
        assert 'local_maps' in result
        assert 'primes' in result
        assert 'curve' in result
        
        print("✓ construct_global_selmer_group works")
        print(f"  Primes: {result['primes']}")
        print(f"  Local maps: {len(result['local_maps'])}")
        return True
    except Exception as e:
        print(f"✗ construct_global_selmer_group failed: {e}")
        return False


def test_selmer_map_different_reduction_types():
    """Test Selmer map on curves with different reduction types"""
    try:
        from src.cohomology.spectral_selmer_map import SpectralSelmerMap
        
        # Test curves with different properties
        test_cases = [
            ('11a1', 2, 'good/bad reduction'),
            ('37a1', 37, 'multiplicative reduction'),
            ('389a1', 389, 'additive reduction'),
        ]
        
        results = []
        for label, p, description in test_cases:
            E = EllipticCurve(label)
            selmer = SpectralSelmerMap(E, p)
            
            results.append({
                'curve': label,
                'prime': p,
                'reduction_type': selmer.reduction_type,
                'description': description
            })
        
        print("✓ Selmer map handles different reduction types")
        for r in results:
            print(f"  {r['curve']} at p={r['prime']}: {r['reduction_type']}")
        
        return True
    except Exception as e:
        print(f"✗ Different reduction types test failed: {e}")
        return False


def test_p_adic_integration_import():
    """Test p-adic integration module import"""
    try:
        from src.cohomology.p_adic_integration import PAdicIntegration
        print("✓ PAdicIntegration imported successfully")
        return True
    except Exception as e:
        print(f"✗ PAdicIntegration import failed: {e}")
        return False


def test_p_adic_integration():
    """Test p-adic integration functionality"""
    try:
        from src.cohomology.p_adic_integration import PAdicIntegration
        
        E = EllipticCurve('11a1')
        p = 2
        
        integrator = PAdicIntegration(E, p, precision=20)
        
        assert integrator.E == E
        assert integrator.p == p
        assert integrator.prec == 20
        
        print("✓ PAdicIntegration initialized")
        print(f"  Reduction type: {integrator.reduction_type}")
        return True
    except Exception as e:
        print(f"✗ PAdicIntegration test failed: {e}")
        return False


def test_bloch_kato_conditions_import():
    """Test Bloch-Kato conditions module import"""
    try:
        from src.cohomology.bloch_kato_conditions import BlochKatoConditions
        print("✓ BlochKatoConditions imported successfully")
        return True
    except Exception as e:
        print(f"✗ BlochKatoConditions import failed: {e}")
        return False


def test_bloch_kato_verification():
    """Test Bloch-Kato conditions verification"""
    try:
        from src.cohomology.bloch_kato_conditions import verify_bloch_kato
        
        E = EllipticCurve('11a1')
        p = 2
        
        result = verify_bloch_kato(E, p)
        
        assert 'curve' in result
        assert 'verification' in result
        assert 'certificate_valid' in result
        
        print("✓ Bloch-Kato verification works")
        print(f"  Certificate valid: {result['certificate_valid']}")
        return True
    except Exception as e:
        print(f"✗ Bloch-Kato verification failed: {e}")
        return False


def run_all_tests():
    """Run all tests"""
    print("\n" + "="*70)
    print("SPECTRAL SELMER MAP TESTS")
    print("="*70 + "\n")
    
    tests = [
        ("Import SpectralSelmerMap", test_spectral_selmer_map_import),
        ("Initialize SpectralSelmerMap", test_spectral_selmer_map_initialization),
        ("Compute Selmer map", test_compute_selmer_map),
        ("Verify Selmer compatibility", test_verify_selmer_compatibility),
        ("Construct global Selmer group", test_construct_global_selmer_group),
        ("Different reduction types", test_selmer_map_different_reduction_types),
        ("Import PAdicIntegration", test_p_adic_integration_import),
        ("Test p-adic integration", test_p_adic_integration),
        ("Import BlochKatoConditions", test_bloch_kato_conditions_import),
        ("Verify Bloch-Kato conditions", test_bloch_kato_verification),
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
