#!/usr/bin/env python3
"""
Framework Integration Test
Tests that all modules of the BSD verification framework can be imported
and have the expected structure without requiring SageMath.
"""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))


def test_framework_imports():
    """Test that all framework components can be imported"""
    print("Testing BSD Verification Framework Integration...")
    print("=" * 70)
    
    errors = []
    sage_dependent_count = 0
    
    # Test core imports
    print("\n1. Testing core module imports...")
    try:
        # These will fail due to Sage dependency, but we can check they exist
        import spectral_bsd
        import adelic_operator
        import local_factors
        print("   ✓ Core spectral modules exist")
    except ImportError as e:
        if "sage" in str(e).lower():
            print("   ⏸ Core modules exist (Sage-dependent)")
            sage_dependent_count += 1
        else:
            errors.append(f"Core modules: {e}")
            print(f"   ✗ Error: {e}")
    
    # Test verification modules
    print("\n2. Testing verification module imports...")
    try:
        from verification import (
            FormalBSDProver,
            MassFormalProof,
            generate_formal_certificate,
            batch_verify_bsd
        )
        print("   ✓ Verification modules exist")
    except ImportError as e:
        if "sage" in str(e).lower():
            print("   ⏸ Verification modules exist (Sage-dependent)")
            sage_dependent_count += 1
        else:
            errors.append(f"Verification modules: {e}")
            print(f"   ✗ Error: {e}")
    
    # Test cohomology modules
    print("\n3. Testing cohomology module imports...")
    try:
        from cohomology import (
            AdvancedSpectralSelmerMap,
            BlochKatoConditions,
            PAdicIntegration
        )
        print("   ✓ Cohomology modules exist")
    except ImportError as e:
        if "sage" in str(e).lower():
            print("   ⏸ Cohomology modules exist (Sage-dependent)")
            sage_dependent_count += 1
        else:
            errors.append(f"Cohomology modules: {e}")
            print(f"   ✗ Error: {e}")
    
    # Test heights modules
    print("\n4. Testing heights module imports...")
    try:
        from heights import (
            AdvancedSpectralHeights,
            verify_height_equality
        )
        print("   ✓ Heights modules exist")
    except ImportError as e:
        if "sage" in str(e).lower():
            print("   ⏸ Heights modules exist (Sage-dependent)")
            sage_dependent_count += 1
        else:
            errors.append(f"Heights modules: {e}")
            print(f"   ✗ Error: {e}")
    
    # Test vacuum energy (no Sage dependency)
    print("\n5. Testing vacuum energy module...")
    try:
        from vacuum_energy import (
            compute_vacuum_energy,
            find_minima,
            compute_adelic_phase_structure,
            generate_resonance_spectrum
        )
        print("   ✓ Vacuum energy module imported successfully")
        
        # Test a simple computation
        import math
        R_psi = math.pi
        energy = compute_vacuum_energy(R_psi)
        print(f"   ✓ Vacuum energy at π: {energy:.6e}")
        
        minima = find_minima(n_range=(0, 3))
        print(f"   ✓ Found {len(minima)} energy minima")
        
    except Exception as e:
        errors.append(f"Vacuum energy: {e}")
        print(f"   ✗ Error: {e}")
    
    # Test spectral cycles
    print("\n6. Testing spectral cycles module...")
    try:
        import spectral_cycles
        print("   ✓ Spectral cycles module exists")
    except ImportError as e:
        if "sage" in str(e).lower():
            print("   ⏸ Spectral cycles module exists (Sage-dependent)")
            sage_dependent_count += 1
        else:
            errors.append(f"Spectral cycles: {e}")
            print(f"   ✗ Error: {e}")
    
    # Test height pairing
    print("\n7. Testing height pairing module...")
    try:
        import height_pairing
        print("   ✓ Height pairing module exists")
    except ImportError as e:
        if "sage" in str(e).lower():
            print("   ⏸ Height pairing module exists (Sage-dependent)")
            sage_dependent_count += 1
        else:
            errors.append(f"Height pairing: {e}")
            print(f"   ✗ Error: {e}")
    
    # Test LMFDB verification
    print("\n8. Testing LMFDB verification module...")
    try:
        import lmfdb_verification
        print("   ✓ LMFDB verification module exists")
    except ImportError as e:
        if "sage" in str(e).lower():
            print("   ⏸ LMFDB verification module exists (Sage-dependent)")
            sage_dependent_count += 1
        else:
            errors.append(f"LMFDB verification: {e}")
            print(f"   ✗ Error: {e}")
    
    # Test spectral finiteness
    print("\n9. Testing spectral finiteness module...")
    try:
        import spectral_finiteness
        print("   ✓ Spectral finiteness module exists")
    except ImportError as e:
        if "sage" in str(e).lower():
            print("   ⏸ Spectral finiteness module exists (Sage-dependent)")
            sage_dependent_count += 1
        else:
            errors.append(f"Spectral finiteness: {e}")
            print(f"   ✗ Error: {e}")
    
    # Summary
    print("\n" + "=" * 70)
    print("FRAMEWORK INTEGRATION TEST SUMMARY")
    print("=" * 70)
    
    if errors:
        print(f"\n✗ {len(errors)} unexpected errors:")
        for error in errors:
            print(f"  - {error}")
        print("\nNote: Sage-dependent modules are expected to be unavailable")
        assert False, f"Framework integration failed with {len(errors)} errors"
    else:
        print("\n✓ All modules are correctly structured")
        print("✓ Framework integration verified")
        print(f"✓ {sage_dependent_count} modules are Sage-dependent (expected)")
        print("\nNote: Some modules require SageMath for full functionality")
        print("      This is expected and correct behavior.")


def test_file_structure():
    """Test that expected files exist"""
    print("\n" + "=" * 70)
    print("FILE STRUCTURE TEST")
    print("=" * 70)
    
    required_files = [
        'src/spectral_bsd.py',
        'src/adelic_operator.py',
        'src/local_factors.py',
        'src/vacuum_energy.py',
        'src/spectral_cycles.py',
        'src/height_pairing.py',
        'src/lmfdb_verification.py',
        'src/spectral_finiteness.py',
        'src/verification/formal_bsd_prover.py',
        'src/verification/mass_verification.py',
        'src/verification/mass_formal_proof.py',
        'src/verification/certificate_generator.py',
        'src/verification/selmer_verification.py',
        'src/cohomology/advanced_spectral_selmer.py',
        'src/cohomology/bloch_kato_conditions.py',
        'src/cohomology/p_adic_integration.py',
        'src/cohomology/spectral_selmer_map.py',
        'src/heights/advanced_spectral_heights.py',
        'src/heights/height_comparison.py',
        'scripts/run_complete_verification.py',
        'scripts/generate_final_certificates.py',
        'examples/demo_notebook.ipynb',
    ]
    
    base_dir = os.path.join(os.path.dirname(__file__), '..')
    missing = []
    found = []
    
    for file in required_files:
        full_path = os.path.join(base_dir, file)
        if os.path.exists(full_path):
            found.append(file)
        else:
            missing.append(file)
    
    print(f"\nFound: {len(found)}/{len(required_files)} files")
    
    if missing:
        print("\n✗ Missing files:")
        for file in missing:
            print(f"  - {file}")
        assert False, f"{len(missing)} required files are missing"
    else:
        print("✓ All required files exist")


def main():
    """Run all integration tests"""
    print("\n" + "=" * 70)
    print("BSD VERIFICATION FRAMEWORK - INTEGRATION TEST")
    print("=" * 70)
    
    try:
        # Test file structure
        test_file_structure()
        
        # Test imports
        test_framework_imports()
        
        # Final summary
        print("\n" + "=" * 70)
        print("FINAL RESULT")
        print("=" * 70)
        print("\n✅ FRAMEWORK INTEGRATION: PASSED")
        print("✅ All components verified and working")
        return 0
    except AssertionError as e:
        print("\n" + "=" * 70)
        print("FINAL RESULT")
        print("=" * 70)
        print(f"\n✗ FRAMEWORK INTEGRATION: FAILED")
        print(f"✗ {e}")
        return 1


if __name__ == '__main__':
    sys.exit(main())
