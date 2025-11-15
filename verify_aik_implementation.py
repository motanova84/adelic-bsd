#!/usr/bin/env python3
"""
AIK Implementation Verification Script
======================================

This script verifies that the AIK (Activo Inmutable de Conocimiento) beacon
implementation is complete and working correctly.

It performs the following checks:
1. Cryptographic functions are available and working
2. Integrity hash generation is deterministic and unique
3. ECDSA signatures can be generated and verified
4. Tamper detection works correctly
5. All required files are present
6. Documentation is complete
"""

import sys
import os
from pathlib import Path

# Add paths for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'sage_plugin'))

def verify_imports():
    """Verify all required imports are available"""
    print("\n" + "="*70)
    print("1. VERIFYING IMPORTS")
    print("="*70)
    
    try:
        from adelic_bsd.verify import (
            generate_integrity_hash,
            generate_ecdsa_signature,
            verify_ecdsa_signature
        )
        print("✅ Core cryptographic functions imported successfully")
        return True
    except ImportError as e:
        print(f"❌ Import failed: {e}")
        return False


def verify_cryptographic_functions():
    """Verify cryptographic functions work correctly"""
    print("\n" + "="*70)
    print("2. VERIFYING CRYPTOGRAPHIC FUNCTIONS")
    print("="*70)
    
    from adelic_bsd.verify import (
        generate_integrity_hash,
        generate_ecdsa_signature,
        verify_ecdsa_signature
    )
    
    # Test data
    curve_data = {
        'curve_label': 'test_curve',
        'conductor': 11,
        'discriminant': -161051,
        'j_invariant': '123456',
        'analytic_rank': 0
    }
    l_value = 0.2538418608559107
    params = {'s': 1, 'timestamp': '2025-01-15T00:00:00Z'}
    
    # Test 1: Integrity hash generation
    print("\n  Testing integrity hash generation...")
    try:
        hash1 = generate_integrity_hash(curve_data, l_value, params)
        assert len(hash1) == 64, "Hash should be 64 characters"
        assert all(c in '0123456789abcdef' for c in hash1), "Hash should be hexadecimal"
        print(f"  ✅ Integrity hash: {hash1[:32]}...")
    except Exception as e:
        print(f"  ❌ Integrity hash failed: {e}")
        return False
    
    # Test 2: Determinism
    print("\n  Testing determinism...")
    try:
        hash2 = generate_integrity_hash(curve_data, l_value, params)
        assert hash1 == hash2, "Same input should produce same hash"
        print("  ✅ Hash generation is deterministic")
    except Exception as e:
        print(f"  ❌ Determinism test failed: {e}")
        return False
    
    # Test 3: Uniqueness
    print("\n  Testing uniqueness...")
    try:
        params_different = {'s': 2, 'timestamp': '2025-01-15T00:00:00Z'}
        hash3 = generate_integrity_hash(curve_data, l_value, params_different)
        assert hash1 != hash3, "Different input should produce different hash"
        print("  ✅ Different inputs produce different hashes")
    except Exception as e:
        print(f"  ❌ Uniqueness test failed: {e}")
        return False
    
    # Test 4: ECDSA signature generation
    print("\n  Testing ECDSA signature generation...")
    try:
        sig_data = generate_ecdsa_signature(hash1)
        assert 'signature' in sig_data
        assert 'public_key' in sig_data
        assert 'algorithm' in sig_data
        assert sig_data['algorithm'] == 'ECDSA-SECP256R1-SHA256'
        print(f"  ✅ ECDSA signature generated")
        print(f"     Algorithm: {sig_data['algorithm']}")
        print(f"     Curve: {sig_data['curve']}")
    except Exception as e:
        print(f"  ❌ Signature generation failed: {e}")
        return False
    
    # Test 5: Signature verification
    print("\n  Testing signature verification...")
    try:
        is_valid = verify_ecdsa_signature(hash1, sig_data)
        assert is_valid, "Valid signature should verify"
        print("  ✅ Valid signature verified successfully")
    except Exception as e:
        print(f"  ❌ Signature verification failed: {e}")
        return False
    
    # Test 6: Tamper detection
    print("\n  Testing tamper detection...")
    try:
        tampered_hash = "0" * 64
        is_invalid = verify_ecdsa_signature(tampered_hash, sig_data)
        assert not is_invalid, "Invalid signature should not verify"
        print("  ✅ Tampered signature correctly rejected")
    except Exception as e:
        print(f"  ❌ Tamper detection failed: {e}")
        return False
    
    print("\n✅ All cryptographic function tests passed")
    return True


def verify_file_structure():
    """Verify all required files are present"""
    print("\n" + "="*70)
    print("3. VERIFYING FILE STRUCTURE")
    print("="*70)
    
    repo_root = Path(__file__).parent
    
    required_files = {
        'Core Implementation': [
            'sage_plugin/adelic_bsd/__init__.py',
            'sage_plugin/adelic_bsd/verify.py',
        ],
        'Documentation': [
            'docs/AIK_BEACON_DOCUMENTATION.md',
            'sage_plugin/README.md',
            'AIK_IMPLEMENTATION_SUMMARY.md',
        ],
        'Testing': [
            'tests/test_aik_beacon.py',
        ],
        'Examples': [
            'examples/aik_beacon_demo.py',
        ],
        'Configuration': [
            'requirements.txt',
        ]
    }
    
    all_present = True
    for category, files in required_files.items():
        print(f"\n  {category}:")
        for file_path in files:
            full_path = repo_root / file_path
            if full_path.exists():
                print(f"    ✅ {file_path}")
            else:
                print(f"    ❌ {file_path} (MISSING)")
                all_present = False
    
    if all_present:
        print("\n✅ All required files are present")
    else:
        print("\n❌ Some files are missing")
    
    return all_present


def verify_documentation():
    """Verify documentation is complete"""
    print("\n" + "="*70)
    print("4. VERIFYING DOCUMENTATION")
    print("="*70)
    
    repo_root = Path(__file__).parent
    
    # Check AIK documentation
    aik_doc = repo_root / 'docs' / 'AIK_BEACON_DOCUMENTATION.md'
    if aik_doc.exists():
        content = aik_doc.read_text()
        required_sections = [
            'Integrity Audit',
            'Inmutabilidad',
            'ECDSA',
            'verify_bsd',
            'generate_integrity_hash',
            'generate_ecdsa_signature',
            'verify_ecdsa_signature'
        ]
        
        print("\n  Checking AIK_BEACON_DOCUMENTATION.md:")
        all_present = True
        for section in required_sections:
            if section in content:
                print(f"    ✅ {section}")
            else:
                print(f"    ❌ {section} (MISSING)")
                all_present = False
        
        if not all_present:
            return False
    else:
        print("  ❌ AIK_BEACON_DOCUMENTATION.md not found")
        return False
    
    # Check implementation summary
    summary = repo_root / 'AIK_IMPLEMENTATION_SUMMARY.md'
    if summary.exists():
        print("  ✅ AIK_IMPLEMENTATION_SUMMARY.md present")
    else:
        print("  ❌ AIK_IMPLEMENTATION_SUMMARY.md missing")
        return False
    
    print("\n✅ Documentation is complete")
    return True


def verify_requirements():
    """Verify requirements.txt includes cryptography"""
    print("\n" + "="*70)
    print("5. VERIFYING REQUIREMENTS")
    print("="*70)
    
    repo_root = Path(__file__).parent
    req_file = repo_root / 'requirements.txt'
    
    if req_file.exists():
        content = req_file.read_text()
        if 'cryptography' in content:
            print("  ✅ cryptography dependency present in requirements.txt")
            return True
        else:
            print("  ❌ cryptography dependency missing from requirements.txt")
            return False
    else:
        print("  ❌ requirements.txt not found")
        return False


def main():
    """Run all verification checks"""
    print("\n" + "="*70)
    print("AIK IMPLEMENTATION VERIFICATION")
    print("Activo Inmutable de Conocimiento - BSD Verification")
    print("="*70)
    
    checks = [
        ("Imports", verify_imports),
        ("Cryptographic Functions", verify_cryptographic_functions),
        ("File Structure", verify_file_structure),
        ("Documentation", verify_documentation),
        ("Requirements", verify_requirements),
    ]
    
    results = {}
    for name, check_func in checks:
        try:
            results[name] = check_func()
        except Exception as e:
            print(f"\n❌ Error in {name}: {e}")
            results[name] = False
    
    # Summary
    print("\n" + "="*70)
    print("VERIFICATION SUMMARY")
    print("="*70)
    
    all_passed = True
    for name, passed in results.items():
        status = "✅ PASSED" if passed else "❌ FAILED"
        print(f"  {name:.<30} {status}")
        if not passed:
            all_passed = False
    
    print("\n" + "="*70)
    if all_passed:
        print("🎉 ALL VERIFICATION CHECKS PASSED!")
        print("="*70)
        print("\nThe AIK beacon implementation is complete and working correctly.")
        print("\nKey capabilities:")
        print("  • Integrity hash generation (SHA-256)")
        print("  • ECDSA signature generation (SECP256R1)")
        print("  • Signature verification")
        print("  • Tamper detection")
        print("  • Complete documentation")
        print("  • Comprehensive test suite")
        print("\nThe BSD verification module is ready for use in the SageMath")
        print("computational mathematics ecosystem with full cryptographic")
        print("certification capabilities.")
        return 0
    else:
        print("❌ SOME VERIFICATION CHECKS FAILED")
        print("="*70)
        print("\nPlease review the failed checks above and address any issues.")
        return 1


if __name__ == "__main__":
    sys.exit(main())
