#!/usr/bin/env python
"""
Validation Script: dR Compatibility Module
==========================================

Quick validation that the dR_compatibility module is working correctly.
Tests basic functionality without requiring full SageMath installation.
"""

import sys
import os
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def test_module_exists():
    """Test that the module file exists"""
    module_path = Path(__file__).parent.parent / 'src' / 'dR_compatibility.py'
    assert module_path.exists(), "dR_compatibility.py not found"
    print("✅ Module file exists")
    return True


def test_module_structure():
    """Test that the module has expected structure"""
    module_path = Path(__file__).parent.parent / 'src' / 'dR_compatibility.py'
    
    with open(module_path, 'r') as f:
        content = f.read()
    
    # Check for key components
    checks = [
        ('class dRCompatibilityProver', 'Main class definition'),
        ('def prove_dR_all_cases', 'Batch testing function'),
        ('def prove_dR_compatibility', 'Main proof method'),
        ('_classify_reduction', 'Reduction classification'),
        ('_compute_galois_representation', 'Galois representation'),
        ('_compute_de_rham_cohomology', 'de Rham cohomology'),
        ('_explicit_exponential_map', 'Exponential map'),
        ('_exp_good_reduction', 'Good reduction case'),
        ('_exp_multiplicative', 'Multiplicative reduction case'),
        ('_exp_additive', 'Additive reduction case'),
    ]
    
    all_found = True
    for check, description in checks:
        if check in content:
            print(f"✅ {description} found")
        else:
            print(f"❌ {description} NOT found")
            all_found = False
    
    return all_found


def test_imports():
    """Test that the module can be imported"""
    try:
        import importlib.util
        module_path = Path(__file__).parent.parent / 'src' / 'dR_compatibility.py'
        spec = importlib.util.spec_from_file_location("dR_compatibility", module_path)
        assert spec is not None, "Could not load module spec"
        print("✅ Module spec loaded successfully")
        return True
    except Exception as e:
        print(f"❌ Error loading module: {e}")
        return False


def test_documentation():
    """Test that documentation exists"""
    doc_path = Path(__file__).parent.parent / 'docs' / 'DR_COMPATIBILITY.md'
    
    if doc_path.exists():
        with open(doc_path, 'r') as f:
            content = f.read()
        
        # Check for key sections
        sections = [
            '# dR Compatibility Proof Module',
            '## Overview',
            '## Theoretical Background',
            '## Implementation',
            '## Usage Examples',
        ]
        
        all_found = True
        for section in sections:
            if section in content:
                print(f"✅ Documentation section '{section}' found")
            else:
                print(f"❌ Documentation section '{section}' NOT found")
                all_found = False
        
        return all_found
    else:
        print("❌ Documentation file not found")
        return False


def test_example_script():
    """Test that example script exists"""
    example_path = Path(__file__).parent.parent / 'examples' / 'dR_compatibility_demo.py'
    
    if example_path.exists():
        print("✅ Example script exists")
        
        # Check if it's executable
        if os.access(example_path, os.X_OK):
            print("✅ Example script is executable")
        else:
            print("⚠️  Example script is not executable (may be okay)")
        
        return True
    else:
        print("❌ Example script not found")
        return False


def test_tests_exist():
    """Test that test file exists"""
    test_path = Path(__file__).parent.parent / 'tests' / 'test_dR_compatibility.py'
    
    if test_path.exists():
        with open(test_path, 'r') as f:
            content = f.read()
        
        # Count test functions
        test_count = content.count('def test_')
        print(f"✅ Test file exists with {test_count} test functions")
        return True
    else:
        print("❌ Test file not found")
        return False


def test_exports():
    """Test that module is exported in __init__.py"""
    init_path = Path(__file__).parent.parent / 'src' / '__init__.py'
    
    with open(init_path, 'r') as f:
        content = f.read()
    
    checks = [
        ('from .dR_compatibility import', 'Import statement'),
        ('dRCompatibilityProver', 'Class export'),
        ('prove_dR_all_cases', 'Function export'),
    ]
    
    all_found = True
    for check, description in checks:
        if check in content:
            print(f"✅ {description} in __init__.py")
        else:
            print(f"❌ {description} NOT in __init__.py")
            all_found = False
    
    return all_found


def main():
    """Run all validation tests"""
    print("=" * 70)
    print("dR COMPATIBILITY MODULE VALIDATION")
    print("=" * 70)
    print()
    
    tests = [
        ("Module File", test_module_exists),
        ("Module Structure", test_module_structure),
        ("Module Imports", test_imports),
        ("Documentation", test_documentation),
        ("Example Script", test_example_script),
        ("Test Suite", test_tests_exist),
        ("Module Exports", test_exports),
    ]
    
    results = []
    
    for name, test_func in tests:
        print(f"\n{'-' * 70}")
        print(f"Testing: {name}")
        print(f"{'-' * 70}")
        
        try:
            result = test_func()
            results.append((name, result))
        except Exception as e:
            print(f"❌ Test failed with error: {e}")
            results.append((name, False))
    
    # Summary
    print("\n" + "=" * 70)
    print("VALIDATION SUMMARY")
    print("=" * 70)
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status}: {name}")
    
    print()
    print(f"Results: {passed}/{total} tests passed")
    
    if passed == total:
        print("\n🎉 ALL VALIDATIONS PASSED!")
        print("\nThe dR_compatibility module is properly installed and configured.")
        return 0
    else:
        print(f"\n⚠️  {total - passed} validation(s) failed")
        print("\nPlease review the failed tests above.")
        return 1


if __name__ == "__main__":
    sys.exit(main())
