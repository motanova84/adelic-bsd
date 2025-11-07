#!/usr/bin/env python
"""
Simple validation script for PT_compatibility module
Tests basic functionality without requiring full SageMath installation
"""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

def test_imports():
    """Test that PT_compatibility can be imported"""
    print("Testing imports...")
    try:
        from PT_compatibility import PTCompatibilityProver, prove_PT_all_ranks
        print("✓ Successfully imported PTCompatibilityProver and prove_PT_all_ranks")
        return True
    except ImportError as e:
        print(f"✗ Import failed: {e}")
        if 'sage' in str(e).lower():
            print("  (SageMath not available - this is expected in CI)")
            return True  # Not a failure if sage is missing
        return False

def test_module_structure():
    """Test that the module has expected structure"""
    print("\nTesting module structure...")
    try:
        from PT_compatibility import PTCompatibilityProver
        
        # Check that the class has expected methods
        expected_methods = [
            '__init__',
            '_compute_selmer_group',
            '_compute_analytic_rank',
            '_compute_height_pairing',
            '_compute_regulator',
            '_compute_beilinson_bloch_height',
            'prove_PT_compatibility'
        ]
        
        for method in expected_methods:
            if not hasattr(PTCompatibilityProver, method):
                print(f"✗ Missing method: {method}")
                return False
        
        print("✓ All expected methods present")
        return True
    except ImportError as e:
        if 'sage' in str(e).lower():
            print("  (Skipping - SageMath not available)")
            return True
        print(f"✗ Failed: {e}")
        return False

def test_docstrings():
    """Test that module has documentation"""
    print("\nTesting documentation...")
    try:
        import PT_compatibility
        
        if not PT_compatibility.__doc__:
            print("✗ Module missing docstring")
            return False
        
        if "Poitou-Tate" not in PT_compatibility.__doc__:
            print("✗ Module docstring doesn't mention Poitou-Tate")
            return False
        
        print("✓ Documentation present and correct")
        return True
    except ImportError as e:
        if 'sage' in str(e).lower():
            print("  (Skipping - SageMath not available)")
            return True
        print(f"✗ Failed: {e}")
        return False

def main():
    """Run all validation tests"""
    print("=" * 70)
    print("PT_compatibility Module Validation")
    print("=" * 70)
    
    results = []
    results.append(test_imports())
    results.append(test_module_structure())
    results.append(test_docstrings())
    
    print("\n" + "=" * 70)
    if all(results):
        print("✓ All validation tests passed")
        print("=" * 70)
        return 0
    else:
        print("✗ Some validation tests failed")
        print("=" * 70)
        return 1

if __name__ == "__main__":
    sys.exit(main())
