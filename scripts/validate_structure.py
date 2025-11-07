#!/usr/bin/env python
"""
Validate repository structure for advanced modules
Can run without SageMath
"""

import os
import sys


def check_file(path, description):
    """Check if a file exists"""
    if os.path.exists(path):
        print(f"✓ {description}: {path}")
        return True
    else:
        print(f"✗ {description} MISSING: {path}")
        return False


def check_directory(path, description):
    """Check if a directory exists"""
    if os.path.isdir(path):
        print(f"✓ {description}: {path}")
        return True
    else:
        print(f"✗ {description} MISSING: {path}")
        return False


def validate_structure():
    """Validate complete repository structure"""
    print("="*60)
    print("VALIDATING REPOSITORY STRUCTURE")
    print("="*60)

    checks = []

    # Check directories
    print("\n1. Checking directories...")
    checks.append(check_directory('src', 'Source directory'))
    checks.append(check_directory('src/cohomology', 'Cohomology module'))
    checks.append(check_directory('src/heights', 'Heights module'))
    checks.append(check_directory('src/verification', 'Verification module'))
    checks.append(check_directory('tests', 'Tests directory'))
    checks.append(check_directory('examples', 'Examples directory'))
    checks.append(check_directory('docs', 'Documentation directory'))

    # Check core module files
    print("\n2. Checking core modules...")
    checks.append(check_file('src/__init__.py', 'Main init'))
    checks.append(check_file('src/spectral_finiteness.py', 'Spectral finiteness'))
    checks.append(check_file('src/spectral_cycles.py', 'Spectral cycles'))
    checks.append(check_file('src/height_pairing.py', 'Height pairing'))
    checks.append(check_file('src/lmfdb_verification.py', 'LMFDB verification'))

    # Check cohomology module
    print("\n3. Checking cohomology module...")
    checks.append(check_file('src/cohomology/__init__.py', 'Cohomology init'))
    checks.append(check_file('src/cohomology/advanced_spectral_selmer.py', 'Selmer map'))

    # Check heights module
    print("\n4. Checking heights module...")
    checks.append(check_file('src/heights/__init__.py', 'Heights init'))
    checks.append(check_file('src/heights/advanced_spectral_heights.py', 'Height pairing'))

    # Check verification module
    print("\n5. Checking verification module...")
    checks.append(check_file('src/verification/__init__.py', 'Verification init'))
    checks.append(check_file('src/verification/formal_bsd_prover.py', 'Formal prover'))
    checks.append(check_file('src/verification/mass_formal_proof.py', 'Mass verification'))

    # Check tests
    print("\n6. Checking tests...")
    checks.append(check_file('tests/test_advanced_modules.py', 'Advanced tests'))
    checks.append(check_file('tests/test_spectral_cycles.py', 'Spectral cycles tests'))
    checks.append(check_file('tests/test_finiteness_basic.py', 'Basic tests'))

    # Check examples
    print("\n7. Checking examples...")
    checks.append(check_file('examples/advanced_bsd_demo.py', 'Advanced demo'))

    # Check documentation
    print("\n8. Checking documentation...")
    checks.append(check_file('docs/ADVANCED_MODULES.md', 'Advanced modules doc'))
    checks.append(check_file('docs/QUICKSTART_ADVANCED.md', 'Quick start guide'))
    checks.append(check_file('README.md', 'Main README'))
    checks.append(check_file('CONTRIBUTING.md', 'Contributing guide'))

    # Summary
    print("\n" + "="*60)
    passed = sum(checks)
    total = len(checks)
    print(f"RESULTS: {passed}/{total} checks passed")

    if passed == total:
        print("✓ All structure checks passed!")
        print("="*60)
        return True
    else:
        print(f"✗ {total - passed} checks failed")
        print("="*60)
        return False


def check_imports_syntax():
    """Check that Python files have valid syntax"""
    print("\n" + "="*60)
    print("CHECKING PYTHON SYNTAX")
    print("="*60)

    python_files = [
        'src/cohomology/advanced_spectral_selmer.py',
        'src/heights/advanced_spectral_heights.py',
        'src/verification/formal_bsd_prover.py',
        'src/verification/mass_formal_proof.py',
        'tests/test_advanced_modules.py',
        'examples/advanced_bsd_demo.py'
    ]

    all_valid = True
    for filepath in python_files:
        if os.path.exists(filepath):
            try:
                with open(filepath, 'r') as f:
                    compile(f.read(), filepath, 'exec')
                print(f"✓ Valid syntax: {filepath}")
            except SyntaxError as e:
                print(f"✗ Syntax error in {filepath}: {e}")
                all_valid = False
        else:
            print(f"✗ File not found: {filepath}")
            all_valid = False

    print("="*60)
    if all_valid:
        print("✓ All Python files have valid syntax")
    else:
        print("✗ Some files have syntax errors")

    return all_valid


if __name__ == '__main__':
    # Change to repository root
    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(script_dir)
    os.chdir(repo_root)

    print(f"Repository root: {repo_root}\n")

    # Run validations
    structure_ok = validate_structure()
    syntax_ok = check_imports_syntax()

    # Final result
    print("\n" + "="*60)
    if structure_ok and syntax_ok:
        print("✓✓✓ ALL VALIDATIONS PASSED ✓✓✓")
        print("="*60)
        sys.exit(0)
    else:
        print("✗✗✗ SOME VALIDATIONS FAILED ✗✗✗")
        print("="*60)
        sys.exit(1)
