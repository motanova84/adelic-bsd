#!/usr/bin/env python3
"""
Structural validation for analytical BSD proof implementation
==============================================================

This script validates that all required files and structures are in place
for the analytical BSD proof, without requiring SageMath.

It checks:
1. LaTeX file structure and content
2. Python module structure and imports
3. Test file structure
4. Demo file structure
5. Documentation references
"""

import os
import sys
import re
from pathlib import Path


def check_file_exists(filepath, description):
    """Check if a file exists and report"""
    if os.path.exists(filepath):
        print(f"✓ {description}: {filepath}")
        return True
    else:
        print(f"✗ {description}: {filepath} NOT FOUND")
        return False


def check_latex_structure(filepath):
    """Check LaTeX file has expected structure"""
    print(f"\nChecking LaTeX file: {filepath}")
    
    if not os.path.exists(filepath):
        print(f"✗ File not found: {filepath}")
        return False
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    checks = {
        'section': r'\\section\{.*Identidad.*BSD.*\}',
        'definition': r'\\begin\{definition\}',
        'theorem': r'\\begin\{theorem\}',
        'proof': r'\\begin\{proof\}',
        'M_E operator': r'M_E\(s\)',
        'determinant': r'\\det\(I - M_E',
        'L function': r'L\(E.*s\)',
        'Fredholm': r'Fredholm',
        'trace': r'\\operatorname\{Tr\}',
    }
    
    results = []
    for name, pattern in checks.items():
        if re.search(pattern, content):
            print(f"  ✓ Contains {name}")
            results.append(True)
        else:
            print(f"  ✗ Missing {name}")
            results.append(False)
    
    return all(results)


def check_python_module(filepath):
    """Check Python module has expected structure"""
    print(f"\nChecking Python module: {filepath}")
    
    if not os.path.exists(filepath):
        print(f"✗ File not found: {filepath}")
        return False
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    checks = {
        'SpectralOperatorBSD class': r'class SpectralOperatorBSD',
        'fourier_coeffs property': r'def fourier_coeffs',
        'compute_trace method': r'def compute_trace',
        'fredholm_determinant method': r'def fredholm_determinant',
        'compare_with_L_function method': r'def compare_with_L_function',
        'verify_compactness method': r'def verify_compactness',
        'verify_nuclearity method': r'def verify_nuclearity',
        'demonstrate_analytical_bsd function': r'def demonstrate_analytical_bsd',
        'batch_verification function': r'def batch_verification',
    }
    
    results = []
    for name, pattern in checks.items():
        if re.search(pattern, content):
            print(f"  ✓ Contains {name}")
            results.append(True)
        else:
            print(f"  ✗ Missing {name}")
            results.append(False)
    
    return all(results)


def check_test_module(filepath):
    """Check test module has expected structure"""
    print(f"\nChecking test module: {filepath}")
    
    if not os.path.exists(filepath):
        print(f"✗ File not found: {filepath}")
        return False
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    checks = {
        'TestSpectralOperatorBSD class': r'class TestSpectralOperatorBSD',
        'test_initialization': r'def test_initialization',
        'test_fourier_coefficients': r'def test_fourier_coefficients',
        'test_compute_trace': r'def test_compute_trace',
        'test_fredholm_determinant': r'def test_fredholm_determinant',
        'test_compare_with_L_function': r'def test_compare_with_L_function',
        'TestDemonstrateAnalyticalBSD class': r'class TestDemonstrateAnalyticalBSD',
        'TestBatchVerification class': r'class TestBatchVerification',
        'pytest.mark.skipif': r'pytest\.mark\.skipif',
    }
    
    results = []
    for name, pattern in checks.items():
        if re.search(pattern, content):
            print(f"  ✓ Contains {name}")
            results.append(True)
        else:
            print(f"  ✗ Missing {name}")
            results.append(False)
    
    return all(results)


def check_demo_file(filepath):
    """Check demo file has expected structure"""
    print(f"\nChecking demo file: {filepath}")
    
    if not os.path.exists(filepath):
        print(f"✗ File not found: {filepath}")
        return False
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    checks = {
        'demo_basic_example': r'def demo_basic_example',
        'demo_trace_computations': r'def demo_trace_computations',
        'demo_fredholm_expansion': r'def demo_fredholm_expansion',
        'demo_comparison_with_L_function': r'def demo_comparison_with_L_function',
        'demo_multiple_curves': r'def demo_multiple_curves',
        'main function': r'def main\(\)',
        'shebang': r'#!/usr/bin/env python3',
    }
    
    results = []
    for name, pattern in checks.items():
        if re.search(pattern, content):
            print(f"  ✓ Contains {name}")
            results.append(True)
        else:
            print(f"  ✗ Missing {name}")
            results.append(False)
    
    return all(results)


def check_readme_references(filepath):
    """Check README has references to analytical BSD proof"""
    print(f"\nChecking README references: {filepath}")
    
    if not os.path.exists(filepath):
        print(f"✗ File not found: {filepath}")
        return False
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    checks = {
        'Analytical BSD mention': r'[Aa]nalytical.*BSD',
        'analytical_bsd_proof.py reference': r'analytical_bsd_proof\.py',
        'demonstrate_analytical_bsd mention': r'demonstrate_analytical_bsd',
        'LaTeX paper reference': r'12_analytical_bsd_identity\.tex',
    }
    
    results = []
    for name, pattern in checks.items():
        if re.search(pattern, content):
            print(f"  ✓ Contains {name}")
            results.append(True)
        else:
            print(f"  ✗ Missing {name}")
            results.append(False)
    
    return all(results)


def check_paper_integration(main_tex):
    """Check that main.tex includes the new section"""
    print(f"\nChecking paper integration: {main_tex}")
    
    if not os.path.exists(main_tex):
        print(f"✗ File not found: {main_tex}")
        return False
    
    with open(main_tex, 'r', encoding='utf-8') as f:
        content = f.read()
    
    if r'\input{sections/12_analytical_bsd_identity.tex}' in content:
        print("  ✓ Main paper includes analytical BSD section")
        return True
    else:
        print("  ✗ Main paper does NOT include analytical BSD section")
        return False


def main():
    """Run all validation checks"""
    print("=" * 80)
    print("Analytical BSD Proof Structure Validation")
    print("=" * 80)
    print()
    
    base_dir = Path(__file__).parent
    
    # Files to check
    files = {
        'LaTeX paper': base_dir / 'paper' / 'sections' / '12_analytical_bsd_identity.tex',
        'Python module': base_dir / 'src' / 'analytical_bsd_proof.py',
        'Test module': base_dir / 'tests' / 'test_analytical_bsd_proof.py',
        'Demo file': base_dir / 'examples' / 'analytical_bsd_demo.py',
        'README': base_dir / 'README.md',
        'Main paper': base_dir / 'paper' / 'main.tex',
    }
    
    print("1. Checking file existence:")
    print("-" * 80)
    existence_results = []
    for desc, filepath in files.items():
        result = check_file_exists(filepath, desc)
        existence_results.append(result)
    
    print("\n" + "=" * 80)
    print("2. Detailed structure validation:")
    print("=" * 80)
    
    structure_results = []
    
    # Check LaTeX structure
    structure_results.append(check_latex_structure(files['LaTeX paper']))
    
    # Check Python module structure
    structure_results.append(check_python_module(files['Python module']))
    
    # Check test module structure
    structure_results.append(check_test_module(files['Test module']))
    
    # Check demo file structure
    structure_results.append(check_demo_file(files['Demo file']))
    
    # Check README references
    structure_results.append(check_readme_references(files['README']))
    
    # Check paper integration
    structure_results.append(check_paper_integration(files['Main paper']))
    
    # Summary
    print("\n" + "=" * 80)
    print("VALIDATION SUMMARY")
    print("=" * 80)
    print()
    
    total_checks = len(existence_results) + len(structure_results)
    passed_checks = sum(existence_results) + sum(structure_results)
    
    print(f"File existence: {sum(existence_results)}/{len(existence_results)} passed")
    print(f"Structure validation: {sum(structure_results)}/{len(structure_results)} passed")
    print()
    print(f"Overall: {passed_checks}/{total_checks} checks passed")
    print()
    
    if all(existence_results) and all(structure_results):
        print("✓ All validation checks PASSED!")
        print()
        print("The analytical BSD proof implementation is structurally complete.")
        print("Run tests with SageMath to verify full functionality:")
        print("  pytest tests/test_analytical_bsd_proof.py -v")
        print()
        return 0
    else:
        print("✗ Some validation checks FAILED")
        print()
        print("Please review the failures above and fix them.")
        print()
        return 1


if __name__ == '__main__':
    sys.exit(main())
