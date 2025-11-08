"""
Test SageMath integration module structure

This test verifies that the SageMath integration module is correctly structured
and can be imported (when SageMath is available).
"""

import os
import sys
import pytest


def test_module_structure():
    """Test that all required files exist in the SageMath integration structure"""
    base_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sagemath_integration',
        'sage',
        'schemes',
        'elliptic_curves',
        'bsd_spectral'
    )
    
    required_files = [
        '__init__.py',
        'spectral_finiteness.py',
        'dR_compatibility.py',
        'PT_compatibility.py',
        'all.py'
    ]
    
    for filename in required_files:
        filepath = os.path.join(base_path, filename)
        assert os.path.exists(filepath), f"Required file {filename} does not exist"
        
        # Check file is not empty (more than just a comment)
        with open(filepath, 'r') as f:
            content = f.read()
            assert len(content) > 100, f"File {filename} appears to be empty or too small"
            assert 'r"""' in content or '"""' in content, f"File {filename} missing docstring"


def test_module_imports_structure():
    """Test that module files have proper import structure"""
    base_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sagemath_integration',
        'sage',
        'schemes',
        'elliptic_curves',
        'bsd_spectral'
    )
    
    # Check __init__.py has lazy imports
    init_file = os.path.join(base_path, '__init__.py')
    with open(init_file, 'r') as f:
        content = f.read()
        assert 'lazy_import' in content, "__init__.py should use lazy imports"
        assert 'SpectralFinitenessProver' in content
        assert '__all__' in content
    
    # Check spectral_finiteness.py
    sf_file = os.path.join(base_path, 'spectral_finiteness.py')
    with open(sf_file, 'r') as f:
        content = f.read()
        assert 'class SpectralFinitenessProver' in content
        assert 'def prove_finiteness' in content
        assert 'EXAMPLES::' in content
        assert 'TESTS::' in content
    
    # Check dR_compatibility.py
    dr_file = os.path.join(base_path, 'dR_compatibility.py')
    with open(dr_file, 'r') as f:
        content = f.read()
        assert 'def verify_dR_compatibility' in content
        assert 'def compute_h1f_dimension' in content
        assert 'def compute_dR_dimension' in content
        assert 'EXAMPLES::' in content
    
    # Check PT_compatibility.py
    pt_file = os.path.join(base_path, 'PT_compatibility.py')
    with open(pt_file, 'r') as f:
        content = f.read()
        assert 'def verify_PT_compatibility' in content
        assert 'def compute_gross_zagier_height' in content
        assert 'def compute_yzz_height' in content
        assert 'EXAMPLES::' in content
    
    # Check all.py
    all_file = os.path.join(base_path, 'all.py')
    with open(all_file, 'r') as f:
        content = f.read()
        assert 'from sage.schemes.elliptic_curves.bsd_spectral.spectral_finiteness import' in content
        assert 'from sage.schemes.elliptic_curves.bsd_spectral.dR_compatibility import' in content
        assert 'from sage.schemes.elliptic_curves.bsd_spectral.PT_compatibility import' in content
        assert '__all__' in content


def test_docstring_format():
    """Test that docstrings follow SageMath conventions"""
    base_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sagemath_integration',
        'sage',
        'schemes',
        'elliptic_curves',
        'bsd_spectral'
    )
    
    files_to_check = [
        'spectral_finiteness.py',
        'dR_compatibility.py',
        'PT_compatibility.py'
    ]
    
    for filename in files_to_check:
        filepath = os.path.join(base_path, filename)
        with open(filepath, 'r') as f:
            content = f.read()
            
            # Check for SageMath-style docstrings
            assert 'EXAMPLES::' in content, f"{filename} should have EXAMPLES section"
            assert 'sage:' in content, f"{filename} should have sage prompt in examples"
            
            # Check for proper structure
            assert 'INPUT:' in content or 'OUTPUT:' in content, \
                f"{filename} should document inputs/outputs"
            
            # Check for references
            if filename == 'spectral_finiteness.py':
                assert 'REFERENCES:' in content
                assert 'ALGORITHM:' in content


def test_api_completeness():
    """Test that all required API functions are defined"""
    base_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sagemath_integration',
        'sage',
        'schemes',
        'elliptic_curves',
        'bsd_spectral'
    )
    
    # Check spectral_finiteness.py exports
    sf_file = os.path.join(base_path, 'spectral_finiteness.py')
    with open(sf_file, 'r') as f:
        content = f.read()
        assert 'class SpectralFinitenessProver:' in content
        assert 'def prove_sha_finiteness(' in content
    
    # Check dR_compatibility.py exports
    dr_file = os.path.join(base_path, 'dR_compatibility.py')
    with open(dr_file, 'r') as f:
        content = f.read()
        required_functions = [
            'verify_dR_compatibility',
            'compute_h1f_dimension',
            'compute_dR_dimension'
        ]
        for func in required_functions:
            assert f'def {func}(' in content, f"Function {func} not found"
    
    # Check PT_compatibility.py exports
    pt_file = os.path.join(base_path, 'PT_compatibility.py')
    with open(pt_file, 'r') as f:
        content = f.read()
        required_functions = [
            'verify_PT_compatibility',
            'compute_gross_zagier_height',
            'compute_yzz_height'
        ]
        for func in required_functions:
            assert f'def {func}(' in content, f"Function {func} not found"


def test_all_py_exports():
    """Test that all.py exports all required names"""
    base_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sagemath_integration',
        'sage',
        'schemes',
        'elliptic_curves',
        'bsd_spectral'
    )
    
    all_file = os.path.join(base_path, 'all.py')
    with open(all_file, 'r') as f:
        content = f.read()
        
        required_exports = [
            'SpectralFinitenessProver',
            'prove_sha_finiteness',
            'verify_dR_compatibility',
            'compute_h1f_dimension',
            'compute_dR_dimension',
            'verify_PT_compatibility',
            'compute_gross_zagier_height',
            'compute_yzz_height'
        ]
        
        for export in required_exports:
            assert export in content, f"Export {export} not found in all.py"


if __name__ == '__main__':
    # Run tests manually
    test_module_structure()
    print("✅ Module structure test passed")
    
    test_module_imports_structure()
    print("✅ Module imports structure test passed")
    
    test_docstring_format()
    print("✅ Docstring format test passed")
    
    test_api_completeness()
    print("✅ API completeness test passed")
    
    test_all_py_exports()
    print("✅ all.py exports test passed")
    
    print("\n✅ All tests passed!")
