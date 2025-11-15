"""
Test sage_plugin structure and setup

This test verifies that the sage_plugin directory is correctly structured
and can be imported (basic structure validation).
"""

import os
import sys
import pytest


def test_sage_plugin_structure():
    """Test that all required files exist in the sage_plugin structure"""
    base_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin'
    )
    
    required_files = [
        'setup.py',
        'README.md',
        'DEMO_bsd_sage.ipynb',
        'adelic_bsd/__init__.py',
        'adelic_bsd/verify.py',
    ]
    
    for filename in required_files:
        filepath = os.path.join(base_path, filename)
        assert os.path.exists(filepath), f"Required file {filename} does not exist"


def test_sage_plugin_setup_valid():
    """Test that setup.py is valid"""
    setup_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin',
        'setup.py'
    )
    
    with open(setup_path, 'r') as f:
        content = f.read()
        assert 'setup(' in content, "setup.py should contain setup() call"
        assert 'adelic_bsd' in content, "setup.py should reference adelic_bsd package"
        assert 'find_packages()' in content, "setup.py should use find_packages()"


def test_verify_module_structure():
    """Test that verify.py has proper structure"""
    verify_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin',
        'adelic_bsd',
        'verify.py'
    )
    
    with open(verify_path, 'r') as f:
        content = f.read()
        assert 'def verify_bsd' in content, "verify.py should define verify_bsd function"
        assert 'EllipticCurve' in content, "verify.py should import EllipticCurve"
        assert 'hashlib' in content, "verify.py should import hashlib"
        # Check function has proper docstring
        assert '"""' in content, "verify_bsd should have a docstring"
        assert 'Args:' in content, "verify_bsd docstring should have Args section"
        assert 'Returns:' in content, "verify_bsd docstring should have Returns section"


def test_init_exports_verify_bsd():
    """Test that __init__.py exports verify_bsd"""
    init_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin',
        'adelic_bsd',
        '__init__.py'
    )
    
    with open(init_path, 'r') as f:
        content = f.read()
        assert 'from .verify import verify_bsd' in content, "__init__.py should import verify_bsd"
        assert '__all__ = ["verify_bsd"]' in content, "__init__.py should export verify_bsd in __all__"


def test_demo_notebook_structure():
    """Test that demo notebook has proper structure"""
    notebook_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin',
        'DEMO_bsd_sage.ipynb'
    )
    
    with open(notebook_path, 'r') as f:
        content = f.read()
        assert '"cells"' in content, "Notebook should have cells"
        assert 'verify_bsd' in content, "Notebook should demonstrate verify_bsd"
        assert '11a1' in content, "Notebook should use example curve 11a1"


def test_readme_exists_and_contains_usage():
    """Test that README.md exists and has usage instructions"""
    readme_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin',
        'README.md'
    )
    
    with open(readme_path, 'r') as f:
        content = f.read()
        assert '# SageMath Plugin: adelic_bsd' in content, "README should have proper title"
        assert 'verify_bsd' in content, "README should mention verify_bsd function"
        assert 'Instalación' in content or 'Installation' in content, "README should have installation instructions"
        assert 'Uso' in content or 'Usage' in content, "README should have usage instructions"
