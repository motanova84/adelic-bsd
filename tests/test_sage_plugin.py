"""
Test sage_plugin module structure

This test verifies that the sage_plugin module is correctly structured
with all required files as specified in the problem statement.
"""

import os
import pytest
import json


def test_sage_plugin_structure():
    """Test that all required files exist in the sage_plugin structure"""
    base_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin'
    )
    
    # Check main directory exists
    assert os.path.exists(base_path), "sage_plugin directory does not exist"
    
    # Check required files in root
    required_root_files = [
        'setup.py',
        'DEMO_bsd_sage.ipynb',
        'README.md'
    ]
    
    for filename in required_root_files:
        filepath = os.path.join(base_path, filename)
        assert os.path.exists(filepath), f"Required file {filename} does not exist"
    
    # Check adelic_bsd package structure
    package_path = os.path.join(base_path, 'adelic_bsd')
    assert os.path.exists(package_path), "adelic_bsd package directory does not exist"
    
    required_package_files = [
        '__init__.py',
        'verify.py'
    ]
    
    for filename in required_package_files:
        filepath = os.path.join(package_path, filename)
        assert os.path.exists(filepath), f"Required package file {filename} does not exist"


def test_init_file_content():
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
        assert 'from .verify import verify_bsd' in content, "__init__.py missing import"
        assert '__all__ = ["verify_bsd"]' in content, "__init__.py missing __all__"


def test_verify_file_structure():
    """Test that verify.py contains verify_bsd function"""
    verify_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin',
        'adelic_bsd',
        'verify.py'
    )
    
    with open(verify_path, 'r') as f:
        content = f.read()
        assert 'def verify_bsd(label_or_curve, s=1):' in content, "verify_bsd function not found"
        assert 'EllipticCurve' in content, "Missing EllipticCurve import"
        assert 'hashlib' in content, "Missing hashlib import"
        assert 'return {' in content, "Function doesn't return dictionary"


def test_setup_file_content():
    """Test that setup.py has correct package configuration"""
    setup_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin',
        'setup.py'
    )
    
    with open(setup_path, 'r') as f:
        content = f.read()
        assert 'name="adelic_bsd"' in content, "Package name incorrect"
        assert 'version="0.1.0"' in content, "Version incorrect"
        assert 'José Manuel Mota Burruezo' in content, "Author incorrect"
        assert 'find_packages()' in content, "Missing find_packages()"


def test_demo_notebook_structure():
    """Test that DEMO notebook has correct structure"""
    notebook_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin',
        'DEMO_bsd_sage.ipynb'
    )
    
    with open(notebook_path, 'r') as f:
        content = json.load(f)
        
        # Check notebook structure
        assert 'cells' in content, "Notebook missing cells"
        assert len(content['cells']) == 2, "Notebook should have 2 cells"
        
        # Check metadata
        assert 'metadata' in content, "Notebook missing metadata"
        assert 'kernelspec' in content['metadata'], "Notebook missing kernelspec"
        assert content['metadata']['kernelspec']['name'] == 'sagemath', "Incorrect kernel"
        
        # Check cells content
        cells = content['cells']
        assert cells[0]['cell_type'] == 'markdown', "First cell should be markdown"
        assert 'DEMO BSD' in ''.join(cells[0]['source']), "Title missing from first cell"
        
        assert cells[1]['cell_type'] == 'code', "Second cell should be code"
        code_content = ''.join(cells[1]['source'])
        assert 'from adelic_bsd import verify_bsd' in code_content, "Missing import"
        assert 'verify_bsd("11a1", s=1)' in code_content, "Missing function call"


def test_readme_content():
    """Test that README.md has proper documentation"""
    readme_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin',
        'README.md'
    )
    
    with open(readme_path, 'r') as f:
        content = f.read()
        assert '# SageMath Plugin: adelic_bsd' in content, "Missing title"
        assert 'Instalación' in content or 'Installation' in content, "Missing installation section"
        assert 'verify_bsd' in content, "Missing function documentation"
        assert 'sage -pip install' in content, "Missing installation instructions"


def test_verify_function_docstring():
    """Test that verify_bsd has proper docstring"""
    verify_path = os.path.join(
        os.path.dirname(__file__), 
        '..', 
        'sage_plugin',
        'adelic_bsd',
        'verify.py'
    )
    
    with open(verify_path, 'r') as f:
        content = f.read()
        assert '"""' in content, "Missing docstring"
        assert 'Args:' in content, "Missing Args section in docstring"
        assert 'Returns:' in content, "Missing Returns section in docstring"
        assert 'label_or_curve' in content, "Missing parameter documentation"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
