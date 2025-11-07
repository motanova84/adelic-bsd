"""
Tests for setup_sagemath_module - SageMath integration preparation
"""

import sys
import os
import pytest
from pathlib import Path
import shutil

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))


@pytest.fixture
def cleanup_sagemath_integration():
    """Cleanup fixture to remove generated sagemath_integration directory"""
    yield
    # Cleanup after test
    integration_dir = Path(__file__).parent.parent / 'sagemath_integration'
    if integration_dir.exists():
        shutil.rmtree(integration_dir)


@pytest.mark.basic
def test_setup_module_exists():
    """Test that setup_sagemath_module.py exists"""
    module_path = Path(__file__).parent.parent / 'setup_sagemath_module.py'
    assert module_path.exists(), "setup_sagemath_module.py not found"
    print("✓ setup_sagemath_module.py exists")


@pytest.mark.basic
def test_setup_module_imports():
    """Test that the module can be imported"""
    try:
        import setup_sagemath_module
        assert setup_sagemath_module is not None
        print("✓ setup_sagemath_module can be imported")
    except ImportError as e:
        pytest.fail(f"Cannot import setup_sagemath_module: {e}")


@pytest.mark.basic
def test_functions_exist():
    """Test that key functions exist"""
    import setup_sagemath_module
    
    assert hasattr(setup_sagemath_module, 'create_sagemath_package_structure')
    assert hasattr(setup_sagemath_module, 'generate_sagemath_docstrings')
    assert hasattr(setup_sagemath_module, 'create_sagemath_tests')
    assert hasattr(setup_sagemath_module, 'generate_integration_pr')
    assert hasattr(setup_sagemath_module, 'execute_integration_plan')
    
    print("✓ All key functions exist")


@pytest.mark.basic
def test_create_structure(cleanup_sagemath_integration):
    """Test structure creation"""
    import setup_sagemath_module
    
    base = setup_sagemath_module.create_sagemath_package_structure()
    
    # Check that directory was created
    assert base.exists()
    assert (base / 'sage').exists()
    assert (base / 'doc').exists()
    
    # Check key subdirectories
    assert (base / 'sage' / 'schemes' / 'elliptic_curves' / 'bsd_spectral').exists()
    assert (base / 'doc' / 'en' / 'reference' / 'bsd_spectral').exists()
    
    print("✓ Structure creation works")


@pytest.mark.basic
def test_generate_docstrings():
    """Test docstring generation"""
    import setup_sagemath_module
    
    docstrings = setup_sagemath_module.generate_sagemath_docstrings()
    
    # Check that docstring contains key elements
    assert 'r"""' in docstrings
    assert 'BSD Spectral Framework' in docstrings
    assert 'EXAMPLES::' in docstrings
    assert 'REFERENCES:' in docstrings
    assert 'AUTHORS:' in docstrings
    
    print("✓ Docstring generation works")


@pytest.mark.basic
def test_generate_tests():
    """Test test generation"""
    import setup_sagemath_module
    
    tests = setup_sagemath_module.create_sagemath_tests()
    
    # Check that tests contain key elements
    assert 'def test_spectral_finiteness()' in tests
    assert 'EXAMPLES::' in tests
    assert 'TESTS::' in tests
    assert 'sage:' in tests
    
    print("✓ Test generation works")


@pytest.mark.basic
def test_generate_pr_template():
    """Test PR template generation"""
    import setup_sagemath_module
    
    pr = setup_sagemath_module.generate_integration_pr()
    
    # Check that PR contains key sections
    assert '# Pull Request:' in pr
    assert '## Summary' in pr
    assert '## Features' in pr
    assert '## Usage' in pr
    assert '## Testing' in pr
    assert '## References' in pr
    assert '## Checklist' in pr
    
    print("✓ PR template generation works")


@pytest.mark.basic
def test_execute_integration_plan(cleanup_sagemath_integration):
    """Test the complete integration plan execution"""
    import setup_sagemath_module
    
    setup_sagemath_module.execute_integration_plan()
    
    base = Path(__file__).parent.parent / 'sagemath_integration'
    
    # Check that all expected files were created
    assert (base / 'docstrings_template.py').exists()
    assert (base / 'tests_template.py').exists()
    assert (base / 'PULL_REQUEST_TEMPLATE.md').exists()
    assert (base / 'INTEGRATION_INSTRUCTIONS.md').exists()
    
    # Check that key Python modules are present
    assert (base / 'sage' / 'schemes' / 'elliptic_curves' / 'bsd_spectral' / '__init__.py').exists()
    assert (base / 'sage' / 'schemes' / 'elliptic_curves' / 'bsd_spectral' / 'spectral_finiteness.py').exists()
    assert (base / 'sage' / 'schemes' / 'elliptic_curves' / 'bsd_spectral' / 'dR_compatibility.py').exists()
    assert (base / 'sage' / 'schemes' / 'elliptic_curves' / 'bsd_spectral' / 'PT_compatibility.py').exists()
    
    # Check that documentation files are present
    assert (base / 'doc' / 'en' / 'reference' / 'bsd_spectral' / 'index.rst').exists()
    
    print("✓ Complete integration plan execution works")


@pytest.mark.basic
def test_integration_instructions_content(cleanup_sagemath_integration):
    """Test that integration instructions are comprehensive"""
    import setup_sagemath_module
    
    setup_sagemath_module.execute_integration_plan()
    
    base = Path(__file__).parent.parent / 'sagemath_integration'
    instructions = (base / 'INTEGRATION_INSTRUCTIONS.md').read_text()
    
    # Check for key sections
    assert 'Paso 1: Preparar Fork' in instructions or 'Step 1: Prepare Fork' in instructions
    assert 'Paso 2: Copiar Archivos' in instructions or 'Step 2: Copy Files' in instructions
    assert 'git clone' in instructions
    assert 'sage -t' in instructions
    
    print("✓ Integration instructions are comprehensive")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
