"""
Basic tests that don't require SageMath
Tests the structure and imports of the package
"""

import sys
import os


def test_package_structure():
    """Test that the package structure is correct"""
    # Check that src directory exists
    assert os.path.isdir('src'), "src directory should exist"

    # Check that key files exist
    assert os.path.isfile('src/spectral_finiteness.py'), "Main module should exist"
    assert os.path.isfile('src/__init__.py'), "__init__.py should exist"
    assert os.path.isfile('setup.py'), "setup.py should exist"
    assert os.path.isfile('requirements.txt'), "requirements.txt should exist"

    print("✓ Package structure is correct")


def test_imports():
    """Test that the module can be imported (structure only)"""
    # Add parent directory to path
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

    try:
        # This will fail without Sage but tests the import structure
        import src
        assert hasattr(src, '__version__'), "Package should have version"
        print("✓ Module imports correctly")
    except ImportError as e:
        # Expected when Sage is not installed
        if 'sage' in str(e).lower():
            print("⚠ Sage not installed - skipping full import test")
            # But we can still check the file exists and has basic structure
            with open('src/__init__.py', 'r') as f:
                content = f.read()
                assert '__version__' in content, "Version should be defined"
                print("✓ Module structure is correct")
        else:
            raise


def test_documentation():
    """Test that documentation files exist"""
    docs = ['README.md', 'USAGE.md', 'CONTRIBUTING.md', 'LICENSE']
    for doc in docs:
        assert os.path.isfile(doc), f"{doc} should exist"

    # Check README content
    with open('README.md', 'r') as f:
        content = f.read()
        assert 'Algoritmo' in content or 'algoritmo' in content
        assert 'Installation' in content
        assert 'Usage' in content

    print("✓ Documentation files present and valid")


def test_example_files():
    """Test that example files exist"""
    assert os.path.isdir('examples'), "examples directory should exist"
    assert os.path.isfile('examples/quick_demo.py'), "quick_demo.py should exist"

    print("✓ Example files present")


def test_configuration_files():
    """Test that configuration files are present"""
    config_files = [
        'environment.yml',
        'pytest.ini',
        '.gitignore',
        'MANIFEST.in'
    ]

    for config_file in config_files:
        assert os.path.isfile(config_file), f"{config_file} should exist"

    print("✓ Configuration files present")


if __name__ == "__main__":
    print("Running basic package tests...")
    print("=" * 50)

    test_package_structure()
    test_imports()
    test_documentation()
    test_example_files()
    test_configuration_files()

    print("=" * 50)
    print("🎉 ALL BASIC TESTS PASSED!")
