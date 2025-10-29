"""
Pytest configuration and fixtures for adelic-bsd tests
"""

import pytest
import sys


def pytest_configure(config):
    """Configure pytest markers"""
    config.addinivalue_line(
        "markers", "sage_required: mark test as requiring SageMath"
    )


def check_sage_available():
    """Check if SageMath is available"""
    try:
        import sage.all
        return True
    except ImportError:
        return False


# Create a module-level flag for sage availability
sage_available = check_sage_available()


@pytest.fixture
def sage_available_fixture():
    """Fixture that provides sage availability status"""
    return sage_available


def pytest_collection_modifyitems(config, items):
    """
    Automatically mark tests in sage-requiring modules and skip them if sage is not available
    """
    sage_required_modules = [
        'test_advanced_modules',
        'test_certificate_generation',
        'test_finiteness',
        'test_integration_advanced',
        'test_lmfdb_crosscheck',
        'test_spectral_core',
        'test_spectral_cycles',
        'test_spectral_selmer_map',
    ]

    skip_sage = pytest.mark.skip(reason="SageMath not available")
    mark_sage_required = pytest.mark.sage_required

    for item in items:
        # Get the module name from the test's nodeid
        module_name = item.nodeid.split("::")[0].replace("tests/", "").replace(".py", "")

        # Check if this test is in a sage-required module
        if module_name in sage_required_modules:
            item.add_marker(mark_sage_required)
            if not sage_available:
                item.add_marker(skip_sage)
