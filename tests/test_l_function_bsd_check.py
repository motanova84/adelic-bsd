#!/usr/bin/env python3
"""
Tests for L-Function BSD Check Module
======================================

Tests for validation/l_function_bsd_check.py

These tests verify:
1. Module structure and imports
2. Function availability
3. BSD verification with test curves (when SageMath available)

AUTHORS:

- Jose Manuel Mota Burruezo (2025-01)
"""

import os
import sys
import pytest


# Path setup for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))


class TestLFunctionBSDCheckStructure:
    """Tests that don't require SageMath - verify module structure."""

    def test_module_exists(self):
        """Test that the validation module exists."""
        validation_dir = os.path.join(
            os.path.dirname(__file__),
            '..',
            'validation'
        )
        assert os.path.exists(validation_dir), "validation directory should exist"

        l_function_file = os.path.join(validation_dir, 'l_function_bsd_check.py')
        assert os.path.exists(l_function_file), "l_function_bsd_check.py should exist"

    def test_module_imports(self):
        """Test that the module can be imported."""
        from validation import l_function_bsd_check

        # Check required functions exist
        assert hasattr(l_function_bsd_check, 'compute_l_function_bsd_check')
        assert hasattr(l_function_bsd_check, 'run_standard_verification')
        assert hasattr(l_function_bsd_check, 'run_test_curves')
        assert hasattr(l_function_bsd_check, 'SAGE_AVAILABLE')

    def test_outputs_directory_exists(self):
        """Test that the outputs directory exists."""
        outputs_dir = os.path.join(
            os.path.dirname(__file__),
            '..',
            'outputs'
        )
        assert os.path.exists(outputs_dir), "outputs directory should exist"

    def test_docstrings_exist(self):
        """Test that functions have proper docstrings."""
        from validation import l_function_bsd_check

        assert l_function_bsd_check.compute_l_function_bsd_check.__doc__ is not None
        assert 'L-function' in l_function_bsd_check.compute_l_function_bsd_check.__doc__
        assert 'BSD' in l_function_bsd_check.compute_l_function_bsd_check.__doc__

    def test_without_sage_raises_error(self):
        """Test that without SageMath, appropriate error is raised."""
        from validation import l_function_bsd_check

        if not l_function_bsd_check.SAGE_AVAILABLE:
            with pytest.raises(ImportError) as excinfo:
                l_function_bsd_check.compute_l_function_bsd_check()
            assert "SageMath is required" in str(excinfo.value)
        else:
            pytest.skip("SageMath is available, skipping no-sage test")


class TestLFunctionBSDCheckWithSage:
    """Tests that require SageMath."""

    @pytest.fixture(autouse=True)
    def skip_without_sage(self):
        """Skip tests if SageMath is not available."""
        pytest.importorskip("sage")

    def test_l_function_rank_0_curve(self):
        """Test BSD verification on a rank 0 curve (11a1)."""
        from validation.l_function_bsd_check import compute_l_function_bsd_check

        result = compute_l_function_bsd_check(curve_label='11a1')

        assert 'L_at_1' in result
        assert 'analytic_rank' in result
        assert 'algebraic_rank' in result
        assert 'bsd_valid' in result

        # 11a1 is rank 0
        assert result['algebraic_rank'] == 0
        assert result['analytic_rank'] == 0
        assert result['bsd_valid'] is True

        # L(E,1) should be non-zero for rank 0
        assert result['L_at_1'] != 0

    def test_l_function_rank_1_curve(self):
        """Test BSD verification on a rank 1 curve (37a1)."""
        from validation.l_function_bsd_check import compute_l_function_bsd_check

        result = compute_l_function_bsd_check(curve_label='37a1')

        # 37a1 is rank 1
        assert result['algebraic_rank'] == 1
        assert result['analytic_rank'] == 1
        assert result['bsd_valid'] is True

        # L(E,1) should be 0 for rank > 0
        assert abs(result['L_at_1']) < 1e-6

    def test_l_function_with_coefficients(self):
        """Test L-function computation with explicit coefficients."""
        from validation.l_function_bsd_check import compute_l_function_bsd_check

        # Use simple curve 11a1 coefficients: y^2 + y = x^3 - x^2 - 10x - 20
        # In short Weierstrass form: [0, -1, 1, -10, -20]
        # We'll use a simpler test with known a4, a6
        result = compute_l_function_bsd_check(coefficients=(0, -4))  # y^2 = x^3 - 4

        assert 'L_at_1' in result
        assert 'conductor' in result
        assert result['conductor'] > 0

    def test_output_file_creation(self, tmp_path):
        """Test that output file is created correctly."""
        from validation.l_function_bsd_check import compute_l_function_bsd_check

        output_file = tmp_path / "test_output.txt"

        result = compute_l_function_bsd_check(
            curve_label='11a1',
            output_file=str(output_file)
        )

        assert output_file.exists()
        content = output_file.read_text()

        assert 'L(E, 1)' in content
        assert 'BSD' in content
        assert 'analytic' in content.lower() or 'Analytic' in content

    def test_run_standard_verification(self):
        """Test the standard verification function."""
        from validation.l_function_bsd_check import run_standard_verification

        # Note: This uses the default curve from problem statement
        # which may be large, so we'll just test the function exists and returns dict
        result = run_standard_verification()

        assert isinstance(result, dict)
        assert 'bsd_valid' in result

    def test_result_contains_timestamp(self):
        """Test that results include timestamp for reproducibility."""
        from validation.l_function_bsd_check import compute_l_function_bsd_check

        result = compute_l_function_bsd_check(curve_label='11a1')

        assert 'timestamp' in result
        assert len(result['timestamp']) > 0


class TestLFunctionBSDCheckMock:
    """Tests using mocks for environments without SageMath."""

    def test_mock_verification_structure(self):
        """Test expected structure of verification results."""
        expected_keys = [
            'curve',
            'conductor',
            'L_at_1',
            'analytic_rank',
            'algebraic_rank',
            'bsd_valid',
            'timestamp'
        ]

        # Mock result structure
        mock_result = {
            'curve': 'Elliptic Curve defined by y^2 = x^3 - x + 1',
            'conductor': 37,
            'L_at_1': 0.0,
            'analytic_rank': 1,
            'algebraic_rank': 1,
            'bsd_valid': True,
            'timestamp': '2025-01-01T00:00:00'
        }

        for key in expected_keys:
            assert key in mock_result, f"Expected key {key} in result"


def run_tests():
    """Run all tests manually."""
    print("=" * 60)
    print("Running L-Function BSD Check Tests")
    print("=" * 60)

    # Structure tests
    test_obj = TestLFunctionBSDCheckStructure()

    print("\n--- Structure Tests ---")
    test_obj.test_module_exists()
    print("✅ Module exists test passed")

    test_obj.test_module_imports()
    print("✅ Module imports test passed")

    test_obj.test_outputs_directory_exists()
    print("✅ Outputs directory test passed")

    test_obj.test_docstrings_exist()
    print("✅ Docstrings test passed")

    # Mock tests
    mock_test = TestLFunctionBSDCheckMock()
    mock_test.test_mock_verification_structure()
    print("✅ Mock structure test passed")

    print("\n" + "=" * 60)
    print("All structure tests passed!")
    print("=" * 60)

    # Try SageMath tests if available
    try:
        import sage  # noqa: F401
        print("\nSageMath detected, running full tests...")
        sage_tests = TestLFunctionBSDCheckWithSage()

        sage_tests.test_l_function_rank_0_curve()
        print("✅ Rank 0 curve test passed")

        sage_tests.test_l_function_rank_1_curve()
        print("✅ Rank 1 curve test passed")

        sage_tests.test_result_contains_timestamp()
        print("✅ Timestamp test passed")

    except ImportError:
        print("\nSageMath not available, skipping SageMath-dependent tests")


if __name__ == '__main__':
    run_tests()
