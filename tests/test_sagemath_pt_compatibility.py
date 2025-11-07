"""
Tests for SageMath integration PT_compatibility module.

These tests require SageMath to be installed.
"""

import pytest
import sys
from pathlib import Path

# Add sagemath_integration to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))

# Mark all tests in this module as requiring sage
pytestmark = pytest.mark.sage_required


@pytest.fixture
def sage_imports():
    """Import Sage components, skip if not available"""
    try:
        from sage.all import EllipticCurve
        from sage.schemes.elliptic_curves.bsd_spectral import (
            compute_gross_zagier_height,
            compute_yzz_height,
            verify_PT_compatibility
        )
        return {
            'EllipticCurve': EllipticCurve,
            'compute_gross_zagier_height': compute_gross_zagier_height,
            'compute_yzz_height': compute_yzz_height,
            'verify_PT_compatibility': verify_PT_compatibility
        }
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


class TestComputeGrossZagierHeight:
    """Tests for compute_gross_zagier_height function"""

    def test_rank_1_curve(self, sage_imports):
        """Test Gross-Zagier height for rank 1 curve"""
        E = sage_imports['EllipticCurve']('37a1')
        compute_gz = sage_imports['compute_gross_zagier_height']

        h = compute_gz(E)

        assert h is not None
        assert h > 0
        assert isinstance(h, (int, float))

    def test_rank_0_curve(self, sage_imports):
        """Test that rank 0 curve returns None"""
        E = sage_imports['EllipticCurve']('11a1')
        compute_gz = sage_imports['compute_gross_zagier_height']

        h = compute_gz(E)

        assert h is None

    def test_rank_2_curve(self, sage_imports):
        """Test that rank 2 curve returns None"""
        E = sage_imports['EllipticCurve']('389a1')
        compute_gz = sage_imports['compute_gross_zagier_height']

        h = compute_gz(E)

        assert h is None

    def test_rank_3_curve(self, sage_imports):
        """Test that rank 3 curve returns None"""
        E = sage_imports['EllipticCurve']('5077a1')
        compute_gz = sage_imports['compute_gross_zagier_height']

        h = compute_gz(E)

        assert h is None


class TestComputeYZZHeight:
    """Tests for compute_yzz_height function"""

    def test_rank_2_curve(self, sage_imports):
        """Test YZZ height for rank 2 curve"""
        E = sage_imports['EllipticCurve']('389a1')
        compute_yzz = sage_imports['compute_yzz_height']

        h = compute_yzz(E)

        assert h is not None
        assert h > 0
        assert isinstance(h, (int, float))

    def test_rank_3_curve(self, sage_imports):
        """Test YZZ height for rank 3 curve"""
        E = sage_imports['EllipticCurve']('5077a1')
        compute_yzz = sage_imports['compute_yzz_height']

        h = compute_yzz(E)

        assert h is not None
        assert h > 0
        assert isinstance(h, (int, float))

    def test_rank_0_curve(self, sage_imports):
        """Test that rank 0 curve returns None"""
        E = sage_imports['EllipticCurve']('11a1')
        compute_yzz = sage_imports['compute_yzz_height']

        h = compute_yzz(E)

        assert h is None

    def test_rank_1_curve(self, sage_imports):
        """Test that rank 1 curve returns None"""
        E = sage_imports['EllipticCurve']('37a1')
        compute_yzz = sage_imports['compute_yzz_height']

        h = compute_yzz(E)

        assert h is None


class TestVerifyPTCompatibility:
    """Tests for verify_PT_compatibility function"""

    def test_rank_0_curve(self, sage_imports):
        """Test PT compatibility for rank 0 curve (trivial case)"""
        E = sage_imports['EllipticCurve']('11a1')
        verify_pt = sage_imports['verify_PT_compatibility']

        result = verify_pt(E)

        assert isinstance(result, dict)
        assert 'PT_compatible' in result
        assert 'rank' in result
        assert 'height_algebraic' in result
        assert 'method' in result
        assert 'curve' in result

        assert result['PT_compatible'] is True
        assert result['rank'] == 0
        assert result['height_algebraic'] == 0.0
        assert result['method'] == 'trivial'

    def test_rank_1_curve(self, sage_imports):
        """Test PT compatibility for rank 1 curve (Gross-Zagier)"""
        E = sage_imports['EllipticCurve']('37a1')
        verify_pt = sage_imports['verify_PT_compatibility']

        result = verify_pt(E)

        assert isinstance(result, dict)
        assert 'PT_compatible' in result
        assert 'rank' in result
        assert 'height_algebraic' in result
        assert 'method' in result

        assert result['PT_compatible'] is True
        assert result['rank'] == 1
        assert result['height_algebraic'] > 0
        assert result['method'] == 'Gross-Zagier'

    def test_rank_2_curve(self, sage_imports):
        """Test PT compatibility for rank 2 curve (Yuan-Zhang-Zhang)"""
        E = sage_imports['EllipticCurve']('389a1')
        verify_pt = sage_imports['verify_PT_compatibility']

        result = verify_pt(E)

        assert isinstance(result, dict)
        assert 'PT_compatible' in result
        assert 'rank' in result
        assert 'height_algebraic' in result
        assert 'method' in result

        assert result['PT_compatible'] is True
        assert result['rank'] == 2
        assert result['height_algebraic'] > 0
        assert result['method'] == 'Yuan-Zhang-Zhang'

    def test_rank_3_curve(self, sage_imports):
        """Test PT compatibility for rank 3 curve (Yuan-Zhang-Zhang)"""
        E = sage_imports['EllipticCurve']('5077a1')
        verify_pt = sage_imports['verify_PT_compatibility']

        result = verify_pt(E)

        assert isinstance(result, dict)
        assert 'PT_compatible' in result
        assert 'rank' in result
        assert 'method' in result

        assert result['rank'] == 3
        assert result['method'] == 'Yuan-Zhang-Zhang'

    def test_return_structure(self, sage_imports):
        """Test that return structure is consistent across all ranks"""
        E = sage_imports['EllipticCurve']('11a1')
        verify_pt = sage_imports['verify_PT_compatibility']

        result = verify_pt(E)

        # Check all required keys are present
        required_keys = ['PT_compatible', 'rank', 'height_algebraic', 'method', 'curve']
        for key in required_keys:
            assert key in result, f"Missing required key: {key}"

        # Check types
        assert isinstance(result['PT_compatible'], bool)
        assert isinstance(result['rank'], int)
        assert isinstance(result['height_algebraic'], float)
        assert isinstance(result['method'], str)
        assert isinstance(result['curve'], str)

    def test_method_names(self, sage_imports):
        """Test that correct method names are returned"""
        verify_pt = sage_imports['verify_PT_compatibility']
        EllipticCurve = sage_imports['EllipticCurve']

        # Rank 0 should use 'trivial'
        E0 = EllipticCurve('11a1')
        result0 = verify_pt(E0)
        assert result0['method'] == 'trivial'

        # Rank 1 should use 'Gross-Zagier'
        E1 = EllipticCurve('37a1')
        result1 = verify_pt(E1)
        assert result1['method'] == 'Gross-Zagier'

        # Rank 2+ should use 'Yuan-Zhang-Zhang'
        E2 = EllipticCurve('389a1')
        result2 = verify_pt(E2)
        assert result2['method'] == 'Yuan-Zhang-Zhang'


class TestEdgeCases:
    """Test edge cases and error handling"""

    def test_curve_without_label(self, sage_imports):
        """Test that curves without labels are handled"""
        E = sage_imports['EllipticCurve']([0, 0, 1, -1, 0])  # Curve 37a1 by Weierstrass equation
        verify_pt = sage_imports['verify_PT_compatibility']

        result = verify_pt(E)

        assert 'curve' in result
        assert isinstance(result['curve'], str)
        # Should fall back to string representation
        assert len(result['curve']) > 0


class TestModuleImports:
    """Test module imports and structure"""

    def test_direct_import(self, sage_imports):
        """Test that functions can be imported directly"""
        # Already tested through fixture, but verify all functions exist
        assert 'compute_gross_zagier_height' in sage_imports
        assert 'compute_yzz_height' in sage_imports
        assert 'verify_PT_compatibility' in sage_imports

        # Verify they are callable
        assert callable(sage_imports['compute_gross_zagier_height'])
        assert callable(sage_imports['compute_yzz_height'])
        assert callable(sage_imports['verify_PT_compatibility'])
