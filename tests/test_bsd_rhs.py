#!/usr/bin/env python3
"""
Tests for the BSD Right-Hand Side computation module.

These tests verify the computation of:
1. Néron-Tate height pairings
2. Regulator computation
3. BSD formula components
4. Full BSD verification

Author: Generated for adelic-bsd project
Date: November 2025
"""

import sys
import os
import pytest

# Add paths for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../validation'))

# Import sage if available
pytest.importorskip("sage.all")
from sage.all import EllipticCurve

from validation.birch_swinnerton_rhs import BSDRightHandSide, format_output


class TestBSDRightHandSide:
    """Tests for the BSDRightHandSide class."""

    def test_initialization_with_label(self):
        """Test initialization with Cremona label."""
        bsd = BSDRightHandSide('11a1')
        assert bsd.E is not None
        assert bsd.label == '11a1'
        print("✅ Initialization with label: OK")

    def test_initialization_with_curve(self):
        """Test initialization with EllipticCurve object."""
        E = EllipticCurve('37a1')
        bsd = BSDRightHandSide(E)
        assert bsd.E == E
        assert bsd.label == '37a1'
        print("✅ Initialization with curve: OK")

    def test_rank_computation(self):
        """Test rank computation for known curves."""
        # 11a1 has rank 0
        bsd_rank0 = BSDRightHandSide('11a1')
        assert bsd_rank0.get_rank() == 0

        # 37a1 has rank 1
        bsd_rank1 = BSDRightHandSide('37a1')
        assert bsd_rank1.get_rank() == 1

        print("✅ Rank computation: OK")

    def test_torsion_order(self):
        """Test torsion order computation."""
        # 11a1 has torsion order 5
        bsd = BSDRightHandSide('11a1')
        assert bsd.compute_torsion_order() == 5

        # 37a1 has torsion order 1
        bsd = BSDRightHandSide('37a1')
        assert bsd.compute_torsion_order() == 1

        print("✅ Torsion order computation: OK")

    def test_real_period(self):
        """Test real period computation."""
        bsd = BSDRightHandSide('11a1')
        omega = bsd.compute_real_period()
        assert omega > 0
        # 11a1 real period is approximately 1.26920...
        assert 1.2 < omega < 1.4
        print("✅ Real period computation: OK")

    def test_tamagawa_numbers(self):
        """Test Tamagawa number computation."""
        bsd = BSDRightHandSide('11a1')
        tamagawa = bsd.get_tamagawa_numbers()
        # 11a1 has conductor 11, c_11 = 5
        assert 11 in tamagawa
        assert tamagawa[11] == 5
        print("✅ Tamagawa numbers: OK")

    def test_tamagawa_product(self):
        """Test Tamagawa product computation."""
        bsd = BSDRightHandSide('11a1')
        product = bsd.compute_tamagawa_product()
        assert product == 5
        print("✅ Tamagawa product: OK")

    def test_generators_rank0(self):
        """Test generators for rank 0 curve."""
        bsd = BSDRightHandSide('11a1')
        gens = bsd.get_generators()
        assert len(gens) == 0
        print("✅ Generators (rank 0): OK")

    def test_generators_rank1(self):
        """Test generators for rank 1 curve."""
        bsd = BSDRightHandSide('37a1')
        gens = bsd.get_generators()
        assert len(gens) == 1
        print("✅ Generators (rank 1): OK")

    def test_height_computation_rank1(self):
        """Test height computation for rank 1 curve."""
        bsd = BSDRightHandSide('37a1')
        gens = bsd.get_generators()
        if len(gens) > 0:
            height = bsd.compute_height(gens[0])
            assert height > 0
            # 37a1 generator has height approximately 0.05...
            assert 0.01 < height < 0.2
        print("✅ Height computation: OK")

    def test_height_matrix_rank0(self):
        """Test height matrix for rank 0 curve."""
        bsd = BSDRightHandSide('11a1')
        H = bsd.compute_height_matrix()
        assert H.nrows() == 0
        assert H.ncols() == 0
        print("✅ Height matrix (rank 0): OK")

    def test_height_matrix_rank1(self):
        """Test height matrix for rank 1 curve."""
        bsd = BSDRightHandSide('37a1')
        H = bsd.compute_height_matrix()
        assert H.nrows() == 1
        assert H.ncols() == 1
        # Matrix entry should equal the height of generator
        assert H[0, 0] > 0
        print("✅ Height matrix (rank 1): OK")

    def test_regulator_rank0(self):
        """Test regulator for rank 0 curve."""
        bsd = BSDRightHandSide('11a1')
        R = bsd.compute_regulator()
        # For rank 0, regulator is 1 by convention
        assert R == 1.0
        print("✅ Regulator (rank 0): OK")

    def test_regulator_rank1(self):
        """Test regulator for rank 1 curve."""
        bsd = BSDRightHandSide('37a1')
        R = bsd.compute_regulator()
        assert R > 0
        # For rank 1, regulator equals height of generator
        print("✅ Regulator (rank 1): OK")

    def test_bsd_rhs_rank0(self):
        """Test BSD RHS computation for rank 0 curve."""
        bsd = BSDRightHandSide('11a1')
        rhs = bsd.compute_rhs()
        assert rhs > 0
        # For 11a1: RHS ≈ 0.2538... (with Sha = 1)
        assert 0.2 < rhs < 0.3
        print("✅ BSD RHS (rank 0): OK")

    def test_full_computation(self):
        """Test full computation returns all expected fields."""
        bsd = BSDRightHandSide('11a1')
        result = bsd.full_computation()

        # Check all required fields are present
        assert 'curve' in result
        assert 'generators' in result
        assert 'height_matrix' in result
        assert 'regulator' in result
        assert 'torsion' in result
        assert 'real_period' in result
        assert 'tamagawa' in result
        assert 'bsd_rhs' in result
        assert 'verification' in result

        print("✅ Full computation: OK")

    def test_format_output(self):
        """Test that format_output produces valid output."""
        bsd = BSDRightHandSide('11a1')
        result = bsd.full_computation()
        output = format_output(result)

        assert isinstance(output, str)
        assert 'BSD' in output
        assert '11a1' in output
        assert 'REGULADOR' in output

        print("✅ Format output: OK")


class TestBSDVerification:
    """Tests for BSD formula verification."""

    def test_verify_bsd_rank0(self):
        """Test BSD verification for rank 0 curve."""
        bsd = BSDRightHandSide('11a1')
        verification = bsd.verify_bsd()

        assert 'curve' in verification
        assert 'rank' in verification
        assert verification['rank'] == 0
        assert 'lhs' in verification
        assert 'rhs' in verification

        print("✅ BSD verification (rank 0): OK")

    def test_verify_bsd_rank1(self):
        """Test BSD verification for rank 1 curve."""
        bsd = BSDRightHandSide('37a1')
        verification = bsd.verify_bsd()

        assert verification['rank'] == 1
        # For rank 1, verification may depend on L-function computation

        print("✅ BSD verification (rank 1): OK")


def run_all_tests():
    """Run all BSD RHS tests."""
    print("=" * 60)
    print("BSD RIGHT-HAND SIDE TESTS")
    print("=" * 60)

    test_cases = TestBSDRightHandSide()
    verification_tests = TestBSDVerification()

    tests = [
        test_cases.test_initialization_with_label,
        test_cases.test_initialization_with_curve,
        test_cases.test_rank_computation,
        test_cases.test_torsion_order,
        test_cases.test_real_period,
        test_cases.test_tamagawa_numbers,
        test_cases.test_tamagawa_product,
        test_cases.test_generators_rank0,
        test_cases.test_generators_rank1,
        test_cases.test_height_computation_rank1,
        test_cases.test_height_matrix_rank0,
        test_cases.test_height_matrix_rank1,
        test_cases.test_regulator_rank0,
        test_cases.test_regulator_rank1,
        test_cases.test_bsd_rhs_rank0,
        test_cases.test_full_computation,
        test_cases.test_format_output,
        verification_tests.test_verify_bsd_rank0,
        verification_tests.test_verify_bsd_rank1,
    ]

    passed = 0
    failed = 0

    for test in tests:
        try:
            test()
            passed += 1
        except Exception as e:
            print(f"❌ {test.__name__}: FAILED - {e}")
            failed += 1

    print(f"\n📊 Tests: {passed}/{passed + failed} passed")
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
