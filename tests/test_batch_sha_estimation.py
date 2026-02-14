"""
Tests for batch_sha_estimation module

Tests the BSD-based |Ш| estimation for elliptic curves with rank >= 2.
"""

import os
import sys
import tempfile
import pytest

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from experiments.batch_sha_estimation import (
    ShaEstimationResult,
    export_results_to_csv,
)


class TestShaEstimationResult:
    """Tests for ShaEstimationResult dataclass."""

    def test_result_creation(self):
        """Test creating a ShaEstimationResult."""
        result = ShaEstimationResult(
            label="389a1",
            rank=2,
            sha_estimate=1.0,
            l_derivative=0.759,
            omega=4.98,
            regulator=0.152,
            torsion_order=1,
            tamagawa_product=1,
            success=True,
            error_message=None,
        )
        assert result.label == "389a1"
        assert result.rank == 2
        assert result.success is True

    def test_result_to_dict(self):
        """Test converting result to dictionary."""
        result = ShaEstimationResult(
            label="389a1",
            rank=2,
            sha_estimate=1.0,
            l_derivative=0.759,
            omega=4.98,
            regulator=0.152,
            torsion_order=1,
            tamagawa_product=1,
            success=True,
        )
        d = result.to_dict()
        assert isinstance(d, dict)
        assert d["label"] == "389a1"
        assert d["rank"] == 2

    def test_failed_result(self):
        """Test creating a failed result."""
        result = ShaEstimationResult(
            label="unknown",
            rank=-1,
            sha_estimate=None,
            l_derivative=None,
            omega=None,
            regulator=None,
            torsion_order=0,
            tamagawa_product=0,
            success=False,
            error_message="Test error",
        )
        assert result.success is False
        assert result.error_message == "Test error"


class TestCsvExport:
    """Tests for CSV export functionality."""

    def test_export_empty_results(self):
        """Test exporting empty results list."""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".csv", delete=False) as f:
            path = f.name

        try:
            output = export_results_to_csv([], path)
            assert os.path.exists(output)
            with open(output, "r") as f:
                content = f.read()
            # Should have header only
            assert "label" in content
            assert "rank" in content
            assert "sha_estimate" in content
        finally:
            if os.path.exists(path):
                os.remove(path)

    def test_export_with_results(self):
        """Test exporting results to CSV."""
        results = [
            ShaEstimationResult(
                label="389a1",
                rank=2,
                sha_estimate=1.0,
                l_derivative=0.759,
                omega=4.98,
                regulator=0.152,
                torsion_order=1,
                tamagawa_product=1,
                success=True,
            ),
            ShaEstimationResult(
                label="433a1",
                rank=2,
                sha_estimate=1.0,
                l_derivative=0.65,
                omega=3.2,
                regulator=0.12,
                torsion_order=1,
                tamagawa_product=1,
                success=True,
            ),
        ]

        with tempfile.NamedTemporaryFile(mode="w", suffix=".csv", delete=False) as f:
            path = f.name

        try:
            output = export_results_to_csv(results, path)
            assert os.path.exists(output)

            with open(output, "r") as f:
                lines = f.readlines()

            # Header + 2 data rows
            assert len(lines) == 3
            assert "389a1" in lines[1]
            assert "433a1" in lines[2]
        finally:
            if os.path.exists(path):
                os.remove(path)


# Mark SageMath-requiring tests
@pytest.mark.sage_required
class TestSageEstimation:
    """Tests requiring SageMath."""

    def test_estimate_sha_import(self):
        """Test that estimate_sha can be imported with Sage."""
        from experiments.batch_sha_estimation import estimate_sha
        assert callable(estimate_sha)

    def test_estimate_sha_rank2_curve(self):
        """Test estimation on a known rank-2 curve."""
        from experiments.batch_sha_estimation import estimate_sha

        result = estimate_sha("389a1")

        assert result.label == "389a1"
        assert result.rank == 2
        # 389a1 is known to have |Sha| = 1
        if result.success:
            assert result.sha_estimate is not None
            # Should be approximately 1
            assert 0.5 < result.sha_estimate < 2.0

    def test_estimate_sha_low_rank_skipped(self):
        """Test that low-rank curves are properly skipped."""
        from experiments.batch_sha_estimation import estimate_sha

        # 11a1 has rank 0
        result = estimate_sha("11a1")
        assert result.rank == 0
        assert result.success is False
        assert "rank" in result.error_message.lower()

    def test_estimate_sha_from_curve(self):
        """Test estimation from EllipticCurve object."""
        from sage.all import EllipticCurve
        from experiments.batch_sha_estimation import estimate_sha_from_curve

        E = EllipticCurve("389a1")
        result = estimate_sha_from_curve(E)

        assert result.rank == 2
        if result.success:
            assert result.l_derivative is not None
            assert result.omega is not None
            assert result.regulator is not None

    def test_get_curves_by_rank(self):
        """Test curve discovery by rank."""
        from experiments.batch_sha_estimation.estimate_sha import get_curves_by_rank

        curves = get_curves_by_rank(min_rank=2, max_rank=2, limit_per_rank=5)

        assert isinstance(curves, list)
        # Should find at least some curves
        assert len(curves) > 0

    def test_batch_estimate_small(self):
        """Test batch estimation with a small set."""
        from experiments.batch_sha_estimation import batch_estimate_sha

        results = batch_estimate_sha(
            labels=["389a1", "433a1"],
            verbose=False,
        )

        assert len(results) == 2
        assert all(r.rank >= 2 or not r.success for r in results)


def run_basic_tests():
    """Run basic tests without pytest."""
    print("Running basic tests...")

    # Test dataclass
    result = ShaEstimationResult(
        label="test",
        rank=2,
        sha_estimate=1.0,
        l_derivative=0.5,
        omega=1.0,
        regulator=1.0,
        torsion_order=1,
        tamagawa_product=1,
        success=True,
    )
    assert result.to_dict()["label"] == "test"
    print("✓ ShaEstimationResult dataclass works")

    # Test CSV export
    with tempfile.NamedTemporaryFile(mode="w", suffix=".csv", delete=False) as f:
        path = f.name
    try:
        export_results_to_csv([result], path)
        assert os.path.exists(path)
        print("✓ CSV export works")
    finally:
        os.remove(path)

    print("\nAll basic tests passed!")


if __name__ == "__main__":
    run_basic_tests()
