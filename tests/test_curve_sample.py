"""
Tests for BSD Curve Sample Module.

This module tests the curve_sample functionality including:
- CurveData dataclass
- BSDCurveSample class
- Sample generation and display
- Sha estimation for rank >= 2 curves
"""

import sys
import os

import pytest

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from bsd_spectral.curve_sample import (  # noqa: E402
    CurveData,
    BSDCurveSample,
    generate_bsd_sample,
    display_sample_table
)


class TestCurveData:
    """Tests for CurveData dataclass."""

    def test_create_curve_data(self):
        """Test creating a CurveData instance."""
        curve = CurveData(
            label='11a1',
            conductor=11,
            rank=0,
            torsion=5,
            real_period=3.057,
            regulator=1.0,
            sha_estimate=1.0,
            tamagawa_product=1,
            leading_term=0.2536,
            bsd_verified='✅'
        )

        assert curve.label == '11a1'
        assert curve.conductor == 11
        assert curve.rank == 0
        assert curve.torsion == 5
        assert curve.bsd_verified == '✅'

    def test_curve_data_to_dict(self):
        """Test converting CurveData to dictionary."""
        curve = CurveData(
            label='37a1',
            conductor=37,
            rank=1,
            torsion=1,
            real_period=2.622,
            regulator=1.0,
            sha_estimate=1.0,
            tamagawa_product=1,
            leading_term=0.4214,
            bsd_verified='✅'
        )

        d = curve.to_dict()
        assert isinstance(d, dict)
        assert d['label'] == '37a1'
        assert d['rank'] == 1
        assert d['bsd_verified'] == '✅'


class TestBSDCurveSample:
    """Tests for BSDCurveSample class."""

    def test_create_sample(self):
        """Test creating a BSDCurveSample."""
        sample = BSDCurveSample()
        assert len(sample.curves) == 0

    def test_add_known_curve(self):
        """Test adding a known curve from the problem statement."""
        sample = BSDCurveSample()
        curve = sample.add_curve('11a1')

        assert curve is not None
        assert curve.label == '11a1'
        assert curve.conductor == 11
        assert curve.rank == 0
        assert len(sample.curves) == 1

    def test_add_multiple_curves(self):
        """Test adding multiple curves."""
        sample = BSDCurveSample()

        for label in ['11a1', '37a1', '389a1']:
            sample.add_curve(label)

        assert len(sample.curves) == 3

    def test_to_table(self):
        """Test generating ASCII table."""
        sample = BSDCurveSample()
        sample.add_curve('11a1')
        sample.add_curve('37a1')

        table = sample.to_table()

        assert isinstance(table, str)
        assert '11a1' in table
        assert '37a1' in table
        assert '✅' in table

    def test_to_latex_table(self):
        """Test generating LaTeX table."""
        sample = BSDCurveSample()
        sample.add_curve('11a1')

        latex = sample.to_latex_table()

        assert isinstance(latex, str)
        assert r'\begin{table}' in latex
        assert r'\end{table}' in latex
        assert '11a1' in latex

    def test_summary(self):
        """Test summary statistics."""
        sample = BSDCurveSample()
        sample.add_curve('11a1')
        sample.add_curve('37a1')
        sample.add_curve('389a1')

        summary = sample.summary()

        assert summary['total'] == 3
        assert summary['verified'] == 2
        assert summary['pending'] == 1
        assert summary['failed'] == 0
        assert 'by_rank' in summary

    def test_known_curves_data(self):
        """Test that known curves have correct data."""
        sample = BSDCurveSample()

        # Test 11a1 (rank 0)
        curve = sample.add_curve('11a1')
        assert curve.rank == 0
        assert curve.torsion == 5
        assert curve.bsd_verified == '✅'

        sample.curves = []  # Reset

        # Test 389a1 (rank 2)
        curve = sample.add_curve('389a1')
        assert curve.rank == 2
        assert curve.bsd_verified == '⧗'


class TestShaEstimation:
    """Tests for Sha estimation for rank >= 2 curves."""

    def test_sha_estimate_rank0(self):
        """Test Sha estimation for rank 0 curve."""
        sample = BSDCurveSample()
        curve = sample.add_curve('11a1')

        sha = sample.estimate_sha_rank2(curve)
        assert sha == 1.0

    def test_sha_estimate_rank1(self):
        """Test Sha estimation for rank 1 curve."""
        sample = BSDCurveSample()
        curve = sample.add_curve('37a1')

        sha = sample.estimate_sha_rank2(curve)
        assert sha == 1.0

    def test_sha_estimate_rank2(self):
        """Test Sha estimation for rank 2 curve."""
        sample = BSDCurveSample()
        curve = sample.add_curve('389a1')

        sha = sample.estimate_sha_rank2(curve)
        # Should return a positive value or None
        assert sha is None or sha >= 1.0


class TestGenerateBSDSample:
    """Tests for generate_bsd_sample function."""

    def test_generate_default_sample(self):
        """Test generating default sample."""
        sample = generate_bsd_sample()

        assert len(sample.curves) == 5

    def test_generate_sample_with_labels(self):
        """Test generating sample with specific labels."""
        sample = generate_bsd_sample(labels=['11a1', '37a1'])

        assert len(sample.curves) == 2
        labels = [c.label for c in sample.curves]
        assert '11a1' in labels
        assert '37a1' in labels

    def test_generate_sample_include_known(self):
        """Test generating sample with known curves."""
        sample = generate_bsd_sample(include_known=True)

        labels = [c.label for c in sample.curves]
        assert '11a1' in labels
        assert '37a1' in labels
        assert '389a1' in labels


class TestDisplaySampleTable:
    """Tests for display_sample_table function."""

    def test_display_sample_table(self):
        """Test displaying sample table."""
        output = display_sample_table()

        assert isinstance(output, str)
        assert '🔍 BSD Verification Sample' in output
        assert '11a1' in output
        assert '37a1' in output
        assert '389a1' in output
        assert 'Legend:' in output
        assert 'Summary:' in output

    def test_display_table_has_legend(self):
        """Test that display table includes legend."""
        output = display_sample_table()

        assert '✅' in output
        assert '⧗' in output
        assert 'rank 0 or 1' in output
        assert 'rank ≥ 2' in output


class TestProblemStatementCurves:
    """Tests for specific curves mentioned in the problem statement."""

    def test_11a1_verified(self):
        """Test 11a1 (rank 0) is verified."""
        sample = BSDCurveSample()
        curve = sample.add_curve('11a1')

        assert curve.conductor == 11
        assert curve.rank == 0
        assert curve.torsion == 5
        assert abs(curve.real_period - 3.057) < 0.001
        assert curve.bsd_verified == '✅'

    def test_37a1_verified(self):
        """Test 37a1 (rank 1) is verified."""
        sample = BSDCurveSample()
        curve = sample.add_curve('37a1')

        assert curve.conductor == 37
        assert curve.rank == 1
        assert curve.bsd_verified == '✅'

    def test_389a1_pending(self):
        """Test 389a1 (rank 2) is pending."""
        sample = BSDCurveSample()
        curve = sample.add_curve('389a1')

        assert curve.conductor == 389
        assert curve.rank == 2
        assert curve.bsd_verified == '⧗'

    def test_5077a1_pending(self):
        """Test 5077a1 (rank 2) is pending."""
        sample = BSDCurveSample()
        curve = sample.add_curve('5077a1')

        assert curve.conductor == 5077
        assert curve.rank == 2
        assert curve.bsd_verified == '⧗'

    def test_9907a1_pending(self):
        """Test 9907a1 (rank 3) is pending."""
        sample = BSDCurveSample()
        curve = sample.add_curve('9907a1')

        assert curve.conductor == 9907
        assert curve.rank == 3
        assert curve.bsd_verified == '⧗'


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
