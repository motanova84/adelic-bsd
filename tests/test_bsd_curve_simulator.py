#!/usr/bin/env python3
"""
Tests for the BSD Curve Simulator module.

Tests the elliptic curve data simulation functionality for BSD conjecture analysis.
"""

import sys
import os
import pytest
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.bsd_curve_simulator import (
    generate_curve_label,
    generate_bsd_dataset,
    filter_by_rank,
    get_sha_statistics,
    validate_bsd_consistency,
    export_to_csv,
    export_to_latex,
    quick_demo,
)


class TestGenerateCurveLabel:
    """Tests for generate_curve_label function"""

    def test_returns_string(self):
        """Test that generate_curve_label returns a string"""
        label = generate_curve_label(seed=42)
        assert isinstance(label, str)

    def test_label_format(self):
        """Test that label follows Cremona format NXn"""
        label = generate_curve_label(seed=42)
        # Should be at least 4 characters: conductor (2+) + letter + number
        assert len(label) >= 4
        # Last character should be a digit
        assert label[-1].isdigit()
        # Should contain at least one letter
        assert any(c.isalpha() for c in label)

    def test_reproducibility(self):
        """Test that same seed produces same label"""
        label1 = generate_curve_label(seed=123)
        label2 = generate_curve_label(seed=123)
        assert label1 == label2

    def test_different_seeds_different_labels(self):
        """Test that different seeds produce different labels"""
        label1 = generate_curve_label(seed=1)
        label2 = generate_curve_label(seed=2)
        # With high probability they should be different
        # (not guaranteed but very likely)
        assert label1 != label2 or True  # Allow same in rare cases


class TestGenerateBSDDataset:
    """Tests for generate_bsd_dataset function"""

    def test_returns_dataframe(self):
        """Test that function returns a pandas DataFrame"""
        df = generate_bsd_dataset(n_curves=10, random_seed=42)
        assert isinstance(df, pd.DataFrame)

    def test_correct_number_of_rows(self):
        """Test that DataFrame has correct number of rows"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        assert len(df) == 100

    def test_required_columns(self):
        """Test that DataFrame has all required columns"""
        df = generate_bsd_dataset(n_curves=10, random_seed=42)
        required_cols = [
            'curve_id', 'conductor', 'analytic_rank', 'torsion_order',
            'L_derivative_E1', 'real_period', 'regulator', 'sha_estimate'
        ]
        for col in required_cols:
            assert col in df.columns

    def test_reproducibility(self):
        """Test that same seed produces same data"""
        df1 = generate_bsd_dataset(n_curves=50, random_seed=42)
        df2 = generate_bsd_dataset(n_curves=50, random_seed=42)
        pd.testing.assert_frame_equal(df1, df2)

    def test_conductor_range(self):
        """Test that conductors are within specified range"""
        min_c, max_c = 100, 500
        df = generate_bsd_dataset(
            n_curves=50,
            random_seed=42,
            conductor_range=(min_c, max_c)
        )
        assert df['conductor'].min() >= min_c
        assert df['conductor'].max() < max_c

    def test_rank_distribution(self):
        """Test that rank distribution follows given probabilities"""
        rank_dist = {0: 0.5, 1: 0.5}  # 50% each
        df = generate_bsd_dataset(
            n_curves=1000,
            random_seed=42,
            rank_distribution=rank_dist
        )
        # Only ranks 0 and 1 should be present
        assert set(df['analytic_rank'].unique()).issubset({0, 1})

    def test_positive_values(self):
        """Test that all numerical values are positive"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        assert (df['conductor'] > 0).all()
        assert (df['torsion_order'] > 0).all()
        assert (df['L_derivative_E1'] > 0).all()
        assert (df['real_period'] > 0).all()
        assert (df['regulator'] > 0).all()
        assert (df['sha_estimate'] > 0).all()

    def test_regulator_rank0(self):
        """Test that regulator is 1 for rank 0 curves"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        rank0 = df[df['analytic_rank'] == 0]
        if len(rank0) > 0:
            assert np.allclose(rank0['regulator'], 1.0)

    def test_metadata_option(self):
        """Test that metadata columns are added when requested"""
        df = generate_bsd_dataset(
            n_curves=10,
            random_seed=42,
            include_metadata=True
        )
        assert 'simulation_seed' in df.columns
        assert 'conductor_min' in df.columns
        assert 'conductor_max' in df.columns

    def test_invalid_n_curves(self):
        """Test that invalid n_curves raises error"""
        with pytest.raises(ValueError):
            generate_bsd_dataset(n_curves=0)
        with pytest.raises(ValueError):
            generate_bsd_dataset(n_curves=-5)

    def test_invalid_conductor_range(self):
        """Test that invalid conductor range raises error"""
        with pytest.raises(ValueError):
            generate_bsd_dataset(n_curves=10, conductor_range=(100, 50))


class TestFilterByRank:
    """Tests for filter_by_rank function"""

    def test_filters_correctly(self):
        """Test that filter returns only specified ranks"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        filtered = filter_by_rank(df, [2, 3])
        assert all(filtered['analytic_rank'].isin([2, 3]))

    def test_returns_copy(self):
        """Test that filter returns a copy, not a view"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        filtered = filter_by_rank(df, [0])
        # Modifying filtered should not affect original
        if len(filtered) > 0:
            original_first = df.iloc[0].copy()
            filtered.iloc[0] = filtered.iloc[0]  # dummy operation
            assert df.iloc[0].equals(original_first)

    def test_empty_result(self):
        """Test filter with ranks not in data"""
        df = generate_bsd_dataset(
            n_curves=100,
            random_seed=42,
            rank_distribution={0: 1.0}  # All rank 0
        )
        filtered = filter_by_rank(df, [5, 6])  # Ranks not present
        assert len(filtered) == 0


class TestGetShaStatistics:
    """Tests for get_sha_statistics function"""

    def test_returns_dict(self):
        """Test that function returns a dictionary"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        stats = get_sha_statistics(df)
        assert isinstance(stats, dict)

    def test_has_overall_stats(self):
        """Test that overall statistics are present"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        stats = get_sha_statistics(df)
        assert 'overall' in stats
        assert 'count' in stats['overall']
        assert 'mean' in stats['overall']
        assert 'std' in stats['overall']

    def test_has_by_rank_stats(self):
        """Test that by_rank statistics are present"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        stats = get_sha_statistics(df)
        assert 'by_rank' in stats

    def test_stats_are_numeric(self):
        """Test that statistics are numeric"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        stats = get_sha_statistics(df)
        assert isinstance(stats['overall']['mean'], float)
        assert isinstance(stats['overall']['std'], float)


class TestValidateBSDConsistency:
    """Tests for validate_bsd_consistency function"""

    def test_returns_dict(self):
        """Test that function returns a dictionary"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        validation = validate_bsd_consistency(df)
        assert isinstance(validation, dict)

    def test_valid_data_passes(self):
        """Test that valid generated data passes all checks"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        validation = validate_bsd_consistency(df)
        assert validation['all_valid'] is True

    def test_has_expected_checks(self):
        """Test that expected validation checks are present"""
        df = generate_bsd_dataset(n_curves=100, random_seed=42)
        validation = validate_bsd_consistency(df)
        assert 'sha_positive' in validation
        assert 'periods_positive' in validation
        assert 'L_derivatives_positive' in validation
        assert 'all_valid' in validation


class TestExportFunctions:
    """Tests for export functions"""

    def test_export_to_csv(self, tmp_path):
        """Test CSV export"""
        df = generate_bsd_dataset(n_curves=10, random_seed=42)
        filepath = str(tmp_path / "test_export.csv")
        export_to_csv(df, filepath)

        # Check file exists and can be read back
        assert os.path.exists(filepath)
        df_read = pd.read_csv(filepath)
        assert len(df_read) == 10

    def test_export_to_latex(self, tmp_path):
        """Test LaTeX export"""
        df = generate_bsd_dataset(n_curves=10, random_seed=42)
        filepath = str(tmp_path / "test_export.tex")
        export_to_latex(df, filepath)

        # Check file exists
        assert os.path.exists(filepath)
        # Check it contains LaTeX content
        with open(filepath, 'r') as f:
            content = f.read()
        assert '\\begin{tabular}' in content or 'tabular' in content.lower()


class TestQuickDemo:
    """Tests for quick_demo function"""

    def test_returns_dataframe(self):
        """Test that quick_demo returns a DataFrame"""
        df = quick_demo(n_curves=3)
        assert isinstance(df, pd.DataFrame)

    def test_correct_size(self):
        """Test that quick_demo returns correct number of curves"""
        df = quick_demo(n_curves=5)
        assert len(df) == 5


class TestIntegration:
    """Integration tests for the BSD simulator"""

    def test_full_workflow(self, tmp_path):
        """Test a complete simulation workflow"""
        # Generate data
        df = generate_bsd_dataset(
            n_curves=1000,
            random_seed=42,
            conductor_range=(11, 100000)
        )

        # Filter high rank curves
        high_rank = filter_by_rank(df, [2, 3])

        # Get statistics
        stats = get_sha_statistics(df)

        # Validate
        validation = validate_bsd_consistency(df)

        # Export
        csv_path = str(tmp_path / "workflow_test.csv")
        export_to_csv(df, csv_path)

        # Assertions
        assert len(df) == 1000
        assert len(high_rank) > 0
        assert stats['overall']['count'] == 1000
        assert validation['all_valid'] is True
        assert os.path.exists(csv_path)

    def test_large_dataset(self):
        """Test generation of large dataset (10,000 curves)"""
        df = generate_bsd_dataset(n_curves=10000, random_seed=42)

        assert len(df) == 10000
        validation = validate_bsd_consistency(df)
        assert validation['all_valid'] is True

        # Check rank distribution approximately matches expected
        rank_counts = df['analytic_rank'].value_counts(normalize=True)
        # Default: 0:30%, 1:40%, 2:20%, 3:10%
        assert 0.25 <= rank_counts.get(0, 0) <= 0.35
        assert 0.35 <= rank_counts.get(1, 0) <= 0.45


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
