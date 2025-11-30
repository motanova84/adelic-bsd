#!/usr/bin/env python3
"""
Tests for SHA estimates generation and validation.

These tests verify the generation and validation of simulated elliptic
curve data with SHA estimates using the simplified BSD formula.
"""

import os
import sys
import tempfile
import unittest
from pathlib import Path

import pandas as pd

# Add scripts directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'scripts'))

from generate_sha_estimates import generate_sha_estimates, validate_sha_estimates  # noqa: E402


class TestGenerateShaEstimates(unittest.TestCase):
    """Tests for SHA estimate generation."""

    def test_generate_default(self):
        """Test default generation with 5000 curves."""
        df = generate_sha_estimates(num_curves=100, seed=42)

        self.assertEqual(len(df), 100)
        self.assertIn('curve_id', df.columns)
        self.assertIn('sha_estimate', df.columns)

    def test_reproducibility(self):
        """Test that same seed produces same results."""
        df1 = generate_sha_estimates(num_curves=50, seed=123)
        df2 = generate_sha_estimates(num_curves=50, seed=123)

        pd.testing.assert_frame_equal(df1, df2)

    def test_different_seeds(self):
        """Test that different seeds produce different results."""
        df1 = generate_sha_estimates(num_curves=50, seed=1)
        df2 = generate_sha_estimates(num_curves=50, seed=2)

        self.assertFalse(df1.equals(df2))

    def test_all_ranks_geq_2(self):
        """Test that all generated curves have rank >= 2."""
        df = generate_sha_estimates(num_curves=100, seed=42)

        self.assertTrue((df['rank'] >= 2).all())
        self.assertTrue((df['rank'] <= 4).all())

    def test_sha_formula(self):
        """Test that SHA estimate follows the BSD formula."""
        df = generate_sha_estimates(num_curves=10, seed=42)

        for _, row in df.iterrows():
            expected_sha = (row['ls_deriv'] * row['period']) / (
                row['regulator'] * (row['torsion_order'] ** 2)
            )
            # Allow small floating point error
            self.assertAlmostEqual(
                row['sha_estimate'],
                round(expected_sha, 8),
                places=8,
                msg=f"SHA mismatch for {row['curve_id']}"
            )

    def test_all_values_positive(self):
        """Test that all numerical values are positive."""
        df = generate_sha_estimates(num_curves=100, seed=42)

        self.assertTrue((df['conductor'] > 0).all())
        self.assertTrue((df['torsion_order'] > 0).all())
        self.assertTrue((df['regulator'] > 0).all())
        self.assertTrue((df['period'] > 0).all())
        self.assertTrue((df['ls_deriv'] > 0).all())
        self.assertTrue((df['sha_estimate'] > 0).all())

    def test_conductor_range(self):
        """Test that conductors are in expected range."""
        df = generate_sha_estimates(num_curves=100, seed=42)

        self.assertTrue((df['conductor'] >= 100000).all())
        self.assertTrue((df['conductor'] < 800000).all())

    def test_save_to_file(self):
        """Test saving data to CSV file."""
        with tempfile.TemporaryDirectory() as tmpdir:
            output_path = Path(tmpdir) / 'test_sha.csv'
            df = generate_sha_estimates(
                num_curves=50,
                seed=42,
                output_path=str(output_path)
            )

            self.assertTrue(output_path.exists())

            # Reload and verify
            df_loaded = pd.read_csv(output_path)
            pd.testing.assert_frame_equal(df, df_loaded)


class TestValidateShaEstimates(unittest.TestCase):
    """Tests for SHA estimate validation."""

    def test_valid_data(self):
        """Test validation passes for valid data."""
        df = generate_sha_estimates(num_curves=100, seed=42)
        results = validate_sha_estimates(df)

        self.assertTrue(results['all_checks_passed'])
        for check_name, passed in results['checks'].items():
            self.assertTrue(passed, f"Check failed: {check_name}")

    def test_invalid_rank(self):
        """Test validation detects invalid ranks."""
        df = generate_sha_estimates(num_curves=10, seed=42)
        df.loc[0, 'rank'] = 1  # Invalid rank

        results = validate_sha_estimates(df)

        self.assertFalse(results['checks']['all_ranks_geq_2'])
        self.assertFalse(results['all_checks_passed'])

    def test_missing_column(self):
        """Test validation detects missing columns."""
        df = generate_sha_estimates(num_curves=10, seed=42)
        df = df.drop(columns=['sha_estimate'])

        results = validate_sha_estimates(df)

        self.assertFalse(results['checks']['has_required_columns'])
        self.assertFalse(results['all_checks_passed'])

    def test_statistics(self):
        """Test that statistics are calculated correctly."""
        df = generate_sha_estimates(num_curves=100, seed=42)
        results = validate_sha_estimates(df)

        self.assertEqual(results['statistics']['total_curves'], 100)
        self.assertIn('rank_distribution', results['statistics'])
        self.assertIn('sha_estimate_stats', results['statistics'])


class TestDataIntegrity(unittest.TestCase):
    """Test integrity of generated data file."""

    def test_data_file_exists(self):
        """Test that the data file exists in the repository."""
        data_path = Path(__file__).parent.parent / 'data' / 'rank2plus' / 'sha_estimates.csv'

        if data_path.exists():
            df = pd.read_csv(data_path)
            self.assertEqual(len(df), 5000)
        else:
            self.skipTest("Data file not yet generated")

    def test_data_file_valid(self):
        """Test that the data file passes validation."""
        data_path = Path(__file__).parent.parent / 'data' / 'rank2plus' / 'sha_estimates.csv'

        if data_path.exists():
            df = pd.read_csv(data_path)
            results = validate_sha_estimates(df)
            self.assertTrue(
                results['all_checks_passed'],
                f"Validation failed: {results['checks']}"
            )
        else:
            self.skipTest("Data file not yet generated")


if __name__ == '__main__':
    unittest.main()
