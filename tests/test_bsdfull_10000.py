"""
Tests for bsdfull_10000 experimental module.

Tests the BSD-10000 spectral analysis functionality for large-scale
elliptic curve analysis.
"""

import sys
import pytest
from pathlib import Path
import tempfile
import shutil

# Add paths for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from scripts.experimental.bsdfull_10000 import BSDFull10000, SAGE_AVAILABLE


@pytest.mark.basic
class TestBSDFull10000Basic:
    """Basic tests that don't require SageMath."""

    def test_module_imports(self):
        """Test that module can be imported."""
        from scripts.experimental import bsdfull_10000
        assert bsdfull_10000 is not None

    def test_class_exists(self):
        """Test that BSDFull10000 class exists."""
        assert BSDFull10000 is not None

    def test_initialization_default(self):
        """Test default initialization."""
        with tempfile.TemporaryDirectory() as tmpdir:
            analyzer = BSDFull10000(output_dir=tmpdir)
            assert analyzer.number == 10000
            assert analyzer.rank_range == (0, 5)
            assert analyzer.conductor_max == 500000
            assert analyzer.verbose is True

    def test_initialization_custom(self):
        """Test custom initialization."""
        with tempfile.TemporaryDirectory() as tmpdir:
            analyzer = BSDFull10000(
                number=100,
                rank_range=(2, 4),
                conductor_max=1000,
                output_dir=tmpdir,
                verbose=False
            )
            assert analyzer.number == 100
            assert analyzer.rank_range == (2, 4)
            assert analyzer.conductor_max == 1000
            assert analyzer.verbose is False

    def test_output_directory_creation(self):
        """Test that output directory is created."""
        with tempfile.TemporaryDirectory() as tmpdir:
            output_path = Path(tmpdir) / 'new_output'
            analyzer = BSDFull10000(output_dir=str(output_path))
            assert output_path.exists()

    def test_generate_mock_curves(self):
        """Test mock curve generation."""
        with tempfile.TemporaryDirectory() as tmpdir:
            analyzer = BSDFull10000(number=10, output_dir=tmpdir)
            curves = analyzer._generate_mock_curves()
            assert isinstance(curves, list)
            assert len(curves) <= 10
            assert all(isinstance(c, str) for c in curves)

    def test_numerical_stability_check(self):
        """Test numerical stability checking."""
        with tempfile.TemporaryDirectory() as tmpdir:
            analyzer = BSDFull10000(output_dir=tmpdir)

            # Test stable case
            stability = analyzer._check_numerical_stability(
                sha=1.0, rank=1, conductor=11, leading_coef=0.25
            )
            assert stability['stable'] is True

            # Test unstable case - negative sha
            stability = analyzer._check_numerical_stability(
                sha=-1.0, rank=1, conductor=11, leading_coef=0.25
            )
            assert stability['stable'] is False

            # Test unstable case - large sha
            stability = analyzer._check_numerical_stability(
                sha=1e15, rank=1, conductor=11, leading_coef=0.25
            )
            assert stability['stable'] is False


@pytest.mark.sage_required
class TestBSDFull10000Sage:
    """Tests that require SageMath."""

    @pytest.fixture
    def analyzer(self):
        """Create analyzer instance with temp directory."""
        tmpdir = tempfile.mkdtemp()
        analyzer = BSDFull10000(number=5, output_dir=tmpdir)
        yield analyzer
        # Cleanup
        shutil.rmtree(tmpdir, ignore_errors=True)

    def test_get_curves_from_lmfdb(self, analyzer):
        """Test curve retrieval from LMFDB."""
        if not SAGE_AVAILABLE:
            pytest.skip("SageMath not available")

        curves = analyzer.get_curves_from_lmfdb()
        assert isinstance(curves, list)
        assert len(curves) > 0

    def test_analyze_single_curve(self, analyzer):
        """Test single curve analysis."""
        if not SAGE_AVAILABLE:
            pytest.skip("SageMath not available")

        result = analyzer.analyze_curve('11a1')
        assert 'label' in result
        assert result['label'] == '11a1'
        assert 'N' in result
        assert 'rank' in result

    def test_compute_analytic_sha(self, analyzer):
        """Test analytic Sha computation."""
        if not SAGE_AVAILABLE:
            pytest.skip("SageMath not available")

        from sage.all import EllipticCurve
        E = EllipticCurve('11a1')

        result = analyzer.compute_analytic_sha(E)
        assert 'analytic_sha' in result
        assert 'real_period' in result
        assert 'regulator' in result

    def test_run_analysis_small(self, analyzer):
        """Test running analysis on small sample."""
        if not SAGE_AVAILABLE:
            pytest.skip("SageMath not available")

        results = analyzer.run_analysis()
        assert results is not None
        assert len(results) > 0
        assert 'label' in results.columns
        assert 'BSD_verified' in results.columns

    def test_save_results(self, analyzer):
        """Test saving results to CSV."""
        if not SAGE_AVAILABLE:
            pytest.skip("SageMath not available")

        analyzer.run_analysis()
        filepath = analyzer.save_results('test_output.csv')

        assert filepath is not None
        assert Path(filepath).exists()

    def test_save_json_report(self, analyzer):
        """Test saving JSON report."""
        if not SAGE_AVAILABLE:
            pytest.skip("SageMath not available")

        analyzer.run_analysis()
        filepath = analyzer.save_json_report('test_report.json')

        assert filepath is not None
        assert Path(filepath).exists()


@pytest.mark.basic
class TestBSDFull10000MockMode:
    """Tests for mock mode (without SageMath)."""

    def test_mock_mode_runs(self):
        """Test that analysis runs in mock mode."""
        with tempfile.TemporaryDirectory() as tmpdir:
            analyzer = BSDFull10000(number=5, output_dir=tmpdir, verbose=False)

            # Even without Sage, should be able to run
            results = analyzer.run_analysis()
            assert results is not None

    def test_mock_curves_contain_known_labels(self):
        """Test that mock curves contain well-known labels."""
        with tempfile.TemporaryDirectory() as tmpdir:
            analyzer = BSDFull10000(number=100, output_dir=tmpdir)
            curves = analyzer._generate_mock_curves()

            # Should contain some well-known curves
            assert '11a1' in curves
            # 37a1 should be included if we request enough curves
            if len(curves) > 50:
                assert '37a1' in curves


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
