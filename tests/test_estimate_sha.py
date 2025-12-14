"""
Tests for BSD LMFDB 10,000 Curve Experimental Analysis
======================================================

Tests for scripts/estimate_sha.py module.
"""

import sys
import os
import pytest
import json
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'scripts'))


@pytest.mark.basic
class TestLMFDBCurveSelector:
    """Tests for LMFDBCurveSelector class."""
    
    def test_import(self):
        """Test that the module can be imported."""
        from scripts.estimate_sha import LMFDBCurveSelector
        assert LMFDBCurveSelector is not None
    
    def test_initialization(self):
        """Test selector initialization."""
        from scripts.estimate_sha import LMFDBCurveSelector
        
        selector = LMFDBCurveSelector(conductor_max=1000)
        assert selector.conductor_max == 1000
        assert 0 in selector.ranks
        assert 2 in selector.ranks
    
    def test_get_curves_fallback(self):
        """Test fallback curve list generation."""
        from scripts.estimate_sha import LMFDBCurveSelector
        
        selector = LMFDBCurveSelector()
        curves = selector._get_fallback_curves(limit=50, stratified=False)
        
        assert len(curves) == 50
        assert '11a1' in curves
    
    def test_high_rank_curves_included(self):
        """Test that high-rank curves are in fallback list."""
        from scripts.estimate_sha import LMFDBCurveSelector
        
        selector = LMFDBCurveSelector()
        # Need larger limit to include high-rank curves which come after basic curves
        curves = selector._get_fallback_curves(limit=200, stratified=True)
        
        # Check that known rank 2 curves are included
        assert '389a1' in curves
        assert '433a1' in curves


@pytest.mark.basic
class TestShaEstimator:
    """Tests for ShaEstimator class."""
    
    def test_import(self):
        """Test that estimator can be imported."""
        from scripts.estimate_sha import ShaEstimator
        assert ShaEstimator is not None
    
    def test_initialization(self):
        """Test estimator initialization."""
        from scripts.estimate_sha import ShaEstimator
        
        estimator = ShaEstimator(precision=30)
        assert estimator.precision == 30
    
    def test_status_determination(self):
        """Test status determination logic."""
        from scripts.estimate_sha import ShaEstimator
        
        estimator = ShaEstimator()
        
        # Test validated status (near perfect square)
        assert estimator._determine_status(1.0, 0) == 'rank0_trivial'
        assert estimator._determine_status(4.0, 0) == 'rank0_nontrivial'
        assert estimator._determine_status(1.0, 2) == 'validated'
        
        # Test outliers
        assert estimator._determine_status(0.001, 0) == 'outlier_low'
        assert estimator._determine_status(2000000, 0) == 'outlier_high'
        
        # Test invalid
        assert estimator._determine_status(-1, 0) == 'invalid'


@pytest.mark.basic
class TestResonanceDetector:
    """Tests for ResonanceDetector class."""
    
    def test_import(self):
        """Test that detector can be imported."""
        from scripts.estimate_sha import ResonanceDetector
        assert ResonanceDetector is not None
    
    def test_initialization(self):
        """Test detector initialization with f0."""
        from scripts.estimate_sha import ResonanceDetector, F0_RESONANCE
        
        detector = ResonanceDetector()
        assert detector.f0 == F0_RESONANCE
        assert detector.f0 == 141.7001
    
    def test_detect_harmonics_empty(self):
        """Test harmonic detection with empty data."""
        from scripts.estimate_sha import ResonanceDetector
        import numpy as np
        
        detector = ResonanceDetector()
        harmonics = detector._detect_harmonics(np.array([1.0, 4.0, 9.0]))
        
        # Low values shouldn't match f0 harmonics
        assert isinstance(harmonics, list)
    
    def test_cluster_detection(self):
        """Test cluster detection near perfect squares."""
        from scripts.estimate_sha import ResonanceDetector
        import numpy as np
        
        detector = ResonanceDetector()
        
        # Create values clustered near perfect squares
        values = np.array([1.0, 1.1, 0.9, 4.0, 4.1, 3.9, 9.0, 9.1])
        clusters = detector._detect_clusters(values)
        
        assert len(clusters) >= 2  # Should find clusters at 1 and 4


@pytest.mark.basic
class TestBSDExperimentalAnalyzer:
    """Tests for BSDExperimentalAnalyzer class."""
    
    def test_import(self):
        """Test that analyzer can be imported."""
        from scripts.estimate_sha import BSDExperimentalAnalyzer
        assert BSDExperimentalAnalyzer is not None
    
    def test_initialization(self):
        """Test analyzer initialization."""
        from scripts.estimate_sha import BSDExperimentalAnalyzer
        
        analyzer = BSDExperimentalAnalyzer(output_dir='/tmp/test_bsd')
        assert analyzer.output_dir.exists()
    
    def test_mock_result_generation(self):
        """Test mock result generation for testing."""
        from scripts.estimate_sha import BSDExperimentalAnalyzer
        
        analyzer = BSDExperimentalAnalyzer(output_dir='/tmp/test_bsd')
        
        result = analyzer._generate_mock_result('11a1')
        assert result['label'] == '11a1'
        assert result['conductor'] == 11
        assert 'sha_estimate' in result
        assert result['sha_estimate'] > 0
    
    def test_mock_result_rank2(self):
        """Test mock result for rank 2 curve."""
        from scripts.estimate_sha import BSDExperimentalAnalyzer
        
        analyzer = BSDExperimentalAnalyzer(output_dir='/tmp/test_bsd')
        
        result = analyzer._generate_mock_result('389a1')
        assert result['label'] == '389a1'
        assert result['rank'] == 2
    
    def test_statistics_computation(self):
        """Test statistics computation."""
        from scripts.estimate_sha import BSDExperimentalAnalyzer
        
        analyzer = BSDExperimentalAnalyzer(output_dir='/tmp/test_bsd')
        
        mock_results = [
            {'success': True, 'rank': 0, 'sha_estimate': 1.0, 'status': 'validated'},
            {'success': True, 'rank': 1, 'sha_estimate': 1.0, 'status': 'validated'},
            {'success': False, 'rank': 2, 'sha_estimate': -1, 'status': 'error'},
        ]
        
        patterns = {'detected': False, 'patterns': []}
        stats = analyzer._compute_statistics(mock_results, patterns)
        
        assert stats['total_curves'] == 3
        assert stats['successful'] == 2
        assert 0 in stats['by_rank']
        assert 1 in stats['by_rank']


@pytest.mark.basic
class TestConstants:
    """Tests for module constants."""
    
    def test_f0_resonance(self):
        """Test F0 resonance constant."""
        from scripts.estimate_sha import F0_RESONANCE
        assert F0_RESONANCE == 141.7001
    
    def test_conductor_max(self):
        """Test conductor max constant."""
        from scripts.estimate_sha import CONDUCTOR_MAX_DEFAULT
        assert CONDUCTOR_MAX_DEFAULT == 1_000_000
    
    def test_outlier_thresholds(self):
        """Test outlier thresholds."""
        from scripts.estimate_sha import SHA_OUTLIER_LOW, SHA_OUTLIER_HIGH
        assert SHA_OUTLIER_LOW == 0.01
        assert SHA_OUTLIER_HIGH == 1_000_000


@pytest.mark.basic
class TestIntegration:
    """Integration tests for the full analysis pipeline."""
    
    def test_small_analysis_run(self):
        """Test a small analysis run."""
        from scripts.estimate_sha import BSDExperimentalAnalyzer
        import shutil
        
        output_dir = '/tmp/test_bsd_integration'
        
        try:
            analyzer = BSDExperimentalAnalyzer(output_dir=output_dir)
            results = analyzer.run_analysis(n_curves=10, verbose=False)
            
            assert 'results' in results
            assert 'statistics' in results
            assert 'patterns' in results
            assert 'beacon' in results
            
            # Check files were created
            assert (Path(output_dir) / 'bsd_lmfdb_10000.csv').exists()
            assert (Path(output_dir) / 'bsd_analysis_results.json').exists()
            assert (Path(output_dir) / 'qcal_beacon.json').exists()
            
        finally:
            # Cleanup
            if Path(output_dir).exists():
                shutil.rmtree(output_dir)
    
    def test_beacon_generation(self):
        """Test QCAL beacon generation."""
        from scripts.estimate_sha import BSDExperimentalAnalyzer
        import shutil
        
        output_dir = '/tmp/test_beacon'
        
        try:
            analyzer = BSDExperimentalAnalyzer(output_dir=output_dir)
            analyzer.results = [
                {'success': True, 'rank': 0, 'sha_estimate': 1.0, 'status': 'validated'}
            ]
            analyzer.statistics = {
                'total_curves': 1,
                'success_rate': 1.0
            }
            
            beacon = analyzer._generate_beacon()
            
            assert 'hash' in beacon
            assert 'type' in beacon
            assert beacon['type'] == 'BSD_LMFDB_10000_VALIDATION'
            assert beacon['f0_resonance'] == 141.7001
            
        finally:
            if Path(output_dir).exists():
                shutil.rmtree(output_dir)


@pytest.mark.basic
def test_main_function_exists():
    """Test that main function exists and is callable."""
    from scripts.estimate_sha import main
    assert callable(main)


@pytest.mark.basic
def test_lean4_files_exist():
    """Test that Lean 4 verification files exist."""
    lean_dir = Path(__file__).parent.parent / 'lean4' / 'sha_verification'
    
    assert lean_dir.exists(), "lean4/sha_verification directory should exist"
    assert (lean_dir / 'ShaVerification.lean').exists(), "ShaVerification.lean should exist"
    assert (lean_dir / 'Representatives.lean').exists(), "Representatives.lean should exist"
    assert (lean_dir / 'Main.lean').exists(), "Main.lean should exist"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
