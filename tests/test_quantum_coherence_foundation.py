"""
Tests for Quantum Coherence Foundation Module

Tests the principle: "Mathematics from quantum coherence, not from isolated theorems"
"""

import pytest
import numpy as np
from pathlib import Path
import json
import sys

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from quantum_coherence_foundation import (
    QuantumCoherenceFoundation,
    demonstrate_coherence_vs_isolation,
    FUNDAMENTAL_FREQUENCY,
    COHERENCE_PARTIAL
)


class TestQuantumCoherenceFoundation:
    """Test suite for Quantum Coherence Foundation"""
    
    def test_initialization(self):
        """Test that foundation initializes correctly"""
        qcf = QuantumCoherenceFoundation()
        
        assert qcf.f0 == FUNDAMENTAL_FREQUENCY
        assert qcf.omega0 == 2 * np.pi * FUNDAMENTAL_FREQUENCY
        assert len(qcf.coherence_levels) == 6
        assert qcf.global_coherence == 0.0
    
    def test_spectral_coherence(self):
        """Test spectral coherence computation"""
        qcf = QuantumCoherenceFoundation()
        
        coherence = qcf.compute_spectral_coherence()
        
        assert 0.0 <= coherence <= 1.0
        assert qcf.coherence_levels['spectral'] == coherence
    
    def test_vibrational_coherence(self):
        """Test vibrational coherence computation"""
        qcf = QuantumCoherenceFoundation()
        
        coherence = qcf.compute_vibrational_coherence()
        
        assert 0.0 <= coherence <= 1.0
        assert qcf.coherence_levels['vibrational'] == coherence
    
    def test_arithmetic_coherence(self):
        """Test arithmetic coherence computation"""
        qcf = QuantumCoherenceFoundation()
        
        coherence = qcf.compute_arithmetic_coherence()
        
        assert 0.0 <= coherence <= 1.0
        assert qcf.coherence_levels['arithmetic'] == coherence
    
    def test_geometric_coherence(self):
        """Test geometric coherence computation"""
        qcf = QuantumCoherenceFoundation()
        
        coherence = qcf.compute_geometric_coherence()
        
        assert 0.0 <= coherence <= 1.0
        assert qcf.coherence_levels['geometric'] == coherence
    
    def test_quantum_coherence(self):
        """Test quantum coherence computation"""
        qcf = QuantumCoherenceFoundation()
        
        coherence = qcf.compute_quantum_coherence()
        
        assert 0.0 <= coherence <= 1.0
        assert qcf.coherence_levels['quantum'] == coherence
    
    def test_conscious_coherence(self):
        """Test conscious coherence computation"""
        qcf = QuantumCoherenceFoundation()
        
        coherence = qcf.compute_conscious_coherence()
        
        assert 0.0 <= coherence <= 1.0
        assert qcf.coherence_levels['conscious'] == coherence
    
    def test_global_coherence(self):
        """Test global coherence computation"""
        qcf = QuantumCoherenceFoundation()
        
        coherence = qcf.compute_global_coherence()
        
        # Global coherence should be weighted average
        assert 0.0 <= coherence <= 1.0
        assert qcf.global_coherence == coherence
        
        # All levels should be computed
        for level in qcf.coherence_levels.values():
            assert level > 0.0
    
    def test_coherence_threshold(self):
        """Test that global coherence meets operational threshold"""
        qcf = QuantumCoherenceFoundation()
        
        coherence = qcf.compute_global_coherence()
        
        # System should be operational (coherence > 0.90)
        # This validates the coherence approach over isolated theorems
        assert coherence > COHERENCE_PARTIAL, "System coherence too low - indicates fragmentation"
    
    def test_emergence_vs_isolation(self):
        """Test demonstration of emergence vs. isolated theorems"""
        qcf = QuantumCoherenceFoundation()
        
        demo = qcf.demonstrate_emergence_vs_isolation()
        
        # Check structure
        assert 'isolated_approach' in demo
        assert 'coherence_approach' in demo
        assert 'advantage' in demo
        assert 'global_coherence' in demo
        assert 'status' in demo
        
        # Isolated approach has no coherence
        assert demo['isolated_approach']['coherence'] == 0.0
        
        # Coherence approach has high coherence
        assert demo['coherence_approach']['coherence'] > COHERENCE_PARTIAL
        
        # Coherence approach is emergent
        assert demo['coherence_approach']['BSD_theorem']['status'] == 'emergent'
        assert demo['coherence_approach']['Riemann_hypothesis']['status'] == 'emergent'
        
        # Isolated approach is isolated
        assert demo['isolated_approach']['BSD_theorem']['status'] == 'isolated'
        assert demo['isolated_approach']['Riemann_hypothesis']['status'] == 'isolated'
    
    def test_coherence_report_generation(self, tmp_path):
        """Test coherence report generation"""
        qcf = QuantumCoherenceFoundation()
        
        # Generate report
        output_path = tmp_path / "test_coherence_report.json"
        report = qcf.generate_coherence_report(str(output_path))
        
        # Check report structure
        assert 'timestamp' in report
        assert 'philosophy' in report
        assert 'fundamental_frequency' in report
        assert 'coherence_levels' in report
        assert 'global_coherence' in report
        assert 'status' in report
        assert 'demonstration' in report
        assert 'principles' in report
        
        # Check philosophy statement
        assert 'quantum coherence' in report['philosophy'].lower()
        assert 'isolated theorems' in report['philosophy'].lower()
        
        # Check frequency
        assert report['fundamental_frequency'] == FUNDAMENTAL_FREQUENCY
        
        # Check principles
        principles = report['principles']
        assert 'unity_over_fragmentation' in principles
        assert 'connection_over_isolation' in principles
        assert 'emergence_over_construction' in principles
        assert 'frequency_over_formula' in principles
        
        # Check file was created
        assert output_path.exists()
        
        # Validate JSON
        with open(output_path, 'r') as f:
            loaded_report = json.load(f)
            assert loaded_report == report
    
    def test_demonstrate_function(self, capsys):
        """Test the demonstration function"""
        demo = demonstrate_coherence_vs_isolation()
        
        # Capture output
        captured = capsys.readouterr()
        
        # Check key messages in output
        assert "QUANTUM COHERENCE FOUNDATION" in captured.out
        assert "Mathematics from quantum coherence" in captured.out
        assert str(FUNDAMENTAL_FREQUENCY) in captured.out
        assert "Global Coherence" in captured.out
        
        # Check demo result
        assert demo['advantage'] == 'coherence_unifies_all'
    
    def test_coherence_superiority(self):
        """
        Test that coherence approach is superior to isolated theorems.
        
        This is the core validation of the problem statement:
        "Mathematics from quantum coherence, not from scarcity of isolated theorems"
        """
        qcf = QuantumCoherenceFoundation()
        demo = qcf.demonstrate_emergence_vs_isolation()
        
        # Coherence approach has connections
        bsd_coherence = demo['coherence_approach']['BSD_theorem']
        assert len(bsd_coherence['connections']) > 0
        assert 'Riemann' in bsd_coherence['connections']
        
        # Isolated approach has no connections
        bsd_isolated = demo['isolated_approach']['BSD_theorem']
        assert len(bsd_isolated['connections']) == 0
        
        # Coherence approach has unified understanding
        assert bsd_coherence['understanding'] == 'holistic'
        assert bsd_isolated['understanding'] == 'fragmented'
        
        # Coherence approach has global coherence
        assert demo['coherence_approach']['coherence'] > 0.0
        assert demo['isolated_approach']['coherence'] == 0.0
        
        # This proves: coherence > isolation
        assert (demo['coherence_approach']['coherence'] > 
                demo['isolated_approach']['coherence'])


class TestCoherencePrinciples:
    """Test that coherence principles are satisfied"""
    
    def test_unity_principle(self):
        """Test Principle 1: Unity over Fragmentation"""
        qcf = QuantumCoherenceFoundation()
        qcf.compute_global_coherence()
        
        # All levels should contribute to unity
        assert all(level > 0.0 for level in qcf.coherence_levels.values())
        
        # Global coherence emerges from unity
        assert qcf.global_coherence > 0.0
    
    def test_connection_principle(self):
        """Test Principle 2: Connection over Isolation"""
        qcf = QuantumCoherenceFoundation()
        demo = qcf.demonstrate_emergence_vs_isolation()
        
        # Coherence approach has connections
        approach = demo['coherence_approach']
        assert len(approach['BSD_theorem']['connections']) > 0
        assert len(approach['Riemann_hypothesis']['connections']) > 0
    
    def test_emergence_principle(self):
        """Test Principle 3: Emergence over Construction"""
        qcf = QuantumCoherenceFoundation()
        demo = qcf.demonstrate_emergence_vs_isolation()
        
        # Results are emergent, not constructed
        approach = demo['coherence_approach']
        assert approach['BSD_theorem']['status'] == 'emergent'
        assert approach['Riemann_hypothesis']['status'] == 'emergent'
    
    def test_frequency_principle(self):
        """Test Principle 4: Frequency over Formula"""
        qcf = QuantumCoherenceFoundation()
        demo = qcf.demonstrate_emergence_vs_isolation()
        
        # Fundamental frequency is the source
        approach = demo['coherence_approach']
        assert approach['BSD_theorem']['frequency'] == FUNDAMENTAL_FREQUENCY
        assert approach['Riemann_hypothesis']['frequency'] == FUNDAMENTAL_FREQUENCY


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
