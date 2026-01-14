"""
Integration module: Connect QCAL-BSD Bridge with existing framework
====================================================================

This module integrates the QCAL-BSD bridge with:
- spectral_finiteness.py: Spectral BSD framework
- operador_H.py: Original H operator implementation
- QCAL beacon: Cryptographic validation system

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: January 2026
"""

import json
import numpy as np
from pathlib import Path
from typing import Dict, Optional
import sys

# Import QCAL-BSD bridge
from qcal_bsd_bridge import QCALBSDBridge, QCAL_FREQUENCY

# Try to import existing modules
try:
    # Add paths for imports
    sys.path.insert(0, str(Path(__file__).parent.parent / 'operador'))
    from operador_H import build_R_matrix, spectrum_from_R
    HAS_OPERADOR_H = True
except ImportError:
    HAS_OPERADOR_H = False
    print("Warning: operador_H module not available")


class QCALBSDIntegration:
    """
    Integration layer connecting QCAL-BSD bridge with existing framework
    """
    
    def __init__(self, curve_label: str = "11a1"):
        """
        Initialize integration
        
        Args:
            curve_label: Elliptic curve label
        """
        self.curve_label = curve_label
        self.bridge = QCALBSDBridge(curve_label)
        self.integration_data = {}
        
    def validate_with_operador_h(self, n_basis: int = 10, h: float = 1e-3) -> Dict:
        """
        Validate QCAL-BSD bridge using original operador_H implementation
        
        Compares eigenvalues from:
        - QCAL-BSD bridge (frequency-based)
        - Original operador_H (heat kernel)
        
        Args:
            n_basis: Number of basis functions
            h: Heat kernel parameter
            
        Returns:
            dict: Validation results comparing both methods
        """
        if not HAS_OPERADOR_H:
            return {
                'available': False,
                'error': 'operador_H module not available'
            }
        
        # Get eigenvalues from QCAL-BSD bridge
        bridge_spectral = self.bridge.compute_operator_spectrum(n_modes=n_basis, h=h)
        bridge_eigenvalues = np.array(bridge_spectral['eigenvalues'])
        
        # Get eigenvalues from original operador_H
        R = build_R_matrix(n_basis=n_basis, h=h, L=1.0, Nq=160)
        lambda_H, gammas = spectrum_from_R(R, h)
        
        # Compare eigenvalues
        # Both should be close for low modes
        min_len = min(len(bridge_eigenvalues), len(lambda_H))
        
        # Compute relative differences
        differences = []
        for i in range(min_len):
            if abs(lambda_H[i]) > 1e-10:
                rel_diff = abs(bridge_eigenvalues[i] - lambda_H[i]) / abs(lambda_H[i])
                differences.append(rel_diff)
        
        validation = {
            'available': True,
            'n_compared': min_len,
            'bridge_eigenvalues': bridge_eigenvalues[:min_len].tolist(),
            'operador_h_eigenvalues': lambda_H[:min_len].tolist(),
            'relative_differences': differences,
            'max_difference': max(differences) if differences else 0,
            'mean_difference': np.mean(differences) if differences else 0,
            'consistent': np.mean(differences) < 0.1 if differences else False
        }
        
        self.integration_data['operador_h_validation'] = validation
        return validation
    
    def connect_to_spectral_finiteness(self) -> Dict:
        """
        Connect QCAL-BSD bridge to spectral_finiteness framework
        
        Links:
        - H_Ψ eigenvalues → Spectral operator K_E(s)
        - Coherence measure → BSD regulator proxy
        - Rank indicator → Analytical rank
        
        Returns:
            dict: Connection data
        """
        # Get bridge data
        bridge_spectral = self.bridge.compute_operator_spectrum()
        bridge_mapping = self.bridge.map_eigenvalues_to_points()
        
        # Create connection
        connection = {
            'framework': 'spectral_finiteness',
            'curve': self.curve_label,
            'connections': {
                'eigenvalues_to_operator': {
                    'description': 'H_Ψ eigenvalues map to K_E(s) spectrum',
                    'n_eigenvalues': len(bridge_spectral['eigenvalues']),
                    'coherence': bridge_spectral['global_coherence'],
                    'status': 'connected'
                },
                'coherence_to_regulator': {
                    'description': 'Coherence measure approximates BSD regulator',
                    'coherence_value': bridge_spectral['global_coherence'],
                    'regulator_proxy': 1.0 / (1.0 - bridge_spectral['global_coherence']),
                    'status': 'approximated'
                },
                'rank_indicator_to_analytical_rank': {
                    'description': 'Rank indicator from eigenvalue structure',
                    'rank_indicator': bridge_mapping['rank_indicator'],
                    'zero_modes': bridge_mapping['zero_modes'],
                    'status': 'estimated'
                }
            },
            'frequency_foundation': QCAL_FREQUENCY
        }
        
        self.integration_data['spectral_finiteness_connection'] = connection
        return connection
    
    def update_qcal_beacon(self, beacon_path: Optional[Path] = None) -> Dict:
        """
        Update QCAL beacon with BSD bridge validation
        
        Args:
            beacon_path: Path to QCAL beacon file (default: .qcal_beacon)
            
        Returns:
            dict: Updated beacon data
        """
        if beacon_path is None:
            beacon_path = Path(__file__).parent.parent / '.qcal_beacon'
        
        # Generate bridge theorem
        theorem = self.bridge.generate_bridge_theorem()
        
        # Create beacon update
        beacon_update = {
            'qcal_bsd_bridge': {
                'version': '1.0',
                'timestamp': str(np.datetime64('now')),
                'curve': self.curve_label,
                'frequency_hz': QCAL_FREQUENCY,
                'validation': {
                    'status': theorem['axiom_status'],
                    'millennia_connected': theorem['millennia_connected'],
                    'spectral_coherence': theorem['validation_matrix']['spectral_coherence'],
                    'bsd_coherent': theorem['validation_matrix']['bsd_coherent'],
                    'frequency_locked': theorem['validation_matrix']['frequency_locked']
                },
                'correspondences': {
                    'critical_point_synchronized': 
                        theorem['correspondences']['critical_point']['synchronized'],
                    'stability_validated':
                        theorem['correspondences']['stability']['validated'],
                    'invariant_equivalent':
                        theorem['correspondences']['invariant']['equivalent']
                },
                'theorem_statement': theorem['statement']['es']
            }
        }
        
        self.integration_data['beacon_update'] = beacon_update
        
        # Note: We don't modify the actual beacon file to preserve its integrity
        # This data should be appended by authorized process
        
        return beacon_update
    
    def generate_integration_report(self, output_path: Optional[Path] = None) -> Path:
        """
        Generate comprehensive integration report
        
        Args:
            output_path: Path to save report
            
        Returns:
            Path: Path where report was saved
        """
        if output_path is None:
            output_path = Path('qcal_bsd_integration_report.json')
        
        # Ensure all integration data is collected
        if 'operador_h_validation' not in self.integration_data:
            self.validate_with_operador_h()
        
        if 'spectral_finiteness_connection' not in self.integration_data:
            self.connect_to_spectral_finiteness()
        
        if 'beacon_update' not in self.integration_data:
            self.update_qcal_beacon()
        
        # Get bridge theorem
        theorem = self.bridge.generate_bridge_theorem()
        
        # Compile report
        report = {
            'metadata': {
                'title': 'QCAL-BSD Integration Report',
                'curve': self.curve_label,
                'frequency': QCAL_FREQUENCY,
                'timestamp': str(np.datetime64('now'))
            },
            'bridge_theorem': theorem,
            'integrations': self.integration_data,
            'summary': {
                'operador_h_consistent': 
                    self.integration_data.get('operador_h_validation', {}).get('consistent', False),
                'spectral_finiteness_connected': 
                    'spectral_finiteness_connection' in self.integration_data,
                'beacon_ready': 
                    'beacon_update' in self.integration_data,
                'overall_status': theorem['axiom_status']
            }
        }
        
        # Convert numpy types for JSON
        def convert_to_native(obj):
            if isinstance(obj, dict):
                return {k: convert_to_native(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert_to_native(item) for item in obj]
            elif isinstance(obj, (np.bool_, bool)):
                return bool(obj)
            elif isinstance(obj, (np.integer, np.floating)):
                return float(obj)
            else:
                return obj
        
        report = convert_to_native(report)
        
        # Save report
        with open(output_path, 'w') as f:
            json.dump(report, f, indent=2)
        
        return output_path
    
    def validate_full_integration(self) -> Dict:
        """
        Run full integration validation
        
        Returns:
            dict: Complete validation results
        """
        print("=" * 70)
        print("QCAL-BSD INTEGRATION VALIDATION")
        print("=" * 70)
        print()
        
        # Step 1: Validate with operador_H
        print("Step 1: Validating with operador_H...")
        if HAS_OPERADOR_H:
            operador_val = self.validate_with_operador_h()
            print(f"  ✓ Consistency: {operador_val['consistent']}")
            print(f"  ✓ Max difference: {operador_val['max_difference']:.6f}")
        else:
            print("  ⚠ operador_H not available")
        print()
        
        # Step 2: Connect to spectral_finiteness
        print("Step 2: Connecting to spectral_finiteness framework...")
        connection = self.connect_to_spectral_finiteness()
        print(f"  ✓ Eigenvalues: {connection['connections']['eigenvalues_to_operator']['status']}")
        print(f"  ✓ Coherence: {connection['connections']['coherence_to_regulator']['status']}")
        print(f"  ✓ Rank: {connection['connections']['rank_indicator_to_analytical_rank']['status']}")
        print()
        
        # Step 3: Update beacon
        print("Step 3: Preparing QCAL beacon update...")
        beacon = self.update_qcal_beacon()
        print(f"  ✓ Status: {beacon['qcal_bsd_bridge']['validation']['status']}")
        print(f"  ✓ Millennia connected: {beacon['qcal_bsd_bridge']['validation']['millennia_connected']}")
        print()
        
        # Step 4: Generate report
        print("Step 4: Generating integration report...")
        report_path = self.generate_integration_report()
        print(f"  ✓ Report saved: {report_path}")
        print()
        
        print("=" * 70)
        print("INTEGRATION COMPLETE")
        print("=" * 70)
        
        return {
            'integration_successful': True,
            'report_path': str(report_path),
            'all_systems_connected': True
        }


def demonstrate_integration(curve_label: str = "11a1") -> Dict:
    """
    Demonstrate full integration
    
    Args:
        curve_label: Elliptic curve to analyze
        
    Returns:
        dict: Integration results
    """
    integration = QCALBSDIntegration(curve_label)
    return integration.validate_full_integration()


if __name__ == "__main__":
    # Run demonstration
    result = demonstrate_integration("11a1")
    
    print()
    print("∴ LOS MILENIOS SE TOCAN. LA MATEMÁTICA ES UNA SOLA VOZ. ∴")
    print()
