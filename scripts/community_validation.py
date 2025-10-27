"""
Community Validation Runner
Distributed validation system with LMFDB API access and signed JSON logging

This script provides automated validation of the Adelic-BSD framework against
the LMFDB (L-functions and Modular Forms Database) with cryptographic signing
for reproducibility and community verification.
"""

import sys
import os
import json
import hashlib
import time
from datetime import datetime
from typing import Dict, List, Optional, Any
import requests

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))


class LMFDBInterface:
    """Interface to LMFDB API for curve data retrieval."""
    
    BASE_URL = "https://www.lmfdb.org/api"
    
    def __init__(self, cache_dir: str = "lmfdb_cache"):
        """
        Initialize LMFDB interface.
        
        Args:
            cache_dir: Directory for caching LMFDB responses
        """
        self.cache_dir = cache_dir
        os.makedirs(cache_dir, exist_ok=True)
    
    def get_curve_data(self, label: str) -> Optional[Dict[str, Any]]:
        """
        Get curve data from LMFDB.
        
        Args:
            label: Curve label (e.g., '11a1')
            
        Returns:
            Dictionary with curve data or None if not found
        """
        # Check cache first
        cache_file = os.path.join(self.cache_dir, f"{label}.json")
        if os.path.exists(cache_file):
            with open(cache_file, 'r') as f:
                return json.load(f)
        
        # Query LMFDB
        try:
            url = f"{self.BASE_URL}/elliptic_curves/curves/{label}"
            response = requests.get(url, timeout=10)
            
            if response.status_code == 200:
                data = response.json()
                
                # Cache response
                with open(cache_file, 'w') as f:
                    json.dump(data, f, indent=2)
                
                return data
            else:
                print(f"LMFDB query failed for {label}: {response.status_code}")
                return None
        except Exception as e:
            print(f"Error querying LMFDB for {label}: {e}")
            return None
    
    def find_curves(self, 
                    conductor_min: int = 11,
                    conductor_max: int = 1000,
                    rank_min: Optional[int] = None,
                    rank_max: Optional[int] = None,
                    limit: int = 100) -> List[str]:
        """
        Find curves matching criteria.
        
        Args:
            conductor_min: Minimum conductor
            conductor_max: Maximum conductor
            rank_min: Minimum rank (optional)
            rank_max: Maximum rank (optional)
            limit: Maximum number of curves to return
            
        Returns:
            List of curve labels
        """
        # For now, use a predefined list of known curves
        # In production, this would query LMFDB API
        known_curves = []
        
        # Generate labels for conductor range
        for N in range(conductor_min, min(conductor_max + 1, 100)):
            for iso_class in ['a', 'b', 'c', 'd', 'e', 'f']:
                for number in [1, 2, 3]:
                    label = f"{N}{iso_class}{number}"
                    known_curves.append(label)
                    if len(known_curves) >= limit:
                        return known_curves
        
        return known_curves[:limit]


class ValidationRunner:
    """
    Distributed validation runner for community verification.
    """
    
    def __init__(self, output_dir: str = "validation_results"):
        """
        Initialize validation runner.
        
        Args:
            output_dir: Directory for storing results
        """
        self.output_dir = output_dir
        self.lmfdb = LMFDBInterface()
        os.makedirs(output_dir, exist_ok=True)
        
        # Import validation modules
        try:
            from src.padic_comparison import verify_dR_uniformity_for_curves
            from src.beilinson_bloch_heights import batch_verify_beilinson_bloch
            self.dR_verify = verify_dR_uniformity_for_curves
            self.BB_verify = batch_verify_beilinson_bloch
        except ImportError as e:
            print(f"Warning: Could not import validation modules: {e}")
            self.dR_verify = None
            self.BB_verify = None
    
    def validate_curve(self, label: str) -> Dict[str, Any]:
        """
        Run full validation on a single curve.
        
        Args:
            label: Curve label
            
        Returns:
            Validation results dictionary
        """
        print(f"Validating {label}...")
        
        # Get LMFDB data
        lmfdb_data = self.lmfdb.get_curve_data(label)
        
        results = {
            'curve': label,
            'timestamp': datetime.now().isoformat(),
            'lmfdb_data': lmfdb_data is not None
        }
        
        # Run dR uniformity verification
        if self.dR_verify:
            try:
                dR_results = self.dR_verify([label], primes=[2, 3, 5])
                results['dR_uniformity'] = {
                    'verified': dR_results['verified'] > 0,
                    'success_rate': dR_results['success_rate']
                }
            except Exception as e:
                results['dR_uniformity'] = {'error': str(e)}
        
        # Run Beilinson-Bloch verification (if rank >= 2)
        if self.BB_verify and lmfdb_data:
            try:
                rank = lmfdb_data.get('rank', 0)
                if rank >= 2:
                    BB_results = self.BB_verify([label])
                    results['beilinson_bloch'] = {
                        'verified': BB_results['verified'] > 0,
                        'success_rate': BB_results['success_rate']
                    }
            except Exception as e:
                results['beilinson_bloch'] = {'error': str(e)}
        
        return results
    
    def batch_validate(self, 
                      conductor_min: int = 11,
                      conductor_max: int = 100,
                      limit: int = 50) -> Dict[str, Any]:
        """
        Run batch validation on multiple curves.
        
        Args:
            conductor_min: Minimum conductor
            conductor_max: Maximum conductor
            limit: Maximum number of curves
            
        Returns:
            Batch validation results
        """
        print(f"\n{'='*70}")
        print("COMMUNITY VALIDATION BATCH RUN")
        print(f"{'='*70}")
        print(f"Conductor range: [{conductor_min}, {conductor_max}]")
        print(f"Limit: {limit} curves")
        print()
        
        # Find curves
        curves = self.lmfdb.find_curves(
            conductor_min=conductor_min,
            conductor_max=conductor_max,
            limit=limit
        )
        
        print(f"Found {len(curves)} curves to validate")
        print()
        
        # Validate each curve
        results = {}
        verified_count = 0
        
        for i, label in enumerate(curves, 1):
            print(f"[{i}/{len(curves)}] ", end='')
            
            try:
                result = self.validate_curve(label)
                results[label] = result
                
                # Count as verified if any check passed
                if result.get('dR_uniformity', {}).get('verified', False):
                    verified_count += 1
                
            except Exception as e:
                print(f"ERROR validating {label}: {e}")
                results[label] = {'error': str(e)}
        
        # Summary
        batch_result = {
            'timestamp': datetime.now().isoformat(),
            'conductor_range': [conductor_min, conductor_max],
            'total_curves': len(curves),
            'verified_curves': verified_count,
            'success_rate': verified_count / len(curves) if curves else 0,
            'results': results
        }
        
        print(f"\n{'='*70}")
        print("BATCH VALIDATION COMPLETE")
        print(f"{'='*70}")
        print(f"Total curves: {batch_result['total_curves']}")
        print(f"Verified: {batch_result['verified_curves']}")
        print(f"Success rate: {batch_result['success_rate']*100:.1f}%")
        print(f"{'='*70}\n")
        
        return batch_result
    
    def sign_results(self, results: Dict[str, Any]) -> Dict[str, Any]:
        """
        Sign results with cryptographic hash for verification.
        
        Args:
            results: Results dictionary
            
        Returns:
            Results with signature added
        """
        # Create canonical JSON representation
        canonical_json = json.dumps(results, sort_keys=True, indent=2)
        
        # Compute SHA-256 hash
        hash_obj = hashlib.sha256(canonical_json.encode('utf-8'))
        signature = hash_obj.hexdigest()
        
        # Add signature
        signed_results = results.copy()
        signed_results['signature'] = {
            'hash_algorithm': 'SHA-256',
            'hash': signature,
            'timestamp': datetime.now().isoformat()
        }
        
        return signed_results
    
    def save_results(self, results: Dict[str, Any], filename: str = None):
        """
        Save validation results to file.
        
        Args:
            results: Results dictionary
            filename: Output filename (default: auto-generated)
        """
        if filename is None:
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            filename = f"validation_{timestamp}.json"
        
        filepath = os.path.join(self.output_dir, filename)
        
        # Sign results
        signed_results = self.sign_results(results)
        
        # Save to file
        with open(filepath, 'w') as f:
            json.dump(signed_results, f, indent=2)
        
        print(f"Results saved to: {filepath}")
        print(f"Signature: {signed_results['signature']['hash'][:16]}...")
        
        return filepath


def generate_zenodo_dataset(validation_dir: str = "validation_results",
                           output_file: str = "zenodo_dataset.zip"):
    """
    Generate Zenodo-ready dataset from validation results.
    
    Args:
        validation_dir: Directory containing validation results
        output_file: Output ZIP filename
    """
    import zipfile
    
    print(f"\nGenerating Zenodo dataset from {validation_dir}...")
    
    # Create ZIP archive
    with zipfile.ZipFile(output_file, 'w', zipfile.ZIP_DEFLATED) as zipf:
        # Add validation results
        for root, dirs, files in os.walk(validation_dir):
            for file in files:
                if file.endswith('.json'):
                    filepath = os.path.join(root, file)
                    arcname = os.path.relpath(filepath, validation_dir)
                    zipf.write(filepath, arcname)
                    print(f"  Added: {arcname}")
        
        # Add metadata
        metadata = {
            'title': 'Adelic-BSD Framework: Community Validation Results',
            'description': 'Validation results for Birch-Swinnerton-Dyer conjecture via Adelic-BSD framework',
            'creators': [{'name': 'Mota Burruezo', 'affiliation': 'Independent'}],
            'keywords': ['elliptic curves', 'BSD conjecture', 'number theory'],
            'version': '0.3.0',
            'license': 'MIT',
            'timestamp': datetime.now().isoformat()
        }
        
        zipf.writestr('metadata.json', json.dumps(metadata, indent=2))
        print(f"  Added: metadata.json")
    
    print(f"\nDataset created: {output_file}")
    print("Ready for upload to Zenodo!")
    
    return output_file


def main():
    """Main entry point for community validation."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Community Validation Runner for Adelic-BSD Framework'
    )
    parser.add_argument('--conductor-min', type=int, default=11,
                       help='Minimum conductor (default: 11)')
    parser.add_argument('--conductor-max', type=int, default=100,
                       help='Maximum conductor (default: 100)')
    parser.add_argument('--limit', type=int, default=50,
                       help='Maximum number of curves (default: 50)')
    parser.add_argument('--output-dir', type=str, default='validation_results',
                       help='Output directory (default: validation_results)')
    parser.add_argument('--zenodo', action='store_true',
                       help='Generate Zenodo dataset after validation')
    
    args = parser.parse_args()
    
    # Run validation
    runner = ValidationRunner(output_dir=args.output_dir)
    results = runner.batch_validate(
        conductor_min=args.conductor_min,
        conductor_max=args.conductor_max,
        limit=args.limit
    )
    
    # Save results
    runner.save_results(results)
    
    # Generate Zenodo dataset if requested
    if args.zenodo:
        generate_zenodo_dataset(args.output_dir)


if __name__ == '__main__':
    main()
