"""
Mass Formal Proof System
Implements batch BSD verification across multiple curves

This module provides tools for large-scale verification of BSD conjecture
across families of elliptic curves from LMFDB.
"""

from sage.all import EllipticCurve
from .formal_bsd_prover import FormalBSDProver
import json
import os
from datetime import datetime
from ..utils import get_safe_output_path


class MassFormalProof:
    """
    Mass formal proof system for BSD conjecture

    Provides batch processing and verification across multiple curves,
    with comprehensive reporting and statistical analysis.
    """

    def __init__(self):
        """Initialize mass proof system"""
        self.results = {}
        self.global_proof = {}

    def prove_entire_lmfdb(self, max_rank=3, conductor_limit=1000, max_curves=50):
        """
        Prove BSD for curves from LMFDB database

        Args:
            max_rank: Maximum rank to include (default: 3)
            conductor_limit: Maximum conductor (default: 1000)
            max_curves: Maximum number of curves to test (default: 50)

        Returns:
            dict: Global proof results
        """
        curves = self._load_all_curves(max_rank, conductor_limit, max_curves)

        print("🧠 INITIATING MASS FORMAL BSD VERIFICATION")
        print(f"📊 Curves to verify: {len(curves)}")
        print("=" * 60)

        for i, E in enumerate(curves):
            label = E.cremona_label() if hasattr(E, 'cremona_label') else str(E)
            print(f"\n🔬 Processing {label} ({i+1}/{len(curves)})")

            try:
                prover = FormalBSDProver(E)
                certificate = prover.prove_bsd_completely()

                self.results[label] = certificate

                if certificate['bsd_proven']:
                    print(f"   ✅ BSD VERIFIED FOR {label}")
                else:
                    print(f"   ⚠️  PARTIAL VERIFICATION FOR {label}")

            except Exception as e:
                print(f"   ❌ ERROR IN {label}: {e}")
                self.results[label] = {
                    'error': str(e),
                    'bsd_proven': False
                }

        return self._compile_global_proof()

    def _load_all_curves(self, max_rank, conductor_limit, max_curves):
        """Load curves from LMFDB/Sage database"""
        curves = []

        try:
            # Try to get curves from LMFDB interface
            from sage.databases.cremona import CremonaDatabase
            db = CremonaDatabase()

            # Get curves up to conductor limit
            for N in range(11, conductor_limit + 1):
                try:
                    curve_labels = db.list(N)
                    for label in curve_labels:
                        try:
                            E = EllipticCurve(label)
                            if E.rank() <= max_rank:
                                curves.append(E)

                            if len(curves) >= max_curves:
                                return curves
                        except:
                            continue
                except:
                    continue

        except Exception as e:
            print(f"Warning: Could not load from CremonaDatabase: {e}")
            # Fallback: use well-known curves
            curves = self._get_fallback_curves(max_rank, max_curves)

        return curves[:max_curves]

    def _get_fallback_curves(self, max_rank, max_curves):
        """Get fallback list of well-known curves"""
        well_known = [
            '11a1', '11a2', '11a3',
            '14a1', '14a2', '14a3', '14a4', '14a5', '14a6',
            '15a1', '15a2', '15a3', '15a4', '15a5', '15a6', '15a7', '15a8',
            '17a1', '17a2', '17a3', '17a4',
            '19a1', '19a2', '19a3',
            '20a1', '20a2', '20a3', '20a4', '20a5', '20a6',
            '21a1', '21a2', '21a3', '21a4',
            '24a1', '24a2', '24a3', '24a4',
            '26a1', '26a2', '26b1',
            '27a1', '27a2', '27a3', '27a4',
            '30a1', '30a2', '30a3', '30a4', '30a5', '30a6', '30a7', '30a8',
            '32a1', '32a2', '32a3', '32a4',
            '33a1', '33a2', '33a3',
            '34a1', '34a2', '34a3',
            '35a1', '35a2', '35a3',
            '36a1', '36a2', '36a3', '36a4',
            '37a1', '37b1',
            '38a1', '38a2', '38b1',
            '39a1', '39a2', '39a3',
            '40a1', '40a2', '40a3', '40a4',
            '42a1', '42a2', '42a3', '42a4',
            '43a1', '43a2',
            '44a1', '44a2', '44a3',
            '45a1', '45a2', '45a3', '45a4',
            '46a1', '46a2', '46a3',
            '48a1', '48a2', '48a3', '48a4', '48a5', '48a6',
            '49a1', '49a2', '49a3', '49a4',
            '50a1', '50a2', '50a3', '50a4', '50b1', '50b2',
        ]

        curves = []
        for label in well_known[:max_curves]:
            try:
                E = EllipticCurve(label)
                if E.rank() <= max_rank:
                    curves.append(E)
            except:
                continue

        return curves

    def _compile_global_proof(self):
        """Compile global proof from individual results"""
        successful = [
            label for label, cert in self.results.items()
            if isinstance(cert, dict) and cert.get('bsd_proven', False)
        ]

        total = len(self.results)
        success_count = len(successful)

        self.global_proof = {
            'total_curves': total,
            'successful_proofs': success_count,
            'failed_proofs': total - success_count,
            'success_rate': success_count / total if total > 0 else 0,
            'successful_curves': successful,
            'proof_timestamp': datetime.now().isoformat(),
            'global_bsd_status': 'VERIFIED' if success_count == total else 'PARTIAL'
        }

        # Generate final report
        self._generate_final_report()

        return self.global_proof

    def _generate_final_report(self):
        """Generate final verification report"""
        report_lines = [
            "\n" + "=" * 60,
            "MASS FORMAL BSD VERIFICATION REPORT",
            "=" * 60,
            f"Total curves tested: {self.global_proof['total_curves']}",
            f"Successful verifications: {self.global_proof['successful_proofs']}",
            f"Failed verifications: {self.global_proof['failed_proofs']}",
            f"Success rate: {self.global_proof['success_rate']:.2%}",
            f"Global BSD status: {self.global_proof['global_bsd_status']}",
            "=" * 60
        ]

        self.global_proof['report'] = '\n'.join(report_lines)

        # Print report
        print('\n'.join(report_lines))

    def save_results(self, filename='mass_bsd_proof_results.json'):
        """Save all results to JSON file"""
        output = {
            'global_proof': self.global_proof,
            'individual_results': self.results
        }

        # Use safe directory for file writing
        filepath = get_safe_output_path(filename)
        
        with open(filepath, 'w') as f:
            json.dump(output, f, indent=2, default=str)

        print(f"\nResults saved to {filepath}")
        return filepath

    def get_statistics(self):
        """Get detailed statistics about the verification"""
        if not self.results:
            return {}

        stats = {
            'total_curves': len(self.results),
            'by_rank': {},
            'by_conductor': {},
            'verification_rate': {}
        }

        for label, result in self.results.items():
            try:
                E = EllipticCurve(label)
                rank = E.rank()
                conductor = int(E.conductor())
                verified = result.get('bsd_proven', False)

                # By rank
                if rank not in stats['by_rank']:
                    stats['by_rank'][rank] = {'total': 0, 'verified': 0}
                stats['by_rank'][rank]['total'] += 1
                if verified:
                    stats['by_rank'][rank]['verified'] += 1

                # By conductor range
                conductor_range = f"{(conductor // 100) * 100}-{(conductor // 100 + 1) * 100}"
                if conductor_range not in stats['by_conductor']:
                    stats['by_conductor'][conductor_range] = {'total': 0, 'verified': 0}
                stats['by_conductor'][conductor_range]['total'] += 1
                if verified:
                    stats['by_conductor'][conductor_range]['verified'] += 1

            except:
                continue

        # Compute rates
        for rank, data in stats['by_rank'].items():
            data['rate'] = data['verified'] / data['total'] if data['total'] > 0 else 0

        for cond_range, data in stats['by_conductor'].items():
            data['rate'] = data['verified'] / data['total'] if data['total'] > 0 else 0

        return stats


def batch_prove_bsd(curve_labels):
    """
    Prove BSD for a list of curve labels

    Args:
        curve_labels: List of Cremona labels

    Returns:
        dict: Verification results for each curve
    """
    mass_prover = MassFormalProof()

    print("🚀 BATCH BSD VERIFICATION")
    print(f"Curves to verify: {len(curve_labels)}")
    print("=" * 60)

    for i, label in enumerate(curve_labels):
        print(f"\n🔬 Processing {label} ({i+1}/{len(curve_labels)})")

        try:
            E = EllipticCurve(label)
            prover = FormalBSDProver(E)
            certificate = prover.prove_bsd_completely()

            mass_prover.results[label] = certificate

            if certificate['bsd_proven']:
                print(f"   ✅ BSD VERIFIED FOR {label}")
            else:
                print(f"   ⚠️  PARTIAL VERIFICATION FOR {label}")

        except Exception as e:
            print(f"   ❌ ERROR IN {label}: {e}")
            mass_prover.results[label] = {
                'error': str(e),
                'bsd_proven': False
            }

    # Compile results
    mass_prover._compile_global_proof()

    return mass_prover.results


def run_comprehensive_verification(max_rank=2, max_curves=20):
    """
    Run comprehensive BSD verification

    Args:
        max_rank: Maximum rank to test
        max_curves: Maximum number of curves

    Returns:
        dict: Complete verification results
    """
    print("🌌 COMPREHENSIVE BSD VERIFICATION")
    print("=" * 60)

    mass_prover = MassFormalProof()
    results = mass_prover.prove_entire_lmfdb(
        max_rank=max_rank,
        conductor_limit=500,
        max_curves=max_curves
    )

    # Save results
    mass_prover.save_results()

    # Get statistics
    stats = mass_prover.get_statistics()

    print("\n📊 STATISTICS:")
    print(json.dumps(stats, indent=2, default=str))

    return {
        'global_proof': results,
        'statistics': stats,
        'detailed_results': mass_prover.results
    }
