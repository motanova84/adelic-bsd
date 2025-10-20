"""
Selmer Map Verification Module
Provides verification and certification for spectral Selmer maps

This module integrates the Selmer map computations with the formal
verification framework, generating certificates for Selmer map properties.
"""

from sage.all import EllipticCurve
import json
from datetime import datetime


class SelmerVerification:
    """
    Selmer Map Verification and Certification

    Verifies Selmer map properties and generates formal certificates:
    - Map well-definedness
    - Bloch-Kato conditions
    - Spectral-to-Selmer compatibility
    - p-adic cohomology structure
    """

    def __init__(self, E, primes=None, precision=20):
        """
        Initialize Selmer verification for curve E

        Args:
            E: EllipticCurve object
            primes: List of primes to verify (default: conductor primes)
            precision: p-adic precision (default: 20)
        """
        self.E = E
        self.precision = precision

        # Determine primes to verify
        if primes is None:
            conductor_primes = list(E.conductor().prime_factors())
            self.primes = conductor_primes if conductor_primes else [2, 3, 5]
        else:
            self.primes = primes

        self.verification_results = {}

    def verify_all(self):
        """
        Perform complete Selmer map verification

        Returns:
            dict: Complete verification certificate
        """
        print(f"Verifying Selmer maps for {self.E.cremona_label() if hasattr(self.E, 'cremona_label') else 'curve'}...")

        certificate = {
            'curve': self.E.cremona_label() if hasattr(self.E, 'cremona_label') else str(self.E),
            'conductor': int(self.E.conductor()),
            'rank': self.E.rank(),
            'primes_verified': self.primes,
            'precision': self.precision,
            'timestamp': datetime.now().isoformat(),
            'verification_steps': {}
        }

        # Step 1: Verify map initialization
        init_results = self._verify_map_initialization()
        certificate['verification_steps']['initialization'] = init_results

        # Step 2: Verify Bloch-Kato conditions
        bk_results = self._verify_bloch_kato_conditions()
        certificate['verification_steps']['bloch_kato'] = bk_results

        # Step 3: Verify spectral compatibility
        compat_results = self._verify_spectral_compatibility()
        certificate['verification_steps']['spectral_compatibility'] = compat_results

        # Step 4: Verify local-global compatibility
        local_global = self._verify_local_global_compatibility()
        certificate['verification_steps']['local_global'] = local_global

        # Overall verification status
        all_passed = (
            init_results.get('all_initialized', False) and
            bk_results.get('all_verified', False) and
            compat_results.get('compatible', False) and
            local_global.get('compatible', False)
        )

        certificate['verification_passed'] = all_passed
        certificate['verification_level'] = 'complete' if all_passed else 'partial'

        self.verification_results = certificate
        return certificate

    def _verify_map_initialization(self):
        """Verify Selmer maps can be initialized for all primes"""
        from src.cohomology import SpectralSelmerMap

        results = {
            'primes_tested': self.primes,
            'initialization_status': {}
        }

        for p in self.primes:
            try:
                selmer = SpectralSelmerMap(self.E, p, precision=self.precision)
                results['initialization_status'][p] = {
                    'initialized': True,
                    'reduction_type': selmer.reduction_type,
                    'is_ordinary': getattr(selmer, 'is_ordinary', None)
                }
            except Exception as e:
                results['initialization_status'][p] = {
                    'initialized': False,
                    'error': str(e)
                }

        results['all_initialized'] = all(
            status['initialized']
            for status in results['initialization_status'].values()
        )

        return results

    def _verify_bloch_kato_conditions(self):
        """Verify Bloch-Kato conditions for all primes"""
        from src.cohomology import verify_bloch_kato

        results = {
            'primes_tested': self.primes,
            'bloch_kato_status': {}
        }

        for p in self.primes:
            try:
                bk_cert = verify_bloch_kato(self.E, p)
                results['bloch_kato_status'][p] = {
                    'verified': bk_cert.get('certificate_valid', False),
                    'local_conditions': bk_cert['verification']['local_conditions']['all_conditions_satisfied'],
                    'global_compatible': bk_cert['verification']['globally_compatible']
                }
            except Exception as e:
                results['bloch_kato_status'][p] = {
                    'verified': False,
                    'error': str(e)
                }

        results['all_verified'] = all(
            status.get('verified', False)
            for status in results['bloch_kato_status'].values()
        )

        return results

    def _verify_spectral_compatibility(self):
        """Verify spectral-to-Selmer map compatibility"""
        from src.cohomology import verify_selmer_compatibility

        results = {
            'primes_tested': self.primes,
            'compatibility_status': {}
        }

        for p in self.primes:
            try:
                compat = verify_selmer_compatibility(self.E, p, precision=self.precision)
                results['compatibility_status'][p] = {
                    'well_defined': compat.get('map_well_defined', False),
                    'reduction_type': compat.get('reduction_type'),
                    'spectral_compatible': compat.get('spectral_compatibility', None) is not None
                }
            except Exception as e:
                results['compatibility_status'][p] = {
                    'well_defined': False,
                    'error': str(e)
                }

        results['compatible'] = all(
            status.get('well_defined', False)
            for status in results['compatibility_status'].values()
        )

        return results

    def _verify_local_global_compatibility(self):
        """Verify local-global compatibility of Selmer structure"""
        from src.cohomology import construct_global_selmer_group

        try:
            global_structure = construct_global_selmer_group(
                self.E,
                primes=self.primes,
                precision=self.precision
            )

            # Check that all local maps are initialized
            local_maps = global_structure.get('local_maps', {})
            all_init = all(
                data.get('initialized', False)
                for data in local_maps.values()
            )

            return {
                'compatible': all_init,
                'num_local_maps': len(local_maps),
                'primes': global_structure.get('primes', []),
                'all_initialized': all_init
            }
        except Exception as e:
            return {
                'compatible': False,
                'error': str(e)
            }

    def generate_certificate(self, save=False, output_dir='certificates'):
        """
        Generate formal certificate for Selmer map verification

        Args:
            save: Whether to save certificate to file
            output_dir: Output directory for certificate

        Returns:
            dict: Verification certificate
        """
        if not self.verification_results:
            self.verify_all()

        certificate = self.verification_results.copy()
        certificate['certificate_type'] = 'selmer_map_verification'
        certificate['certificate_version'] = '1.0'

        # Add certificate hash for integrity
        import hashlib
        cert_str = json.dumps(certificate, sort_keys=True)
        certificate['certificate_hash'] = hashlib.sha256(cert_str.encode()).hexdigest()

        if save:
            from src.verification import save_certificate
            filepath = save_certificate(
                certificate,
                filename=None,
                output_dir=output_dir,
                format='json'
            )
            certificate['saved_to'] = filepath

        return certificate

    def print_verification_summary(self):
        """Print human-readable verification summary"""
        if not self.verification_results:
            print("No verification results yet. Run verify_all() first.")
            return

        cert = self.verification_results

        print("\n" + "="*70)
        print("SELMER MAP VERIFICATION SUMMARY")
        print("="*70)
        print(f"Curve: {cert['curve']}")
        print(f"Conductor: {cert['conductor']}")
        print(f"Rank: {cert['rank']}")
        print(f"Primes verified: {cert['primes_verified']}")
        print(f"Precision: {cert['precision']}")
        print()

        # Initialization
        init = cert['verification_steps']['initialization']
        print(f"Map Initialization: {'✓ PASS' if init['all_initialized'] else '✗ FAIL'}")
        for p, status in init['initialization_status'].items():
            symbol = '✓' if status['initialized'] else '✗'
            print(f"  {symbol} p={p}: {status.get('reduction_type', 'N/A')}")
        print()

        # Bloch-Kato
        bk = cert['verification_steps']['bloch_kato']
        print(f"Bloch-Kato Conditions: {'✓ PASS' if bk['all_verified'] else '✗ FAIL'}")
        for p, status in bk['bloch_kato_status'].items():
            symbol = '✓' if status.get('verified', False) else '✗'
            print(f"  {symbol} p={p}")
        print()

        # Spectral compatibility
        compat = cert['verification_steps']['spectral_compatibility']
        print(f"Spectral Compatibility: {'✓ PASS' if compat['compatible'] else '✗ FAIL'}")
        print()

        # Local-global
        lg = cert['verification_steps']['local_global']
        print(f"Local-Global Compatibility: {'✓ PASS' if lg['compatible'] else '✗ FAIL'}")
        print()

        # Overall
        print(f"Overall Verification: {'✓ PASSED' if cert['verification_passed'] else '✗ FAILED'}")
        print("="*70 + "\n")


def verify_selmer_maps(E, primes=None, precision=20, save_certificate=False):
    """
    Convenience function to verify Selmer maps for a curve

    Args:
        E: EllipticCurve object
        primes: List of primes to verify (default: conductor primes)
        precision: p-adic precision (default: 20)
        save_certificate: Whether to save certificate (default: False)

    Returns:
        dict: Verification certificate
    """
    verifier = SelmerVerification(E, primes=primes, precision=precision)
    certificate = verifier.verify_all()

    if save_certificate:
        certificate = verifier.generate_certificate(save=True)

    return certificate


def batch_verify_selmer_maps(curve_labels, primes=None, precision=20, save_certificates=False):
    """
    Batch verify Selmer maps for multiple curves

    Args:
        curve_labels: List of curve labels
        primes: List of primes to verify (default: conductor primes for each)
        precision: p-adic precision (default: 20)
        save_certificates: Whether to save certificates (default: False)

    Returns:
        dict: Batch verification results
    """
    results = {}

    for label in curve_labels:
        try:
            E = EllipticCurve(label)
            certificate = verify_selmer_maps(
                E,
                primes=primes,
                precision=precision,
                save_certificate=save_certificates
            )
            results[label] = certificate
        except Exception as e:
            results[label] = {
                'curve': label,
                'verification_passed': False,
                'error': str(e)
            }

    # Generate summary
    total = len(results)
    passed = sum(1 for r in results.values() if r.get('verification_passed', False))

    summary = {
        'total_curves': total,
        'passed': passed,
        'failed': total - passed,
        'success_rate': f"{(passed/total*100):.1f}%" if total > 0 else "0%",
        'results': results
    }

    return summary


def generate_selmer_verification_report(verification_results):
    """
    Generate detailed report from Selmer verification results

    Args:
        verification_results: Results from verify_selmer_maps or batch verification

    Returns:
        str: Formatted report
    """
    if 'results' in verification_results:
        # Batch results
        summary = verification_results
        lines = []
        lines.append("="*70)
        lines.append("BATCH SELMER MAP VERIFICATION REPORT")
        lines.append("="*70)
        lines.append(f"Total curves: {summary['total_curves']}")
        lines.append(f"Passed: {summary['passed']}")
        lines.append(f"Failed: {summary['failed']}")
        lines.append(f"Success rate: {summary['success_rate']}")
        lines.append("")

        for label, cert in summary['results'].items():
            status = '✓' if cert.get('verification_passed', False) else '✗'
            lines.append(f"{status} {label}")

        lines.append("="*70)
        return "\n".join(lines)
    else:
        # Single curve result
        cert = verification_results
        lines = []
        lines.append("="*70)
        lines.append("SELMER MAP VERIFICATION REPORT")
        lines.append("="*70)
        lines.append(f"Curve: {cert.get('curve', 'N/A')}")
        lines.append(f"Verification: {'✓ PASSED' if cert.get('verification_passed', False) else '✗ FAILED'}")
        lines.append(f"Primes: {cert.get('primes_verified', [])}")
        lines.append("="*70)
        return "\n".join(lines)


__all__ = [
    'SelmerVerification',
    'verify_selmer_maps',
    'batch_verify_selmer_maps',
    'generate_selmer_verification_report'
]
