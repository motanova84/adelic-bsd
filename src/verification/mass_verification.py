"""
Mass Verification System
Wrapper providing unified interface for mass BSD verification

This module re-exports MassFormalProof with a simpler name and
provides convenience functions for batch verification.
"""

from .mass_formal_proof import MassFormalProof
from .formal_bsd_prover import FormalBSDProver, generate_formal_certificate


# Re-export main class
MassVerification = MassFormalProof


def batch_verify_bsd(curve_labels, max_curves=None, save_certificates=False):
    """
    Batch verify BSD for multiple curves

    Args:
        curve_labels: List of curve labels or conductor range
        max_curves: Maximum number of curves to process (default: None)
        save_certificates: Whether to save certificates (default: False)

    Returns:
        dict: Batch verification results
    """
    verifier = MassVerification(
        curve_labels=curve_labels,
        max_curves=max_curves
    )

    results = verifier.batch_prove_bsd(save_certificates=save_certificates)

    return results


def verify_single_curve(curve_label, proof_level="full", save_certificate=False):
    """
    Verify BSD for a single curve

    Args:
        curve_label: Curve label (e.g., '11a1')
        proof_level: Level of proof detail (default: 'full')
        save_certificate: Whether to save certificate (default: False)

    Returns:
        dict: Verification certificate
    """
    from sage.all import EllipticCurve

    try:
        E = EllipticCurve(curve_label)
        certificate = generate_formal_certificate(
            E,
            save_to_file=save_certificate
        )
        return certificate
    except Exception as e:
        return {
            'curve': curve_label,
            'error': str(e),
            'bsd_proven': False
        }


def generate_verification_report(results):
    """
    Generate summary report from verification results

    Args:
        results: Results from batch verification

    Returns:
        dict: Summary report
    """
    total = len(results)
    successful = sum(1 for r in results.values() if r.get('bsd_proven', False))
    failed = total - successful

    success_rate = (successful / total * 100) if total > 0 else 0

    return {
        'total_curves': total,
        'successful': successful,
        'failed': failed,
        'success_rate': f"{success_rate:.1f}%",
        'curve_labels': list(results.keys())
    }


def verify_conductor_range(min_conductor, max_conductor, save_certificates=False):
    """
    Verify all curves in a conductor range

    Args:
        min_conductor: Minimum conductor
        max_conductor: Maximum conductor
        save_certificates: Whether to save certificates

    Returns:
        dict: Verification results
    """
    from sage.all import cremona_curves

    # Get all curves in range
    curve_labels = []
    for N in range(min_conductor, max_conductor + 1):
        try:
            for label in cremona_curves(N):
                curve_labels.append(label)
        except:
            continue

    # Batch verify
    results = batch_verify_bsd(
        curve_labels,
        save_certificates=save_certificates
    )

    # Generate report
    report = generate_verification_report(results)
    report['conductor_range'] = [min_conductor, max_conductor]

    return {
        'results': results,
        'report': report
    }


def verify_rank_class(rank, num_curves=10, save_certificates=False):
    """
    Verify curves of specific rank

    Args:
        rank: Target rank
        num_curves: Number of curves to verify
        save_certificates: Whether to save certificates

    Returns:
        dict: Verification results
    """
    from sage.all import EllipticCurve, cremona_curves

    # Find curves with target rank
    curve_labels = []
    conductor = 11

    while len(curve_labels) < num_curves and conductor < 1000:
        try:
            for label in cremona_curves(conductor):
                if len(curve_labels) >= num_curves:
                    break

                try:
                    E = EllipticCurve(label)
                    if E.rank() == rank:
                        curve_labels.append(label)
                except:
                    continue
        except:
            pass

        conductor += 1

    # Verify found curves
    results = batch_verify_bsd(
        curve_labels,
        save_certificates=save_certificates
    )

    report = generate_verification_report(results)
    report['target_rank'] = rank

    return {
        'results': results,
        'report': report
    }


__all__ = [
    'MassVerification',
    'MassFormalProof',
    'batch_verify_bsd',
    'verify_single_curve',
    'generate_verification_report',
    'verify_conductor_range',
    'verify_rank_class'
]
