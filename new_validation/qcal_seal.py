"""
QCAL Seal Module for BSD Experimental Validation
=================================================

Implements QCAL (Quantum Certified Adelic Lattice) seal validation
with cryptographic hashes for curve verification.

Each curve is marked with:
- Hash of j-invariant
- Timestamp
- Relative error
- Status (✓ experimental match or × mismatch)

Author: BSD Spectral Framework
Date: November 2025
"""

import hashlib
import json
from datetime import datetime


# QCAL frequency constant (from the framework)
QCAL_FREQUENCY = 141.7001  # Hz


def compute_j_invariant_hash(j_invariant):
    """
    Compute SHA-256 hash of j-invariant.

    Args:
        j_invariant: j-invariant value (any type convertible to string)

    Returns:
        str: Hexadecimal hash string
    """
    j_str = str(j_invariant).encode('utf-8')
    return hashlib.sha256(j_str).hexdigest()


def compute_curve_hash(curve_data):
    """
    Compute comprehensive hash of curve data.

    Args:
        curve_data: Dictionary with curve information

    Returns:
        str: Hexadecimal hash string
    """
    # Create canonical representation
    canonical = json.dumps(curve_data, sort_keys=True, default=str)
    return hashlib.sha256(canonical.encode('utf-8')).hexdigest()


def generate_qcal_seal(experiment_results):
    """
    Generate QCAL seal for BSD experiment results.

    Args:
        experiment_results: Results from BSDExperiment.compute_bsd_comparison()

    Returns:
        dict: QCAL seal data
    """
    terms = experiment_results.get('terms', {})

    # Extract key data
    j_invariant = terms.get('j_invariant', 'unknown')
    conductor = terms.get('conductor', 0)
    rank = terms.get('rank', 0)

    # Compute hashes
    j_hash = compute_j_invariant_hash(j_invariant)

    # Get error and status
    relative_error = experiment_results.get('relative_error')
    sha_estimate = experiment_results.get('sha_estimate')

    if relative_error is not None:
        error_percent = relative_error * 100
        # Consider match if error < 1%
        status = '✓ experimental match' if relative_error < 0.01 else '× mismatch'
    else:
        error_percent = None
        status = '? incomplete'

    # Generate timestamp
    timestamp = datetime.now().isoformat()

    # Create seal
    seal = {
        'version': '1.0',
        'type': 'BSD_EXPERIMENTAL_QCAL_SEAL',
        'timestamp': timestamp,
        'qcal_frequency_hz': QCAL_FREQUENCY,
        'curve_data': {
            'conductor': conductor,
            'rank': rank,
            'j_invariant_hash': j_hash,
        },
        'validation': {
            'sha_estimate': sha_estimate,
            'relative_error_percent': error_percent,
            'status': status,
        },
        'verification': {
            'method': 'BSD_spectral_comparison',
            'framework': 'Adelic-BSD',
        }
    }

    # Compute seal signature (hash of seal content)
    seal_content = json.dumps(
        {k: v for k, v in seal.items() if k != 'signature'},
        sort_keys=True, default=str)
    seal['signature'] = hashlib.sha256(seal_content.encode('utf-8')).hexdigest()[:32]

    return seal


def verify_qcal_seal(seal):
    """
    Verify integrity of a QCAL seal.

    Args:
        seal: QCAL seal dictionary

    Returns:
        dict: Verification result
    """
    try:
        # Recompute signature
        seal_copy = dict(seal)
        original_signature = seal_copy.pop('signature', None)

        seal_content = json.dumps(seal_copy, sort_keys=True, default=str)
        computed_signature = hashlib.sha256(seal_content.encode('utf-8')).hexdigest()[:32]

        signature_valid = (original_signature == computed_signature)

        return {
            'valid': signature_valid,
            'signature_match': signature_valid,
            'timestamp': seal.get('timestamp'),
            'status': seal.get('validation', {}).get('status'),
            'error_percent': seal.get('validation', {}).get('relative_error_percent'),
        }

    except Exception as e:
        return {
            'valid': False,
            'error': str(e),
        }


def generate_seal_certificate(seal, format='text'):
    """
    Generate human-readable certificate from QCAL seal.

    Args:
        seal: QCAL seal dictionary
        format: 'text' or 'latex'

    Returns:
        str: Formatted certificate
    """
    if format == 'text':
        lines = [
            "=" * 60,
            "QCAL SEAL CERTIFICATE",
            "=" * 60,
            f"Version: {seal.get('version', 'N/A')}",
            f"Timestamp: {seal.get('timestamp', 'N/A')}",
            f"QCAL Frequency: {seal.get('qcal_frequency_hz', 'N/A')} Hz",
            "",
            "CURVE:",
            f"  Conductor: {seal.get('curve_data', {}).get('conductor', 'N/A')}",
            f"  Rank: {seal.get('curve_data', {}).get('rank', 'N/A')}",
            f"  j-invariant hash: {seal.get('curve_data', {}).get('j_invariant_hash', 'N/A')[:16]}...",
            "",
            "VALIDATION:",
            f"  Sha estimate: {seal.get('validation', {}).get('sha_estimate', 'N/A')}",
            f"  Error: {seal.get('validation', {}).get('relative_error_percent', 'N/A')}%",
            f"  Status: {seal.get('validation', {}).get('status', 'N/A')}",
            "",
            f"Signature: {seal.get('signature', 'N/A')}",
            "=" * 60,
        ]
        return "\n".join(lines)

    elif format == 'latex':
        lines = [
            "\\begin{table}[h]",
            "\\centering",
            "\\begin{tabular}{ll}",
            "\\hline",
            "\\textbf{Property} & \\textbf{Value} \\\\",
            "\\hline",
            f"Timestamp & {seal.get('timestamp', 'N/A')} \\\\",
            f"Conductor & {seal.get('curve_data', {}).get('conductor', 'N/A')} \\\\",
            f"Rank & {seal.get('curve_data', {}).get('rank', 'N/A')} \\\\",
            f"$|\\Sha|$ estimate & {seal.get('validation', {}).get('sha_estimate', 'N/A')} \\\\",
            f"Error & {seal.get('validation', {}).get('relative_error_percent', 'N/A')}\\% \\\\",
            f"Status & {seal.get('validation', {}).get('status', 'N/A')} \\\\",
            "\\hline",
            "\\end{tabular}",
            "\\caption{QCAL BSD Validation Seal}",
            "\\end{table}",
        ]
        return "\n".join(lines)

    return str(seal)
