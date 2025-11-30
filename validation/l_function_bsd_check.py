#!/usr/bin/env python3
r"""
L-Function and BSD Partial Validation
======================================

PASO 4 — Cálculo numérico de la función L y verificación BSD parcial

This script computes the L-function L(E,s) for an elliptic curve E/ℚ
and experimentally verifies the partial validity of the Birch-Swinnerton-Dyer
Conjecture in order of vanishing (analytic rank), with reproducible numerical
validation.

Key results computed:
- L(E,1): Value of the L-function at s=1
- Analytic rank: Order of vanishing of L(E,s) at s=1
- Algebraic rank: Rank of the Mordell-Weil group E(Q)
- BSD Consistency: Comparison of analytic and algebraic ranks

The BSD conjecture predicts that:
    rank E(Q) = ord_{s=1} L(E,s)

USAGE::

    sage -python l_function_bsd_check.py

Or in a SageMath session::

    sage: %run l_function_bsd_check.py

AUTHORS:

- Jose Manuel Mota Burruezo (2025-01)

REFERENCES:

- Birch, B. J., Swinnerton-Dyer, H. P. F., "Notes on elliptic curves. II"
  J. reine angew. Math. 218 (1965), 79-108.

- Dokchitser, Tim. "Computing special values of motivic L-functions."
  Experimental mathematics 13.2 (2004): 137-149.
"""

import sys
import os
from datetime import datetime

# Global flag for SageMath availability
SAGE_AVAILABLE = False

try:
    from sage.all import EllipticCurve
    SAGE_AVAILABLE = True
except ImportError:
    pass


def compute_l_function_bsd_check(coefficients=None, curve_label=None, output_file=None):
    """
    Compute L-function values and verify BSD partial conjecture.

    This function:
    1. Initializes the elliptic curve from coefficients or label
    2. Constructs the L-function L(E,s)
    3. Evaluates L(E,1)
    4. Calculates order of vanishing (analytic rank)
    5. Compares with algebraic rank
    6. Outputs BSD consistency verification

    INPUT:

    - ``coefficients`` -- tuple (a4, a6) for curve y^2 = x^3 + a4*x + a6,
      or None to use default curve
    - ``curve_label`` -- string label like '11a1' for LMFDB curve,
      overrides coefficients if provided
    - ``output_file`` -- path to save output, or None for stdout only

    OUTPUT:

    - dict: Dictionary containing all computed values and verification results

    EXAMPLES::

        sage: from validation.l_function_bsd_check import compute_l_function_bsd_check
        sage: result = compute_l_function_bsd_check(curve_label='11a1')
        sage: result['bsd_valid']
        True
        sage: result['analytic_rank'] == result['algebraic_rank']
        True

    TESTS::

        sage: result = compute_l_function_bsd_check(curve_label='37a1')
        sage: 'L_at_1' in result
        True
    """
    if not SAGE_AVAILABLE:
        raise ImportError(
            "SageMath is required for L-function computation. "
            "Run this script with 'sage -python l_function_bsd_check.py'"
        )

    # Default coefficients as specified in the problem statement
    default_a4 = -7423918274321
    default_a6 = 139820174982374921

    output_lines = []

    def log(msg):
        """Log message to output and optionally to file."""
        output_lines.append(msg)
        print(msg)

    log("=" * 70)
    log("PASO 4: L-Function BSD Partial Validation")
    log("=" * 70)
    log(f"Timestamp: {datetime.now().isoformat()}")
    log("")

    # Step 1: Initialize curve
    log("-" * 50)
    log("STEP 1: Initialize Elliptic Curve")
    log("-" * 50)

    if curve_label is not None:
        E = EllipticCurve(curve_label)
        log(f"Curve label: {curve_label}")
    elif coefficients is not None:
        a4, a6 = coefficients
        E = EllipticCurve([a4, a6])
        log(f"Curve coefficients: a4 = {a4}, a6 = {a6}")
    else:
        E = EllipticCurve([default_a4, default_a6])
        log(f"Using default curve: y^2 = x^3 + ({default_a4})*x + ({default_a6})")

    log(f"Curve E: {E}")
    conductor = E.conductor()
    log(f"Conductor N: {conductor}")
    log("")

    # Step 2: Construct L-function
    log("-" * 50)
    log("STEP 2: Construct L-function L(E, s)")
    log("-" * 50)

    L = E.lseries()
    log("L-series constructed successfully using dokchitser algorithm")
    log("")

    # Step 3: Evaluate L(E, 1)
    log("-" * 50)
    log("STEP 3: Evaluate L(E, 1)")
    log("-" * 50)

    L_at_1 = L(1)
    log(f"L(E, 1) ≈ {L_at_1}")
    log("")

    # Step 4: Calculate analytic rank (order of vanishing)
    log("-" * 50)
    log("STEP 4: Calculate Analytic Rank (Order of Vanishing at s = 1)")
    log("-" * 50)

    analytic_rank = E.analytic_rank()
    log(f"Orden de anulación en s = 1 (rango analítico): {analytic_rank}")
    log("")

    # Step 5: Compute algebraic rank
    log("-" * 50)
    log("STEP 5: Compute Algebraic Rank")
    log("-" * 50)

    algebraic_rank = E.rank()
    log(f"Rango algebraico: {algebraic_rank}")
    log("")

    # Step 6: BSD Consistency Verification
    log("-" * 50)
    log("STEP 6: BSD Partial Verification (Rank Consistency)")
    log("-" * 50)

    bsd_valid = (analytic_rank == algebraic_rank)
    log(f"Analytic rank: {analytic_rank}")
    log(f"Algebraic rank: {algebraic_rank}")
    log(f"¿BSD valida en rango?: {bsd_valid}")
    log("")

    # Summary
    log("=" * 70)
    log("SUMMARY: BSD Partial Validation Results")
    log("=" * 70)

    result = {
        'curve': str(E),
        'conductor': int(conductor),
        'L_at_1': float(L_at_1),
        'analytic_rank': int(analytic_rank),
        'algebraic_rank': int(algebraic_rank),
        'bsd_valid': bsd_valid,
        'timestamp': datetime.now().isoformat()
    }

    if bsd_valid:
        log("✅ BSD conjecture VALIDATED for this curve (partial verification)")
        log(f"   - L(E,1) = {L_at_1}")
        log(f"   - ord_{{s=1}} L(E,s) = {analytic_rank}")
        log(f"   - rank E(Q) = {algebraic_rank}")
        log("   - Consistency: analytic_rank == algebraic_rank ✓")
    else:
        log("❌ BSD conjecture INCONSISTENCY detected")
        log(f"   - Analytic rank: {analytic_rank}")
        log(f"   - Algebraic rank: {algebraic_rank}")
        log("   - This may indicate computational issues or requires further investigation")

    log("")
    log("=" * 70)

    # Save to file if specified
    if output_file:
        output_dir = os.path.dirname(output_file)
        if output_dir and not os.path.exists(output_dir):
            os.makedirs(output_dir)
        with open(output_file, 'w') as f:
            f.write('\n'.join(output_lines))
        log(f"Output saved to: {output_file}")

    return result


def run_standard_verification():
    """
    Run the standard BSD verification as specified in the problem statement.

    This uses the curve E / ℚ defined by:
        y^2 = x^3 - 7423918274321*x + 139820174982374921

    OUTPUT:

    - dict: Verification results

    EXAMPLES::

        sage: from validation.l_function_bsd_check import run_standard_verification
        sage: result = run_standard_verification()
        sage: 'bsd_valid' in result
        True
    """
    # Default output path
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_root = os.path.dirname(script_dir)
    output_file = os.path.join(project_root, 'outputs', 'bsd_partial_validation.txt')

    return compute_l_function_bsd_check(output_file=output_file)


def run_test_curves():
    """
    Run BSD verification on a set of test curves from LMFDB.

    Uses well-known curves with known properties for validation.

    OUTPUT:

    - list: List of verification results for each curve

    EXAMPLES::

        sage: from validation.l_function_bsd_check import run_test_curves
        sage: results = run_test_curves()
        sage: len(results) > 0
        True
    """
    test_labels = [
        '11a1',   # Rank 0, conductor 11
        '37a1',   # Rank 1, conductor 37
        '389a1',  # Rank 2, conductor 389
    ]

    results = []
    for label in test_labels:
        print(f"\n{'='*70}")
        print(f"Testing curve: {label}")
        print(f"{'='*70}\n")
        try:
            result = compute_l_function_bsd_check(curve_label=label)
            results.append(result)
        except Exception as e:
            print(f"Error processing {label}: {e}")
            results.append({'curve_label': label, 'error': str(e)})

    return results


if __name__ == '__main__':
    if not SAGE_AVAILABLE:
        print("ERROR: SageMath is required for this script.")
        print("Please run with: sage -python l_function_bsd_check.py")
        print("Or use: sage l_function_bsd_check.sage")
        sys.exit(1)

    result = run_standard_verification()
    print(f"\nFinal result: BSD valid = {result['bsd_valid']}")
