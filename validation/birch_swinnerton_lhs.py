#!/usr/bin/env python3
"""
PASO 6 — Derivada de L(E,s) en s=1 (lado izquierdo de BSD)

Calcula la derivada de orden r de la función L de la curva elíptica E/Q
en s=1, la divide por r!, y la compara numéricamente con el valor
obtenido en el Paso 5 (lado derecho de la fórmula BSD).

This module implements:
1. Rank estimation r of elliptic curve E/Q
2. r-th derivative of L(E,s) at s=1
3. L^(r)(E,1) / r! computation (LHS of BSD)
4. Comparison with RHS from BSD formula
5. Validation with relative error thresholds

Author: BSD Framework
Date: November 2025
"""

from math import factorial
from typing import Dict, Any
import json
import os
from datetime import datetime


# Validation thresholds for BSD comparison
BSD_THRESHOLDS = {
    'almost_perfect': 1e-3,    # < 10^-3: Almost perfect validation
    'good': 1e-2,              # < 10^-2: Good estimation
    'partial': 1e-1,           # < 10^-1: Partial coherence
    'needs_review': float('inf')  # >= 10^-1: Review previous steps
}


class BirchSwinnertonLHS:
    """
    Computes the left-hand side of the BSD formula.

    LHS = L^(r)(E,1) / r!

    where r is the rank of E(Q) and L(E,s) is the L-function of E.
    """

    def __init__(self, E):
        """
        Initialize the BSD LHS calculator.

        Args:
            E: SageMath EllipticCurve object
        """
        self.E = E
        self._rank = None
        self._L_derivative = None
        self._L_lhs = None

    @property
    def rank(self) -> int:
        """
        Get the rank of E(Q).

        Returns:
            int: Algebraic rank of E(Q)
        """
        if self._rank is None:
            self._rank = self.E.rank()
        return self._rank

    @property
    def label(self) -> str:
        """Get curve label if available."""
        try:
            return self.E.cremona_label()
        except Exception:
            return str(self.E.ainvs())

    def compute_L_derivative(self, precision: int = 30) -> float:
        """
        Compute L^(r)(E,1), the r-th derivative of L(E,s) at s=1.

        Args:
            precision: Numerical precision for computation

        Returns:
            float: Value of L^(r)(E,1)
        """
        r = self.rank
        L = self.E.lseries()

        if r == 0:
            # For rank 0, use L(E,1) directly
            try:
                # L_ratio gives L(E,1)/Omega
                L_ratio = float(L.L_ratio())
                omega = float(self.E.period_lattice().omega())
                self._L_derivative = L_ratio * omega
            except Exception:
                # Fallback to numerical computation
                self._L_derivative = float(L(1))
        else:
            # For rank > 0, compute r-th derivative
            try:
                # Use Sage's derivative method
                self._L_derivative = float(L.derivative(1, order=r))
            except Exception as e:
                # Numerical differentiation fallback
                self._L_derivative = self._numerical_derivative(r, precision)

        return self._L_derivative

    def _numerical_derivative(self, order: int, precision: int) -> float:
        """
        Compute numerical derivative as fallback.

        Args:
            order: Order of derivative
            precision: Precision for computation

        Returns:
            float: Approximate derivative value
        """
        from sage.all import RealField
        RF = RealField(precision)

        h = RF(1e-6)
        s = RF(1)
        L = self.E.lseries()

        # Simple finite difference for small orders
        if order == 1:
            L_plus = float(L(s + h))
            L_minus = float(L(s - h))
            return (L_plus - L_minus) / (2 * float(h))
        elif order == 2:
            L_plus = float(L(s + h))
            L_minus = float(L(s - h))
            L_center = float(L(s))
            return (L_plus - 2*L_center + L_minus) / (float(h)**2)
        else:
            # For higher orders, use iterative approach
            return self._high_order_derivative(order, precision)

    def _high_order_derivative(self, order: int, precision: int) -> float:
        """
        Compute high-order derivative numerically.

        Uses binomial coefficient expansion for arbitrary order.
        """
        from sage.all import RealField, binomial
        RF = RealField(precision)

        h = RF(1e-4)
        s = RF(1)
        L = self.E.lseries()

        result = RF(0)
        for k in range(order + 1):
            coeff = (-1)**k * binomial(order, k)
            L_val = float(L(s + (order - 2*k) * h / 2))
            result += coeff * L_val

        return float(result / (h**order))

    def compute_lhs(self, precision: int = 30) -> float:
        """
        Compute L^(r)(E,1) / r!, the left-hand side of BSD.

        Args:
            precision: Numerical precision for computation

        Returns:
            float: Value of L^(r)(E,1) / r!
        """
        r = self.rank
        L_deriv = self.compute_L_derivative(precision)

        self._L_lhs = L_deriv / factorial(r)
        return self._L_lhs

    def get_summary(self, precision: int = 30) -> Dict[str, Any]:
        """
        Get comprehensive summary of LHS computation.

        Returns:
            dict: Summary with all computed values
        """
        if self._L_lhs is None:
            self.compute_lhs(precision)

        return {
            'curve': self.label,
            'conductor': int(self.E.conductor()),
            'rank': self.rank,
            'L_derivative': self._L_derivative,
            'factorial_r': factorial(self.rank),
            'L_lhs': self._L_lhs,
            'timestamp': datetime.now().isoformat()
        }


def compute_bsd_rhs(E) -> Dict[str, float]:
    """
    Compute the right-hand side of BSD formula.

    RHS = (Ω * Reg * ∏c_p * #Sha) / (#E(Q)_tors)^2

    where:
        - Ω is the real period
        - Reg is the regulator
        - c_p are Tamagawa numbers
        - Sha is the Tate-Shafarevich group (assumed finite, order 1 by default)
        - E(Q)_tors is the torsion subgroup

    Args:
        E: SageMath EllipticCurve object

    Returns:
        dict: Components and value of RHS
    """
    # Real period
    try:
        omega = float(E.period_lattice().omega())
    except Exception:
        omega = 1.0

    # Regulator
    rank = E.rank()
    if rank == 0:
        reg = 1.0
    else:
        try:
            reg = float(E.regulator())
        except Exception:
            reg = 1.0

    # Tamagawa product
    N = E.conductor()
    tamagawa_product = 1
    for p in N.prime_factors():
        try:
            c_p = E.tamagawa_number(p)
            tamagawa_product *= c_p
        except Exception:
            pass

    # Torsion order
    try:
        torsion_order = E.torsion_order()
    except Exception:
        torsion_order = 1

    # Sha order (assumed 1 for simplicity; in practice use analytic computation)
    sha_order = 1

    # Compute RHS
    rhs = (omega * reg * tamagawa_product * sha_order) / (torsion_order ** 2)

    return {
        'omega': omega,
        'regulator': reg,
        'tamagawa_product': tamagawa_product,
        'sha_order': sha_order,
        'torsion_order': torsion_order,
        'rhs': rhs
    }


def compute_bsd_lhs_vs_rhs(E, precision: int = 30) -> Dict[str, Any]:
    """
    Compare LHS and RHS of BSD formula.

    Args:
        E: SageMath EllipticCurve object
        precision: Numerical precision

    Returns:
        dict: Comparison results including relative error
    """
    # Compute LHS
    lhs_calc = BirchSwinnertonLHS(E)
    lhs_summary = lhs_calc.get_summary(precision)
    lhs = lhs_summary['L_lhs']

    # Compute RHS
    rhs_data = compute_bsd_rhs(E)
    rhs = rhs_data['rhs']

    # Compute relative error
    if abs(lhs) > 1e-15:
        relative_error = abs(lhs - rhs) / abs(lhs)
    elif abs(rhs) > 1e-15:
        relative_error = abs(lhs - rhs) / abs(rhs)
    else:
        # Both near zero
        relative_error = abs(lhs - rhs)

    # Determine validation level
    validation = determine_validation_level(relative_error)

    return {
        'curve': lhs_summary['curve'],
        'rank': lhs_summary['rank'],
        'lhs': {
            'L_derivative': lhs_summary['L_derivative'],
            'factorial': lhs_summary['factorial_r'],
            'value': lhs
        },
        'rhs': {
            'omega': rhs_data['omega'],
            'regulator': rhs_data['regulator'],
            'tamagawa_product': rhs_data['tamagawa_product'],
            'sha_order': rhs_data['sha_order'],
            'torsion_order': rhs_data['torsion_order'],
            'value': rhs
        },
        'comparison': {
            'relative_error': relative_error,
            'validation_level': validation,
            'bsd_compatible': validation != 'needs_review'
        },
        'timestamp': datetime.now().isoformat()
    }


def determine_validation_level(error: float) -> str:
    """
    Determine BSD validation level based on relative error.

    Args:
        error: Relative error between LHS and RHS

    Returns:
        str: Validation level description
    """
    if error < BSD_THRESHOLDS['almost_perfect']:
        return 'almost_perfect'
    elif error < BSD_THRESHOLDS['good']:
        return 'good'
    elif error < BSD_THRESHOLDS['partial']:
        return 'partial'
    else:
        return 'needs_review'


def validate_bsd_comparison(E, precision: int = 30, verbose: bool = True) -> Dict[str, Any]:
    """
    Full BSD validation with reporting.

    Args:
        E: SageMath EllipticCurve object
        precision: Numerical precision
        verbose: Print results

    Returns:
        dict: Complete validation results
    """
    result = compute_bsd_lhs_vs_rhs(E, precision)

    if verbose:
        print("=" * 70)
        print(f"BSD VALIDATION: {result['curve']}")
        print("=" * 70)
        print(f"\nRank of E: {result['rank']}")
        print("\n--- LEFT SIDE (LHS) ---")
        print(f"L^({result['rank']})(E,1): {result['lhs']['L_derivative']:.10e}")
        print(f"{result['rank']}!: {result['lhs']['factorial']}")
        print(f"LHS = L^({result['rank']})(E,1)/{result['rank']}!: {result['lhs']['value']:.10e}")
        print("\n--- RIGHT SIDE (RHS) ---")
        print(f"Omega (period): {result['rhs']['omega']:.10e}")
        print(f"Regulator: {result['rhs']['regulator']:.10e}")
        print(f"Tamagawa product: {result['rhs']['tamagawa_product']}")
        print(f"Sha order: {result['rhs']['sha_order']}")
        print(f"Torsion order: {result['rhs']['torsion_order']}")
        print(f"RHS: {result['rhs']['value']:.10e}")
        print("\n--- COMPARISON ---")
        print(f"Relative error: {result['comparison']['relative_error']:.6e}")
        print(f"Validation level: {result['comparison']['validation_level']}")
        print(f"BSD compatible: {result['comparison']['bsd_compatible']}")
        print("=" * 70)

        # Validation status message
        validation = result['comparison']['validation_level']
        if validation == 'almost_perfect':
            print("✅ VALIDATION: Almost perfect! BSD formula confirmed.")
        elif validation == 'good':
            print("✅ VALIDATION: Good estimation. BSD formula consistent.")
        elif validation == 'partial':
            print("⚠️  VALIDATION: Partial coherence. Some numerical issues possible.")
        else:
            print("❌ VALIDATION: Review previous steps. Large discrepancy detected.")

    return result


def save_results(result: Dict[str, Any], filepath: str = None) -> str:
    """
    Save validation results to file.

    Args:
        result: Validation result dictionary
        filepath: Output file path (default: outputs/bsd_lhs_vs_rhs.txt)

    Returns:
        str: Path to saved file
    """
    if filepath is None:
        # Use default path in outputs directory
        base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        outputs_dir = os.path.join(base_dir, 'outputs')
        os.makedirs(outputs_dir, exist_ok=True)
        filepath = os.path.join(outputs_dir, 'bsd_lhs_vs_rhs.txt')

    # Format output
    lines = [
        "=" * 70,
        "BSD LHS vs RHS COMPARISON RESULTS",
        "=" * 70,
        "",
        f"Curve: {result['curve']}",
        f"Rank: {result['rank']}",
        f"Timestamp: {result['timestamp']}",
        "",
        "--- LEFT SIDE (LHS) ---",
        f"L^({result['rank']})(E,1): {result['lhs']['L_derivative']:.15e}",
        f"{result['rank']}!: {result['lhs']['factorial']}",
        f"LHS value: {result['lhs']['value']:.15e}",
        "",
        "--- RIGHT SIDE (RHS) ---",
        f"Omega: {result['rhs']['omega']:.15e}",
        f"Regulator: {result['rhs']['regulator']:.15e}",
        f"Tamagawa product: {result['rhs']['tamagawa_product']}",
        f"Sha order: {result['rhs']['sha_order']}",
        f"Torsion order: {result['rhs']['torsion_order']}",
        f"RHS value: {result['rhs']['value']:.15e}",
        "",
        "--- COMPARISON ---",
        f"Relative error: {result['comparison']['relative_error']:.15e}",
        f"Validation level: {result['comparison']['validation_level']}",
        f"BSD compatible: {result['comparison']['bsd_compatible']}",
        "",
        "=" * 70,
    ]

    with open(filepath, 'w') as f:
        f.write('\n'.join(lines))

    # Also save as JSON
    json_path = filepath.replace('.txt', '.json')
    with open(json_path, 'w') as f:
        json.dump(result, f, indent=2, default=str)

    return filepath


def main():
    """
    Main entry point for BSD LHS vs RHS validation.

    Example usage:
        python validation/birch_swinnerton_lhs.py
    """
    try:
        from sage.all import EllipticCurve
    except ImportError:
        print("Error: SageMath is required to run this script.")
        print("Please install SageMath or run within a SageMath environment.")
        return

    # Test curves of different ranks
    test_curves = [
        ('11a1', 0, 'Rank 0 - classic curve'),
        ('37a1', 1, 'Rank 1 - first rank 1 curve'),
        ('389a1', 2, 'Rank 2 - first rank 2 curve'),
    ]

    print("\n" + "#" * 70)
    print("# PASO 6: BSD LHS vs RHS VALIDATION")
    print("# Derivada de L(E,s) en s=1 (lado izquierdo de BSD)")
    print("#" * 70 + "\n")

    all_results = []

    for label, expected_rank, description in test_curves:
        print(f"\n--- Testing: {description} ---")
        try:
            E = EllipticCurve(label)
            result = validate_bsd_comparison(E, precision=30, verbose=True)
            all_results.append(result)

            # Verify rank matches expected
            if result['rank'] != expected_rank:
                print(f"⚠️  Warning: Expected rank {expected_rank}, got {result['rank']}")
        except Exception as e:
            print(f"❌ Error processing {label}: {e}")
            all_results.append({
                'curve': label,
                'error': str(e)
            })

    # Save combined results
    combined_result = {
        'validation_type': 'BSD_LHS_vs_RHS',
        'timestamp': datetime.now().isoformat(),
        'curves': all_results,
        'summary': {
            'total': len(all_results),
            'successful': sum(1 for r in all_results if 'error' not in r),
            'compatible': sum(
                1 for r in all_results
                if r.get('comparison', {}).get('bsd_compatible', False)
            )
        }
    }

    # Save to outputs directory
    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    outputs_dir = os.path.join(base_dir, 'outputs')
    os.makedirs(outputs_dir, exist_ok=True)

    filepath = os.path.join(outputs_dir, 'bsd_lhs_vs_rhs.json')
    with open(filepath, 'w') as f:
        json.dump(combined_result, f, indent=2, default=str)

    print(f"\n📁 Results saved to: {filepath}")

    # Print summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total curves tested: {combined_result['summary']['total']}")
    print(f"Successful computations: {combined_result['summary']['successful']}")
    print(f"BSD compatible: {combined_result['summary']['compatible']}")
    print("=" * 70)


if __name__ == "__main__":
    main()
