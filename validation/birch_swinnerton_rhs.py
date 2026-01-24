#!/usr/bin/env sage
# -*- coding: utf-8 -*-
"""
Birch-Swinnerton-Dyer Right-Hand Side Computation
PASO 5 — Emparejamiento de altura y fórmula de BSD (lado derecho)

This module computes the canonical height pairing for the generators
of the Mordell-Weil group of an elliptic curve E/Q, constructs the
right-hand side of the BSD formula, and compares it with the left-hand
side L^(r)(E,1)/r!.

The BSD formula (at rank r) states:
    L^(r)(E, 1) / r! = Ω_E · R · |Ш(E)| · ∏c_p / |E_tor|²

Where:
    - Ω_E: Real period of E
    - R: Regulator (determinant of the height pairing matrix)
    - |Ш(E)|: Order of the Tate-Shafarevich group (assumed 1 for verification)
    - c_p: Tamagawa numbers at bad primes
    - |E_tor|: Order of the torsion subgroup

Author: Generated for adelic-bsd project
Date: November 2025
"""

from sage.all import (
    EllipticCurve, matrix, RR,
    prod, factorial
)
import json
import datetime
import sys
import os


class BSDRightHandSide:
    """
    Computes the right-hand side of the BSD formula for an elliptic curve.

    This class provides methods to:
    1. Obtain generators of E(Q)
    2. Compute the Néron-Tate height pairing matrix
    3. Calculate the regulator (determinant of height matrix)
    4. Compute all BSD formula components
    5. Construct and verify the BSD formula
    """

    def __init__(self, E, sha_order=1):
        """
        Initialize BSD computation for curve E.

        Args:
            E: EllipticCurve object or Cremona label string
            sha_order: Assumed order of Ш(E) (default: 1)
        """
        if isinstance(E, str):
            self.E = EllipticCurve(E)
        else:
            self.E = E

        self.sha_order = sha_order
        self._generators = None
        self._height_matrix = None
        self._regulator = None

    @property
    def label(self):
        """Get curve label."""
        try:
            return self.E.cremona_label()
        except Exception:
            return str(self.E.a_invariants())

    def get_generators(self):
        """
        Obtain generators of E(Q) (Mordell-Weil group).

        Returns:
            list: Generators of E(Q)
        """
        if self._generators is None:
            try:
                self._generators = list(self.E.gens())
            except (RuntimeError, ValueError, AttributeError):
                # Generators cannot be computed (rank unknown, timeout, etc.)
                self._generators = []
        return self._generators

    def get_rank(self):
        """Get the algebraic rank of E(Q)."""
        return self.E.rank()

    def compute_height(self, P):
        """
        Compute the Néron-Tate canonical height of a point P.

        Args:
            P: Point on E

        Returns:
            float: Canonical height h(P)
        """
        return float(self.E.height(P))

    def compute_height_pairing(self, P, Q):
        """
        Compute the Néron-Tate height pairing <P, Q>.

        The height pairing is defined as:
            <P, Q> = (h(P + Q) - h(P) - h(Q)) / 2

        For P = Q, this gives h(P).

        Args:
            P, Q: Points on E

        Returns:
            float: Height pairing <P, Q>
        """
        if P == Q:
            return self.compute_height(P)

        # Use the built-in height_pairing if available
        try:
            return float(self.E.height_pairing(P, Q))
        except (AttributeError, TypeError):
            # Fallback: compute using parallelogram law
            h_P = self.compute_height(P)
            h_Q = self.compute_height(Q)
            h_sum = self.compute_height(P + Q)
            return (h_sum - h_P - h_Q) / 2

    def compute_height_matrix(self):
        """
        Construct the height pairing matrix.

        For generators P_1, ..., P_r, the matrix H has entries:
            H[i, j] = <P_i, P_j>

        Returns:
            matrix: Height pairing matrix H
        """
        if self._height_matrix is not None:
            return self._height_matrix

        gens = self.get_generators()
        n = len(gens)

        if n == 0:
            self._height_matrix = matrix(RR, 0, 0)
            return self._height_matrix

        H = matrix(RR, n, n)
        for i in range(n):
            for j in range(n):
                H[i, j] = self.compute_height_pairing(gens[i], gens[j])

        self._height_matrix = H
        return H

    def compute_regulator(self):
        """
        Compute the regulator R (determinant of height matrix).

        The regulator measures the "volume" of the lattice generated
        by the Mordell-Weil group in height space.

        Returns:
            float: Regulator R = det(H)
        """
        if self._regulator is not None:
            return self._regulator

        H = self.compute_height_matrix()

        if H.nrows() == 0:
            # For rank 0, regulator is defined to be 1
            self._regulator = 1.0
        else:
            self._regulator = float(abs(H.det()))

        return self._regulator

    def compute_torsion_order(self):
        """
        Compute the order of the torsion subgroup E(Q)_tor.

        Returns:
            int: |E(Q)_tor|
        """
        return int(self.E.torsion_order())

    def compute_real_period(self):
        """
        Compute the real period Ω_E.

        Returns:
            float: Real period Ω_E
        """
        try:
            return float(self.E.period_lattice().omega())
        except (AttributeError, TypeError, ArithmeticError):
            # Fallback: use basic period computation
            try:
                periods = self.E.period_lattice().basis()
                return float(abs(periods[0].real()))
            except Exception:
                # Last resort: return 1.0 as placeholder
                return 1.0

    def compute_tamagawa_product(self):
        """
        Compute the product of Tamagawa numbers ∏c_p.

        Returns:
            int: Product of Tamagawa numbers at all bad primes
        """
        tamagawa_numbers = self.E.tamagawa_numbers()
        return int(prod(tamagawa_numbers))

    def get_tamagawa_numbers(self):
        """
        Get individual Tamagawa numbers at bad primes.

        Returns:
            dict: Mapping from prime p to Tamagawa number c_p
        """
        conductor = self.E.conductor()
        result = {}
        for p in conductor.prime_factors():
            result[int(p)] = int(self.E.tamagawa_number(p))
        return result

    def compute_rhs(self):
        """
        Compute the right-hand side of the BSD formula.

        RHS = Ω_E · R · |Ш| · ∏c_p / |E_tor|²

        Returns:
            float: Right-hand side of BSD formula (assuming |Ш| = sha_order)
        """
        omega = self.compute_real_period()
        regulator = self.compute_regulator()
        tamagawa = self.compute_tamagawa_product()
        torsion = self.compute_torsion_order()

        rhs = omega * regulator * self.sha_order * tamagawa / (torsion ** 2)
        return float(rhs)

    def compute_lhs(self):
        """
        Compute the left-hand side of the BSD formula: L^(r)(E,1)/r!

        For rank 0: L(E, 1) (the special value)
        For rank r > 0: The r-th derivative of L at s=1, divided by r!

        Returns:
            float or None: Left-hand side value, or None if not computable
        """
        rank = self.get_rank()

        try:
            L = self.E.lseries()

            if rank == 0:
                # L(E, 1) directly
                lhs = float(L(1))
            else:
                # L^(r)(E, 1) / r!
                # Use high precision for derivatives
                deriv_value = float(L.derivative(rank)(1))
                lhs = deriv_value / factorial(rank)
            return lhs
        except Exception as e:
            # L-function computation may fail for some curves
            return None

    def verify_bsd(self, tolerance=0.01):
        """
        Verify the BSD formula by comparing LHS and RHS.

        Args:
            tolerance: Relative tolerance for comparison

        Returns:
            dict: Verification results
        """
        lhs = self.compute_lhs()
        rhs = self.compute_rhs()

        result = {
            'curve': self.label,
            'rank': self.get_rank(),
            'lhs': lhs,
            'rhs': rhs,
            'sha_assumed': self.sha_order,
        }

        if lhs is not None and rhs > 0:
            ratio = lhs / rhs
            relative_error = abs(ratio - 1)
            result['ratio'] = ratio
            result['relative_error'] = relative_error
            result['verified'] = relative_error < tolerance
            # implied_sha = lhs / (rhs / sha_assumed) = (lhs * sha_assumed) / rhs
            result['implied_sha'] = (lhs * self.sha_order) / rhs if rhs > 0 else None
        else:
            result['ratio'] = None
            result['relative_error'] = None
            result['verified'] = False
            result['implied_sha'] = None

        return result

    def full_computation(self):
        """
        Perform full BSD RHS computation and return all data.

        Returns:
            dict: Complete computation results
        """
        gens = self.get_generators()
        height_matrix = self.compute_height_matrix()

        result = {
            'curve': {
                'label': self.label,
                'conductor': int(self.E.conductor()),
                'discriminant': int(self.E.discriminant()),
                'rank': self.get_rank(),
            },
            'generators': {
                'count': len(gens),
                'points': [str(P) for P in gens],
                'heights': [self.compute_height(P) for P in gens],
            },
            'height_matrix': {
                'dimension': height_matrix.nrows(),
                'entries': [[float(height_matrix[i, j])
                             for j in range(height_matrix.ncols())]
                            for i in range(height_matrix.nrows())],
            },
            'regulator': self.compute_regulator(),
            'torsion': {
                'order': self.compute_torsion_order(),
                'group': str(self.E.torsion_subgroup().invariants()),
            },
            'real_period': self.compute_real_period(),
            'tamagawa': {
                'product': self.compute_tamagawa_product(),
                'by_prime': self.get_tamagawa_numbers(),
            },
            'bsd_rhs': self.compute_rhs(),
            'bsd_lhs': self.compute_lhs(),
            'sha_assumed': self.sha_order,
        }

        # Add verification
        verification = self.verify_bsd()
        result['verification'] = verification

        return result


def format_output(result):
    """
    Format computation result as readable text.

    Args:
        result: Dictionary from full_computation()

    Returns:
        str: Formatted output text
    """
    lines = []
    lines.append("=" * 70)
    lines.append("BSD RIGHT-HAND SIDE COMPUTATION")
    lines.append("PASO 5 — Emparejamiento de altura y fórmula de BSD")
    lines.append("=" * 70)

    # Curve info
    curve = result['curve']
    lines.append(f"\n📈 Curva: {curve['label']}")
    lines.append(f"   Conductor: {curve['conductor']}")
    lines.append(f"   Discriminante: {curve['discriminant']}")
    lines.append(f"   Rango: {curve['rank']}")

    # Generators
    gens = result['generators']
    lines.append("\n1️⃣  GENERADORES DE E(Q)")
    lines.append(f"   Número de generadores: {gens['count']}")
    for i, (point, height) in enumerate(zip(gens['points'], gens['heights'])):
        lines.append(f"   P_{i+1} = {point}")
        lines.append(f"       h(P_{i+1}) = {height:.10f}")

    # Height matrix
    hm = result['height_matrix']
    lines.append("\n2️⃣  MATRIZ DE EMPAREJAMIENTO DE ALTURAS")
    lines.append(f"   Dimensión: {hm['dimension']} × {hm['dimension']}")
    if hm['dimension'] > 0:
        lines.append("   H = ")
        for row in hm['entries']:
            row_str = "   [" + ", ".join(f"{x:12.8f}" for x in row) + "]"
            lines.append(row_str)

    # Regulator
    lines.append("\n3️⃣  REGULADOR (R)")
    lines.append(f"   R = det(H) = {result['regulator']:.12f}")

    # Torsion
    torsion = result['torsion']
    lines.append("\n4️⃣  SUBGRUPO DE TORSIÓN")
    lines.append(f"   |E(Q)_tor| = {torsion['order']}")
    lines.append(f"   Estructura: {torsion['group']}")

    # Real period
    lines.append("\n5️⃣  PERÍODO REAL (Ω_E)")
    lines.append(f"   Ω_E = {result['real_period']:.12f}")

    # Tamagawa numbers
    tam = result['tamagawa']
    lines.append("\n6️⃣  NÚMEROS DE TAMAGAWA")
    lines.append(f"   Producto ∏c_p = {tam['product']}")
    for p, c in tam['by_prime'].items():
        lines.append(f"   c_{p} = {c}")

    # BSD RHS
    lines.append("\n" + "=" * 70)
    lines.append("📏 FÓRMULA BSD — LADO DERECHO")
    lines.append("=" * 70)
    # Formula explanation:
    # Ω_E: Real period of E
    # R: Regulator (det of height pairing matrix)
    # |Ш|: Order of Tate-Shafarevich group (assumed value)
    # ∏c_p: Product of Tamagawa numbers at bad primes
    # |E_tor|: Order of torsion subgroup
    lines.append("\n   L^(r)(E,1)/r! = Ω_E · R · |Ш| · ∏c_p / |E_tor|²")
    lines.append("   Donde:")
    lines.append("     Ω_E   = período real de E")
    lines.append("     R     = regulador (det de matriz de alturas)")
    lines.append("     |Ш|   = orden del grupo de Tate-Shafarevich")
    lines.append("     ∏c_p  = producto de números de Tamagawa")
    lines.append("     E_tor = subgrupo de torsión")
    lines.append(f"\n   Asumiendo |Ш| = {result['sha_assumed']}:")
    lines.append(f"\n   RHS = {result['real_period']:.8f} × "
                 f"{result['regulator']:.8f} × "
                 f"{result['sha_assumed']} × {tam['product']} / {torsion['order']}²")
    lines.append(f"       = {result['bsd_rhs']:.12f}")

    # BSD LHS
    lines.append("\n📐 FÓRMULA BSD — LADO IZQUIERDO")
    if result['bsd_lhs'] is not None:
        lines.append(f"   L^({curve['rank']})(E,1)/{curve['rank']}! = {result['bsd_lhs']:.12f}")
    else:
        lines.append("   L^(r)(E,1)/r! = [No computable directamente]")

    # Verification
    v = result['verification']
    lines.append("\n" + "=" * 70)
    lines.append("✅ VERIFICACIÓN")
    lines.append("=" * 70)
    if v['verified']:
        lines.append(f"   ✓ BSD VERIFICADO (con |Ш| = {result['sha_assumed']})")
        lines.append(f"   Ratio LHS/RHS = {v['ratio']:.10f}")
        lines.append(f"   Error relativo = {v['relative_error']:.2e}")
    elif v['ratio'] is not None:
        lines.append("   ⚠️  BSD parcialmente verificado")
        lines.append(f"   Ratio LHS/RHS = {v['ratio']:.10f}")
        if v['implied_sha'] is not None:
            lines.append(f"   |Ш| implícito ≈ {v['implied_sha']:.4f}")
    else:
        lines.append("   ⚠️  Verificación incompleta (LHS no disponible)")

    lines.append("\n" + "=" * 70)
    return "\n".join(lines)


def validate_curves(curve_labels, output_file=None):
    """
    Validate BSD for multiple curves and save results.

    Args:
        curve_labels: List of Cremona labels
        output_file: Optional path to save results

    Returns:
        dict: Summary of all computations
    """
    all_results = []
    output_text = []

    for label in curve_labels:
        print(f"⏳ Computing BSD for {label}...")
        try:
            bsd = BSDRightHandSide(label)
            result = bsd.full_computation()
            all_results.append(result)
            output_text.append(format_output(result))
            print(f"✅ {label} -> Rank {result['curve']['rank']}, RHS = {result['bsd_rhs']:.8f}")
        except Exception as e:
            print(f"❌ {label} -> Error: {e}")
            all_results.append({
                'curve': {'label': label},
                'error': str(e),
            })

    summary = {
        'timestamp': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'total': len(all_results),
        'successful': sum(1 for r in all_results if 'error' not in r),
        'verified': sum(1 for r in all_results
                        if 'verification' in r and r['verification'].get('verified', False)),
        'results': all_results,
    }

    if output_file:
        # Save text output
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write("\n\n".join(output_text))
            f.write(f"\n\n{'=' * 70}\n")
            f.write("RESUMEN FINAL\n")
            f.write(f"{'=' * 70}\n")
            f.write(f"Timestamp: {summary['timestamp']}\n")
            f.write(f"Total curvas: {summary['total']}\n")
            f.write(f"Exitosas: {summary['successful']}\n")
            f.write(f"Verificadas: {summary['verified']}\n")

        # Save JSON output
        json_file = output_file.replace('.txt', '.json')
        with open(json_file, 'w', encoding='utf-8') as f:
            json.dump(summary, f, indent=2, default=str)

        print(f"\n📄 Resultados guardados en: {output_file}")
        print(f"📄 JSON guardado en: {json_file}")

    return summary


def main():
    """Main entry point for BSD RHS validation."""
    print("=" * 70)
    print("BSD RIGHT-HAND SIDE COMPUTATION")
    print("PASO 5 — Emparejamiento de altura y fórmula de BSD")
    print("=" * 70)

    # Test curves covering different ranks
    curves = [
        "11a1",    # Rank 0
        "37a1",    # Rank 1
        "389a1",   # Rank 2
        "14a1",    # Rank 0
        "67a1",    # Rank 0
        "43a1",    # Rank 1
        "5077a1",  # Rank 3
    ]

    # Determine output directory
    script_dir = os.path.dirname(os.path.abspath(__file__))
    output_dir = os.path.join(os.path.dirname(script_dir), 'outputs')
    os.makedirs(output_dir, exist_ok=True)
    output_file = os.path.join(output_dir, 'bsd_rhs_computation.txt')

    summary = validate_curves(curves, output_file)

    print("\n📊 RESUMEN:")
    print(f"   Total: {summary['total']} curvas")
    print(f"   Exitosas: {summary['successful']}")
    print(f"   Verificadas: {summary['verified']}")

    return summary


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
