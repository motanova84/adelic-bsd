"""
BSD Experiment Core Module
===========================

Implements the complete BSD formula computation and comparison:
- Left side: L(E,1) / Ω (or derivative for rank > 0)
- Right side: Sha * Reg * prod(c_p) / |E_tors|²

Provides experimental verification with error analysis.

Author: BSD Spectral Framework
Date: November 2025
"""

import json
import os
from datetime import datetime


class BSDExperiment:
    """
    BSD Formula Experiment for a single elliptic curve.

    Computes all terms of the BSD formula and compares LHS vs RHS
    to evaluate |Sha(E)| ≈ 1 or other quadratic structures.
    """

    def __init__(self, E, label=None):
        """
        Initialize BSD experiment for curve E.

        Args:
            E: SageMath EllipticCurve object
            label: Optional label for the curve
        """
        self.E = E
        self.label = label or self._get_label()
        self._results = None
        self._computed = False

    def _get_label(self):
        """Get curve label from Cremona database or generate one."""
        try:
            return self.E.cremona_label()
        except Exception:
            return f"E_{self.E.conductor()}"

    def compute_bsd_terms(self):
        """
        Compute all terms appearing in the BSD formula.

        Returns:
            dict: All BSD formula components
        """
        # Basic invariants
        conductor = int(self.E.conductor())
        rank = int(self.E.rank())
        discriminant = int(self.E.discriminant())
        j_invariant = self.E.j_invariant()

        # Compute all BSD terms
        terms = {
            'conductor': conductor,
            'rank': rank,
            'discriminant': discriminant,
            'j_invariant': str(j_invariant),
        }

        # Torsion
        terms['torsion'] = self._compute_torsion()

        # Regulator
        terms['regulator'] = self._compute_regulator()

        # Real period Omega
        terms['omega'] = self._compute_omega()

        # Tamagawa numbers
        terms['tamagawa'] = self._compute_tamagawa()

        # L-function value
        terms['l_value'] = self._compute_l_value()

        return terms

    def _compute_torsion(self):
        """Compute torsion subgroup information."""
        try:
            tors = self.E.torsion_subgroup()
            order = int(tors.order())
            structure = [int(g.order()) for g in tors.gens()]
            return {
                'order': order,
                'structure': structure,
            }
        except Exception as e:
            return {'order': 1, 'structure': [], 'error': str(e)}

    def _compute_regulator(self):
        """Compute regulator of Mordell-Weil group."""
        rank = int(self.E.rank())

        if rank == 0:
            return {'value': 1.0, 'rank': 0}

        try:
            reg = float(self.E.regulator())
            return {'value': reg, 'rank': rank}
        except Exception as e:
            return {'value': 1.0, 'rank': rank, 'error': str(e)}

    def _compute_omega(self):
        """Compute real period Omega_E."""
        try:
            # Get the real period using period lattice
            period_lattice = self.E.period_lattice()
            omega = float(period_lattice.omega())

            # Also compute the omega+ (positive real period)
            # which appears in the BSD formula
            omega_plus = abs(omega)

            return {
                'omega': omega,
                'omega_plus': omega_plus,
            }
        except Exception as e:
            return {'omega': 1.0, 'omega_plus': 1.0, 'error': str(e)}

    def _compute_tamagawa(self):
        """Compute Tamagawa numbers at all bad primes."""
        N = self.E.conductor()
        bad_primes = list(N.prime_factors())

        tamagawa_numbers = {}
        product = 1

        for p in bad_primes:
            try:
                c_p = int(self.E.tamagawa_number(p))
                tamagawa_numbers[str(p)] = c_p
                product *= c_p
            except Exception:
                tamagawa_numbers[str(p)] = 1

        return {
            'by_prime': tamagawa_numbers,
            'product': product,
        }

    def _compute_l_value(self):
        """Compute L-function value at s=1."""
        rank = int(self.E.rank())

        try:
            L = self.E.lseries()

            if rank == 0:
                # L(E,1) directly
                try:
                    L_ratio = float(L.L_ratio())  # L(E,1) / Omega
                    omega = self._compute_omega()['omega_plus']
                    L_value = L_ratio * omega

                    return {
                        'L_at_1': L_value,
                        'L_ratio': L_ratio,
                        'vanishes': False,
                    }
                except Exception:
                    # Try numerical evaluation
                    L_value = float(L(1))
                    return {
                        'L_at_1': L_value,
                        'L_ratio': None,
                        'vanishes': abs(L_value) < 1e-10,
                    }

            else:
                # For rank > 0, L(E,1) = 0
                # Use L-series derivative
                try:
                    # L^(r)(E,1) / r!
                    L_deriv = float(L.deriv_at_critical_point(rank))
                    return {
                        'L_at_1': 0.0,
                        'L_deriv': L_deriv,
                        'deriv_order': rank,
                        'vanishes': True,
                    }
                except Exception as e:
                    return {
                        'L_at_1': 0.0,
                        'L_deriv': None,
                        'deriv_order': rank,
                        'vanishes': True,
                        'error': str(e),
                    }

        except Exception as e:
            return {'L_at_1': None, 'error': str(e)}

    def compute_bsd_comparison(self):
        """
        Compare LHS and RHS of BSD formula.

        BSD formula (rank 0):
            L(E,1) / Omega = |Sha| * prod(c_p) / |E_tors|²

        BSD formula (rank r > 0):
            L^(r)(E,1) / (r! * Omega * Reg) = |Sha| * prod(c_p) / |E_tors|²

        Returns:
            dict: Comparison results including error estimate
        """
        terms = self.compute_bsd_terms()
        rank = terms['rank']

        # Get values
        torsion_order = terms['torsion']['order']
        tamagawa_product = terms['tamagawa']['product']
        regulator = terms['regulator']['value']
        omega = terms['omega']['omega_plus']

        comparison = {
            'terms': terms,
            'rank': rank,
        }

        if rank == 0:
            # LHS = L(E,1) / Omega
            L_at_1 = terms['l_value'].get('L_at_1', 0)
            if L_at_1 is not None and omega > 0:
                lhs = L_at_1 / omega
            else:
                lhs = None

            # RHS (assuming Sha = 1): prod(c_p) / |E_tors|²
            rhs_sha_1 = tamagawa_product / (torsion_order ** 2)

            if lhs is not None and rhs_sha_1 > 0:
                # Estimate |Sha| from ratio
                sha_estimate = lhs / rhs_sha_1
                error = abs(sha_estimate - 1.0) if sha_estimate is not None else None

                comparison.update({
                    'lhs': lhs,
                    'rhs_sha_1': rhs_sha_1,
                    'sha_estimate': sha_estimate,
                    'relative_error': error,
                    'sha_is_1': error is not None and error < 0.01,
                })
            else:
                comparison.update({
                    'lhs': lhs,
                    'rhs_sha_1': rhs_sha_1,
                    'sha_estimate': None,
                    'error': 'Could not compute comparison',
                })

        else:  # rank > 0
            # LHS = L^(r)(E,1) / (r! * Omega * Reg)
            L_deriv = terms['l_value'].get('L_deriv')

            if L_deriv is not None and omega > 0 and regulator > 0:
                import math
                factorial_r = math.factorial(rank)
                lhs = L_deriv / (factorial_r * omega * regulator)
            else:
                lhs = None

            # RHS (assuming Sha = 1): prod(c_p) / |E_tors|²
            rhs_sha_1 = tamagawa_product / (torsion_order ** 2)

            if lhs is not None and rhs_sha_1 > 0:
                sha_estimate = lhs / rhs_sha_1
                error = abs(sha_estimate - 1.0) if sha_estimate is not None else None

                comparison.update({
                    'lhs': lhs,
                    'rhs_sha_1': rhs_sha_1,
                    'sha_estimate': sha_estimate,
                    'relative_error': error,
                    'sha_is_1': error is not None and error < 0.01,
                })
            else:
                comparison.update({
                    'lhs': lhs,
                    'rhs_sha_1': rhs_sha_1,
                    'sha_estimate': None,
                    'note': 'Could not fully compute BSD comparison for rank > 0',
                })

        self._results = comparison
        self._computed = True

        return comparison

    def generate_output(self, output_format='text'):
        """
        Generate output for the BSD experiment.

        Args:
            output_format: 'text', 'json', or 'detailed'

        Returns:
            str: Formatted output
        """
        if not self._computed:
            self.compute_bsd_comparison()

        results = self._results
        terms = results['terms']

        if output_format == 'json':
            return json.dumps(results, indent=2, default=str)

        elif output_format == 'detailed':
            output = []
            output.append("=" * 70)
            output.append(f"BSD EXPERIMENTAL VALIDATION: {self.label}")
            output.append("=" * 70)
            output.append("")
            output.append("CURVE DATA:")
            output.append(f"  Conductor: {terms['conductor']}")
            output.append(f"  Rank: {terms['rank']}")
            output.append(f"  j-invariant: {terms['j_invariant']}")
            output.append(f"  Discriminant: {terms['discriminant']}")
            output.append("")
            output.append("TORSION:")
            output.append(f"  Order: {terms['torsion']['order']}")
            output.append(f"  Structure: {terms['torsion']['structure']}")
            output.append("")
            output.append("BSD TERMS:")
            output.append(f"  Omega (real period): {terms['omega']['omega_plus']:.10f}")
            output.append(f"  Regulator: {terms['regulator']['value']:.10f}")
            output.append(f"  Tamagawa product: {terms['tamagawa']['product']}")
            output.append("")
            output.append("L-FUNCTION:")
            l_data = terms['l_value']
            if 'L_at_1' in l_data:
                output.append(f"  L(E,1): {l_data.get('L_at_1', 'N/A')}")
            if 'L_deriv' in l_data:
                output.append(f"  L^({l_data.get('deriv_order', '?')})(E,1): {l_data.get('L_deriv', 'N/A')}")
            output.append("")
            output.append("BSD COMPARISON:")
            if results.get('lhs') is not None:
                output.append(f"  LHS: {results['lhs']:.10e}")
                output.append(f"  RHS (Sha=1): {results['rhs_sha_1']:.10e}")
                if results.get('sha_estimate') is not None:
                    output.append(f"  Sha(E) estimate: {results['sha_estimate']:.6f}")
                    output.append(f"  Relative error: {results.get('relative_error', 0) * 100:.4f}%")
                    if results.get('sha_is_1'):
                        output.append("  Status: ✓ Sha ≈ 1 (experimental match)")
                    else:
                        output.append("  Status: Sha ≠ 1 or further analysis needed")
            else:
                output.append("  Could not compute full BSD comparison")
            output.append("")
            output.append("=" * 70)
            return "\n".join(output)

        else:  # text
            output = []
            output.append(f"Curve: {self.label}")
            output.append(f"Conductor: {terms['conductor']}")
            output.append(f"Rank: {terms['rank']}")
            if results.get('lhs') is not None:
                output.append(f"LHS: {results['lhs']:.6e}")
                output.append(f"RHS: {results['rhs_sha_1']:.6e}")
                if results.get('sha_estimate') is not None:
                    output.append(f"Error: {results.get('relative_error', 0) * 100:.2f}%")
                    output.append(f"Sha(E): {results['sha_estimate']:.5f}")
            return "\n".join(output)


def compute_bsd_comparison(E, label=None):
    """
    Convenience function to compute BSD comparison for a curve.

    Args:
        E: SageMath EllipticCurve
        label: Optional label

    Returns:
        dict: BSD comparison results
    """
    experiment = BSDExperiment(E, label)
    return experiment.compute_bsd_comparison()


def generate_curve_json(E, label=None, output_path=None):
    """
    Generate JSON file with curve data and j-invariant.

    Args:
        E: SageMath EllipticCurve
        label: Optional label
        output_path: Optional path for output file

    Returns:
        dict: Curve data as dictionary (also saved to file if path given)
    """
    experiment = BSDExperiment(E, label)
    terms = experiment.compute_bsd_terms()

    curve_data = {
        'label': experiment.label,
        'a_invariants': [int(a) for a in E.a_invariants()],
        'conductor': terms['conductor'],
        'rank': terms['rank'],
        'j_invariant': terms['j_invariant'],
        'discriminant': terms['discriminant'],
        'torsion_order': terms['torsion']['order'],
        'torsion_structure': terms['torsion']['structure'],
        'timestamp': datetime.now().isoformat(),
    }

    if output_path:
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        with open(output_path, 'w') as f:
            json.dump(curve_data, f, indent=2)

    return curve_data


def run_bsd_experiment(E, label=None, output_dir=None):
    """
    Run complete BSD experiment for a curve.

    Args:
        E: SageMath EllipticCurve
        label: Optional label
        output_dir: Directory for output files

    Returns:
        dict: Complete experiment results
    """
    experiment = BSDExperiment(E, label)
    comparison = experiment.compute_bsd_comparison()

    # Generate output
    detailed_output = experiment.generate_output('detailed')

    if output_dir:
        os.makedirs(output_dir, exist_ok=True)

        # Save curve JSON
        curve_path = os.path.join(output_dir, 'curve.json')
        generate_curve_json(E, label, curve_path)

        # Save output text
        output_path = os.path.join(output_dir, 'output.txt')
        with open(output_path, 'w') as f:
            f.write(detailed_output)

        # Save full results JSON
        results_path = os.path.join(output_dir, 'bsd_results.json')
        with open(results_path, 'w') as f:
            json.dump(comparison, f, indent=2, default=str)

    return {
        'comparison': comparison,
        'output': detailed_output,
        'label': experiment.label,
    }
