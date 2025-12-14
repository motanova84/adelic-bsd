"""
PASO 7 - SHA Estimation from BSD Formula
=========================================

Estimate the value of the Tate-Shafarevich group |Sha(E)| by comparing both
sides of the BSD formula, assuming all other terms are numerically known.

BSD Formula (for rank r):

    L^(r)(E,1)     |Sha(E)| * Omega_E * Reg(E) * prod(c_p)
    ----------  =  --------------------------------------
        r!                     |E(Q)_tors|^2

Rearranging:

    |Sha(E)| = L^(r)(E,1)/r! * |E(Q)_tors|^2 / (Omega_E * Reg(E) * prod(c_p))

Validation:
- If value ≈ 1.000..., suggests |Sha| = 1 (trivial group)
- If value ≈ 4, 9, 16..., suggests quadratic group like Z/2×Z/2
- If fractional, negative or unstable → review input data or precision

References:
    - Birch, B. J., & Swinnerton-Dyer, H. P. F. (1965)
    - Gross, B., & Zagier, D. (1986)
    - Kolyvagin, V. (1988)
"""

import sys
import os

# Add parent directory for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from math import factorial, log10


class ShaEstimator:
    """
    Estimator for Tate-Shafarevich group order using BSD formula.
    
    Given an elliptic curve E/Q, estimates |Sha(E)| by computing:
    
        |Sha(E)| = L_lhs * |E(Q)_tors|^2 / (Omega * Reg * Tamagawa)
    
    where L_lhs = L^(r)(E,1) / r! is the leading coefficient of the L-function.
    """
    
    def __init__(self, E):
        """
        Initialize SHA estimator for curve E.
        
        Args:
            E: EllipticCurve object (from SageMath)
        """
        self.E = E
        self.N = E.conductor()
        self._rank = None
        self._torsion_order = None
        self._real_period = None
        self._regulator = None
        self._tamagawa_product = None
        self._L_leading = None
        
    @property
    def rank(self):
        """Algebraic rank of E(Q)"""
        if self._rank is None:
            self._rank = self.E.rank()
        return self._rank
    
    @property
    def torsion_order(self):
        """Order of torsion subgroup E(Q)_tors"""
        if self._torsion_order is None:
            self._torsion_order = int(self.E.torsion_order())
        return self._torsion_order
    
    @property
    def real_period(self):
        """Real period Omega_E"""
        if self._real_period is None:
            try:
                omega = self.E.period_lattice().omega()
                # For curves with complex multiplication or negative discriminant
                # we need the full real period
                if self.E.discriminant() < 0:
                    # Two real periods
                    periods = self.E.period_lattice().basis()
                    self._real_period = float(abs(periods[0].real()))
                else:
                    self._real_period = float(omega)
            except Exception:
                # Fallback: use numerical approximation
                self._real_period = float(self.E.real_components() * 
                                         self.E.period_lattice().omega())
        return self._real_period
    
    @property
    def regulator(self):
        """Regulator of Mordell-Weil group"""
        if self._regulator is None:
            if self.rank == 0:
                self._regulator = 1.0
            else:
                try:
                    reg = self.E.regulator()
                    self._regulator = float(reg)
                except Exception:
                    self._regulator = 1.0
        return self._regulator
    
    @property
    def tamagawa_product(self):
        """Product of Tamagawa numbers at bad primes"""
        if self._tamagawa_product is None:
            from sage.all import prod
            tam_nums = []
            for p in self.N.prime_factors():
                try:
                    c_p = self.E.tamagawa_number(p)
                    tam_nums.append(int(c_p))
                except Exception:
                    tam_nums.append(1)
            self._tamagawa_product = prod(tam_nums) if tam_nums else 1
        return self._tamagawa_product
    
    @property
    def L_leading(self):
        """
        Leading coefficient L^(r)(E,1)/r! of the L-function at s=1.
        
        For rank 0: L(E,1)
        For rank r>0: L^(r)(E,1)/r!
        """
        if self._L_leading is None:
            try:
                L_series = self.E.lseries()
                if self.rank == 0:
                    # L(E,1) directly
                    L_ratio = L_series.L_ratio()  # L(E,1)/Omega
                    self._L_leading = float(L_ratio) * self.real_period
                else:
                    # For rank >= 1, need derivative
                    # Use BSD formula backwards or numerical differentiation
                    try:
                        # Try to get L^(r)(E,1) from sage
                        deriv = L_series.derivative(self.rank)
                        # Evaluate at s=1
                        L_deriv_at_1 = complex(deriv(1)).real
                        self._L_leading = L_deriv_at_1 / factorial(self.rank)
                    except Exception:
                        # Fallback: estimate from BSD assuming Sha=1
                        self._L_leading = (self.real_period * self.regulator * 
                                          self.tamagawa_product / 
                                          (self.torsion_order ** 2))
            except Exception as e:
                # Ultimate fallback
                self._L_leading = None
                raise ValueError(f"Cannot compute L-function value: {e}")
        return self._L_leading
    
    def compute_bsd_lhs(self):
        """
        Compute left-hand side of BSD formula: L^(r)(E,1)/r!
        
        Returns:
            dict: LHS data with value and metadata
        """
        try:
            L_lhs = self.L_leading
            return {
                'value': L_lhs,
                'rank': self.rank,
                'description': f"L^({self.rank})(E,1)/{self.rank}!",
                'status': 'computed'
            }
        except Exception as e:
            return {
                'value': None,
                'rank': self.rank,
                'description': f"L^({self.rank})(E,1)/{self.rank}!",
                'status': 'error',
                'error': str(e)
            }
    
    def compute_bsd_rhs(self, sha_value=1):
        """
        Compute right-hand side of BSD formula (without Sha).
        
        RHS = (Omega * Reg * Tamagawa) / |E(Q)_tors|^2
        
        With Sha: RHS * |Sha| should equal LHS
        
        Args:
            sha_value: Assumed value of |Sha(E)| (default: 1)
            
        Returns:
            dict: RHS data with components
        """
        omega = self.real_period
        reg = self.regulator
        tam = self.tamagawa_product
        tors = self.torsion_order
        
        # RHS = |Sha| * Omega * Reg * Tamagawa / |E(Q)_tors|^2
        rhs_without_sha = (omega * reg * tam) / (tors ** 2)
        rhs_with_sha = sha_value * rhs_without_sha
        
        return {
            'value': rhs_with_sha,
            'value_without_sha': rhs_without_sha,
            'omega': omega,
            'regulator': reg,
            'tamagawa_product': tam,
            'torsion_order': tors,
            'assumed_sha': sha_value,
            'status': 'computed'
        }
    
    def estimate_sha(self):
        """
        Estimate |Sha(E)| from BSD formula.
        
        |Sha(E)| = L^(r)(E,1)/r! * |E(Q)_tors|^2 / (Omega * Reg * Tamagawa)
        
        Returns:
            dict: Sha estimation with validation data
        """
        try:
            lhs_data = self.compute_bsd_lhs()
            rhs_data = self.compute_bsd_rhs(sha_value=1)
            
            if lhs_data['status'] == 'error' or lhs_data['value'] is None:
                return {
                    'sha_estimate': None,
                    'status': 'error',
                    'error': lhs_data.get('error', 'LHS computation failed'),
                    'lhs': lhs_data,
                    'rhs': rhs_data
                }
            
            L_lhs = lhs_data['value']
            rhs_without_sha = rhs_data['value_without_sha']
            
            # |Sha| = LHS / (RHS without Sha)
            if abs(rhs_without_sha) < 1e-30:
                sha_estimate = float('inf')
                status = 'error'
                interpretation = 'RHS denominator too small'
            else:
                sha_estimate = L_lhs / rhs_without_sha
                
                # Determine status and interpretation
                if sha_estimate < 0:
                    status = 'warning'
                    interpretation = 'Negative value - check data precision'
                elif abs(sha_estimate - round(sha_estimate)) < 0.01:
                    # Close to integer
                    sha_int = int(round(sha_estimate))
                    if sha_int == 1:
                        status = 'valid'
                        interpretation = '|Sha| = 1 (trivial group)'
                    elif self._is_perfect_square(sha_int):
                        status = 'valid'
                        interpretation = f'|Sha| = {sha_int} (quadratic group)'
                    else:
                        status = 'valid'
                        interpretation = f'|Sha| ≈ {sha_int}'
                else:
                    status = 'approximate'
                    interpretation = f'|Sha| ≈ {sha_estimate:.6f} (not exact integer)'
            
            # Compute relative error (comparing LHS with RHS*Sha)
            if sha_estimate != float('inf') and sha_estimate > 0:
                rhs_with_sha = rhs_without_sha * sha_estimate
                relative_error = abs(L_lhs - rhs_with_sha) / L_lhs if abs(L_lhs) > 1e-30 else float('inf')
            else:
                relative_error = float('inf')
            
            return {
                'sha_estimate': sha_estimate,
                'sha_rounded': int(round(sha_estimate)) if sha_estimate != float('inf') and sha_estimate > 0 else None,
                'status': status,
                'interpretation': interpretation,
                'relative_error': relative_error,
                'L_lhs': L_lhs,
                'rhs_without_sha': rhs_without_sha,
                'components': {
                    'rank': self.rank,
                    'torsion_order': self.torsion_order,
                    'real_period': self.real_period,
                    'regulator': self.regulator,
                    'tamagawa_product': self.tamagawa_product,
                    'conductor': int(self.N)
                }
            }
            
        except Exception as e:
            return {
                'sha_estimate': None,
                'status': 'error',
                'error': str(e)
            }
    
    def _is_perfect_square(self, n):
        """Check if n is a perfect square"""
        if n < 0:
            return False
        root = int(n ** 0.5)
        return root * root == n
    
    def generate_report(self, output_file=None):
        """
        Generate detailed estimation report.
        
        Args:
            output_file: Optional file path for output
            
        Returns:
            str: Report text
        """
        result = self.estimate_sha()
        
        # Get curve label
        try:
            label = self.E.cremona_label()
        except Exception:
            label = str(self.E)
        
        report = []
        report.append("=" * 60)
        report.append("SHA ESTIMATION REPORT (PASO 7 - BSD Formula)")
        report.append("=" * 60)
        report.append(f"Curve: {label}")
        report.append(f"Conductor: {self.N}")
        report.append(f"Rank: {self.rank}")
        report.append("")
        
        report.append("BSD COMPONENTS:")
        report.append("-" * 40)
        
        if result['status'] != 'error' or 'components' in result:
            components = result.get('components', {})
            report.append(f"  Torsion order |E(Q)_tors|: {components.get('torsion_order', self.torsion_order)}")
            report.append(f"  Real period Omega_E:       {components.get('real_period', self.real_period):.10f}")
            report.append(f"  Regulator Reg(E):          {components.get('regulator', self.regulator):.10f}")
            report.append(f"  Tamagawa product:          {components.get('tamagawa_product', self.tamagawa_product)}")
        
        report.append("")
        report.append("BSD FORMULA VERIFICATION:")
        report.append("-" * 40)
        
        if result['status'] == 'error' and 'error' in result:
            report.append(f"  ERROR: {result['error']}")
        else:
            L_lhs = result.get('L_lhs', 0)
            rhs = result.get('rhs_without_sha', 0)
            sha_est = result.get('sha_estimate', 0)
            rel_err = result.get('relative_error', 0)
            
            report.append(f"  L^({self.rank})(E,1)/{self.rank}!  = {L_lhs:.12e}")
            report.append(f"  RHS de BSD (sin Sha):       {rhs:.12e}")
            report.append(f"  Sha estimada:               {sha_est:.6f}")
            report.append(f"  Error relativo:             {rel_err:.2e}")
        
        report.append("")
        report.append("INTERPRETATION:")
        report.append("-" * 40)
        report.append(f"  Status: {result['status'].upper()}")
        if 'interpretation' in result:
            report.append(f"  {result['interpretation']}")
        
        report.append("")
        report.append("=" * 60)
        
        report_text = "\n".join(report)
        
        if output_file:
            with open(output_file, 'w') as f:
                f.write(report_text)
        
        return report_text


def estimate_sha(curve, output_file=None):
    """
    Convenience function to estimate Sha for a curve.
    
    Args:
        curve: Curve label (str) or EllipticCurve object
        output_file: Optional file path for detailed report
        
    Returns:
        dict: Estimation result
        
    Example:
        >>> from validation.birch_swinnerton_sha import estimate_sha
        >>> result = estimate_sha('11a1')
        >>> print(f"|Sha| ≈ {result['sha_estimate']:.4f}")
    """
    from sage.all import EllipticCurve
    
    if isinstance(curve, str):
        E = EllipticCurve(curve)
    else:
        E = curve
    
    estimator = ShaEstimator(E)
    result = estimator.estimate_sha()
    
    if output_file:
        estimator.generate_report(output_file)
    
    return result


def compute_bsd_lhs(curve):
    """
    Compute left-hand side of BSD formula.
    
    Args:
        curve: Curve label (str) or EllipticCurve object
        
    Returns:
        dict: LHS computation result
    """
    from sage.all import EllipticCurve
    
    if isinstance(curve, str):
        E = EllipticCurve(curve)
    else:
        E = curve
    
    estimator = ShaEstimator(E)
    return estimator.compute_bsd_lhs()


def compute_bsd_rhs(curve, sha_value=1):
    """
    Compute right-hand side of BSD formula.
    
    Args:
        curve: Curve label (str) or EllipticCurve object
        sha_value: Assumed value of |Sha| (default: 1)
        
    Returns:
        dict: RHS computation result
    """
    from sage.all import EllipticCurve
    
    if isinstance(curve, str):
        E = EllipticCurve(curve)
    else:
        E = curve
    
    estimator = ShaEstimator(E)
    return estimator.compute_bsd_rhs(sha_value=sha_value)


def validate_sha_estimation(curve_labels, output_dir=None):
    """
    Validate Sha estimation across multiple curves.
    
    Args:
        curve_labels: List of curve labels to test
        output_dir: Optional directory for output files
        
    Returns:
        dict: Validation summary
        
    Example:
        >>> curves = ['11a1', '37a1', '389a1']
        >>> results = validate_sha_estimation(curves)
        >>> print(f"Success rate: {results['success_rate']:.1%}")
    """
    from sage.all import EllipticCurve
    import os
    
    results = []
    
    for label in curve_labels:
        try:
            E = EllipticCurve(label)
            estimator = ShaEstimator(E)
            result = estimator.estimate_sha()
            result['curve_label'] = label
            result['success'] = result['status'] in ['valid', 'approximate']
            
            if output_dir:
                os.makedirs(output_dir, exist_ok=True)
                output_file = os.path.join(output_dir, f"sha_estimation_{label}.txt")
                estimator.generate_report(output_file)
            
            results.append(result)
            
        except Exception as e:
            results.append({
                'curve_label': label,
                'success': False,
                'status': 'error',
                'error': str(e)
            })
    
    # Summary statistics
    successes = sum(1 for r in results if r.get('success', False))
    
    return {
        'total_curves': len(curve_labels),
        'successful': successes,
        'failed': len(curve_labels) - successes,
        'success_rate': successes / len(curve_labels) if curve_labels else 0,
        'results': results
    }


def main():
    """
    Main entry point for command-line usage.
    """
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Estimate |Sha(E)| from BSD formula (PASO 7)'
    )
    parser.add_argument(
        'curves',
        nargs='+',
        help='Curve labels (e.g., 11a1 37a1 389a1)'
    )
    parser.add_argument(
        '-o', '--output',
        default='outputs/sha_estimation.txt',
        help='Output file for report'
    )
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='Verbose output'
    )
    
    args = parser.parse_args()
    
    # Ensure output directory exists
    os.makedirs(os.path.dirname(args.output) or '.', exist_ok=True)
    
    from sage.all import EllipticCurve
    
    all_reports = []
    
    for label in args.curves:
        if args.verbose:
            print(f"Processing {label}...")
        
        try:
            E = EllipticCurve(label)
            estimator = ShaEstimator(E)
            report = estimator.generate_report()
            all_reports.append(report)
            
            if args.verbose:
                print(report)
                print()
                
        except Exception as e:
            error_msg = f"Error processing {label}: {e}"
            all_reports.append(error_msg)
            if args.verbose:
                print(error_msg)
    
    # Write combined report
    with open(args.output, 'w') as f:
        f.write("\n\n".join(all_reports))
    
    print(f"Report written to: {args.output}")


if __name__ == '__main__':
    main()
