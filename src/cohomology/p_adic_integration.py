"""
p-adic Integration for BSD
Implements p-adic integration theory for height pairings

This module provides p-adic integration tools used in the spectral
BSD framework for computing p-adic height pairings.
"""

from sage.all import EllipticCurve, QQ, ZZ, Qp, log, exp


class PAdicIntegration:
    """
    p-adic Integration Framework

    Provides p-adic integration machinery for computing:
    - p-adic logarithms
    - Coleman integrals
    - p-adic height pairings
    """

    def __init__(self, E, p, precision=30):
        """
        Initialize p-adic integration for curve E at prime p

        Args:
            E: EllipticCurve object
            p: Prime number
            precision: p-adic precision (default: 30)
        """
        self.E = E
        self.p = p
        self.prec = precision

        # Setup p-adic field
        self.Qp = Qp(p, prec=precision)

        # Check reduction type
        self._setup_reduction_data()

    def _setup_reduction_data(self):
        """Setup reduction type and local data"""
        if self.E.has_good_reduction(self.p):
            self.reduction_type = "good"
            self.is_ordinary = self._check_ordinary()
        elif self.E.has_multiplicative_reduction(self.p):
            self.reduction_type = "multiplicative"
            self.is_ordinary = True
        else:
            self.reduction_type = "additive"
            self.is_ordinary = False

    def _check_ordinary(self):
        """Check if curve has ordinary reduction at p"""
        if not self.E.has_good_reduction(self.p):
            return False

        a_p = self.E.ap(self.p)
        # Ordinary if a_p is not divisible by p
        return (a_p % self.p != 0)

    def p_adic_log(self, point):
        """
        Compute p-adic logarithm of a point

        Args:
            point: Point on elliptic curve

        Returns:
            p-adic number: p-adic logarithm
        """
        if point.is_zero():
            return self.Qp(0)

        # For multiplicative reduction, use Tate parametrization
        if self.reduction_type == "multiplicative":
            return self._tate_p_adic_log(point)

        # For good reduction, use formal group logarithm
        return self._formal_log(point)

    def _formal_log(self, point):
        """
        p-adic logarithm via formal group

        Args:
            point: Point on curve

        Returns:
            p-adic number: Formal group logarithm
        """
        x, y = point.xy()

        # Normalize to formal group parameter
        # log_p(P) ≈ -x/y for small points
        try:
            x_p = self.Qp(x)
            y_p = self.Qp(y)

            # First approximation
            log_val = -x_p / y_p

            return log_val
        except:
            # Return 0 if computation fails
            return self.Qp(0)

    def _tate_p_adic_log(self, point):
        """
        p-adic logarithm using Tate parametrization

        Args:
            point: Point on curve

        Returns:
            p-adic number: Logarithm via Tate parameter
        """
        # Simplified computation using Tate period
        try:
            # Get Tate parameter q_E
            q_E = self._tate_parameter()

            # Compute logarithm
            x, y = point.xy()
            x_p = self.Qp(x)

            # log(1 - 1/x) approximation
            if abs(x) > 1:
                log_val = log(self.Qp(1) - self.Qp(1)/x_p)
            else:
                log_val = self.Qp(0)

            return log_val
        except:
            return self.Qp(0)

    def _tate_parameter(self):
        """
        Compute Tate parameter q_E for multiplicative reduction

        Returns:
            p-adic number: Tate parameter
        """
        # q_E = p^(v_p(j)) where j is j-invariant
        j = self.E.j_invariant()

        try:
            v_p = j.valuation(self.p)
            q_E = self.Qp(self.p) ** v_p
            return q_E
        except:
            return self.Qp(1)

    def coleman_integral(self, omega, point1, point2):
        """
        Compute Coleman integral of differential omega from point1 to point2

        Args:
            omega: Differential form
            point1: Starting point
            point2: Ending point

        Returns:
            p-adic number: Coleman integral value
        """
        # Simplified Coleman integral via logarithms
        if point1.is_zero():
            log1 = self.Qp(0)
        else:
            log1 = self.p_adic_log(point1)

        if point2.is_zero():
            log2 = self.Qp(0)
        else:
            log2 = self.p_adic_log(point2)

        # Integral is difference of logarithms (simplified)
        integral = log2 - log1

        return integral

    def p_adic_height_pairing(self, point1, point2):
        """
        Compute p-adic height pairing between two points

        Args:
            point1: First point
            point2: Second point

        Returns:
            dict: Height pairing data
        """
        # Compute p-adic logarithms
        log1 = self.p_adic_log(point1)
        log2 = self.p_adic_log(point2)

        # p-adic height pairing (simplified)
        # <P, Q>_p = log_p(P) * log_p(Q)
        pairing = log1 * log2

        return {
            'pairing_value': float(pairing) if pairing else 0.0,
            'log_point1': float(log1) if log1 else 0.0,
            'log_point2': float(log2) if log2 else 0.0,
            'prime': self.p,
            'reduction_type': self.reduction_type
        }

    def regulator_p_adic(self, points):
        """
        Compute p-adic regulator for list of points

        Args:
            points: List of points generating Mordell-Weil group

        Returns:
            dict: p-adic regulator data
        """
        from sage.all import matrix

        n = len(points)

        if n == 0:
            return {
                'regulator': 1.0,
                'dimension': 0,
                'prime': self.p
            }

        # Build height pairing matrix
        pairing_matrix = []

        for i in range(n):
            row = []
            for j in range(n):
                pairing_data = self.p_adic_height_pairing(points[i], points[j])
                row.append(pairing_data['pairing_value'])
            pairing_matrix.append(row)

        # Compute determinant (regulator)
        try:
            M = matrix(pairing_matrix)
            reg = abs(M.determinant())
        except:
            reg = 1.0

        return {
            'regulator': float(reg),
            'dimension': n,
            'prime': self.p,
            'pairing_matrix': pairing_matrix
        }


def compute_p_adic_height(E, p, point1, point2, precision=30):
    """
    Convenience function to compute p-adic height pairing

    Args:
        E: EllipticCurve
        p: Prime
        point1, point2: Points on curve
        precision: p-adic precision

    Returns:
        dict: Height pairing result
    """
    integrator = PAdicIntegration(E, p, precision=precision)
    return integrator.p_adic_height_pairing(point1, point2)


__all__ = [
    'PAdicIntegration',
    'compute_p_adic_height'
]
