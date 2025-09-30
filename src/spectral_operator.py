"""
Spectral Operator Construction Module
======================================

This module implements the construction of spectral operators M_E,p(s)
for elliptic curves at various primes p according to the representation theory
of GL₂(ℚ_p).

The construction follows Appendices A and F of the Mota Burruezo framework,
distinguishing between:
- Unramified (good reduction) case
- Steinberg (multiplicative reduction) case  
- Supercuspidal (additive reduction) case

Mathematical Background:
-----------------------
The spectral operator M_E,p(s) encodes the local representation-theoretic
data at each prime p. The kernel of M_E,p(1) relates to the local Selmer
group structure.

Key Identity: det(I - M_E(s)) = c(s) · L(E,s)
This spectral BSD identity connects the operator to the L-function.
"""

from sage.all import matrix, identity_matrix, QQ


class SpectralOperatorBuilder:
    """
    Constructs spectral operators M_E,p(s) for elliptic curves.
    
    The operator construction depends on the reduction type at p:
    - Good reduction: trivial 1×1 matrix
    - Multiplicative: 2×2 Steinberg operator
    - Additive/Supercuspidal: f_p × f_p matrix based on conductor exponent
    """
    
    def __init__(self, E):
        """
        Initialize the operator builder for elliptic curve E.
        
        Args:
            E: An elliptic curve over ℚ
        """
        self.E = E
        self.N = E.conductor()
    
    def construct_operator(self, p, s=1):
        """
        Construct the spectral operator M_E,p(s) at prime p.
        
        This is the main entry point for operator construction.
        
        Args:
            p: Prime number
            s: Complex parameter (default=1 for finiteness proof)
            
        Returns:
            Matrix representing M_E,p(s)
            
        Notes:
            At s=1, the kernel of M_E,p(1) gives local obstruction information
            that bounds the local Selmer group contribution.
        """
        if self.E.has_good_reduction(p):
            return self._good_reduction_operator(p, s)
        elif self.E.has_multiplicative_reduction(p):
            return self._steinberg_operator(p, s)
        else:
            return self._supercuspidal_operator(p, s)
    
    def _good_reduction_operator(self, p, s):
        """
        Construct operator for good (unramified) reduction at p.
        
        Theory (Lemma 3.3):
        ------------------
        For unramified primes, the local representation is principal series.
        The operator is trivial (1×1 matrix) encoding the Hecke eigenvalue a_p.
        
        Formula: M_E,p(s) = [1 - a_p·p^(-s) + p^(1-2s)]
        At s=1: M_E,p(1) = [1 - a_p + p]
        
        Args:
            p: Prime of good reduction
            s: Complex parameter
            
        Returns:
            1×1 matrix
        """
        a_p = self.E.ap(p)
        if s == 1:
            # Simplified form at s=1
            operator = matrix(QQ, [[1 - a_p + p]])
        else:
            # General form for arbitrary s
            from sage.all import var
            s_var = var('s') if not isinstance(s, (int, float)) else s
            operator = matrix([[1 - a_p * p**(-s_var) + p**(1-2*s_var)]])
        
        return operator
    
    def _steinberg_operator(self, p, s):
        """
        Construct operator for multiplicative (Steinberg) reduction at p.
        
        Theory (Appendix A.4):
        ---------------------
        For multiplicative reduction (conductor exponent f_p = 1),
        the local representation is special (Steinberg).
        The operator is 2×2, reflecting the two-dimensional space.
        
        The form depends on the sign of a_p:
        - a_p = 1 (split multiplicative): Lower triangular form
        - a_p = -1 (non-split multiplicative): Upper triangular form
        
        Args:
            p: Prime of multiplicative reduction
            s: Complex parameter
            
        Returns:
            2×2 matrix
        """
        a_p = self.E.ap(p)
        
        if s == 1:
            # At s=1, simplified forms
            if a_p == 1:
                # Split multiplicative case
                operator = matrix(QQ, [[1, 0], [p**(-1), 1]])
            else:  # a_p == -1
                # Non-split multiplicative case
                operator = matrix(QQ, [[1, p**(-1)], [0, 1]])
        else:
            # General s parameter (for spectral analysis)
            if a_p == 1:
                operator = matrix([[1, 0], [p**(-s), 1]])
            else:
                operator = matrix([[1, p**(-s)], [0, 1]])
        
        return operator
    
    def _supercuspidal_operator(self, p, s):
        """
        Construct operator for supercuspidal (additive) reduction at p.
        
        Theory (Appendix A.6):
        ---------------------
        For additive reduction with conductor exponent f_p ≥ 2,
        the local representation is supercuspidal.
        The operator dimension is f_p × f_p.
        
        Construction:
        - Start with f_p × f_p identity matrix
        - Modify bottom-right entry to encode the conductor data
        
        Special case f_p = 2 (most common):
        M_E,p(1) = [[1, 0], [0, 1 + p^(f_p-1)]]
        
        Args:
            p: Prime of additive reduction
            s: Complex parameter
            
        Returns:
            f_p × f_p matrix
        """
        # Estimate conductor exponent at p
        f_p = self._estimate_conductor_exponent(p)
        
        if f_p == 2:
            # Most common case: f_p = 2
            if s == 1:
                operator = matrix(QQ, [[1, 0], [0, 1 + p**(f_p - 1)]])
            else:
                operator = matrix([[1, 0], [0, 1 + p**(f_p - s)]])
        else:
            # General f_p case
            dim = max(2, f_p)
            operator = identity_matrix(QQ, dim)
            if s == 1:
                operator[dim-1, dim-1] = 1 + p**(f_p - 1)
            else:
                operator[dim-1, dim-1] = 1 + p**(f_p - s)
        
        return operator
    
    def _estimate_conductor_exponent(self, p):
        """
        Estimate the local conductor exponent f_p at a prime p.
        
        Theory:
        ------
        The conductor exponent f_p measures the "wildness" of the reduction.
        - f_p = 0: good reduction
        - f_p = 1: multiplicative reduction
        - f_p ≥ 2: additive reduction (supercuspidal)
        
        For implementation, we extract f_p from the global conductor:
        N = ∏ p^(f_p)
        
        Args:
            p: Prime number
            
        Returns:
            Integer f_p ≥ 2 (conductor exponent)
        """
        # Get the exponent of p in the conductor
        valuation = self.N.valuation(p)
        
        # For additive reduction, valuation = f_p
        # Common values: f_p = 2 (most cases), f_p ≥ 3 (wild ramification)
        return max(2, valuation)
    
    def compute_spectral_determinant(self, s=1):
        """
        Compute the spectral determinant det(I - M_E(s)).
        
        This is the key quantity in the spectral BSD formula:
        det(I - M_E(s)) = c(s) · L(E,s)
        
        Args:
            s: Complex parameter (default=1)
            
        Returns:
            The determinant value
            
        Notes:
            This method constructs the global operator by taking the product
            over all bad primes, then computes its determinant.
        """
        # Start with the identity (contribution from good primes is trivial)
        total_det = 1
        
        # Multiply contributions from bad primes
        for p in self.N.prime_factors():
            M_p = self.construct_operator(p, s)
            # For s=1, compute det(I - M_p)
            if s == 1:
                I = identity_matrix(QQ, M_p.nrows())
                local_det = (I - M_p).determinant()
                total_det *= local_det
        
        return total_det


def construct_spectral_operator(E, p, s=1):
    """
    Convenience function to construct a spectral operator.
    
    Args:
        E: Elliptic curve over ℚ
        p: Prime number
        s: Complex parameter (default=1)
        
    Returns:
        Matrix representing M_E,p(s)
        
    Example:
        >>> E = EllipticCurve('11a1')
        >>> M_11 = construct_spectral_operator(E, 11, s=1)
        >>> print(M_11)  # 2×2 Steinberg operator
    """
    builder = SpectralOperatorBuilder(E)
    return builder.construct_operator(p, s)
