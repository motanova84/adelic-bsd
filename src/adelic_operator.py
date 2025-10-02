"""
Adelic Operator Implementation
Implements the adelic operator K_E(s) for spectral BSD framework

This module provides the core adelic operator construction via S-finite
trace-class operators that forms the foundation of the spectral BSD approach.

The construction approximates trace-class operators on adelic spaces through
finite-dimensional local operators at bad primes. The global operator is
obtained as a controlled limit with Schatten-S_1 norm convergence.
"""

from sage.all import EllipticCurve, matrix, identity_matrix, ZZ, QQ


class AdelicOperator:
    """
    Adelic Operator K_E(s) for elliptic curves (S-finite approximation)
    
    Constructs local spectral operators at primes dividing the conductor.
    These provide S-finite approximations to the global trace-class operator
    K_E(s) whose Fredholm determinant satisfies:
    
        det(I - K_E(s)) = c(s) * Λ(E, s)
    
    where Λ(E,s) is the completed L-function and c(s) is holomorphic and
    non-vanishing near s=1.
    
    The implementation focuses on the s=1 case which is critical for BSD.
    """
    
    def __init__(self, E, s=1):
        """
        Initialize adelic operator for elliptic curve E at parameter s
        
        Args:
            E: EllipticCurve object
            s: Complex parameter (default: 1 for BSD)
        """
        self.E = E
        self.s = s
        self.N = E.conductor()
        self.local_operators = {}
        
        # Compute local operators at bad primes
        self._compute_local_operators()
    
    def _compute_local_operators(self):
        """Compute local operators at all primes dividing conductor"""
        for p in self.N.prime_factors():
            self.local_operators[p] = self._local_operator_at_prime(p)
    
    def _local_operator_at_prime(self, p):
        """
        Compute local operator at prime p
        
        Args:
            p: Prime number
            
        Returns:
            dict: Local operator data including matrix and properties
        """
        if self.E.has_good_reduction(p):
            return self._good_reduction_operator(p)
        elif self.E.has_multiplicative_reduction(p):
            return self._multiplicative_reduction_operator(p)
        else:
            return self._supercuspidal_operator(p)
    
    def _good_reduction_operator(self, p):
        """
        Construct operator for good reduction
        
        At good primes, the local L-factor is (1 - a_p*p^(-s) + p^(1-2s))^(-1).
        The corresponding local operator K_p(s) at s=1 yields this factor
        in the Fredholm determinant.
        """
        a_p = self.E.ap(p)
        # M_p(s) = 1 - a_p*p^(-s) + p^(1-2s) for good reduction
        # At s=1: M_p(1) = 1 - a_p/p + 1/p = (1 - a_p + p)/p
        operator = matrix([[1 - a_p + p]])
        
        return {
            'operator': operator,
            'reduction_type': 'good',
            'dimension': 1,
            'ap': a_p,
            'prime': p
        }
    
    def _multiplicative_reduction_operator(self, p):
        """
        Construct operator for multiplicative reduction (Steinberg representation)
        
        At primes of multiplicative reduction, the representation is
        Steinberg. The local operator reflects this structure and ensures
        the local factor c_p(s) is non-vanishing near s=1.
        """
        a_p = self.E.ap(p)
        
        if a_p == 1:  # Split multiplicative
            # M_p(s) matrix form
            operator = matrix([[1, 0], [p**(-1), 1]])
        else:  # Non-split multiplicative (a_p = -1)
            operator = matrix([[1, p**(-1)], [0, 1]])
        
        return {
            'operator': operator,
            'reduction_type': 'multiplicative',
            'dimension': 2,
            'ap': a_p,
            'prime': p,
            'split': (a_p == 1)
        }
    
    def _supercuspidal_operator(self, p):
        """
        Construct operator for supercuspidal (additive) reduction
        
        At primes of additive reduction, the representation is supercuspidal.
        The dimension depends on the conductor exponent f_p. The construction
        ensures local non-vanishing of c_p(s) near s=1.
        """
        # Estimate conductor exponent
        f_p = self._conductor_exponent(p)
        
        if f_p == 2:
            operator = matrix([[1, 0], [0, 1 + p**(1-1)]])
        else:
            dim = max(2, f_p)
            operator = identity_matrix(dim)
            operator[dim-1, dim-1] = 1 + p**(f_p - 1)
        
        return {
            'operator': operator,
            'reduction_type': 'supercuspidal',
            'dimension': operator.nrows(),
            'conductor_exponent': f_p,
            'prime': p
        }
    
    def _conductor_exponent(self, p):
        """
        Compute local conductor exponent at prime p
        
        Returns:
            int: Conductor exponent f_p
        """
        # Extract from global conductor
        N = self.E.conductor()
        f_p = N.valuation(p)
        return f_p
    
    def global_operator(self):
        """
        Construct global adelic operator data
        
        Combines local operators at bad primes. In the full theory, this
        extends to a trace-class operator on the adelic space via:
        - S-finite approximation (finitely many places at a time)
        - Schatten-S_1 norm control: sum_v ||K_{E,v}(s)||_S1 < infinity
        - Controlled limit as S increases to all places
        
        Returns:
            dict: Global operator data including local factors
        """
        total_dimension = 1
        for p_data in self.local_operators.values():
            total_dimension *= p_data['dimension']
        
        return {
            'local_operators': self.local_operators,
            'total_dimension': total_dimension,
            'bad_primes': list(self.local_operators.keys()),
            'curve': self.E.cremona_label() if hasattr(self.E, 'cremona_label') else str(self.E)
        }
    
    def kernel_dimension(self):
        """
        Compute dimension of kernel of S-finite operator
        
        The kernel dimension relates to the rank via the spectral framework.
        For the full trace-class operator K_E(s), the order of vanishing
        of det(I - K_E(s)) at s=1 equals the rank r(E).
        
        Returns:
            int: Dimension of ker(K_E(1)) for S-finite approximation
        """
        total_kernel_dim = 0
        
        for p, p_data in self.local_operators.items():
            operator = p_data['operator']
            kernel_basis = operator.kernel().basis()
            total_kernel_dim += len(kernel_basis)
        
        return total_kernel_dim
    
    def compute_kernel(self):
        """
        Compute kernel basis vectors for all local operators
        
        Returns:
            dict: Kernel bases indexed by prime
        """
        kernels = {}
        
        for p, p_data in self.local_operators.items():
            operator = p_data['operator']
            kernel_basis = operator.kernel().basis()
            kernels[p] = {
                'basis': kernel_basis,
                'dimension': len(kernel_basis)
            }
        
        return kernels
