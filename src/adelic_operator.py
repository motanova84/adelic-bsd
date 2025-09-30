"""
Adelic Operator Implementation
Implements the adelic operator M_E(s) for spectral BSD framework

This module provides the core adelic operator construction that forms
the foundation of the spectral BSD approach.
"""

from sage.all import EllipticCurve, matrix, identity_matrix, ZZ, QQ


class AdelicOperator:
    """
    Adelic Operator M_E(s) for elliptic curves
    
    Constructs the adelic operator from local factors at each prime
    dividing the conductor, providing the spectral framework for BSD.
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
        """Construct operator for good reduction"""
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
        """Construct operator for multiplicative reduction"""
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
        """Construct operator for supercuspidal (additive) reduction"""
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
        Construct global adelic operator as tensor product of local operators
        
        Returns:
            dict: Global operator data
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
        Compute dimension of kernel of global operator
        
        Returns:
            int: Dimension of ker(M_E(1))
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
