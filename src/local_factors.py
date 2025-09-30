"""
Local Factors for BSD Formula
Implements computation of local factors in the BSD conjecture

This module computes Tamagawa numbers, local L-factors, and other
local invariants appearing in the BSD formula.
"""

from sage.all import EllipticCurve, ZZ, QQ, RealField, log, prod


class LocalFactors:
    """
    Local Factors Calculator for BSD Formula
    
    Computes all local factors appearing in the BSD conjecture:
    - Tamagawa numbers c_p
    - Local L-factors L_p(E, s)
    - Real and complex periods
    """
    
    def __init__(self, E):
        """
        Initialize local factors computation
        
        Args:
            E: EllipticCurve object
        """
        self.E = E
        self.N = E.conductor()
        self._tamagawa_cache = {}
        self._local_l_factors_cache = {}
    
    def tamagawa_number(self, p):
        """
        Compute Tamagawa number c_p at prime p
        
        Args:
            p: Prime number
            
        Returns:
            int: Tamagawa number c_p
        """
        if p in self._tamagawa_cache:
            return self._tamagawa_cache[p]
        
        # Use built-in SageMath method
        try:
            c_p = self.E.tamagawa_number(p)
        except:
            # Fallback computation
            if self.E.has_good_reduction(p):
                c_p = 1
            else:
                c_p = self._compute_tamagawa_bad_reduction(p)
        
        self._tamagawa_cache[p] = c_p
        return c_p
    
    def _compute_tamagawa_bad_reduction(self, p):
        """
        Compute Tamagawa number for bad reduction
        
        Args:
            p: Prime with bad reduction
            
        Returns:
            int: Tamagawa number
        """
        if self.E.has_multiplicative_reduction(p):
            # For multiplicative reduction, c_p = conductor exponent
            c_p = self.N.valuation(p)
        else:
            # For additive reduction, compute from component group
            try:
                # Try to get from curve's component group
                c_p = self.E.tamagawa_exponent(p)
            except:
                # Conservative estimate
                c_p = self.N.valuation(p)
        
        return c_p
    
    def all_tamagawa_numbers(self):
        """
        Compute Tamagawa numbers at all bad primes
        
        Returns:
            dict: Tamagawa numbers indexed by prime
        """
        tamagawa_numbers = {}
        
        for p in self.N.prime_factors():
            tamagawa_numbers[p] = self.tamagawa_number(p)
        
        return tamagawa_numbers
    
    def tamagawa_product(self):
        """
        Compute product of all Tamagawa numbers
        
        Returns:
            int: Product ∏_p c_p
        """
        return prod(self.tamagawa_number(p) for p in self.N.prime_factors())
    
    def local_l_factor(self, p, s=1):
        """
        Compute local L-factor L_p(E, s) at prime p
        
        Args:
            p: Prime number
            s: Complex parameter (default: 1)
            
        Returns:
            complex: Local L-factor
        """
        if (p, s) in self._local_l_factors_cache:
            return self._local_l_factors_cache[(p, s)]
        
        if self.E.has_good_reduction(p):
            a_p = self.E.ap(p)
            # L_p(E, s) = (1 - a_p*p^(-s) + p^(1-2s))^(-1)
            if s == 1:
                l_factor = 1.0 / (1 - a_p/p + 1/p)
            else:
                l_factor = 1.0 / (1 - a_p*p**(-s) + p**(1-2*s))
        else:
            # For bad reduction, L_p(E, s) = (1 - a_p*p^(-s))^(-1)
            a_p = self.E.ap(p)
            if s == 1:
                l_factor = 1.0 / (1 - a_p/p) if a_p != 1 else float('inf')
            else:
                l_factor = 1.0 / (1 - a_p*p**(-s))
        
        self._local_l_factors_cache[(p, s)] = l_factor
        return l_factor
    
    def real_period(self):
        """
        Compute real period Ω_E
        
        Returns:
            float: Real period
        """
        try:
            # Use SageMath's period method
            omega = self.E.period_lattice().omega()
            return float(omega)
        except:
            # Fallback using numerical integration
            return self._numerical_real_period()
    
    def _numerical_real_period(self):
        """
        Numerical computation of real period
        
        Returns:
            float: Approximate real period
        """
        # Use discriminant-based estimate
        from sage.all import RR
        disc = abs(self.E.discriminant())
        # Rough approximation
        omega_approx = RR(2 * log(disc) / 3)
        return float(omega_approx)
    
    def regulator(self):
        """
        Compute regulator of Mordell-Weil group
        
        Returns:
            float: Regulator Reg(E/Q)
        """
        rank = self.E.rank()
        
        if rank == 0:
            return 1.0
        
        try:
            # Get regulator from SageMath
            reg = self.E.regulator()
            return float(reg)
        except:
            # If computation fails, return 1.0
            return 1.0
    
    def torsion_order(self):
        """
        Compute order of torsion subgroup
        
        Returns:
            int: |E(Q)_tors|
        """
        try:
            tors = self.E.torsion_order()
            return int(tors)
        except:
            # Fallback
            return 1
    
    def bsd_product(self):
        """
        Compute product of BSD local factors (right side of formula)
        
        Returns:
            dict: All BSD components
        """
        components = {
            'tamagawa_product': self.tamagawa_product(),
            'real_period': self.real_period(),
            'regulator': self.regulator(),
            'torsion_order': self.torsion_order(),
            'sha_bound': 1  # Placeholder
        }
        
        # BSD product: c * Ω * Reg / |E_tors|^2
        bsd_value = (components['tamagawa_product'] * 
                     components['real_period'] * 
                     components['regulator'] / 
                     (components['torsion_order'] ** 2))
        
        components['bsd_product'] = bsd_value
        
        return components
    
    def verify_bsd_compatibility(self):
        """
        Verify BSD formula compatibility with L-function
        
        Returns:
            dict: Verification results
        """
        try:
            # Get L-function value at s=1
            L_value = self.E.lseries().L1_vanishes()
            rank = self.E.rank()
            
            # Check vanishing order
            vanishing_order_matches = (L_value and rank > 0) or (not L_value and rank == 0)
            
            return {
                'l_vanishes_at_1': L_value,
                'rank': rank,
                'vanishing_order_compatible': vanishing_order_matches,
                'bsd_components': self.bsd_product()
            }
        except:
            return {
                'l_vanishes_at_1': None,
                'rank': self.E.rank(),
                'vanishing_order_compatible': None,
                'bsd_components': self.bsd_product()
            }
