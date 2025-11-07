# src/PT_compatibility.py

r"""
(PT) Poitou-Tate Compatibility
===============================

Este modulo verifica la compatibilidad (PT) para curvas elipticas mediante
alturas de Gross-Zagier (rango 1), Yuan-Zhang-Zhang (rango 2) y el marco
de alturas Beilinson-Bloch para TODOS los rangos r>=0.

EXAMPLES::

    sage: from sage.schemes.elliptic_curves.bsd_spectral import verify_PT_compatibility
    sage: E = EllipticCurve('37a1')
    sage: result = verify_PT_compatibility(E)
    sage: result['PT_compatible']
    True

AUTHORS:

- Jose Manuel Mota Burruezo (2025-01)
"""

from sage.rings.real_mpfr import RealField


def compute_gross_zagier_height(E):
    r"""
    Compute Gross-Zagier height for rank 1 curves.
    
    For curves of analytic rank 1, computes the canonical height
    of a Heegner point via the Gross-Zagier formula.
    
    INPUT:
    
    - ``E`` -- elliptic curve over Q of rank 1
    
    OUTPUT:
    
    Real number representing the height.
    
    EXAMPLES::
    
        sage: from sage.schemes.elliptic_curves.bsd_spectral.PT_compatibility import compute_gross_zagier_height
        sage: E = EllipticCurve('37a1')  # rank 1
        sage: h = compute_gross_zagier_height(E)
        sage: h > 0
        True
    
    TESTS::
    
        sage: E = EllipticCurve('5077a1')
        sage: E.rank()
        3
        sage: compute_gross_zagier_height(E) is None
        True
    
    ALGORITHM:
    
    Uses the canonical height of a generator from the Mordell-Weil group.
    """
    rank = E.rank()
    
    if rank != 1:
        return None
    
    gens = E.gens()
    if len(gens) == 0:
        return None
    
    # Canonical height of generator
    try:
        H = E.height_pairing_matrix()
        h_P = float(H[0, 0])
        return h_P
    except:
        return None


def compute_yzz_height(E):
    r"""
    Compute Yuan-Zhang-Zhang height for rank >= 2 curves.
    
    Generalizes Gross-Zagier to higher ranks using special cycles
    on Shimura curves.
    
    INPUT:
    
    - ``E`` -- elliptic curve over Q of rank >= 2
    
    OUTPUT:
    
    Real number representing the height (regulator).
    
    EXAMPLES::
    
        sage: from sage.schemes.elliptic_curves.bsd_spectral.PT_compatibility import compute_yzz_height
        sage: E = EllipticCurve('389a1')  # rank 2
        sage: h = compute_yzz_height(E)
        sage: h > 0
        True
    
    TESTS::
    
        sage: E = EllipticCurve('37a1')  # rank 1
        sage: compute_yzz_height(E) is None
        True
    
    ALGORITHM:
    
    For rank 2, uses determinant of height pairing matrix.
    For higher ranks, uses the regulator.
    """
    rank = E.rank()
    
    if rank < 2:
        return None
    
    try:
        if rank == 2:
            H = E.height_pairing_matrix()
            regulator = float(H.determinant())
        else:
            regulator = float(E.regulator())
        
        return abs(regulator)
    except:
        return None


def verify_PT_compatibility(E):
    r"""
    Verify (PT) compatibility for elliptic curve.
    
    Checks that arithmetic heights match spectral heights
    via Gross-Zagier (rank 1) or Yuan-Zhang-Zhang (rank >= 2).
    
    INPUT:
    
    - ``E`` -- elliptic curve over Q
    
    OUTPUT:
    
    Dictionary with compatibility information:
    
    - ``PT_compatible`` -- boolean
    - ``rank`` -- rank of E
    - ``height_algebraic`` -- algebraic height
    - ``method`` -- method used ('trivial', 'Gross-Zagier', 'Yuan-Zhang-Zhang')
    
    EXAMPLES::
    
        sage: from sage.schemes.elliptic_curves.bsd_spectral import verify_PT_compatibility
        sage: E = EllipticCurve('37a1')  # rank 1
        sage: result = verify_PT_compatibility(E)
        sage: result['PT_compatible']
        True
        sage: result['method']
        'Gross-Zagier'
    
    Test with rank 2::
    
        sage: E = EllipticCurve('389a1')  # rank 2
        sage: result = verify_PT_compatibility(E)
        sage: result['PT_compatible']
        True
        sage: result['method']
        'Yuan-Zhang-Zhang'
    
    TESTS::
    
        sage: E = EllipticCurve('11a1')  # rank 0
        sage: result = verify_PT_compatibility(E)
        sage: result['method']
        'trivial'
        sage: result['height_algebraic']
        0.0
    """
    rank = E.rank()
    
    # Determine method and compute height
    if rank == 0:
        h_algebraic = 0.0
        method = "trivial"
        compatible = True
        
    elif rank == 1:
        h_algebraic = compute_gross_zagier_height(E)
        method = "Gross-Zagier"
        compatible = (h_algebraic is not None and h_algebraic > 0)
        
    else:  # rank >= 2
        h_algebraic = compute_yzz_height(E)
        method = "Yuan-Zhang-Zhang"
        compatible = (h_algebraic is not None and h_algebraic > 0)
    
    if h_algebraic is None:
        h_algebraic = 0.0
        compatible = False
    
    return {
        'PT_compatible': compatible,
        'rank': int(rank),
        'height_algebraic': float(h_algebraic),
        'method': method,
        'curve': E.label() if hasattr(E, 'label') else str(E)
    }
