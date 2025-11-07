
def test_spectral_finiteness():
    """
    Test spectral finiteness for well-known curves
    
    EXAMPLES::
    
        sage: from sage.schemes.elliptic_curves.bsd_spectral import test_spectral_finiteness
        sage: test_spectral_finiteness()
        True
    
    TESTS::
    
        sage: E = EllipticCurve('11a1')
        sage: prover = SpectralFinitenessProver(E)
        sage: result = prover.prove_finiteness()
        sage: result['finiteness_proved']
        True
        sage: result['gamma'] > 0
        True
    """
    from sage.schemes.elliptic_curves.bsd_spectral import SpectralFinitenessProver
    
    test_curves = ['11a1', '37a1', '389a1']
    
    for label in test_curves:
        E = EllipticCurve(label)
        prover = SpectralFinitenessProver(E)
        result = prover.prove_finiteness()
        
        if not result['finiteness_proved']:
            return False
        if not result['gamma'] > 0:
            return False
    
    return True
