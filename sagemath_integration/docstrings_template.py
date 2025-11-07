
r"""
BSD Spectral Framework for Elliptic Curves

This module implements the spectral-adelic framework for the
Birch-Swinnerton-Dyer conjecture, reducing it to explicit
compatibility statements.

EXAMPLES::

    sage: from sage.schemes.elliptic_curves.bsd_spectral import SpectralFinitenessProver
    sage: E = EllipticCurve('11a1')
    sage: prover = SpectralFinitenessProver(E)
    sage: result = prover.prove_finiteness()
    sage: result['finiteness_proved']
    True

REFERENCES:

- [JMMB2025] José Manuel Mota Burruezo, "A Complete Spectral Reduction
  of the Birch-Swinnerton-Dyer Conjecture", 2025.
- [FPR1995] Fontaine, Perrin-Riou, "Autour des conjectures de Bloch et Kato", 1995.
- [YZZ2013] Yuan, Zhang, Zhang, "The Gross-Zagier Formula on Shimura Curves", 2013.

AUTHORS:

- José Manuel Mota Burruezo (2025-01): initial version
"""
