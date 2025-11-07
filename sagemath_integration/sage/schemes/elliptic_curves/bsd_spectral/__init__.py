r"""
BSD Spectral Framework
======================

This module implements the spectral-adelic framework for proving
finiteness of Tate-Shafarevich groups and verifying BSD compatibility.

The framework reduces the Birch-Swinnerton-Dyer conjecture to two
explicit compatibility conditions:

- **(dR)** Hodge p-adic compatibility (Fontaine-Perrin-Riou)
- **(PT)** Poitou-Tate compatibility (Gross-Zagier, Yuan-Zhang-Zhang)

EXAMPLES::

    sage: from sage.schemes.elliptic_curves.bsd_spectral import SpectralFinitenessProver
    sage: E = EllipticCurve('11a1')
    sage: prover = SpectralFinitenessProver(E, a=200.84)
    sage: result = prover.prove_finiteness()
    sage: result['finiteness_proved']
    True

Quick verification of compatibility conditions::

    sage: from sage.schemes.elliptic_curves.bsd_spectral import verify_dR_compatibility
    sage: E = EllipticCurve('37a1')
    sage: result = verify_dR_compatibility(E, p=5)
    sage: result['compatible']
    True

AUTHORS:

- José Manuel Mota Burruezo (2025-01): initial version

REFERENCES:

- [JMMB2025] José Manuel Mota Burruezo, "A Complete Spectral Reduction
  of the Birch-Swinnerton-Dyer Conjecture", 2025.
  DOI: 10.5281/zenodo.17236603

- [FPR1995] Fontaine, J.-M., & Perrin-Riou, B. (1995). Autour des conjectures
  de Bloch et Kato: cohomologie galoisienne et valeurs de fonctions L.

- [GZ1986] Gross, B. H., & Zagier, D. B. (1986). Heegner points and
  derivatives of L-series. Inventiones mathematicae, 84(2), 225-320.

- [YZZ2013] Yuan, X., Zhang, S., & Zhang, W. (2013). The Gross-Zagier
  formula on Shimura curves. Princeton University Press.
"""

# Lazy import to avoid circular dependencies
from sage.misc.lazy_import import lazy_import

lazy_import('sage.schemes.elliptic_curves.bsd_spectral.spectral_finiteness',
            'SpectralFinitenessProver')
lazy_import('sage.schemes.elliptic_curves.bsd_spectral.dR_compatibility',
            ['verify_dR_compatibility', 'prove_dR_all_cases'])
lazy_import('sage.schemes.elliptic_curves.bsd_spectral.PT_compatibility',
            ['verify_PT_compatibility', 'prove_PT_all_ranks'])

__all__ = [
    'SpectralFinitenessProver',
    'verify_dR_compatibility',
    'prove_dR_all_cases',
    'verify_PT_compatibility',
    'prove_PT_all_ranks'
]
