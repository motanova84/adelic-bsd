from sage.all import EllipticCurve
from sage.all import EllipticCurve, QQ, LFunction  # noqa: F401
from mpmath import mp  # noqa: F401
from sympy import symbols  # noqa: F401
import hashlib


def verify_bsd(label_or_curve, s=1):
    """
    Verifica la conjetura BSD para una curva elíptica dada (etiqueta o objeto).

    Args:
        label_or_curve (str | EllipticCurve): Etiqueta LMFDB o curva
        s (float): Punto de evaluación de la función L (default: 1)

    Returns:
        dict: Resultados clave del análisis
    """
    if isinstance(label_or_curve, str):
        E = EllipticCurve(label_or_curve)
    else:
        E = label_or_curve

    L = E.lseries()
    val = L(s)
    analytic_rank = L.analytic_rank()
    conductor = E.conductor()
    sha = hashlib.sha256(str(val).encode()).hexdigest()

    return {
        "curve_label": E.label(),
        "conductor": conductor,
        "L(s)": val,
        "s": s,
        "analytic_rank": analytic_rank,
        "hash_sha256": sha
    }
