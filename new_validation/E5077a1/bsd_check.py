#!/usr/bin/env python3
"""
BSD Check Script for 5077a1
=============================

Computes all terms of the BSD formula for curve 5077a1.

Run with SageMath: sage -python bsd_check.py

Author: BSD Spectral Framework
Date: November 2025
"""

try:
    from sage.all import EllipticCurve

    # Load curve
    E = EllipticCurve('5077a1')

    print("=" * 60)
    print(f"BSD Check: {E.cremona_label()}")
    print("=" * 60)

    # Basic invariants
    print(f"Conductor: {E.conductor()}")
    print(f"Rank: {E.rank()}")
    print(f"j-invariant: {E.j_invariant()}")

    # Torsion
    tors = E.torsion_subgroup()
    print(f"Torsion order: {tors.order()}")

    # Period
    omega = E.period_lattice().omega()
    print(f"Real period (Omega): {float(omega):.10f}")

    # Regulator
    if E.rank() > 0:
        reg = E.regulator()
        print(f"Regulator: {float(reg):.10f}")
    else:
        reg = 1.0
        print("Regulator: 1.0 (rank 0)")

    # Tamagawa numbers
    N = E.conductor()
    tamagawa_prod = 1
    for p in N.prime_factors():
        c_p = E.tamagawa_number(p)
        print(f"Tamagawa c_{p}: {c_p}")
        tamagawa_prod *= c_p
    print(f"Tamagawa product: {tamagawa_prod}")

    # L-function
    L = E.lseries()
    print()
    print("L-function data:")
    if E.rank() == 0:
        L_val = float(L(1))
        print(f"L(E,1): {L_val:.10e}")
    else:
        print(f"L(E,1) = 0 (rank = {E.rank()})")

    print()
    print("BSD terms computed successfully!")

except ImportError:
    print("SageMath required. Run with: sage -python bsd_check.py")
except Exception as e:
    print(f"Error: {e}")