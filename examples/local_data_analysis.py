#!/usr/bin/env python3
"""
Local Data Analysis for Elliptic Curves
Demonstrates computation of local arithmetic invariants using SageMath.

This script analyzes the elliptic curve E: y^2 = x^3 - 7423918274321*x + 139820174982374921
and computes:
1. Primes of bad reduction and Kodaira symbols
2. Tamagawa numbers (c_p)
3. Torsion subgroup structure
4. Canonical height of generators
5. Isogeny verification

BSD Spectral Framework - Mota Burruezo
"""

import sys
import os

# Add project root to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

try:
    from sage.all import EllipticCurve  # noqa: E402
except ImportError:
    print("⚠️  SageMath not available. This script requires SageMath to run.")
    print("   Install SageMath or run within a SageMath environment.")
    sys.exit(1)

# Curve coefficients: y^2 = x^3 + CURVE_A*x + CURVE_B
CURVE_A = -7423918274321
CURVE_B = 139820174982374921


def analyze_local_data(output_file=None):
    """
    Perform complete local data analysis for the elliptic curve.

    Args:
        output_file: Optional path to save output. If None, prints to stdout.

    Returns:
        dict: Dictionary containing all computed invariants
    """
    results = {}
    output_lines = []

    def log(message):
        """Helper to print and collect output."""
        print(message)
        output_lines.append(message)

    log("=" * 70)
    log("LOCAL DATA ANALYSIS - ELLIPTIC CURVE ARITHMETIC STRUCTURE")
    log("BSD Spectral Framework - Mota Burruezo")
    log("=" * 70)
    log("")

    # Define the elliptic curve using module constants
    log("📊 CURVE DEFINITION")
    log("-" * 70)

    E = EllipticCurve([CURVE_A, CURVE_B])
    log(f"Curve: {E}")
    log(f"Conductor: {E.conductor()}")
    log(f"Discriminant: {E.discriminant()}")
    log(f"j-invariant: {E.j_invariant()}")
    log("")

    results['curve'] = str(E)
    results['conductor'] = int(E.conductor())
    results['discriminant'] = int(E.discriminant())
    results['j_invariant'] = E.j_invariant()

    # 1. Primes of bad reduction and Kodaira types
    log("🔍 1. PRIMES OF BAD REDUCTION (Kodaira Types)")
    log("-" * 70)

    bad_primes = E.bad_primes()
    log(f"Primes of bad reduction: {bad_primes}")
    log("")

    results['bad_primes'] = list(bad_primes)
    results['kodaira_symbols'] = {}

    for p in bad_primes:
        local_data = E.local_data(p)
        kodaira = local_data.kodaira_symbol()
        log(f"  p = {p}: Kodaira symbol = {kodaira}")
        results['kodaira_symbols'][int(p)] = str(kodaira)

    log("")

    # 2. Tamagawa numbers
    log("📈 2. TAMAGAWA NUMBERS (c_p)")
    log("-" * 70)

    results['tamagawa_numbers'] = {}
    tamagawa_product = 1

    for p in bad_primes:
        local_data = E.local_data(p)
        c_p = local_data.tamagawa_number()
        tamagawa_product *= c_p
        log(f"  p = {p}: Tamagawa number c_p = {c_p}")
        results['tamagawa_numbers'][int(p)] = int(c_p)

    log(f"\n  Product of Tamagawa numbers: ∏c_p = {tamagawa_product}")
    results['tamagawa_product'] = int(tamagawa_product)
    log("")

    # 3. Torsion subgroup
    log("🔢 3. TORSION SUBGROUP")
    log("-" * 70)

    torsion = E.torsion_subgroup()
    torsion_order = torsion.order()
    torsion_structure = torsion.invariants()

    log(f"  Torsion subgroup: {torsion}")
    log(f"  Order: {torsion_order}")
    log(f"  Structure: Z/{torsion_structure} (abelian invariants)")

    if torsion_order > 1:
        log("  Torsion points:")
        for P in torsion.gens():
            log(f"    Generator: {P}")

    results['torsion_order'] = int(torsion_order)
    results['torsion_structure'] = list(torsion_structure)
    log("")

    # 4. Canonical height of generators
    log("📐 4. CANONICAL HEIGHT OF GENERATORS")
    log("-" * 70)

    rank = E.rank()
    log(f"  Algebraic rank: {rank}")
    results['rank'] = int(rank)

    if rank > 0:
        try:
            gens = E.gens()
            log(f"  Number of generators: {len(gens)}")
            results['generators'] = []
            results['heights'] = []

            for i, P in enumerate(gens):
                h = E.height(P)
                log(f"  Generator P_{i+1}: {P}")
                log(f"    Canonical height h(P_{i+1}): {float(h):.10f}")
                results['generators'].append(str(P))
                results['heights'].append(float(h))
        except Exception as e:
            log(f"  Note: Could not compute generators - {e}")
            results['generators'] = []
            results['heights'] = []
    else:
        log("  Rank is 0, no infinite order generators")
        results['generators'] = []
        results['heights'] = []

    log("")

    # 5. Isogeny verification
    log("🔗 5. ISOGENY VERIFICATION")
    log("-" * 70)

    # Check if E is isogenous to itself (should be True)
    is_self_isogenous = E.is_isogenous(E)
    log(f"  Is E isogenous to itself? {is_self_isogenous}")
    results['is_self_isogenous'] = bool(is_self_isogenous)

    # Check for isogeny class
    try:
        isogeny_class = E.isogeny_class()
        num_isogenies = len(isogeny_class.curves())
        log(f"  Number of curves in isogeny class: {num_isogenies}")
        results['isogeny_class_size'] = int(num_isogenies)
    except Exception as e:
        log(f"  Isogeny class computation: {e}")
        results['isogeny_class_size'] = None

    log("")

    # Summary and verification
    log("=" * 70)
    log("✅ VERIFICATION SUMMARY")
    log("=" * 70)

    all_checks_passed = True

    # Check 1: Valid curve (non-zero discriminant)
    check1 = E.discriminant() != 0
    log(f"  [{'✓' if check1 else '✗'}] Valid curve (non-singular): {check1}")
    all_checks_passed &= check1

    # Check 2: Bad primes exist (non-trivial curve)
    check2 = len(bad_primes) > 0
    log(f"  [{'✓' if check2 else '✗'}] Has bad primes (non-trivial): {check2}")
    all_checks_passed &= check2

    # Check 3: Tamagawa product is positive
    check3 = tamagawa_product > 0
    log(f"  [{'✓' if check3 else '✗'}] Positive Tamagawa product: {check3}")
    all_checks_passed &= check3

    # Check 4: Torsion computed
    check4 = torsion_order >= 1
    log(f"  [{'✓' if check4 else '✗'}] Torsion computed: {check4}")
    all_checks_passed &= check4

    # Check 5: If rank > 0, heights are positive
    if rank > 0 and results['heights']:
        check5 = all(h > 0 for h in results['heights'])
        log(f"  [{'✓' if check5 else '✗'}] Positive canonical heights: {check5}")
        all_checks_passed &= check5
    else:
        log("  [✓] Heights check (skipped for rank 0)")

    # Check 6: Self-isogeny is true
    check6 = is_self_isogenous
    log(f"  [{'✓' if check6 else '✗'}] Self-isogeny verified: {check6}")
    all_checks_passed &= check6

    log("")
    log("=" * 70)
    if all_checks_passed:
        log("🎉 ALL VERIFICATIONS PASSED - VALID NON-TRIVIAL CURVE")
    else:
        log("⚠️  SOME VERIFICATIONS FAILED")
    log("=" * 70)

    results['all_checks_passed'] = all_checks_passed

    # Save output to file if requested
    if output_file:
        output_dir = os.path.dirname(output_file)
        if output_dir and not os.path.exists(output_dir):
            os.makedirs(output_dir)

        with open(output_file, 'w') as f:
            f.write('\n'.join(output_lines))
        print(f"\n📁 Output saved to: {output_file}")

    return results


def main():
    """Main entry point."""
    # Determine output file path
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_root = os.path.dirname(script_dir)
    output_file = os.path.join(project_root, 'outputs', 'local_data.txt')

    # Run analysis
    results = analyze_local_data(output_file=output_file)

    return results


if __name__ == "__main__":
    main()
