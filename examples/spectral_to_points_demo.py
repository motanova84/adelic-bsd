"""
Demonstration of Spectral->Cycles->Points Algorithm

This script demonstrates the complete algorithmic pipeline:
1. Spectral kernel computation
2. Conversion to modular symbols
3. Construction of cycles in Jacobian
4. Projection to rational points
5. Height pairing verification
6. LMFDB validation
"""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from sage.all import EllipticCurve
from src.spectral_cycles import (
    demonstrate_spectral_to_points,
    spectral_kernel_to_rational_points,
    compute_kernel_basis
)
from src.height_pairing import (
    verify_height_compatibility,
    batch_verify_height_compatibility,
    compute_spectral_height_matrix,
    compute_nt_height_matrix
)
from src.lmfdb_verification import (
    large_scale_verification,
    generate_verification_report,
    quick_verification_demo
)


def demo_single_curve(curve_label="11a1"):
    """
    Demonstrate the algorithm for a single curve
    """
    print("\n" + "="*70)
    print(f"DEMO 1: SINGLE CURVE ANALYSIS ({curve_label})")
    print("="*70)
    
    # Full demonstration
    result = demonstrate_spectral_to_points(curve_label)
    
    return result


def demo_height_pairing(curve_label="11a1"):
    """
    Demonstrate height pairing computation and verification
    """
    print("\n" + "="*70)
    print(f"DEMO 2: HEIGHT PAIRING VERIFICATION ({curve_label})")
    print("="*70)
    
    E = EllipticCurve(curve_label)
    result = verify_height_compatibility(E)
    
    return result


def demo_multiple_curves():
    """
    Demonstrate verification on multiple curves
    """
    print("\n" + "="*70)
    print("DEMO 3: MULTIPLE CURVES VERIFICATION")
    print("="*70)
    
    test_curves = ["11a1", "14a1", "15a1", "17a1", "19a1"]
    results = batch_verify_height_compatibility(test_curves)
    
    return results


def demo_lmfdb_verification():
    """
    Demonstrate large-scale LMFDB verification
    """
    print("\n" + "="*70)
    print("DEMO 4: LMFDB LARGE-SCALE VERIFICATION")
    print("="*70)
    
    # Run verification on curves with conductor <= 30
    results = large_scale_verification(
        conductor_range=(11, 30),
        rank_range=[0, 1],  # Start with rank 0 and 1
        limit=10,  # Test 10 curves
        verbose=True
    )
    
    # Generate report
    print("\n" + "="*70)
    print("GENERATING VERIFICATION REPORT")
    print("="*70)
    
    report = generate_verification_report(results)
    print("\n" + report)
    
    return results


def demo_algorithmic_steps():
    """
    Demonstrate individual algorithmic steps
    """
    print("\n" + "="*70)
    print("DEMO 5: ALGORITHMIC STEPS BREAKDOWN")
    print("="*70)
    
    curve_label = "11a1"
    E = EllipticCurve(curve_label)
    
    print(f"\nCurve: {E}")
    print(f"Conductor: {E.conductor()}")
    print(f"Rank: {E.rank()}")
    
    # Step 1: Compute kernel
    print("\n--- Step 1: Spectral Kernel Computation ---")
    kernel_basis = compute_kernel_basis(E)
    print(f"Kernel dimension: {len(kernel_basis)}")
    for i, v in enumerate(kernel_basis):
        if isinstance(v, dict):
            print(f"  v_{i}: dimension={v.get('dimension', '?')}, prime={v.get('prime', '?')}")
        else:
            print(f"  v_{i}: {v}")
    
    # Step 2: Convert to points
    print("\n--- Step 2: Spectral->Points Conversion ---")
    points = spectral_kernel_to_rational_points(kernel_basis, E)
    print(f"Points generated: {len(points)}")
    for p_data in points:
        P = p_data['point']
        if not P.is_zero():
            print(f"  P_{p_data['index']}: ({P[0]}, {P[1]})")
        else:
            print(f"  P_{p_data['index']}: O (identity)")
    
    # Step 3: Compute height matrices
    print("\n--- Step 3: Height Matrix Computation ---")
    H_spec = compute_spectral_height_matrix(kernel_basis, E)
    H_nt = compute_nt_height_matrix(points)
    
    print(f"\nSpectral height matrix H_spec:")
    print(H_spec)
    
    print(f"\nNéron-Tate height matrix H_nt:")
    print(H_nt)
    
    # Step 4: Compare
    print("\n--- Step 4: Compatibility Check ---")
    if H_spec.nrows() > 0 and H_nt.nrows() > 0:
        from sage.all import matrix, RR
        H_spec_rr = matrix(RR, H_spec)
        diff = H_spec_rr - H_nt
        max_diff = max([abs(diff[i,j]) for i in range(diff.nrows()) 
                       for j in range(diff.ncols())])
        print(f"Maximum difference: {max_diff}")
        print(f"Compatible: {max_diff < 1e-6}")
    
    return {
        'kernel_basis': kernel_basis,
        'points': points,
        'H_spec': H_spec,
        'H_nt': H_nt
    }


def run_all_demos():
    """
    Run all demonstration scripts
    """
    print("\n" + "="*70)
    print("SPECTRAL->CYCLES->POINTS COMPLETE DEMONSTRATION")
    print("="*70)
    print("\nThis demonstration implements the algorithmic strategy")
    print("from the problem statement:")
    print("  - Spectral vectors -> Modular symbols")
    print("  - Modular symbols -> Cycles in Jacobian")
    print("  - Cycles -> Rational points on E")
    print("  - Height pairing verification")
    print("  - Large-scale LMFDB validation")
    print("="*70)
    
    results = {}
    
    # Demo 1: Single curve
    try:
        results['single_curve'] = demo_single_curve("11a1")
    except Exception as e:
        print(f"\n✗ Demo 1 failed: {e}")
        results['single_curve'] = {'error': str(e)}
    
    # Demo 2: Height pairing
    try:
        results['height_pairing'] = demo_height_pairing("11a1")
    except Exception as e:
        print(f"\n✗ Demo 2 failed: {e}")
        results['height_pairing'] = {'error': str(e)}
    
    # Demo 3: Multiple curves
    try:
        results['multiple_curves'] = demo_multiple_curves()
    except Exception as e:
        print(f"\n✗ Demo 3 failed: {e}")
        results['multiple_curves'] = {'error': str(e)}
    
    # Demo 4: LMFDB verification (skip if too slow)
    try:
        results['lmfdb'] = demo_lmfdb_verification()
    except Exception as e:
        print(f"\n✗ Demo 4 failed: {e}")
        results['lmfdb'] = {'error': str(e)}
    
    # Demo 5: Step-by-step
    try:
        results['steps'] = demo_algorithmic_steps()
    except Exception as e:
        print(f"\n✗ Demo 5 failed: {e}")
        results['steps'] = {'error': str(e)}
    
    # Final summary
    print("\n" + "="*70)
    print("DEMONSTRATION COMPLETE")
    print("="*70)
    print("\nAll algorithms have been demonstrated.")
    print("See individual demo results above for details.")
    print("="*70)
    
    return results


if __name__ == "__main__":
    # Check command line arguments
    if len(sys.argv) > 1:
        demo_name = sys.argv[1]
        
        if demo_name == "single":
            curve = sys.argv[2] if len(sys.argv) > 2 else "11a1"
            demo_single_curve(curve)
        elif demo_name == "height":
            curve = sys.argv[2] if len(sys.argv) > 2 else "11a1"
            demo_height_pairing(curve)
        elif demo_name == "multiple":
            demo_multiple_curves()
        elif demo_name == "lmfdb":
            demo_lmfdb_verification()
        elif demo_name == "steps":
            demo_algorithmic_steps()
        elif demo_name == "all":
            run_all_demos()
        else:
            print(f"Unknown demo: {demo_name}")
            print("Available demos: single, height, multiple, lmfdb, steps, all")
    else:
        # Run all demos by default
        run_all_demos()
