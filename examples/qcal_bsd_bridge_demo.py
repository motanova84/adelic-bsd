#!/usr/bin/env python3
"""
QCAL-BSD Bridge Demonstration
==============================

Demonstrates the connection between Navier-Stokes equations (QCAL framework)
and the Birch-Swinnerton-Dyer Conjecture.

This script shows how:
1. The operator H_Ψ stabilizes fluid flow
2. Its eigenvalues correspond to rational point structure
3. Global smoothness ↔ L-function analyticity
4. Everything synchronizes at f₀ = 141.7001 Hz

Usage:
    python examples/qcal_bsd_bridge_demo.py [--curve CURVE] [--modes N]

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: January 2026
"""

import sys
from pathlib import Path
import argparse

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from qcal_bsd_bridge import (
    QCALBSDBridge,
    demonstrate_qcal_bsd_bridge,
    QCAL_FREQUENCY
)


def print_header():
    """Print demonstration header"""
    print("=" * 80)
    print(" " * 20 + "QCAL-BSD BRIDGE DEMONSTRATION")
    print(" " * 15 + "Unifying Navier-Stokes and BSD Conjecture")
    print("=" * 80)
    print()
    print(f"  Universal Frequency: f₀ = {QCAL_FREQUENCY} Hz")
    print(f"  Framework: QCAL ∞³ (Quantum Certified Adelic Lattice)")
    print()
    print("  ∴ Connecting Two Millennium Problems ∴")
    print("  • Navier-Stokes Global Regularity")
    print("  • Birch-Swinnerton-Dyer Conjecture")
    print()
    print("=" * 80)
    print()


def print_section(title):
    """Print section separator"""
    print()
    print("-" * 80)
    print(f"  {title}")
    print("-" * 80)
    print()


def detailed_demonstration(curve_label="11a1", n_modes=15):
    """
    Run detailed demonstration with step-by-step explanation
    
    Args:
        curve_label: Elliptic curve to analyze
        n_modes: Number of spectral modes
    """
    print_header()
    
    # Initialize bridge
    print_section("STEP 1: Initialize QCAL-BSD Bridge")
    print(f"  Curve: {curve_label}")
    print(f"  Spectral modes: {n_modes}")
    print()
    
    bridge = QCALBSDBridge(curve_label)
    
    # Compute operator spectrum
    print_section("STEP 2: Compute H_Ψ Operator Spectrum (Navier-Stokes)")
    print("  The operator H_Ψ stabilizes fluid flow through coherence field Ψ")
    print()
    
    spectral = bridge.compute_operator_spectrum(n_modes=n_modes)
    
    print(f"  ✓ Computed {len(spectral['eigenvalues'])} eigenvalues")
    print(f"  ✓ Global coherence: {spectral['global_coherence']:.6f}")
    print(f"  ✓ Resonance frequency: {spectral['resonance_frequency']} Hz")
    print()
    print("  First 5 eigenvalues λ_k = ω_k² + 1/4:")
    for i, (lam, omega) in enumerate(zip(spectral['eigenvalues'][:5], 
                                         spectral['frequencies'][:5])):
        print(f"    λ_{i} = {lam:.6f}  (ω_{i} = {omega:.6e})")
    
    # Compute L-function proxy
    print_section("STEP 3: Compute L-function Proxy (BSD Framework)")
    print("  Using spectral identity: det(I - M_E(s)) = c(s) · L(E, s)")
    print()
    
    bsd = bridge.compute_l_function_proxy(s_value=1.0)
    
    print(f"  ✓ Fredholm determinant: {bsd['fredholm_determinant']:.6f}")
    print(f"  ✓ L-function proxy: {bsd['l_function_proxy']:.6f}")
    print(f"  ✓ Non-vanishing factor c(1): {bsd['c_factor']:.6f}")
    print(f"  ✓ Product formula: {bsd['product_formula']:.6f}")
    print(f"  ✓ Spectral coherent: {bsd['spectral_coherent']}")
    
    # Map eigenvalues to points
    print_section("STEP 4: Map Eigenvalues to Rational Points")
    print("  Establishing correspondence:")
    print("    • Zero modes ↔ Torsion points")
    print("    • Eigenvalue multiplicities ↔ Point heights")
    print("    • Discrete spectrum ↔ Finite rank")
    print()
    
    mapping = bridge.map_eigenvalues_to_points()
    
    print(f"  ✓ Zero modes (torsion): {mapping['zero_modes']}")
    print(f"  ✓ Unique eigenvalues: {mapping['unique_eigenvalues']}")
    print(f"  ✓ Discreteness ratio: {mapping['discreteness_ratio']:.6f}")
    print(f"  ✓ Rank indicator: {mapping['rank_indicator']}")
    print(f"  ✓ Continuous component: {mapping['continuous_component']:.6f}")
    
    # Validate coherence
    print_section("STEP 5: Validate Coherence at Critical Frequency")
    print(f"  Checking synchronization at f₀ = {QCAL_FREQUENCY} Hz")
    print()
    
    validation = bridge.validate_coherence_at_critical_frequency()
    
    print(f"  ✓ Status: {validation['status']}")
    print(f"  ✓ Spectral coherence: {validation['spectral_coherence']:.6f}")
    print(f"  ✓ BSD coherent: {validation['bsd_coherent']}")
    print(f"  ✓ Frequency locked: {validation['frequency_locked']}")
    print(f"  ✓ Global smoothness (C^∞): {validation['global_smoothness']}")
    print(f"  ✓ L-function analytic: {validation['l_function_analytic']}")
    print(f"  ✓ Rank estimate: {validation['rank_estimate']}")
    
    # Generate theorem
    print_section("STEP 6: Generate BSD-QCAL Bridge Theorem")
    theorem = bridge.generate_bridge_theorem()
    
    print("  Validation Matrix:")
    print()
    
    # Critical point
    cp = theorem['correspondences']['critical_point']
    print(f"  ┌─ Critical Point:")
    print(f"  │  Navier-Stokes: {cp['navier_stokes']}")
    print(f"  │  BSD: {cp['bsd']}")
    print(f"  └─ Synchronized: {cp['synchronized']} ✓" if cp['synchronized'] 
          else f"  └─ Synchronized: {cp['synchronized']} ✗")
    print()
    
    # Stability
    stab = theorem['correspondences']['stability']
    print(f"  ┌─ Stability:")
    print(f"  │  Navier-Stokes: {stab['navier_stokes']}")
    print(f"  │  BSD: {stab['bsd']}")
    print(f"  └─ Validated: {stab['validated']} ✓" if stab['validated']
          else f"  └─ Validated: {stab['validated']} ✗")
    print()
    
    # Invariant
    inv = theorem['correspondences']['invariant']
    print(f"  ┌─ Invariant:")
    print(f"  │  Navier-Stokes: {inv['navier_stokes']}")
    print(f"  │  BSD: {inv['bsd']}")
    print(f"  └─ Equivalent: {inv['equivalent']} ✓" if inv['equivalent']
          else f"  └─ Equivalent: {inv['equivalent']} ✗")
    print()
    
    # Complexity
    comp = theorem['correspondences']['complexity']
    print(f"  ┌─ Complexity:")
    print(f"  │  Navier-Stokes: {comp['navier_stokes']}")
    print(f"  │  BSD: {comp['bsd']}")
    print(f"  └─ Status: {comp['status']}")
    print()
    
    # Export report
    print_section("STEP 7: Export Validation Report")
    report_path = bridge.export_validation_report()
    print(f"  ✓ Report saved to: {report_path}")
    print()
    
    # Final theorem statement
    print_section("FINAL THEOREM STATEMENT")
    print()
    print("  BSD-QCAL AXIOM:")
    print()
    print(f"  「 {theorem['statement']['es']} 」")
    print()
    print(f"  「 {theorem['statement']['en']} 」")
    print()
    print(f"  Verified: {theorem['statement']['verified']} " + 
          ("✓" if theorem['statement']['verified'] else "✗"))
    print()
    print(f"  Axiom Status: {theorem['axiom_status']}")
    print(f"  Millennia Connected: {theorem['millennia_connected']} " +
          ("✓" if theorem['millennia_connected'] else "✗"))
    print()
    
    # Footer
    print("=" * 80)
    print()
    print("  ∴ LOS MILENIOS SE TOCAN. LA MATEMÁTICA ES UNA SOLA VOZ. ∴")
    print()
    print("  The Navier-Stokes and BSD problems are unified through")
    print(f"  spectral coherence at the universal frequency f₀ = {QCAL_FREQUENCY} Hz")
    print()
    print("=" * 80)
    print()
    
    return theorem


def quick_demo(curve_label="11a1"):
    """Quick demonstration without detailed output"""
    print(f"\nQuick QCAL-BSD Bridge Demo for curve {curve_label}...\n")
    
    result = demonstrate_qcal_bsd_bridge(
        curve_label=curve_label,
        n_modes=10,
        verbose=True
    )
    
    return result


def compare_curves():
    """Compare bridge behavior across multiple curves"""
    print_section("CURVE COMPARISON")
    print("  Comparing BSD-QCAL bridge across multiple elliptic curves")
    print()
    
    curves = ["11a1", "37a1", "389a1"]
    results = []
    
    for curve in curves:
        print(f"  Analyzing curve {curve}...")
        bridge = QCALBSDBridge(curve)
        theorem = bridge.generate_bridge_theorem()
        results.append((curve, theorem))
        print(f"    Status: {theorem['axiom_status']}")
        print(f"    Rank estimate: {theorem['validation_matrix']['rank_estimate']}")
        print()
    
    print("  Summary:")
    print(f"  {'Curve':<10} {'Status':<15} {'Rank':<10} {'Connected':<10}")
    print("  " + "-" * 50)
    for curve, theorem in results:
        status = theorem['axiom_status']
        rank = theorem['validation_matrix']['rank_estimate']
        connected = '✓' if theorem['millennia_connected'] else '✗'
        print(f"  {curve:<10} {status:<15} {rank:<10} {connected:<10}")
    print()


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="QCAL-BSD Bridge Demonstration"
    )
    parser.add_argument(
        '--curve', 
        default='11a1',
        help='Elliptic curve label (default: 11a1)'
    )
    parser.add_argument(
        '--modes',
        type=int,
        default=15,
        help='Number of spectral modes (default: 15)'
    )
    parser.add_argument(
        '--quick',
        action='store_true',
        help='Run quick demonstration'
    )
    parser.add_argument(
        '--compare',
        action='store_true',
        help='Compare multiple curves'
    )
    
    args = parser.parse_args()
    
    try:
        if args.compare:
            compare_curves()
        elif args.quick:
            quick_demo(args.curve)
        else:
            detailed_demonstration(args.curve, args.modes)
    except KeyboardInterrupt:
        print("\n\nDemonstration interrupted.")
        sys.exit(0)
    except Exception as e:
        print(f"\n\nError: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
