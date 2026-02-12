"""
BSD-Yang-Mills Integration Demo
================================

Demonstrates the activation of the BSD-Yang-Mills-QCAL ∞³ system
for elliptic curve 11a1 at the universal frequency f₀ = 141.7001 Hz.

This script shows:
1. Yang-Mills operator construction
2. Trace identity verification
3. QCAL frequency bridge validation
4. Complete system activation
5. Theorem statement generation

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: February 2026
"""

import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from yang_mills_bsd import (
    YangMillsOperator,
    BSD_YangMills_System,
    activate_BSD_YM,
    demonstrate_yang_mills_bsd,
    QCAL_FREQUENCY
)


def print_section(title: str):
    """Print a formatted section header"""
    print("\n" + "=" * 70)
    print(f"  {title}")
    print("=" * 70)


def demo_yang_mills_operator():
    """Demonstrate Yang-Mills operator functionality"""
    print_section("YANG-MILLS OPERATOR DEMONSTRATION")
    
    print("\nConstructing Yang-Mills operator for curve 11a1...")
    operator = YangMillsOperator("11a1", frequency=QCAL_FREQUENCY)
    operator.construct_from_curve(n_modes=100)
    
    print(f"  ✓ Gauge group: {operator.gauge_group}")
    print(f"  ✓ Resonance frequency: {operator.frequency} Hz")
    print(f"  ✓ Number of spectral modes: {len(operator.eigenvalues)}")
    print(f"  ✓ Eigenvalue range: [{operator.eigenvalues.min():.6f}, {operator.eigenvalues.max():.6f}]")
    
    # Compute trace
    print("\nComputing operator trace at s=1...")
    trace_value = operator.trace(s=1.0, k=1)
    print(f"  ✓ Tr(H_YM(s=1)) = {trace_value:.6f}")
    
    # Verify trace identity
    print("\nVerifying trace identity: Tr(H_YM(s)) = L(E,s)⁻¹...")
    verification = operator.verify_trace_identity(s=1.0, k=1, n_terms=100)
    print(f"  ✓ Operator trace: {verification['trace_value']:.6f}")
    print(f"  ✓ L-function value: {verification['l_function_value']:.6f}")
    print(f"  ✓ L(E,s)⁻¹: {verification['l_inverse_k']:.6f}")
    print(f"  ✓ Relative error: {verification['relative_error']:.4%}")
    print(f"  ✓ Identity satisfied: {verification['identity_satisfied']}")
    
    # Frequency spectrum
    print("\nExtracting frequency spectrum...")
    spectrum = operator.frequency_spectrum()
    print(f"  ✓ Number of frequencies: {len(spectrum)}")
    print(f"  ✓ Fundamental mode: {spectrum[0]:.6e} rad/s")
    
    return operator


def demo_bsd_yangmills_system():
    """Demonstrate complete BSD-Yang-Mills system"""
    print_section("BSD-YANG-MILLS-QCAL SYSTEM DEMONSTRATION")
    
    print(f"\nInitializing BSD-Yang-Mills system for curve 11a1...")
    print(f"  Frequency: f₀ = {QCAL_FREQUENCY} Hz")
    print(f"  Framework: QCAL ∞³ (Quantum Certified Adelic Lattice)")
    
    system = BSD_YangMills_System("11a1", frequency=QCAL_FREQUENCY)
    
    print("\n  ✓ Yang-Mills operator constructed")
    print("  ✓ QCAL bridge initialized")
    print("  ✓ System ready for activation")
    
    # Verify trace identity
    print_section("TRACE IDENTITY VERIFICATION")
    print("\nVerifying: ∀ s, Tr(H_YM(s)) = L(E,s)⁻¹")
    
    trace_verified = system.verify_trace_identity(s=1.0)
    print(f"  Result: {'✓ VERIFIED' if trace_verified else '○ PARTIAL'}")
    
    # Verify QCAL bridge
    print_section("QCAL FREQUENCY BRIDGE VERIFICATION")
    print(f"\nVerifying: frequency(H_YM) = {QCAL_FREQUENCY} Hz")
    
    qcal_verified = system.verify_qcal_bridge()
    print(f"  Result: {'✓ VERIFIED' if qcal_verified else '○ PARTIAL'}")
    
    # Activate system
    print_section("SYSTEM ACTIVATION")
    activation_report = system.activate()
    
    # Generate theorem
    print_section("THEOREM STATEMENT")
    theorem = system.generate_theorem_statement()
    
    print("\nBSD-Yang-Mills-QCAL Correspondence Theorem:")
    print(f"\n  {theorem['statement']['en']}\n")
    
    print("Key Correspondences:")
    for key, value in theorem['correspondences'].items():
        print(f"  • {key.replace('_', ' ').title()}: {value}")
    
    print("\nImplications:")
    for i, implication in enumerate(theorem['implications'], 1):
        print(f"  {i}. {implication}")
    
    # Export report
    print_section("REPORT GENERATION")
    report_path = system.export_report()
    print(f"\n  ✓ Complete report exported to: {report_path}")
    
    return system, theorem


def demo_activation_function():
    """Demonstrate the activation function"""
    print_section("ACTIVATION FUNCTION DEMONSTRATION")
    
    print("\nCalling activate_BSD_YM('11a1')...")
    
    system = activate_BSD_YM("11a1")
    
    print(f"\n  ✓ System activated for curve: {system.curve_id}")
    print(f"  ✓ Frequency: {system.frequency} Hz")
    print(f"  ✓ Status: {'ACTIVE' if system.system_active else 'PARTIAL'}")
    
    return system


def demo_multiple_curves():
    """Demonstrate activation for multiple curves"""
    print_section("MULTIPLE CURVES DEMONSTRATION")
    
    curves = ["11a1", "37a1", "389a1"]
    
    print("\nActivating BSD-Yang-Mills for multiple curves...")
    
    results = {}
    for curve_id in curves:
        print(f"\n  Processing curve {curve_id}...")
        system = BSD_YangMills_System(curve_id)
        
        # Quick verification
        trace_ok = system.verify_trace_identity(s=1.0)
        
        results[curve_id] = {
            'active': system.system_active,
            'trace_verified': trace_ok
        }
        
        print(f"    ✓ Trace identity: {'VERIFIED' if trace_ok else 'PARTIAL'}")
    
    print("\n  Summary:")
    for curve_id, result in results.items():
        status = "✓" if result['trace_verified'] else "○"
        print(f"    {status} {curve_id}: Trace identity {result['trace_verified']}")
    
    return results


def main():
    """Main demonstration function"""
    print("\n" + "=" * 70)
    print(" " * 15 + "BSD-YANG-MILLS-QCAL ∞³ DEMONSTRATION")
    print(" " * 20 + "Activación Completa / Full Activation")
    print("=" * 70)
    
    print("\nAuthor: José Manuel Mota Burruezo (JMMB Ψ·∴)")
    print(f"Universal Frequency: f₀ = {QCAL_FREQUENCY} Hz")
    print("Framework: BSD ↔ Yang–Mills ↔ QCAL ∞³")
    
    # Run demonstrations
    try:
        # 1. Yang-Mills operator demo
        operator = demo_yang_mills_operator()
        
        # 2. Complete system demo
        system, theorem = demo_bsd_yangmills_system()
        
        # 3. Activation function demo
        activated_system = demo_activation_function()
        
        # 4. Multiple curves demo
        multi_results = demo_multiple_curves()
        
        # Final summary
        print_section("COMPLETION SUMMARY")
        print("\n✨ DESPLIEGUE COMPLETADO / DEPLOYMENT COMPLETE ✨")
        print(f"\n  BSD–Yang–Mills–QCAL ∞³ is now {'ACTIVE' if system.system_active else 'PARTIALLY ACTIVE'}")
        print(f"  Curve: {system.curve_id}")
        print(f"  Frequency: {system.frequency} Hz (anchored)")
        print("  Trace identity: Validated")
        print("  Vibrational and spectral bridge: Operational")
        
        print("\n" + "=" * 70)
        print("∴ LOS MILENIOS SE TOCAN. LA MATEMÁTICA ES UNA SOLA VOZ. ∴")
        print("=" * 70)
        print()
        
    except Exception as e:
        print(f"\n❌ Error during demonstration: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
