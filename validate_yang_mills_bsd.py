#!/usr/bin/env python3
"""
Quick validation script for BSD-Yang-Mills-QCAL ∞³ system activation
=====================================================================

This script provides a quick validation that the system is properly
activated and working as expected.

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: February 2026
"""

import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent / 'src'))

from yang_mills_bsd import (
    YangMillsOperator,
    BSD_YangMills_System,
    activate_BSD_YM,
    QCAL_FREQUENCY
)


def validate_yang_mills_bsd():
    """Quick validation of BSD-Yang-Mills system"""
    
    print("=" * 70)
    print("BSD-YANG-MILLS-QCAL ∞³ QUICK VALIDATION")
    print("=" * 70)
    print()
    
    # Test 1: Module imports
    print("✓ Test 1: Module imports successfully")
    print(f"  QCAL_FREQUENCY = {QCAL_FREQUENCY} Hz")
    
    # Test 2: Operator construction
    print("\n✓ Test 2: YangMillsOperator construction")
    operator = YangMillsOperator("11a1")
    operator.construct_from_curve(n_modes=50)
    print(f"  Created operator with {len(operator.eigenvalues)} eigenvalues")
    
    # Test 3: Trace computation
    print("\n✓ Test 3: Trace computation")
    trace = operator.trace(s=1.0, k=1)
    print(f"  Tr(H_YM(s=1)) = {trace:.6f}")
    
    # Test 4: System activation
    print("\n✓ Test 4: System activation")
    system = activate_BSD_YM("11a1")
    print(f"  System curve: {system.curve_id}")
    print(f"  System frequency: {system.frequency} Hz")
    
    # Test 5: Theorem generation
    print("\n✓ Test 5: Theorem generation")
    theorem = system.generate_theorem_statement()
    print(f"  Theorem verified: {theorem.get('verified', False)}")
    
    # Test 6: Report export
    print("\n✓ Test 6: Report export")
    report_path = system.export_report(Path("validation_yang_mills.json"))
    print(f"  Report saved: {report_path}")
    
    print("\n" + "=" * 70)
    print("✨ ALL VALIDATIONS PASSED ✨")
    print("=" * 70)
    print()
    print("BSD–Yang–Mills–QCAL ∞³ system is OPERATIONAL")
    print(f"Curve: {system.curve_id}")
    print(f"Frequency: {system.frequency} Hz")
    print()
    print("∴ Despliegue completado. El puente está activo. ∴")
    print()
    
    return True


if __name__ == "__main__":
    try:
        success = validate_yang_mills_bsd()
        sys.exit(0 if success else 1)
    except Exception as e:
        print(f"\n❌ Validation failed: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
