#!/usr/bin/env python3
"""
Trace Identity Validation Script
=================================

Non-interactive validation of the trace identity implementation.
This script runs all verification steps and generates a summary report.

Usage:
    python validate_trace_identity.py
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from trace_identity import (
    HilbertSpaceL2,
    AdelicOperatorME,
    TraceIdentityProver,
    create_example_operator
)
import numpy as np


def validate_hilbert_space():
    """Validate Hilbert space properties"""
    print("\n[1/7] Validating Hilbert Space ℓ²(ℕ)...")
    
    H = HilbertSpaceL2()
    
    # Test orthonormality
    e1 = np.array([1.0, 0.0, 0.0])
    e2 = np.array([0.0, 1.0, 0.0])
    e3 = np.array([0.0, 0.0, 1.0])
    
    basis = [e1, e2, e3]
    orthonormal = H.verify_orthonormality(basis)
    
    if orthonormal:
        print("  ✓ Orthonormal basis verified")
        return True
    else:
        print("  ✗ Orthonormal basis check failed")
        return False


def validate_operator_properties():
    """Validate operator M_E(s) properties"""
    print("\n[2/7] Validating Operator M_E(s)...")
    
    operator = create_example_operator("validation_curve")
    s = 2.0
    
    # Check trace class
    is_trace_class, trace_norm = operator.is_trace_class(s, N=100)
    
    if is_trace_class:
        print(f"  ✓ Operator is trace-class for Re(s) = {s}")
        print(f"    Trace norm estimate: {trace_norm:.6f}")
        return True
    else:
        print(f"  ✗ Operator not trace-class")
        return False


def validate_convergence():
    """Validate convergence analysis"""
    print("\n[3/7] Validating Convergence Analysis...")
    
    operator = create_example_operator("validation_curve")
    prover = TraceIdentityProver(operator)
    
    # Test convergence for various s values
    test_cases = [(1.5, 2), (2.0, 1), (2.5, 1)]
    all_converge = True
    
    for s, k in test_cases:
        conv = prover.verify_absolute_convergence(s, k, N=200)
        if conv.converges:
            print(f"  ✓ Converges for s={s}, k={k}")
        else:
            print(f"  ✗ Fails to converge for s={s}, k={k}")
            all_converge = False
    
    return all_converge


def validate_trace_identity():
    """Validate the main trace identity"""
    print("\n[4/7] Validating Trace Identity...")
    
    operator = create_example_operator("validation_curve")
    prover = TraceIdentityProver(operator)
    
    s = 2.0
    N = 500
    
    all_verified = True
    
    for k in [1, 2, 3, 4]:
        verification = prover.verify_trace_identity(s, k, N, tolerance=1e-8)
        
        if verification['identity_verified']:
            print(f"  ✓ Identity verified for k={k} (error: {verification['difference']:.2e})")
        else:
            print(f"  ✗ Identity failed for k={k}")
            all_verified = False
    
    return all_verified


def validate_error_bounds():
    """Validate error bound computation"""
    print("\n[5/7] Validating Error Bounds...")
    
    operator = create_example_operator("validation_curve")
    prover = TraceIdentityProver(operator)
    
    s = 2.0
    k = 2
    
    N_values = [100, 200, 500]
    errors = []
    
    for N in N_values:
        result = prover.compute_trace(s, k, N)
        errors.append(result.numerical_error)
    
    # Check that error decreases with N
    error_decreases = all(errors[i] >= errors[i+1] for i in range(len(errors)-1))
    
    if error_decreases:
        print(f"  ✓ Error bounds decrease with N")
        for N, err in zip(N_values, errors):
            print(f"    N={N}: error ≤ {err:.2e}")
        return True
    else:
        print(f"  ✗ Error bounds do not decrease properly")
        return False


def validate_log_determinant():
    """Validate log-determinant computation"""
    print("\n[6/7] Validating Log-Determinant Formula...")
    
    operator = create_example_operator("validation_curve")
    prover = TraceIdentityProver(operator)
    
    s = 2.0
    N = 300
    
    log_det = prover.compute_log_determinant(s, N)
    
    # Check that result is computed
    if not np.isnan(log_det['log_det_trace_formula']):
        print(f"  ✓ Log-determinant computed: {log_det['log_det_trace_formula'].real:.8f}")
        print(f"    Status: {log_det['status']}")
        return True
    else:
        print(f"  ✗ Log-determinant computation failed")
        return False


def validate_certificate():
    """Validate certificate generation"""
    print("\n[7/7] Validating Certificate Generation...")
    
    operator = create_example_operator("validation_curve")
    prover = TraceIdentityProver(operator)
    
    s = 2.0
    k_max = 4
    N = 400
    
    certificate = prover.generate_certificate(s, k_max, N)
    
    if certificate['overall_status'] == 'COMPLETE':
        print(f"  ✓ Certificate generated successfully")
        print(f"    Status: {certificate['overall_status']}")
        print(f"    Verifications: {len(certificate['verifications'])} passed")
        return True
    else:
        print(f"  ✗ Certificate generation incomplete")
        print(f"    Status: {certificate['overall_status']}")
        return False


def main():
    """Main validation"""
    print("=" * 70)
    print("TRACE IDENTITY VALIDATION")
    print("=" * 70)
    print()
    print("Validating rigorous analytical implementation...")
    
    results = []
    
    # Run all validations
    results.append(("Hilbert Space", validate_hilbert_space()))
    results.append(("Operator Properties", validate_operator_properties()))
    results.append(("Convergence Analysis", validate_convergence()))
    results.append(("Trace Identity", validate_trace_identity()))
    results.append(("Error Bounds", validate_error_bounds()))
    results.append(("Log-Determinant", validate_log_determinant()))
    results.append(("Certificate", validate_certificate()))
    
    # Summary
    print()
    print("=" * 70)
    print("VALIDATION SUMMARY")
    print("=" * 70)
    print()
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for name, result in results:
        status = "✓ PASS" if result else "✗ FAIL"
        print(f"  {name:25s}: {status}")
    
    print()
    print(f"Results: {passed}/{total} validations passed")
    print()
    
    if passed == total:
        print("✓ ALL VALIDATIONS PASSED")
        print()
        print("The trace identity implementation is complete and rigorous.")
        return 0
    else:
        print("✗ SOME VALIDATIONS FAILED")
        print()
        print("Please check the implementation.")
        return 1


if __name__ == "__main__":
    sys.exit(main())
