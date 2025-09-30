# Spectral→Cycles→Points Algorithm Guide

## Overview

This guide explains the new algorithmic capabilities for connecting spectral vectors to rational points on elliptic curves, implementing the theoretical framework described in the problem statement.

## 🎯 Core Algorithms

### Algorithm 1: Spectral Vectors → Modular Symbols

Converts spectral vectors from ker M_E(1) to modular symbols using the Manin-Merel theorem.

**Theory**: Modular symbols generate H¹(X₀(N), ℤ).

**Implementation**:
```python
from sage.all import EllipticCurve
from src.spectral_cycles import SpectralCycleConstructor

E = EllipticCurve('11a1')
constructor = SpectralCycleConstructor(E)

# Given a spectral vector v
MS_data = constructor.spectral_vector_to_modular_symbol(v)
```

### Algorithm 2: Modular Symbols → Cycles in Jacobian

Constructs cycles in the Jacobian J₀(N) from modular symbols.

**Methods**:
- **Method A**: Integration (numerical)
- **Method B**: Hecke operators (more robust)

**Implementation**:
```python
cycle_data = constructor.modular_symbol_to_cycle(MS_data)
```

### Algorithm 3: Cycles → Rational Points on E

Projects cycles to rational points using the modular parametrization Φ: X₀(N) → E.

**Implementation**:
```python
point_data = constructor.cycle_to_rational_point(cycle_data, E)
P = point_data['point']

# Verify P is on curve
assert P in E
assert P.is_rational()
```

## 🔗 Main Pipeline

The complete algorithm connecting spectral kernel to rational points:

```python
from src.spectral_cycles import (
    compute_kernel_basis,
    spectral_kernel_to_rational_points
)

# Step 1: Compute kernel of M_E(1)
kernel_basis = compute_kernel_basis(E)

# Step 2: Convert to rational points
points = spectral_kernel_to_rational_points(kernel_basis, E)

# Points correspond to generators of E(ℚ) (conjecturally)
for p_data in points:
    P = p_data['point']
    print(f"Point: {P}")
```

## 📐 Height Pairing Verification

### Computing Spectral Height Matrix

The spectral height pairing is defined as:
⟨v_i, v_j⟩_spec = Res_{s=1} Tr(v_i* M_E'(s) v_j)

```python
from src.height_pairing import compute_spectral_height_matrix

H_spec = compute_spectral_height_matrix(kernel_basis, E)
print(f"Spectral height matrix:\n{H_spec}")
```

### Computing Néron-Tate Height Matrix

The Néron-Tate canonical height pairing:

```python
from src.height_pairing import compute_nt_height_matrix

H_nt = compute_nt_height_matrix(points)
print(f"Néron-Tate height matrix:\n{H_nt}")
```

### Verifying Compatibility

The crucial test: ⟨·,·⟩_spec = ⟨·,·⟩_NT

```python
from src.height_pairing import verify_height_compatibility

result = verify_height_compatibility(E)

if result['compatible']:
    print("✓ Height pairing compatibility VERIFIED")
else:
    print("⚠ Height pairing compatibility PENDING")
```

## 🌐 Large-Scale LMFDB Verification

### Single Curve Verification

```python
from src.lmfdb_verification import large_scale_verification

# Test curves with conductor 11-50, rank 0-2
results = large_scale_verification(
    conductor_range=(11, 50),
    rank_range=[0, 1, 2],
    limit=20,
    verbose=True
)

print(f"Success rate: {results['success_rate']:.1f}%")
```

### Batch Processing

```python
# Process many curves
curves = ["11a1", "14a1", "15a1", "17a1", "19a1", "37a1"]

from src.height_pairing import batch_verify_height_compatibility

results = batch_verify_height_compatibility(curves)
```

### Generate Report

```python
from src.lmfdb_verification import generate_verification_report

report = generate_verification_report(
    results,
    output_file='verification_report.txt'
)
print(report)
```

## 🚀 Quick Start Examples

### Example 1: Complete Pipeline

```python
from sage.all import EllipticCurve
from src.spectral_cycles import demonstrate_spectral_to_points

# Run complete demonstration
result = demonstrate_spectral_to_points('11a1')
```

### Example 2: Step-by-Step

```python
from sage.all import EllipticCurve
from src.spectral_cycles import compute_kernel_basis, spectral_kernel_to_rational_points
from src.height_pairing import verify_height_compatibility

E = EllipticCurve('37a1')

# 1. Compute kernel
print("Computing spectral kernel...")
kernel_basis = compute_kernel_basis(E)
print(f"Kernel dimension: {len(kernel_basis)}")

# 2. Convert to points
print("\nConverting to rational points...")
points = spectral_kernel_to_rational_points(kernel_basis, E)

# 3. Verify height compatibility
print("\nVerifying height pairing...")
compat = verify_height_compatibility(E)

print(f"\nCompatible: {compat['compatible']}")
```

### Example 3: Using Demo Script

```bash
# Run all demonstrations
sage -python examples/spectral_to_points_demo.py all

# Run specific demo
sage -python examples/spectral_to_points_demo.py single 11a1
sage -python examples/spectral_to_points_demo.py height 37a1
sage -python examples/spectral_to_points_demo.py lmfdb
```

## 📊 Expected Results

### Success Metrics

For curves tested from the LMFDB:

1. **Kernel Computation**: Should match known rank
2. **Point Generation**: Should produce valid points on curve
3. **Height Compatibility**: Should verify within numerical tolerance
4. **LMFDB Consistency**: Should align with known Ш bounds

### Interpretation

- ✅ **Compatible**: ⟨·,·⟩_spec = ⟨·,·⟩_NT verified
- ⚠️ **Pending**: Numerical computation needs refinement
- ✗ **Error**: Implementation issue (rare)

## 🔬 Theoretical Background

### Key Theorems

1. **Manin-Merel**: Modular symbols generate H¹(X₀(N), ℤ)
2. **Modular Parametrization**: Φ: X₀(N) → E exists for all elliptic curves (Taylor-Wiles)
3. **Height Compatibility**: Conjectural equality of spectral and arithmetic heights

### Conjectural Framework

The algorithm assumes:

- **(dR)** Local p-adic Hodge landing
- **(PT)** Spectral Beilinson-Bloch compatibility

See [`BSD_FRAMEWORK.md`](BSD_FRAMEWORK.md) for complete details.

## 🧪 Testing

Run tests for the new modules:

```bash
sage -python -m pytest tests/test_spectral_cycles.py -v
```

Or run tests manually:

```bash
sage -python tests/test_spectral_cycles.py
```

## 📚 API Reference

### Main Classes

- `SpectralCycleConstructor`: Core class for algorithm implementation
- `SpectralFinitenessProver`: Original finiteness proof class

### Main Functions

**Spectral Cycles:**
- `spectral_kernel_to_rational_points(kernel_basis, E)`
- `compute_kernel_basis(E)`
- `demonstrate_spectral_to_points(curve_label)`

**Height Pairing:**
- `compute_spectral_height_matrix(kernel_basis, E)`
- `compute_nt_height_matrix(points)`
- `verify_height_compatibility(E)`
- `batch_verify_height_compatibility(curve_labels)`

**LMFDB Verification:**
- `large_scale_verification(conductor_range, rank_range, limit, verbose)`
- `generate_verification_report(verification_data, output_file)`
- `get_lmfdb_curves(conductor_range, rank_range, limit)`

## 🎓 Further Reading

- Main README: [`../README.md`](../README.md)
- Usage Guide: [`../USAGE.md`](../USAGE.md)
- Theoretical Framework: [`BSD_FRAMEWORK.md`](BSD_FRAMEWORK.md)
- Contributing: [`../CONTRIBUTING.md`](../CONTRIBUTING.md)

## 💡 Tips

1. **Start Small**: Test with low-conductor curves (11, 14, 15) first
2. **Check Rank**: Algorithm works best for rank ≤ 3
3. **Numerical Precision**: Height computations are numerical, expect small errors
4. **Large Scale**: Use `limit` parameter to control batch size
5. **Verbose Output**: Set `verbose=True` for detailed progress

## ⚠️ Limitations

- Height pairing computation is numerical (not exact)
- Modular parametrization may be expensive for large conductor
- Full theoretical verification depends on (dR) and (PT) compatibilities
- Some curves may require additional computational resources

---

**Last Updated**: 2025  
**Version**: 0.1.0  
**Author**: José Manuel Mota Burruezo
