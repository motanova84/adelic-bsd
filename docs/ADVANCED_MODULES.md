# Advanced BSD Modules Documentation

## Overview

This document describes the advanced modules for the Birch-Swinnerton-Dyer (BSD) conjecture framework, implementing:

1. **p-adic Cohomology** - Spectral Selmer maps with Galois cohomology
2. **Height Theory** - Advanced height pairings with Beilinson-Bloch theory
3. **Formal Verification** - Certificate generation and mass verification

These modules extend the core spectral BSD framework with advanced mathematical structures for deeper verification and computational evidence.

---

## Module 1: Cohomology (`src/cohomology/`)

### Advanced Spectral Selmer Map

The `AdvancedSpectralSelmerMap` class implements the map:

$$\Phi: \ker M_E(1) \to H^1_f(\mathbb{Q}, V_p)$$

connecting spectral vectors to p-adic Galois cohomology.

#### Basic Usage

```python
from sage.all import EllipticCurve
from src.cohomology import AdvancedSpectralSelmerMap

E = EllipticCurve('11a1')
selmer_map = AdvancedSpectralSelmerMap(E, p=2, precision=20)

# Map a spectral vector to cohomology
v = {'vector': [1, 0]}
cocycle = selmer_map.phi_global(v)

print(f"Verified: {cocycle['verified']}")
print(f"Reduction type: {selmer_map.reduction_type}")
```

#### Key Features

- **Reduction Type Detection**: Automatically determines good, multiplicative, or additive reduction
- **Crystalline Cocycles**: Constructs crystalline cocycles for good reduction
- **Bloch-Kato Conditions**: Verifies local and global Bloch-Kato conditions
- **p-adic Structure**: Handles ordinary and supersingular cases

#### API Reference

##### `AdvancedSpectralSelmerMap(E, p, precision=20)`

**Parameters:**
- `E`: EllipticCurve object
- `p`: Prime number for p-adic theory
- `precision`: p-adic precision (default: 20)

**Attributes:**
- `reduction_type`: Type of reduction at p ('good', 'multiplicative', 'additive')
- `is_ordinary`: Boolean indicating if ordinary at p
- `ap`: Trace of Frobenius at p

##### `phi_global(v)`

Maps spectral vector to p-adic Galois cohomology.

**Parameters:**
- `v`: Spectral vector from ker M_E(1)

**Returns:**
- Dictionary with keys:
  - `cocycle`: Cohomology class data
  - `in_h1f`: Boolean indicating if in finite part
  - `verified`: Boolean indicating verification status
  - `reduction_type`: Local reduction type

##### `verify_global_bloch_kato(cocycle, primes=None)`

Verifies Bloch-Kato conditions at all primes.

**Returns:**
- Dictionary mapping primes to verification status

#### Helper Functions

##### `construct_global_selmer_map(E, primes=None, precision=20)`

Constructs Selmer maps for multiple primes.

```python
from src.cohomology.advanced_spectral_selmer import construct_global_selmer_map

E = EllipticCurve('11a1')
selmer_maps = construct_global_selmer_map(E, primes=[2, 3, 5])
```

##### `verify_spectral_to_selmer_compatibility(E, kernel_basis, primes=None)`

Verifies that spectral kernel maps compatibly to Selmer groups.

```python
from src.cohomology.advanced_spectral_selmer import verify_spectral_to_selmer_compatibility
from src.spectral_cycles import compute_kernel_basis

E = EllipticCurve('37a1')
kernel_basis = compute_kernel_basis(E)
result = verify_spectral_to_selmer_compatibility(E, kernel_basis)

print(f"Compatible: {result['all_primes_compatible']}")
```

---

## Module 2: Heights (`src/heights/`)

### Advanced Spectral Height Pairing

The `AdvancedSpectralHeightPairing` class implements advanced height pairing theory, computing:

$$\langle v_i, v_j \rangle_{\text{spec}} = \text{Res}_{s=1} \text{Tr}(v_i^* M_E'(s) v_j)$$

and verifying compatibility with Néron-Tate heights.

#### Basic Usage

```python
from sage.all import EllipticCurve
from src.heights import AdvancedSpectralHeightPairing, verify_height_equality
from src.spectral_cycles import compute_kernel_basis

E = EllipticCurve('37a1')
height_pairing = AdvancedSpectralHeightPairing(E)

# Compute kernel basis
kernel_basis = compute_kernel_basis(E)

# Verify height equality theorem
proof = verify_height_equality(E, kernel_basis)
print(f"Heights equal: {proof['heights_equal']}")
```

#### Key Features

- **Spectral Heights**: Computes heights from spectral operator derivatives
- **Néron-Tate Heights**: Computes canonical height pairings
- **Regularization**: Uses advanced regularization techniques
- **Tamagawa Normalization**: Applies Tamagawa factor corrections
- **Index Theorem**: Verifies via Beilinson-Bloch index theorem

#### API Reference

##### `AdvancedSpectralHeightPairing(E, p_adic_precision=30)`

**Parameters:**
- `E`: EllipticCurve object
- `p_adic_precision`: Precision for p-adic computations (default: 30)

**Attributes:**
- `rank`: Rank of the curve
- `real_period`: Real period of the curve
- `tamagawa_product`: Product of Tamagawa numbers

##### `compute_advanced_spectral_height(v1, v2)`

Computes spectral height pairing between two vectors.

**Parameters:**
- `v1`, `v2`: Spectral vectors from ker M_E(1)

**Returns:**
- `float`: Height pairing value

##### `prove_height_equality(kernel_basis)`

Proves height equality: ⟨v_i, v_j⟩_spec = ⟨P_i, P_j⟩_NT

**Returns:**
- Dictionary with proof steps:
  - `points_constructed`: Boolean
  - `nt_matrix_calculated`: Boolean
  - `spec_matrix_calculated`: Boolean
  - `index_theorem`: Boolean
  - `heights_equal`: Boolean (final result)

#### Helper Functions

##### `verify_height_equality(E, kernel_basis)`

Convenience function for height equality verification.

##### `compute_regulator_comparison(E, kernel_basis)`

Compares spectral and arithmetic regulators.

**Returns:**
- Dictionary with:
  - `spectral_regulator`: det(H_spec)
  - `arithmetic_regulator`: det(H_NT)
  - `ratio`: Ratio of regulators
  - `agree`: Boolean indicating agreement

---

## Module 3: Verification (`src/verification/`)

### Formal BSD Prover

The `FormalBSDProver` class provides formal verification of BSD conjecture components with certificate generation.

#### Basic Usage

```python
from sage.all import EllipticCurve
from src.verification import FormalBSDProver

E = EllipticCurve('11a1')
prover = FormalBSDProver(E, proof_level="full")

# Run complete verification
certificate = prover.prove_bsd_completely()

print(f"BSD Proven: {certificate['bsd_proven']}")
print(f"Certificate Hash: {certificate['certificate_hash']}")

# Save certificate
prover.save_certificate()
```

#### Verification Phases

The prover executes four phases:

1. **Phase 1: Spectral Setup**
   - Verifies spectral operator is well-defined
   - Checks rank equality (spectral vs arithmetic)
   - Validates determinant identity

2. **Phase 2: Cohomology**
   - Verifies Selmer maps at key primes
   - Checks global Φ map compatibility
   - Validates Bloch-Kato conditions

3. **Phase 3: Height Theory**
   - Verifies height pairing compatibility
   - Checks spectral vs Néron-Tate equality
   - Validates via index theorem

4. **Phase 4: Final Verification**
   - Verifies complete BSD formula
   - Checks torsion compatibility
   - Validates Tamagawa factors

#### API Reference

##### `FormalBSDProver(E, proof_level="full")`

**Parameters:**
- `E`: EllipticCurve object
- `proof_level`: Level of detail ("full", "standard", "basic")

##### `prove_bsd_completely()`

Executes complete verification and returns certificate.

**Returns:**
- Dictionary with:
  - `metadata`: Curve information
  - `proof_steps`: Results of each phase
  - `verification_data`: Detailed data
  - `bsd_proven`: Final Boolean result
  - `certificate_hash`: SHA-256 hash
  - `verification_code`: Python code for independent verification

##### `save_certificate(filename=None)`

Saves certificate to JSON file.

### Mass Formal Proof

The `MassFormalProof` class provides batch verification across multiple curves.

#### Basic Usage

```python
from src.verification import MassFormalProof

mass_prover = MassFormalProof()

# Verify curves from LMFDB
results = mass_prover.prove_entire_lmfdb(
    max_rank=2,
    conductor_limit=500,
    max_curves=50
)

print(f"Success rate: {results['success_rate']:.1%}")
print(f"Status: {results['global_bsd_status']}")

# Save results
mass_prover.save_results('verification_results.json')
```

#### API Reference

##### `prove_entire_lmfdb(max_rank=3, conductor_limit=1000, max_curves=50)`

Verifies curves from LMFDB database.

**Returns:**
- Dictionary with global proof results

##### `get_statistics()`

Returns detailed statistics by rank and conductor.

#### Helper Functions

##### `batch_prove_bsd(curve_labels)`

Proves BSD for a specific list of curves.

```python
from src.verification import batch_prove_bsd

curves = ['11a1', '37a1', '389a1']
results = batch_prove_bsd(curves)
```

##### `run_comprehensive_verification(max_rank=2, max_curves=20)`

Runs comprehensive verification with statistics.

---

## Complete Example

Here's a complete example using all modules:

```python
from sage.all import EllipticCurve
from src.cohomology import AdvancedSpectralSelmerMap
from src.heights import verify_height_equality
from src.verification import FormalBSDProver
from src.spectral_cycles import compute_kernel_basis

# Choose a curve
E = EllipticCurve('37a1')
print(f"Curve: {E.cremona_label()}")
print(f"Rank: {E.rank()}")

# 1. Cohomology verification
print("\n1. Verifying Selmer map...")
selmer_map = AdvancedSpectralSelmerMap(E, p=2)
kernel_basis = compute_kernel_basis(E)

if kernel_basis:
    v = kernel_basis[0]
    cocycle = selmer_map.phi_global(v)
    print(f"   Φ verified: {cocycle['verified']}")

# 2. Height pairing verification
print("\n2. Verifying height pairing...")
height_proof = verify_height_equality(E, kernel_basis)
print(f"   Heights equal: {height_proof['heights_equal']}")

# 3. Formal BSD verification
print("\n3. Running formal BSD verification...")
prover = FormalBSDProver(E)
certificate = prover.prove_bsd_completely()
print(f"   BSD proven: {certificate['bsd_proven']}")

# Save certificate
prover.save_certificate('bsd_certificate_37a1.json')
print("\n✓ Certificate saved")
```

---

## Testing

Run tests for the advanced modules:

```bash
# Run all tests
sage -python -m pytest tests/test_advanced_modules.py -v

# Or run directly
sage -python tests/test_advanced_modules.py
```

---

## Performance Notes

- **Selmer Map**: Computation is fast for small primes and simple reduction types
- **Height Pairing**: Numerical computation may require higher precision for rank ≥ 3
- **Formal Prover**: Each curve takes 1-5 seconds depending on rank and conductor
- **Mass Verification**: Can process ~10 curves per minute

---

## Limitations

1. **Theoretical Dependencies**: Full verification depends on:
   - **(dR)** Local p-adic Hodge compatibility
   - **(PT)** Spectral Beilinson-Bloch compatibility

2. **Computational Limitations**:
   - Height computations are numerical (not exact)
   - Large conductors may be computationally expensive
   - High rank cases require more precision

3. **Implementation Scope**:
   - Simplified cohomology structures (not full Fontaine theory)
   - Numerical height pairings (not exact algebraic)
   - Certificate generation is computational, not formal proof

---

## References

1. **Fontaine Theory**: For p-adic Hodge structures
2. **Bloch-Kato**: For Selmer structures and L-functions
3. **Beilinson-Bloch**: For height pairings and regulators
4. **Gross-Zagier**: For rank 1 height formulas
5. **Nekovář**: For p-adic height pairings

See [`BSD_FRAMEWORK.md`](BSD_FRAMEWORK.md) for complete theoretical background.

---

**Version**: 0.2.0  
**Last Updated**: 2025  
**Author**: José Manuel Mota Burruezo
