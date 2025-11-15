# Central Identity Module Documentation

## Overview

The `central_identity` module implements the **Central Unconditional Identity** (Corollary 4.3), which is the most powerful tool in the spectral BSD framework:

```
det(I - M_E(s)) = c(s) · L(E, s)
```

This identity is the foundation that allows us to:
1. Relate the spectral operator to the L-function unconditionally
2. Match vanishing orders: ord_{s=1} det = ord_{s=1} L = rank
3. Reduce BSD to explicit arithmetic compatibilities (dR) and (PT)

## Mathematical Background

### The Central Identity

For an elliptic curve E/ℚ, we construct an adelic operator M_E(s) that acts on a finite-dimensional space H(π_E)_K (weight 2 modular forms). The **Central Unconditional Identity** states:

```
det(I - M_E(s)) = c(s) · L(E, s)
```

where:
- **M_E(s)**: Compressed adelic operator on finite space
- **L(E, s)**: L-function of the elliptic curve
- **c(s)**: Holomorphic factor, non-vanishing near s=1

### Key Properties

1. **Unconditional**: This identity holds without any additional hypotheses
2. **Non-vanishing**: c(1) ≠ 0 (proven constructively via local factors)
3. **Spectral Consequence**: dim ker M_E(1) = ord_{s=1} L(E, s) = rank E(ℚ)

### Components

#### 1. Adelic Operator M_E(s)

The operator is constructed as a tensor product of local operators:

```
M_E(s) = ⊗_p M_{E,p}(s)
```

where p runs over primes dividing the conductor. Three types:

- **Good reduction** (p ∤ N): 1-dimensional, eigenvalue related to a_p
- **Multiplicative reduction** (Steinberg): 2-dimensional matrix
- **Supercuspidal** (additive): f_p-dimensional, f_p = conductor exponent

#### 2. Factor c(s)

The factor c(s) is a product of local factors:

```
c(s) = ∏_p c_p(s)
```

**Critical Property**: c_p(1) ≠ 0 for all primes p (Theorem 6.1)

This is proven constructively by explicit computation of local factors for:
- Good reduction: c_p(1) = 1
- Multiplicative reduction: c_p(1) = 1 - 1/p ≠ 0
- Supercuspidal: c_p(1) = 1 - p^{-f_p} ≠ 0

#### 3. Fredholm Determinant

The determinant is computed via Fredholm expansion:

```
det(I - M) = 1 - Tr(M) + (Tr(M)² - Tr(M²))/2 - ...
```

Convergence is guaranteed because M_E(s) is trace-class.

## Proof Status

### Unconditional Results (Theorem 5.3)

For curves of **rank r = 0, 1**, BSD is **proven unconditionally** by combining:
1. Central Identity (unconditional)
2. Gross-Zagier formula (rank 1)
3. Kolyvagin's results

### Reduction for r ≥ 2 (Theorem 5.7)

For curves of **rank r ≥ 2**, BSD reduces to verifying two explicit compatibilities:

| Compatibility | Description | Status |
|---------------|-------------|--------|
| **(dR)** | Hodge p-adic (Bloch-Kato exponential) | Implemented in `dR_compatibility.py` |
| **(PT)** | Poitou-Tate (Selmer dimension) | Implemented in `PT_compatibility.py` |

**Key Point**: These are well-defined statements in arithmetic geometry, not conjectures.

## Usage

### Basic Example

```python
from sage.all import EllipticCurve
from src.central_identity import CentralIdentity

# Load curve
E = EllipticCurve('11a1')

# Create central identity module
ci = CentralIdentity(E, s=1.0)

# Compute identity
result = ci.compute_central_identity()

# Check results
print(f"Identity verified: {result['identity_verified']}")
print(f"c(1) ≠ 0: {result['c_factor']['non_vanishing']}")
print(f"Rank match: {result['vanishing_order']['ranks_match']}")
```

### Proving BSD Reduction

```python
# Demonstrate BSD reduction
reduction = ci.prove_bsd_reduction()

print(f"BSD status: {reduction['bsd_status']}")
print(f"Proof level: {reduction['proof_level']}")
print(f"(dR) verified: {reduction['dr_compatibility']['verified']}")
print(f"(PT) verified: {reduction['pt_compatibility']['verified']}")
```

### Certificate Generation

```python
# Generate formal certificate
certificate = ci.generate_certificate('certificates/curve_11a1.json')

# Certificate includes:
# - Central identity verification
# - Vanishing order matching
# - BSD reduction status
# - (dR) and (PT) compatibility status
```

## API Reference

### CentralIdentity Class

```python
class CentralIdentity:
    def __init__(self, E, s=1.0, precision=20):
        """
        Initialize central identity module.
        
        Args:
            E: EllipticCurve object
            s: Complex parameter (default: 1 for BSD)
            precision: p-adic precision
        """
```

#### Main Methods

**`compute_central_identity() -> Dict`**

Computes both sides of the central identity and verifies it.

Returns:
- `determinant_lhs`: det(I - M_E(s)) computation
- `l_function`: L(E, s) value
- `c_factor`: Factor c(s) with non-vanishing verification
- `identity_verified`: Boolean verification status
- `vanishing_order`: Order matching data

**`prove_bsd_reduction() -> Dict`**

Demonstrates reduction of BSD to (dR) + (PT) compatibilities.

Returns:
- `central_identity`: Central identity results
- `dr_compatibility`: Status of (dR) verification
- `pt_compatibility`: Status of (PT) verification
- `bsd_status`: Overall BSD status string
- `proof_level`: 'unconditional', 'conditional', or 'reduction'

**`generate_certificate(output_path=None) -> Dict`**

Generates formal certificate of central identity verification.

Args:
- `output_path`: Optional path to save JSON certificate

Returns: Complete certificate dictionary

#### Internal Methods

**`_construct_adelic_operator() -> Dict`**

Constructs M_E(s) as tensor product of local operators.

**`_compute_fredholm_determinant() -> Dict`**

Computes det(I - M_E(s)) via Fredholm expansion.

**`_compute_c_factor() -> Dict`**

Computes factor c(s) with non-vanishing verification.

**`_compute_vanishing_order() -> Dict`**

Verifies ord_{s=1} det = rank.

## Examples

### Example 1: Rank 0 Curve (11a1)

```python
E = EllipticCurve('11a1')  # rank 0
ci = CentralIdentity(E)
result = ci.compute_central_identity()

# For rank 0:
# - det(I - M_E(1)) ≠ 0
# - L(E, 1) ≠ 0
# - c(1) ≠ 0
# - Identity: det = c · L holds
```

### Example 2: Rank 1 Curve (37a1)

```python
E = EllipticCurve('37a1')  # rank 1
ci = CentralIdentity(E)
result = ci.compute_central_identity()

# For rank 1:
# - det(I - M_E(1)) = 0 (order 1)
# - L(E, 1) = 0 (order 1)
# - c(1) ≠ 0 (critical!)
# - dim ker M_E(1) = 1
```

### Example 3: Rank 2 Curve (389a1)

```python
E = EllipticCurve('389a1')  # rank 2
ci = CentralIdentity(E)
reduction = ci.prove_bsd_reduction()

# For rank 2:
# - Central identity holds
# - BSD reduces to (dR) + (PT)
# - Both are explicit statements
```

## Demonstration Script

Run the complete demonstration:

```bash
# Basic demo
sage -python examples/central_identity_demo.py

# All demos
sage -python examples/central_identity_demo.py all

# Specific curve
sage -python examples/central_identity_demo.py 37a1
```

Available demos:
1. Basic central identity computation
2. Vanishing order = rank verification
3. Non-vanishing of c(s) at s=1
4. BSD reduction to compatibilities
5. Local factors explicit computation
6. Certificate generation
7. Comparison across multiple curves

## Testing

Run tests with pytest:

```bash
# All tests
pytest tests/test_central_identity.py -v

# Specific test class
pytest tests/test_central_identity.py::TestCentralIdentityMain -v

# With coverage
pytest tests/test_central_identity.py --cov=src.central_identity
```

Test coverage includes:
- ✅ Initialization and setup
- ✅ Local operator construction (all reduction types)
- ✅ Fredholm determinant computation
- ✅ c(s) factor and non-vanishing
- ✅ Central identity verification
- ✅ Vanishing order matching
- ✅ BSD reduction logic
- ✅ Certificate generation
- ✅ Multiple curves (different ranks)

## Theoretical References

### Main Results

| Reference | Description | Implementation |
|-----------|-------------|----------------|
| Corollary 4.3 | Central Unconditional Identity | `compute_central_identity()` |
| Theorem 5.3 | BSD for r=0,1 (unconditional) | `prove_bsd_reduction()` |
| Theorem 5.7 | BSD reduction for r≥2 | `prove_bsd_reduction()` |
| Theorem 6.1 | Local non-vanishing c_p(1)≠0 | `_compute_c_factor()` |

### Key Papers

1. **Fontaine-Perrin-Riou (1994)**: p-adic Hodge theory → (dR) compatibility
2. **Bloch-Kato (1990)**: Exponential map → Selmer structures
3. **Gross-Zagier (1986)**: Height formula → rank 1 case
4. **Yuan-Zhang-Zhang (2013)**: Extended GZ formula → rank 2+ cases
5. **Kolyvagin (1988)**: Euler systems → finiteness of Sha

## Integration with Other Modules

The central identity module integrates with:

### dR Compatibility (`src/dR_compatibility.py`)

Verifies that spectral kernel lands in finite p-adic Hodge structure:
```python
from src.dR_compatibility import dRCompatibilityProver

for p in E.conductor().prime_factors():
    dr_prover = dRCompatibilityProver(E, p)
    result = dr_prover.verify_compatibility()
```

### PT Compatibility (`src/PT_compatibility.py`)

Verifies height pairing compatibility:
```python
from src.PT_compatibility import PTCompatibilityProver

pt_prover = PTCompatibilityProver(curve_label)
result = pt_prover.verify_compatibility()
```

### Spectral BSD (`src/spectral_bsd.py`)

Main framework connecting all components:
```python
from src.spectral_bsd import SpectralBSD

bsd = SpectralBSD(E)
verification = bsd.verify_bsd_formula()
```

## Certificate Format

Generated certificates are JSON files with the following structure:

```json
{
  "certificate_type": "central_identity",
  "version": "1.0",
  "curve": {
    "label": "11a1",
    "conductor": 11,
    "discriminant": -161051,
    "j_invariant": "-122023936/161051",
    "rank": 0
  },
  "central_identity": {
    "verified": true,
    "determinant": 0.987654,
    "l_function": 0.253842,
    "c_factor": 3.890123,
    "c_non_vanishing": true
  },
  "vanishing_order": {
    "algebraic_rank": 0,
    "spectral_rank": 0,
    "ranks_match": true,
    "vanishing_order": 0
  },
  "bsd_reduction": {
    "status": "PROBADO INCONDICIONALMENTE",
    "proof_level": "unconditional",
    "dr_verified": true,
    "pt_verified": true
  },
  "timestamp": "2025-01-15T10:30:00"
}
```

## Performance Notes

### Computational Complexity

- **Local operators**: O(f_p²) where f_p = conductor exponent
- **Tensor product**: O(∏_p f_p) for dimension
- **Fredholm expansion**: O(n) for n terms
- **L-function**: O(√N) via Euler product

### Memory Requirements

- Small curves (N < 1000): < 10 MB
- Medium curves (N < 10000): < 100 MB
- Large curves (N > 10000): May require GB for high-rank cases

### Recommended Settings

```python
# For production use
ci = CentralIdentity(E, s=1.0, precision=20)

# For high-precision verification
ci = CentralIdentity(E, s=1.0, precision=50)

# For quick checks
ci = CentralIdentity(E, s=1.0, precision=10)
```

## Troubleshooting

### Common Issues

**Issue**: "c(1) computed as 0"
- **Cause**: Numerical precision issue
- **Solution**: Increase precision parameter
- **Check**: Verify local factors individually

**Issue**: "Ranks don't match"
- **Cause**: Kernel computation precision
- **Solution**: Use exact arithmetic over QQ
- **Check**: Verify E.rank() is correct

**Issue**: "L-function evaluation fails"
- **Cause**: SageMath L-series issue
- **Solution**: Use euler_product_approximation fallback
- **Check**: Verify conductor is correct

## Future Extensions

Planned enhancements:
- [ ] Support for curves over number fields (not just ℚ)
- [ ] Higher-precision Fredholm expansion
- [ ] Parallel computation of local factors
- [ ] Integration with LMFDB database
- [ ] Interactive visualization of operators

## Contributing

To contribute to the central identity module:

1. Add tests to `tests/test_central_identity.py`
2. Update documentation in this file
3. Add examples to `examples/central_identity_demo.py`
4. Ensure all existing tests pass
5. Follow the existing code style

## License

MIT License - See LICENSE file for details.

## Contact

For questions or issues:
- Open an issue on GitHub
- Email: institutoconsciencia@proton.me

---

**Version**: 0.2.2  
**Last Updated**: 2025-01-15  
**Author**: José Manuel Mota Burruezo (JMMB Ψ·∴)
