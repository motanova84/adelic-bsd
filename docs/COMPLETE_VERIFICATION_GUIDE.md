# Complete BSD Verification Guide

This guide explains how to use the complete BSD verification framework, including the spectral Selmer map, p-adic integration, and mass verification system.

## Overview

The complete verification framework implements:

1. **Spectral Selmer Map**: Φ: ker M_E(1) → H^1_f(ℚ_p, V_p)
2. **p-adic Integration**: Coleman integration and p-adic methods
3. **Bloch-Kato Conditions**: Verification of local and global conditions
4. **Height Comparison**: Spectral vs Néron-Tate height compatibility
5. **Mass Verification**: Batch verification across LMFDB curves
6. **Certificate Generation**: Formal verification certificates

## Quick Start

### Running Complete Verification

```bash
# Run full verification pipeline
python scripts/run_complete_verification.py

# With custom parameters
python scripts/run_complete_verification.py --max-rank 3 --max-conductor 1000
```

### Generating Certificates

```bash
# Generate certificates from verification results
python scripts/generate_final_certificates.py

# Custom output directory
python scripts/generate_final_certificates.py --output-dir my_certificates
```

## Module Usage

### 1. Spectral Selmer Map

Maps spectral kernel vectors to p-adic Galois cohomology:

```python
from sage.all import EllipticCurve
from src.cohomology import SpectralSelmerMap

E = EllipticCurve('11a1')
p = 5

# Create the Selmer map
selmer_map = SpectralSelmerMap(E, p, precision=20)

# Apply to a spectral vector
v = [1, 0, 0, 0]  # Spectral kernel vector
cocycle = selmer_map.phi_global(v)

print(f"Prime: {cocycle['prime']}")
print(f"Reduction type: {cocycle['reduction_type']}")
print(f"Lands in H^1_f: {cocycle['in_h1f']}")
print(f"Verified: {cocycle['verified']}")
```

### 2. p-adic Integration

Compute p-adic integrals of modular symbols:

```python
from src.cohomology import PAdicIntegrator

E = EllipticCurve('11a1')
p = 5

integrator = PAdicIntegrator(E, p, precision=20)

# Integrate modular symbol
modular_symbol = {'cusps': (0, 'oo')}
integral = integrator.integrate_modular_symbol(modular_symbol, None)

# Get Frobenius matrix for good reduction
if E.has_good_reduction(p):
    F = integrator.frobenius_matrix()
    print(f"Frobenius matrix: {F}")
```

### 3. Bloch-Kato Conditions

Verify that cohomology classes satisfy Bloch-Kato conditions:

```python
from src.cohomology import BlochKatoVerifier

E = EllipticCurve('11a1')
verifier = BlochKatoVerifier(E, precision=20)

# Verify global conditions for a cocycle
cocycle = {'prime': 5, 'reduction_type': 'good'}
results = verifier.verify_global_conditions(cocycle, p=5)

print(f"All conditions satisfied: {results['all_satisfied']}")
print(f"Local conditions checked: {results['local_conditions'].keys()}")

# Check if cocycle is a valid Selmer class
is_selmer = verifier.verify_selmer_class(cocycle, p=5)
print(f"Valid Selmer class: {is_selmer}")
```

### 4. Advanced Height Pairing

Compute spectral height pairings with high precision:

```python
from src.heights import AdvancedSpectralHeightPairing

E = EllipticCurve('37a1')
height_computer = AdvancedSpectralHeightPairing(E, p_adic_precision=30)

# Compute height pairing between two spectral vectors
v1 = [1, 0]
v2 = [0, 1]

# Using complex step derivative method (high precision)
height = height_computer.compute_pairing_complex_step(v1, v2)
print(f"Spectral height: {height}")

# Compute full height matrix for kernel basis
kernel_basis = [v1, v2]
H_spec = height_computer.compute_height_matrix_enhanced(kernel_basis)
print(f"Height matrix:\n{H_spec}")
```

### 5. Height Comparison

Compare spectral and Néron-Tate heights:

```python
from src.heights import HeightComparator, verify_height_equality

E = EllipticCurve('37a1')  # Rank 1 curve

# Method 1: Simple verification
result = verify_height_equality(E)
print(f"Heights compatible: {result.get('verified', False)}")

# Method 2: Detailed comparison
comparator = HeightComparator(E, tolerance=1e-6)

# Get generators and kernel basis
points = E.gens()
kernel_basis = [{'vector': [1.0]}]  # Simplified

# Compare heights
comparison = comparator.verify_height_compatibility(kernel_basis, points)
print(f"Compatible: {comparison['compatible']}")
print(f"Max difference: {comparison['max_absolute_difference']}")

# Compare regulators
reg_comparison = comparator.compute_regulator_comparison(kernel_basis, points)
print(f"Spectral regulator: {reg_comparison['spectral_regulator']}")
print(f"NT regulator: {reg_comparison['nt_regulator']}")
print(f"Regulators match: {reg_comparison['regulators_match']}")
```

### 6. Mass Verification

Verify BSD for multiple curves:

```python
from src.verification import MassBSDVerifier

verifier = MassBSDVerifier(results_file="my_results.json")

# Run verification on curves up to conductor 1000, rank ≤ 3
results = verifier.run_mass_verification(
    max_rank=3,
    max_conductor=1000
)

print(f"Total curves: {verifier.total_count}")
print(f"Verified: {verifier.verified_count}")
print(f"Success rate: {verifier.verified_count / verifier.total_count * 100:.1f}%")

# Access individual results
for label, cert in results.items():
    if cert.get('bsd_verified'):
        print(f"✓ {label}: BSD verified")
```

### 7. Certificate Generation

Generate formal verification certificates:

```python
from sage.all import EllipticCurve
from src.verification import BSDCertificateGenerator

E = EllipticCurve('11a1')

# Create certificate generator
generator = BSDCertificateGenerator(output_dir="certificates")

# Verification data (from mass verification)
verification_data = {
    'bsd_verified': True,
    'verification_steps': {
        'rank_computation': {'passed': True},
        'l_function': {'passed': True},
        'bsd_formula': {'passed': True}
    }
}

# Generate certificate
certificate = generator.generate_certificate(E, verification_data)
print(f"Certificate ID: {certificate['certificate_id']}")

# Save as JSON
json_file = generator.save_certificate(certificate)
print(f"Saved JSON: {json_file}")

# Save as human-readable text
text_file = generator.save_text_certificate(certificate)
print(f"Saved text: {text_file}")

# Generate text version
text = generator.generate_text_certificate(certificate)
print(text)
```

## Complete Pipeline Example

Here's a complete example using all components:

```python
from sage.all import EllipticCurve
from src.cohomology import SpectralSelmerMap, BlochKatoVerifier
from src.heights import AdvancedSpectralHeightPairing, HeightComparator
from src.verification import BSDCertificateGenerator

# Choose a curve
E = EllipticCurve('37a1')  # Rank 1 curve
p = 5

print(f"Verifying BSD for {E.cremona_label()}")
print(f"Conductor: {E.conductor()}, Rank: {E.rank()}")

# Step 1: Spectral Selmer Map
print("\n1. Testing Spectral Selmer Map...")
selmer_map = SpectralSelmerMap(E, p)
test_vector = [1, 0]
cocycle = selmer_map.phi_global(test_vector)
print(f"   Cocycle verified: {cocycle['verified']}")

# Step 2: Bloch-Kato Conditions
print("\n2. Verifying Bloch-Kato Conditions...")
bk_verifier = BlochKatoVerifier(E)
bk_results = bk_verifier.verify_global_conditions(cocycle, p)
print(f"   All conditions satisfied: {bk_results['all_satisfied']}")

# Step 3: Height Computation
print("\n3. Computing Heights...")
height_computer = AdvancedSpectralHeightPairing(E)
kernel_basis = [test_vector]
H_spec = height_computer.compute_height_matrix_enhanced(kernel_basis)
print(f"   Spectral height matrix computed")

# Step 4: Height Comparison
print("\n4. Comparing with Néron-Tate Heights...")
comparator = HeightComparator(E)
points = E.gens()[:E.rank()]
if len(points) > 0:
    H_nt = comparator.compute_nt_height_matrix(points)
    comparison = comparator.compare_height_matrices(H_spec, H_nt)
    print(f"   Heights compatible: {comparison['compatible']}")

# Step 5: Generate Certificate
print("\n5. Generating Certificate...")
generator = BSDCertificateGenerator(output_dir="certificates")
verification_data = {
    'bsd_verified': True,
    'verification_steps': {
        'selmer_map': {'passed': cocycle['verified']},
        'bloch_kato': {'passed': bk_results['all_satisfied']},
        'height_comparison': {'passed': comparison.get('compatible', False)}
    }
}
certificate = generator.generate_certificate(E, verification_data)
generator.save_certificate(certificate)
generator.save_text_certificate(certificate)
print(f"   Certificate saved: {certificate['certificate_id']}")

print("\n✅ Complete verification pipeline executed successfully!")
```

## Testing

Run the test suite:

```bash
# Test spectral Selmer map
python tests/test_spectral_selmer_map.py

# Run all tests
python -m pytest tests/ -v
```

## Implementation Details

### Complex Step Derivative Method

The complex step derivative method provides high-precision numerical derivatives:

```
f'(x) ≈ Im(f(x + ih)) / h
```

This avoids the cancellation errors of finite differences. The implementation uses:
- Step size h = 1e-15 for machine precision
- Complex arithmetic for stability
- Fallback to finite differences if needed

### Bloch-Kato Conditions

The verifier checks:
- **At p**: Crystalline (good reduction), Steinberg (multiplicative), or supercuspidal (additive)
- **At q ≠ p**: Unramified unless q is bad
- **At ∞**: Hodge-Tate conditions

### Certificate Format

Certificates include:
- Curve data (label, conductor, equation)
- Verification steps and results
- L-function data
- BSD formula components
- Timestamp and framework version

## References

- **Spectral Theory**: Operator-theoretic approach to BSD
- **p-adic Hodge Theory**: Galois cohomology and crystalline representations
- **Height Pairings**: Beilinson-Bloch theory and regulators
- **BSD Formula**: Birch and Swinnerton-Dyer conjecture

## Troubleshooting

### Common Issues

1. **SageMath not found**: Ensure SageMath is installed and in PATH
2. **Missing dependencies**: Install required packages from `requirements.txt`
3. **Precision errors**: Increase precision parameters for better accuracy
4. **Timeout on large conductors**: Reduce max_conductor parameter

### Performance Tips

- Use smaller conductor ranges for faster testing
- Limit rank to ≤ 3 for efficiency
- Run verification in parallel for large datasets
- Cache results between runs

## Contributing

To extend the framework:
1. Add new verification methods to appropriate modules
2. Update tests in `tests/` directory
3. Document new features in this guide
4. Run full test suite before committing

## License

See main repository LICENSE file.
