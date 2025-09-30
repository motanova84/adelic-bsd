# Usage Guide - Spectral Finiteness Framework

## Quick Start Guide

### 1. Basic Usage

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

# Create an elliptic curve
E = EllipticCurve('11a1')  # Curve label from Cremona database

# Initialize prover
prover = SpectralFinitenessProver(E)

# Prove finiteness
result = prover.prove_finiteness()

# Check result
print(f"Finiteness proved: {result['finiteness_proved']}")
print(f"Global bound: {result['global_bound']}")
```

### 2. Generate Certificates

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('37a1')
prover = SpectralFinitenessProver(E)

# Generate text certificate
cert = prover.generate_certificate('text')
print(cert)

# Save to file
with open('certificate_37a1.txt', 'w') as f:
    f.write(cert)

# Generate LaTeX certificate
cert_latex = prover.generate_certificate('latex')
with open('certificate_37a1.tex', 'w') as f:
    f.write(cert_latex)

# Generate JSON certificate
cert_json = prover.generate_certificate('json')
with open('certificate_37a1.json', 'w') as f:
    f.write(cert_json)
```

### 3. Batch Processing

```python
from src.spectral_finiteness import batch_prove_finiteness

# Process multiple curves at once
curves = ['11a1', '14a1', '15a1', '17a1', '19a1', '20a1']
results = batch_prove_finiteness(curves)

# Display summary
for label, result in results.items():
    if 'error' not in result:
        bound = result['global_bound']
        conductor = result['spectral_data']['conductor']
        print(f"{label}: N={conductor}, #Ш ≤ {bound}")
    else:
        print(f"{label}: Error - {result['error']}")
```

### 4. Examining Spectral Data

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('11a1')
prover = SpectralFinitenessProver(E)
result = prover.prove_finiteness()

# Examine local data for each bad prime
for p, data in result['spectral_data']['local_data'].items():
    print(f"\nPrime p = {p}:")
    print(f"  Reduction type: {data['reduction_type']}")
    print(f"  Operator M_{{E,{p}}}(1):")
    print(f"    {data['operator']}")
    print(f"  Kernel dimension: {data['kernel_dim']}")
    print(f"  Local bound: {data['torsion_bound']}")
```

## Advanced Usage

### Working with Spectral Operators

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('14a1')
prover = SpectralFinitenessProver(E)

# Get bad primes
bad_primes = E.conductor().prime_factors()
print(f"Bad primes: {bad_primes}")

# Construct operators for each prime
for p in bad_primes:
    M_p = prover.construct_spectral_operator(p, s=1)
    print(f"\nM_{{E,{p}}}(1) = ")
    print(M_p)
    
    # Compute kernel
    kernel_dim = prover.compute_kernel_dimension(M_p)
    print(f"dim ker(M_{{E,{p}}}(1)) = {kernel_dim}")
```

### Verifying the Spectral BSD Identity

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('11a1')
prover = SpectralFinitenessProver(E)

# Compute spectral determinant
s = 1
spectral_det = prover.compute_spectral_determinant(s)
print(f"det(I - M_E(1)) = {spectral_det}")

# Get L-function value
L_value = E.lseries().at1()
print(f"L(E,1) = {L_value}")

# Compute correction factor
c1 = prover.compute_c1()
print(f"c(1) = {c1}")

# Verify identity: det(I - M_E(1)) = c(1) · L(E,1)
if L_value != 0:
    ratio = spectral_det / L_value
    print(f"\nRatio det/L = {ratio}")
    print(f"Expected c(1) = {c1}")
    print(f"Match: {abs(ratio - c1) < 1e-6}")
```

### Comparing with Known Results

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('11a1')
prover = SpectralFinitenessProver(E)
result = prover.prove_finiteness()

# Try to get known Sha value from database
try:
    known_sha = E.sha().an()
    print(f"Known #Ш = {known_sha}")
    print(f"Our bound = {result['global_bound']}")
    print(f"Bound valid: {result['global_bound'] >= known_sha}")
except:
    print("Sha value not available in database")
```

### Working with Curves of Large Conductor

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

# Curve with larger conductor
E = EllipticCurve('389a1')  # Conductor 389

prover = SpectralFinitenessProver(E)
result = prover.prove_finiteness()

print(f"Conductor: {result['spectral_data']['conductor']}")
print(f"Number of bad primes: {len(result['spectral_data']['local_data'])}")
print(f"Global bound: {result['global_bound']}")

# Generate certificate
cert = prover.generate_certificate('text')
with open('certificate_389a1.txt', 'w') as f:
    f.write(cert)
```

## Using Individual Modules

### Spectral Operator Module

```python
from sage.all import EllipticCurve
from src.spectral_operator import SpectralOperatorBuilder

E = EllipticCurve('11a1')
builder = SpectralOperatorBuilder(E)

# Construct operator at a specific prime
p = 11
M_11 = builder.construct_operator(p, s=1)
print(f"Operator at p={p}:")
print(M_11)

# Compute spectral determinant
spectral_det = builder.compute_spectral_determinant(s=1)
print(f"Spectral determinant: {spectral_det}")
```

### Kernel Computation Module

```python
from sage.all import EllipticCurve
from src.spectral_operator import construct_spectral_operator
from src.kernel_computation import KernelAnalyzer, compute_kernel_dimension

E = EllipticCurve('14a1')
analyzer = KernelAnalyzer(E)

# Get operators for all bad primes
local_operators = {}
for p in E.conductor().prime_factors():
    local_operators[p] = construct_spectral_operator(E, p)

# Analyze kernels
for p, M_p in local_operators.items():
    analysis = analyzer.analyze_local_kernel(p, M_p)
    print(f"Prime {p}:")
    print(f"  Kernel dim: {analysis['kernel_dimension']}")
    print(f"  Operator rank: {analysis['operator_rank']}")

# Verify discreteness
verification = analyzer.verify_discreteness(local_operators)
print(f"\nDiscrete: {verification['is_discrete']}")
print(f"Total kernel dimension: {verification['total_kernel_dimension']}")
```

### Global Bound Module

```python
from sage.all import EllipticCurve
from src.global_bound import GlobalBoundComputer, compute_global_bound

E = EllipticCurve('15a1')
computer = GlobalBoundComputer(E)

# Compute local bounds
local_bounds = computer.compute_local_bounds_data()
print("Local bounds:")
for p, b_p in local_bounds.items():
    print(f"  b_{p} = {b_p}")

# Compute global bound
B = computer.compute_global_bound()
print(f"\nGlobal bound: B = {B}")

# Get detailed data
detailed = computer.compute_detailed_bound_data()
print(f"Formula: {detailed['bound_formula']}")
```

### Certificate Generator Module

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver
from src.certificate_generator import CertificateGenerator

E = EllipticCurve('11a1')
prover = SpectralFinitenessProver(E)
result = prover.prove_finiteness()

generator = CertificateGenerator(E)

# Generate different formats
text_cert = generator.generate_text_certificate(result)
latex_cert = generator.generate_latex_certificate(result)
json_cert = generator.generate_json_certificate(result)

# Save certificates
with open('cert_11a1.txt', 'w') as f:
    f.write(text_cert)
    
with open('cert_11a1.tex', 'w') as f:
    f.write(latex_cert)
    
with open('cert_11a1.json', 'w') as f:
    f.write(json_cert)
```

## Running Examples

### Example Scripts

1. **Quick Demo**: `python examples/quick_demo.py`
   - Analyzes 8 sample curves
   - Shows summary statistics
   - Compares with known results

2. **Comprehensive Demo**: `python spectral_finiteness.py`
   - Extensive testing on many curves
   - Generates LaTeX certificates
   - Creates detailed analysis reports

### Running Tests

```bash
# Run spectral BSD identity tests
python tests/test_spectral_bsd.py

# Run basic finiteness tests
python tests/test_finiteness.py
```

## Tips and Best Practices

1. **Performance**: For curves with very large conductors, computation may be slow
2. **Accuracy**: Bounds are always valid but may not be sharp
3. **Verification**: When possible, compare with known Sha values from LMFDB
4. **Certificates**: Save certificates for important results
5. **Batch Processing**: Use `batch_prove_finiteness()` for multiple curves

## Common Patterns

### Pattern 1: Quick Finiteness Check

```python
from src.spectral_finiteness import prove_finiteness_for_curve

result = prove_finiteness_for_curve('11a1')
print(f"Finite: {result['finiteness_proved']}, Bound: {result['global_bound']}")
```

### Pattern 2: Detailed Analysis

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('37a1')
prover = SpectralFinitenessProver(E)

# Get full spectral data
result = prover.prove_finiteness()

# Examine each component
print(f"Conductor: {result['spectral_data']['conductor']}")
print(f"Rank: {result['spectral_data']['rank']}")
print(f"Bad primes: {list(result['spectral_data']['local_data'].keys())}")
print(f"Global bound: {result['global_bound']}")

# Generate and save certificate
cert = prover.generate_certificate('latex')
with open(f"certificate_{E.cremona_label()}.tex", 'w') as f:
    f.write(cert)
```

### Pattern 3: Batch Analysis with Error Handling

```python
from src.spectral_finiteness import batch_prove_finiteness

curves = ['11a1', '14a1', '15a1', 'invalid_label', '17a1']
results = batch_prove_finiteness(curves)

successful = []
failed = []

for label, result in results.items():
    if 'error' in result:
        failed.append((label, result['error']))
    else:
        successful.append((label, result['global_bound']))

print(f"Successful: {len(successful)}")
print(f"Failed: {len(failed)}")

for label, bound in successful:
    print(f"  {label}: bound = {bound}")

for label, error in failed:
    print(f"  {label}: {error}")
```

## Troubleshooting

### Issue: Sage not found
**Solution**: Ensure SageMath is properly installed and in your PATH.

### Issue: Certificate generation fails
**Solution**: Check that the proof_data dictionary contains all required fields.

### Issue: Slow computation for large conductor
**Solution**: This is expected. Consider parallelizing batch operations for many curves.

### Issue: Bound doesn't match known Sha
**Solution**: The bound is an upper bound, not always sharp. It should always be ≥ known Sha.

## Further Reading

- See `README.md` for architectural overview
- See `tests/test_spectral_bsd.py` for comprehensive examples
- See source code docstrings for detailed API documentation
