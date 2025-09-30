# Usage Guide - Spectral Finiteness Framework

## Quick Start Guide

### 1. Basic Usage

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

# Create an elliptic curve
E = EllipticCurve('11a1')  # Curve 11a1: y² + y = x³ - x² - 10x - 20

# Initialize the prover
prover = SpectralFinitenessProver(E)

# Prove finiteness
result = prover.prove_finiteness()

# Check the result
print(f"Finiteness proved: {result['finiteness_proved']}")
print(f"Global bound on #Ш: {result['global_bound']}")
print(f"Curve label: {result['curve_label']}")
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
```

### 3. Batch Processing

```python
from src.spectral_finiteness import batch_prove_finiteness

# Define multiple curves
curves = ['11a1', '11a2', '14a1', '15a1', '17a1', '19a1', '20a1']

# Process all curves
results = batch_prove_finiteness(curves)

# Display results
for label, result in results.items():
    if 'error' in result:
        print(f"{label}: ERROR - {result['error']}")
    else:
        print(f"{label}: bound = {result['global_bound']}")
```

### 4. Examining Spectral Data

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('11a1')
prover = SpectralFinitenessProver(E)
result = prover.prove_finiteness()

# Access spectral data
spectral_data = result['spectral_data']

print(f"Conductor: {spectral_data['conductor']}")
print(f"Rank: {spectral_data['rank']}")
print(f"Global bound: {spectral_data['global_bound']}")

# Local data for each bad prime
print("\nLocal spectral data:")
for prime, data in spectral_data['local_data'].items():
    print(f"\nPrime {prime}:")
    print(f"  Reduction type: {data['reduction_type']}")
    print(f"  Kernel dimension: {data['kernel_dim']}")
    print(f"  Torsion bound: {data['torsion_bound']}")
```

## Advanced Usage

### Custom Curve Analysis

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

# Create curve from equation
E = EllipticCurve([0, -1, 1, -10, -20])  # Same as 11a1

# Or from Cremona label
E = EllipticCurve('389a1')

prover = SpectralFinitenessProver(E)
result = prover.prove_finiteness()

# Detailed analysis
print(f"Curve: {E}")
print(f"Cremona label: {E.cremona_label()}")
print(f"Conductor: {E.conductor()}")
print(f"Discriminant: {E.discriminant()}")
print(f"j-invariant: {E.j_invariant()}")
print(f"\nRank: {E.rank()}")
print(f"Torsion: {E.torsion_order()}")
print(f"\nFiniteness bound: {result['global_bound']}")
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

### Custom Analysis Script

Create your own analysis script:

```python
#!/usr/bin/env python3
"""
Custom elliptic curve analysis
"""
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

def analyze_curve_family(conductor_range):
    """Analyze all curves in a conductor range"""
    from sage.databases.cremona import CremonaDatabase
    
    db = CremonaDatabase()
    results = []
    
    for N in conductor_range:
        curves = db.list(N)
        for label in curves:
            try:
                E = EllipticCurve(label)
                prover = SpectralFinitenessProver(E)
                result = prover.prove_finiteness()
                
                results.append({
                    'label': label,
                    'conductor': N,
                    'rank': E.rank(),
                    'bound': result['global_bound']
                })
                
                print(f"✓ {label}: bound = {result['global_bound']}")
            except Exception as e:
                print(f"✗ {label}: {e}")
    
    return results

# Run analysis
if __name__ == "__main__":
    results = analyze_curve_family(range(11, 50))
    print(f"\nAnalyzed {len(results)} curves")
```

## Tips and Best Practices

1. **Performance**: For curves with very large conductors, computation may be slow
2. **Accuracy**: Bounds are always valid but may not be sharp
3. **Verification**: When possible, compare with known Sha values from LMFDB
4. **Certificates**: Save certificates for important results
5. **Batch Processing**: Use `batch_prove_finiteness()` for multiple curves

## Troubleshooting

### Import Errors

If you get import errors:
```bash
# Make sure SageMath is installed
sage --version

# Install the package
pip install -e .
```

### Missing Dependencies

```bash
# Install via conda
conda env create -f environment.yml
conda activate algoritmo-spectral

# Or via pip
pip install -r requirements.txt
```

### Curve Not Found

```bash
# Make sure to use valid Cremona labels
# Format: [conductor][isogeny_class][curve_number]
# Examples: 11a1, 37a1, 389a1
```

---

## NEW: Spectral→Cycles→Points Algorithm

### Quick Start with New Features

```python
from sage.all import EllipticCurve
from src.spectral_cycles import demonstrate_spectral_to_points
from src.height_pairing import verify_height_compatibility

# Demo 1: Complete spectral→points pipeline
result = demonstrate_spectral_to_points('11a1')

# Demo 2: Verify height pairing compatibility
E = EllipticCurve('37a1')
compat = verify_height_compatibility(E)
print(f"Height compatibility: {compat['compatible']}")
```

### Using the Demo Script

```bash
# Run all demonstrations
sage -python examples/spectral_to_points_demo.py all

# Run specific demos
sage -python examples/spectral_to_points_demo.py single 11a1
sage -python examples/spectral_to_points_demo.py height 37a1
sage -python examples/spectral_to_points_demo.py multiple
sage -python examples/spectral_to_points_demo.py lmfdb
sage -python examples/spectral_to_points_demo.py steps
```

### Large-Scale LMFDB Verification

```python
from src.lmfdb_verification import large_scale_verification, generate_verification_report

# Run verification on many curves
results = large_scale_verification(
    conductor_range=(11, 100),
    rank_range=[0, 1, 2],
    limit=50,
    verbose=True
)

# Generate detailed report
report = generate_verification_report(results, 'verification_report.txt')
```

### Advanced: Step-by-Step Algorithm

```python
from sage.all import EllipticCurve
from src.spectral_cycles import compute_kernel_basis, spectral_kernel_to_rational_points
from src.height_pairing import (
    compute_spectral_height_matrix,
    compute_nt_height_matrix
)

E = EllipticCurve('11a1')

# Step 1: Compute spectral kernel
kernel_basis = compute_kernel_basis(E)
print(f"Kernel dimension: {len(kernel_basis)}")

# Step 2: Convert to rational points
points = spectral_kernel_to_rational_points(kernel_basis, E)
print(f"Points generated: {len(points)}")

# Step 3: Compute height matrices
H_spec = compute_spectral_height_matrix(kernel_basis, E)
H_nt = compute_nt_height_matrix(points)

# Step 4: Compare
print(f"Spectral height:\n{H_spec}")
print(f"NT height:\n{H_nt}")
```

---

## Further Reading

- **Algorithm Details**: See comments in `src/spectral_finiteness.py`
- **Spectral Cycles Guide**: See `docs/SPECTRAL_CYCLES_GUIDE.md` for complete reference
- **Mathematical Background**: Mota Burruezo Spectral BSD Framework
- **Examples**: Check `examples/quick_demo.py`, `examples/spectral_to_points_demo.py`
- **Tests**: See `tests/test_finiteness.py` and `tests/test_spectral_cycles.py` for usage examples
