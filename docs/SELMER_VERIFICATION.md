# Selmer Map Verification Module

## Overview

The Selmer verification module provides comprehensive verification and certification for spectral Selmer maps within the adelic-BSD framework. It integrates the Selmer map computations with the formal verification system, generating formal certificates that validate Selmer map properties.

## Features

- **Complete Verification Pipeline**: Verifies all aspects of Selmer maps including initialization, Bloch-Kato conditions, and spectral compatibility
- **Certificate Generation**: Generates formal certificates with cryptographic hashes for verification results
- **Batch Processing**: Supports batch verification of multiple curves
- **Report Generation**: Creates human-readable reports of verification results
- **Integration**: Seamlessly integrates with the FormalBSDProver and other verification modules

## Module Structure

### Main Components

1. **SelmerVerification Class**: Core verification class that performs comprehensive Selmer map verification
2. **Convenience Functions**: Quick-use functions for common verification tasks
3. **Certificate Generation**: Formal certificate creation with integrity verification
4. **Batch Processing**: Batch verification capabilities for multiple curves

### Verification Steps

The module performs the following verification steps:

1. **Map Initialization**: Verifies that Selmer maps can be properly initialized for all specified primes
2. **Bloch-Kato Conditions**: Validates Bloch-Kato conditions at all primes
3. **Spectral Compatibility**: Checks spectral-to-Selmer map compatibility
4. **Local-Global Compatibility**: Verifies local-global compatibility of the Selmer structure

## Usage

### Basic Usage

```python
from sage.all import EllipticCurve
from src.verification import verify_selmer_maps

# Verify Selmer maps for a curve
E = EllipticCurve('11a1')
certificate = verify_selmer_maps(E, primes=[2, 3], precision=20)

print(f"Verification passed: {certificate['verification_passed']}")
```

### Detailed Verification

```python
from src.verification import SelmerVerification

E = EllipticCurve('37a1')
verifier = SelmerVerification(E, primes=[2, 3, 5], precision=20)

# Run complete verification
certificate = verifier.verify_all()

# Print detailed summary
verifier.print_verification_summary()

# Generate and save certificate
certificate = verifier.generate_certificate(save=True, output_dir='certificates')
```

### Batch Verification

```python
from src.verification import batch_verify_selmer_maps

curve_labels = ['11a1', '37a1', '389a1', '5077a1']
results = batch_verify_selmer_maps(
    curve_labels,
    primes=[2],
    precision=20,
    save_certificates=True
)

print(f"Success rate: {results['success_rate']}")
```

### Report Generation

```python
from src.verification import (
    verify_selmer_maps,
    generate_selmer_verification_report
)

E = EllipticCurve('11a1')
certificate = verify_selmer_maps(E)

# Generate human-readable report
report = generate_selmer_verification_report(certificate)
print(report)
```

## Certificate Format

Verification certificates are JSON documents with the following structure:

```json
{
  "certificate_type": "selmer_map_verification",
  "certificate_version": "1.0",
  "curve": "11a1",
  "conductor": 11,
  "rank": 0,
  "primes_verified": [2, 3],
  "precision": 20,
  "timestamp": "2025-10-02T16:30:00.000000",
  "verification_steps": {
    "initialization": {
      "all_initialized": true,
      "initialization_status": {...}
    },
    "bloch_kato": {
      "all_verified": true,
      "bloch_kato_status": {...}
    },
    "spectral_compatibility": {
      "compatible": true,
      "compatibility_status": {...}
    },
    "local_global": {
      "compatible": true,
      ...
    }
  },
  "verification_passed": true,
  "verification_level": "complete",
  "certificate_hash": "a1b2c3d4..."
}
```

## API Reference

### SelmerVerification Class

```python
SelmerVerification(E, primes=None, precision=20)
```

**Parameters:**
- `E`: EllipticCurve object
- `primes`: List of primes to verify (default: conductor primes)
- `precision`: p-adic precision (default: 20)

**Methods:**
- `verify_all()`: Run complete verification and return certificate
- `generate_certificate(save=False, output_dir='certificates')`: Generate formal certificate
- `print_verification_summary()`: Print human-readable summary

### Convenience Functions

#### verify_selmer_maps

```python
verify_selmer_maps(E, primes=None, precision=20, save_certificate=False)
```

Quick verification of Selmer maps for a single curve.

#### batch_verify_selmer_maps

```python
batch_verify_selmer_maps(curve_labels, primes=None, precision=20, save_certificates=False)
```

Batch verify Selmer maps for multiple curves.

#### generate_selmer_verification_report

```python
generate_selmer_verification_report(verification_results)
```

Generate human-readable report from verification results.

## Integration with BSD Framework

The Selmer verification module integrates seamlessly with other components:

```python
from src.verification import (
    verify_selmer_maps,
    FormalBSDProver,
    generate_formal_certificate
)

E = EllipticCurve('11a1')

# Step 1: Verify Selmer maps
selmer_cert = verify_selmer_maps(E, primes=[2, 3])

if selmer_cert['verification_passed']:
    # Step 2: Run complete BSD verification
    bsd_prover = FormalBSDProver(E)
    bsd_cert = bsd_prover.prove_bsd_completely()
    
    print("Both Selmer maps and BSD formula verified!")
```

## Examples

See the `examples/selmer_verification_demo.py` script for comprehensive demonstrations of all features.

## Testing

Run the test suite:

```bash
# With SageMath
sage -python -m pytest tests/test_selmer_verification.py -v

# Or using pytest directly (requires sage.all)
python3 -m pytest tests/test_selmer_verification.py -v
```

## Theory Background

The Selmer verification module validates:

1. **Spectral Selmer Map (Φ)**: The map Φ: ker K_E(1) → H^1_f(Q, V_p) that connects spectral vectors to p-adic Galois cohomology

2. **Bloch-Kato Conditions**: Local conditions at finite primes and archimedean places that define the Selmer group

3. **Local-Global Compatibility**: The compatibility of local Selmer conditions with the global structure

4. **Cohomology Properties**: Verification that cohomology classes satisfy crystalline and unramified conditions

## Related Modules

- `src/cohomology/spectral_selmer_map.py`: Core Selmer map implementation
- `src/cohomology/advanced_spectral_selmer.py`: Advanced spectral Selmer computations
- `src/cohomology/bloch_kato_conditions.py`: Bloch-Kato condition verification
- `src/verification/formal_bsd_prover.py`: Complete BSD verification framework

## References

For theoretical background on Selmer groups and p-adic cohomology, see:

- The main README.md for BSD conjecture overview
- Documentation in `docs/` for detailed mathematical background
- Research papers cited in CITATION.cff

## Authors

- Original framework: motanova84
- Selmer verification module: Co-authored with motanova84 <192380069+motanova84@users.noreply.github.com>

## License

This module is part of the adelic-bsd project and is licensed under the MIT License.
