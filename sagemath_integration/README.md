# SageMath Integration Module

This directory contains the SageMath-compatible implementation of the BSD Spectral framework, specifically the PT (Poitou-Tate) compatibility module.

## Structure

```
sagemath_integration/
└── sage/
    └── schemes/
        └── elliptic_curves/
            └── bsd_spectral/
                ├── __init__.py
                └── PT_compatibility.py
```

## Usage

This module is designed to be integrated into SageMath as an official package. Once integrated, it can be used as follows:

```python
sage: from sage.schemes.elliptic_curves.bsd_spectral import verify_PT_compatibility
sage: E = EllipticCurve('37a1')  # rank 1 curve
sage: result = verify_PT_compatibility(E)
sage: result['PT_compatible']
True
sage: result['method']
'Gross-Zagier'
```

## Module Contents

### PT_compatibility.py

Implements verification of (PT) Poitou-Tate compatibility for elliptic curves using:

- **Gross-Zagier formula** for rank 1 curves
- **Yuan-Zhang-Zhang (YZZ) heights** for rank ≥ 2 curves
- Trivial verification for rank 0 curves

#### Functions

1. **`compute_gross_zagier_height(E)`**
   - Computes Gross-Zagier height for rank 1 curves
   - Returns canonical height of a generator

2. **`compute_yzz_height(E)`**
   - Computes Yuan-Zhang-Zhang height for rank ≥ 2 curves
   - Returns regulator (determinant of height pairing matrix)

3. **`verify_PT_compatibility(E)`**
   - Main verification function
   - Returns dictionary with compatibility information:
     - `PT_compatible`: boolean indicating compatibility
     - `rank`: algebraic rank of the curve
     - `height_algebraic`: computed algebraic height
     - `method`: method used ('trivial', 'Gross-Zagier', 'Yuan-Zhang-Zhang')
     - `curve`: curve label or string representation

## Testing

Tests are located in `tests/test_sagemath_pt_compatibility.py`. They require SageMath to be installed and will be skipped automatically if SageMath is not available.

Run tests with:
```bash
pytest tests/test_sagemath_pt_compatibility.py -v
```

## Requirements

- SageMath 9.8 or higher
- Python 3.9+

## References

- Gross, B. H., & Zagier, D. B. (1986). "Heegner points and derivatives of L-series"
- Yuan, X., Zhang, S., & Zhang, W. (2013). "The Gross-Zagier Formula on Shimura Curves"

## Authors

- José Manuel Mota Burruezo (2025-01)

## License

See LICENSE file in the root directory.
