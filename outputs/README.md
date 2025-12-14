# BSD LHS vs RHS Outputs Directory

This directory contains output files from BSD validation computations.

## Files

- `bsd_lhs_vs_rhs.txt` - Human-readable validation results
- `bsd_lhs_vs_rhs.json` - Machine-readable validation results

## Usage

Run the validation script to generate these files:

```bash
# With SageMath available
python validation/birch_swinnerton_lhs.py

# Or from SageMath shell
sage validation/birch_swinnerton_lhs.py
```

## Expected Output Format

The text file contains:
- Curve identifier and rank
- LHS: L^(r)(E,1) / r!
- RHS: BSD arithmetic invariants
- Relative error and validation level

## Validation Levels

| Error Relative | Validation |
|----------------|------------|
| < 10⁻³ | Almost perfect |
| < 10⁻² | Good estimation |
| < 10⁻¹ | Partial coherence |
| ≥ 10⁻¹ | Needs review |
