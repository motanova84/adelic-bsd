# Batch Sha Estimation Module

This module estimates |Ш(E)| (the cardinality of the Tate–Shafarevich group) for elliptic curves with rank ≥ 2 using the BSD (Birch and Swinnerton-Dyer) formula.

## BSD Formula

The estimation is based on the BSD conjecture formula:

```
|Ш(E)| = L^{(r)}(E,1) / (r! · Ω_E · R_E · |Tors(E)|² · ∏c_p)
```

Where:
- **L^{(r)}(E,1)** = r-th derivative of L(E,s) at s=1 (r = rank of E)
- **Ω_E** = real period (or imaginary for CM curves)
- **R_E** = regulator (determinant of the height pairing matrix)
- **Tors(E)** = torsion subgroup
- **∏c_p** = product of Tamagawa numbers at primes of bad reduction

## Requirements

- Python 3.9-3.13
- SageMath 9.x or 10.x (for full functionality)
- pandas (for CSV export)

## Usage

### As a Python Module

```python
from experiments.batch_sha_estimation import estimate_sha, batch_estimate_sha

# Single curve estimation
result = estimate_sha("389a1")
print(f"Rank: {result.rank}, |Ш| ≈ {result.sha_estimate}")

# Batch estimation
results = batch_estimate_sha(limit_rank2=100, limit_rank3=10)
for r in results:
    if r.success:
        print(f"{r.label}: |Ш| ≈ {r.sha_estimate}")
```

### From Command Line

```bash
# Process default curves (500 rank-2, 50 rank-3)
python -m experiments.batch_sha_estimation.estimate_sha

# Process specific curves
python -m experiments.batch_sha_estimation.estimate_sha --labels 389a1 433a1 5077a1

# Custom limits and output
python -m experiments.batch_sha_estimation.estimate_sha \
    --limit-rank2 100 \
    --limit-rank3 10 \
    --output my_results.csv
```

## Output CSV Format

The exported CSV contains the following columns:

| Column | Description |
|--------|-------------|
| label | LMFDB/Cremona curve label |
| rank | Algebraic rank of E |
| sha_estimate | Estimated |Ш| value |
| l_derivative | L^{(r)}(E, 1) |
| omega | Real period Ω_E |
| R | Regulator R_E |
| torsion | |Tors(E)| |
| tamagawa | ∏c_p |
| success | Boolean success flag |
| error_message | Error details if failed |

## API Reference

### `estimate_sha(label: str) -> ShaEstimationResult`

Estimate |Ш(E)| for a single curve given its label.

### `estimate_sha_from_curve(E, label: str = None) -> ShaEstimationResult`

Estimate |Ш(E)| from a SageMath EllipticCurve object.

### `batch_estimate_sha(...) -> List[ShaEstimationResult]`

Process multiple curves in batch mode.

### `export_results_to_csv(results, output_path) -> str`

Export results to CSV format.

## Example Curves

### Rank 2 Curves
- 389a1 (first rank 2 curve by conductor)
- 433a1
- 446a1
- 563a1

### Rank 3 Curves
- 5077a1 (first rank 3 curve by conductor)

## Technical Notes

1. **SageMath Dependency**: Full functionality requires SageMath. Without it, only known curves are available.

2. **Numerical Precision**: L-function derivatives are computed numerically with 10 digits of precision.

3. **Performance**: For large batches, the regulator computation can be slow for high-rank curves.

4. **Error Handling**: Failed computations return `ShaEstimationResult` with `success=False` and an error message.

## References

- Birch, B. J.; Swinnerton-Dyer, H. P. F. (1965). "Notes on elliptic curves. II"
- Gross, B.; Zagier, D. (1986). "Heegner points and derivatives of L-series"
- LMFDB - The L-functions and Modular Forms Database (https://www.lmfdb.org/)
