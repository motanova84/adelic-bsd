# Batch SHA Estimation

This module provides tools for estimating |Ш(E)| (the order of the Tate-Shafarevich group) for elliptic curves with rank ≥ 2, using the BSD (Birch and Swinnerton-Dyer) formula.

## BSD Formula

The estimation is based on the BSD conjecture:

```
|Ш(E)| = L^{(r)}(E,1) / (r! · Ω_E · R_E · |Tors(E)|² · ∏c_p)
```

Where:
- **L^{(r)}(E,1)** = r-th derivative of L(E,s) at s=1
- **r** = analytic rank of E
- **Ω_E** = real period
- **R_E** = regulator (determinant of height pairing matrix)
- **Tors(E)** = torsion subgroup order
- **∏c_p** = product of Tamagawa numbers

## Requirements

- Python 3.9+
- SageMath 9.8+ (for actual curve computations)

## Usage

### Single Curve Estimation

```python
from experiments.batch_sha_estimation import estimate_sha

# Estimate |Ш| for 389a1 (rank 2 curve)
sha_value = estimate_sha('389a1')
print(f"|Ш| ≈ {sha_value}")
```

### Batch Processing

```python
from experiments.batch_sha_estimation import batch_sha_estimation

# Process multiple curves
results = batch_sha_estimation(
    ['389a1', '433a1', '5077a1'],
    output_csv='results/sha_estimation.csv',
    output_json='results/sha_estimation.json',
    verbose=True
)
```

### Command Line Interface

```bash
# Single curve
python estimate_sha.py --curve 389a1

# Multiple curves
python estimate_sha.py --curve 389a1 --curve 433a1 --curve 5077a1

# Run full BSD-10000 Paso 9 operation (500 rank-2, 50 rank-3 curves)
python estimate_sha.py --run-paso9

# Search by conductor range
python estimate_sha.py --conductor-max 1000 --rank-min 2 --limit 100
```

## Output Format

### CSV Columns

| Column | Description |
|--------|-------------|
| `label` | LMFDB/Cremona curve label |
| `rank` | Analytic rank |
| `sha_estimate` | Estimated |Ш| value |
| `l_derivative` | L^{(r)}(E,1) |
| `omega` | Real period Ω_E |
| `R` | Regulator R_E |
| `torsion` | \|Tors(E)\| |
| `tamagawa` | ∏c_p |

### Example Output

```csv
label,rank,sha_estimate,l_derivative,omega,R,torsion,tamagawa
389a1,2,1.0,0.759316882,2.350882553,0.152460177,1,1
433a1,2,1.0,0.581847789,2.104526315,0.138293478,1,1
```

## BSD-10000 → GO · Paso 9

The `--run-paso9` option executes the full operation which processes:
- Up to 500 curves with rank 2
- Up to 50 curves with rank 3

Results are saved to the `results/` directory with timestamps.

## Implementation Details

### ShaEstimator Class

The main class providing:
- `estimate_sha(label)` - Estimate |Ш| for a single curve
- `batch_estimate(labels, ...)` - Process multiple curves
- CSV and JSON output generation
- Progress logging and statistics

### Fallback Curves

When SageMath is not available, a list of known rank ≥ 2 curves is returned:
- Rank 2: 389a1, 433a1, 446d1, 563a1, 571a1, ...
- Rank 3: 5077a1, 234446a1, ...

## References

- Birch & Swinnerton-Dyer Conjecture
- LMFDB: https://www.lmfdb.org/
- SageMath: https://www.sagemath.org/

## License

MIT License - See repository LICENSE file.
