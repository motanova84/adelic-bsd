# Hardy-Littlewood Singular Series - Quick Reference

## Formula (Equation 4)

$$\mathfrak{S}(n) = \prod_{p>2} \left(1 - \frac{1}{(p-1)^2}\right) \prod_{\substack{p \mid n \\ p > 2}} \frac{p-1}{p-2}$$

**Important**: Local factor for p=2 is **omitted** (Hardy-Littlewood 1923 convention)

## Quick Examples

| n | Prime Factorization | S(n) Formula | Approximate Value |
|---|---------------------|--------------|-------------------|
| 1 | - | C₂ | 0.6602 |
| 2 | 2 | C₂ (p=2 omitted) | 0.6602 |
| 3 | 3 | C₂ × 2/1 | 1.3204 |
| 4 | 2² | C₂ (p=2 omitted) | 0.6602 |
| 5 | 5 | C₂ × 4/3 | 0.8803 |
| 6 | 2×3 | C₂ × 2/1 | 1.3204 |
| 7 | 7 | C₂ × 6/5 | 0.7922 |
| 15 | 3×5 | C₂ × 2/1 × 4/3 | 1.7605 |
| 21 | 3×7 | C₂ × 2/1 × 6/5 | 1.5847 |
| 30 | 2×3×5 | C₂ × 2/1 × 4/3 | 1.7605 |

## Usage

```python
from src.local_factors import (
    hardy_littlewood_singular_series,
    hardy_littlewood_constant
)

# Hardy-Littlewood constant
C2 = hardy_littlewood_constant()
# C2 ≈ 0.6601618158

# For any n
S_n = hardy_littlewood_singular_series(n)
```

## Key Properties

1. **Base constant**: S(1) = C₂ ≈ 0.6601618158 (twin prime constant)

2. **p=2 omitted**: S(2ᵏ) = S(1) for any k ≥ 0

3. **Prime correction**: S(p) = C₂ × (p-1)/(p-2) for prime p > 2

4. **Multiplicative structure**: 
   - For coprime m,n not divisible by 2: S(mn)/S(1) = [S(m)/S(1)] × [S(n)/S(1)]
   - With 2: S(2m) = S(m)

## Reference

Hardy, G. H., & Littlewood, J. E. (1923). *Some problems of 'Partitio numerorum'; III: On the expression of a number as a sum of primes.* Acta Mathematica, 44, 1-70.

## See Also

- Full documentation: [`docs/HARDY_LITTLEWOOD.md`](HARDY_LITTLEWOOD.md)
- Implementation: [`src/local_factors.py`](../src/local_factors.py)
- Tests: [`tests/test_hardy_littlewood.py`](../tests/test_hardy_littlewood.py)
- Demo: [`examples/hardy_littlewood_demo.py`](../examples/hardy_littlewood_demo.py)
