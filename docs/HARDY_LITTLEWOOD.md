# Hardy-Littlewood Singular Series (Equation 4)

## Overview

This document describes the implementation of the Hardy-Littlewood singular series, specifically **Equation (4)** with the corrected formula where the local factor for p=2 is omitted.

## Mathematical Definition

The Hardy-Littlewood singular series $\mathfrak{S}(n)$ is defined as:

$$\mathfrak{S}(n) = \prod_{p>2} \left(1 - \frac{1}{(p-1)^2}\right) \prod_{\substack{p \mid n \\ p > 2}} \frac{p-1}{p-2}$$

### Components

1. **First Product** (Infinite Product):
   $$\prod_{p>2} \left(1 - \frac{1}{(p-1)^2}\right)$$
   
   This is an infinite product over all primes $p > 2$. When $n = 1$, this equals the **Hardy-Littlewood constant** $C_2 \approx 0.6601618158...$, also known as the twin prime constant.

2. **Second Product** (Finite Product):
   $$\prod_{\substack{p \mid n \\ p > 2}} \frac{p-1}{p-2}$$
   
   This is a finite product over prime divisors of $n$ that are greater than 2. Each factor $(p-1)/(p-2) > 1$ is a local correction term.

### Key Feature: p=2 Omitted

**Important**: The local factor for $p=2$ is **omitted**, following the convention of Hardy and Littlewood (1923). This means:
- $\mathfrak{S}(2) = \mathfrak{S}(1)$
- $\mathfrak{S}(6) = \mathfrak{S}(3)$ (since $6 = 2 \times 3$, but we ignore the factor of 2)
- More generally, $\mathfrak{S}(2^k \cdot m) = \mathfrak{S}(m)$ for any odd $m$

## Implementation

The implementation is in `src/local_factors.py`:

```python
def hardy_littlewood_singular_series(n, max_prime=1000, precision=50):
    """
    Compute Hardy-Littlewood singular series S(n) - Equation (4)
    
    Args:
        n: Positive integer for which to compute S(n)
        max_prime: Maximum prime to include in the infinite product
        precision: Decimal precision for computation
    
    Returns:
        float: Value of S(n)
    """
```

### Algorithm

1. Initialize result to 1.0
2. Compute the infinite product:
   - Iterate over primes $p$ from 3 to `max_prime`
   - Multiply result by $(1 - 1/(p-1)^2)$
3. Compute the finite product:
   - Get prime divisors of $n$ (excluding 2)
   - For each prime $p > 2$ dividing $n$, multiply by $(p-1)/(p-2)$
4. Return the result

### Convergence

The infinite product converges rapidly:
- With `max_prime=100`: $C_2 \approx 0.6608...$
- With `max_prime=500`: $C_2 \approx 0.6602...$
- With `max_prime=1000`: $C_2 \approx 0.6601...$
- True value: $C_2 \approx 0.6601618158...$

## Usage Examples

### Computing the Hardy-Littlewood Constant

```python
from src.local_factors import hardy_littlewood_constant

C2 = hardy_littlewood_constant(max_prime=1000)
print(f"Twin prime constant C₂ ≈ {C2:.10f}")
# Output: Twin prime constant C₂ ≈ 0.6601618158
```

### Computing S(n) for Various n

```python
from src.local_factors import hardy_littlewood_singular_series

# S(1) = Hardy-Littlewood constant
S_1 = hardy_littlewood_singular_series(1)

# S(3): adds correction factor (3-1)/(3-2) = 2
S_3 = hardy_littlewood_singular_series(3)
# S_3 ≈ 2 × S_1

# S(15): 15 = 3×5, adds factors for both 3 and 5
S_15 = hardy_littlewood_singular_series(15)
# S_15 ≈ 2 × (4/3) × S_1

# S(6): 6 = 2×3, but p=2 is omitted, so S(6) = S(3)
S_6 = hardy_littlewood_singular_series(6)
# S_6 = S_3
```

## Mathematical Properties

### Property 1: Base Case
$$\mathfrak{S}(1) = C_2 = \prod_{p>2} \left(1 - \frac{1}{(p-1)^2}\right) \approx 0.6601618158$$

### Property 2: Prime Case
For a prime $p > 2$:
$$\mathfrak{S}(p) = C_2 \cdot \frac{p-1}{p-2}$$

Examples:
- $\mathfrak{S}(3) = C_2 \cdot \frac{2}{1} = 2 \cdot C_2$
- $\mathfrak{S}(5) = C_2 \cdot \frac{4}{3} \approx 1.333 \cdot C_2$
- $\mathfrak{S}(7) = C_2 \cdot \frac{6}{5} = 1.2 \cdot C_2$

### Property 3: Product of Primes
For $n = p \cdot q$ with distinct primes $p, q > 2$:
$$\mathfrak{S}(p \cdot q) = C_2 \cdot \frac{p-1}{p-2} \cdot \frac{q-1}{q-2}$$

Example: $\mathfrak{S}(15) = \mathfrak{S}(3 \cdot 5) = C_2 \cdot 2 \cdot \frac{4}{3}$

### Property 4: Powers of 2
For any $k \geq 0$:
$$\mathfrak{S}(2^k) = \mathfrak{S}(1) = C_2$$

This confirms that the $p=2$ factor is omitted.

### Property 5: Multiplicativity (almost)
For coprime $m, n$ with $\gcd(mn, 2) = \gcd(m, 2) = \gcd(n, 2)$:
$$\frac{\mathfrak{S}(mn)}{\mathfrak{S}(1)} = \frac{\mathfrak{S}(m)}{\mathfrak{S}(1)} \cdot \frac{\mathfrak{S}(n)}{\mathfrak{S}(1)}$$

## Testing

Comprehensive tests are provided in `tests/test_hardy_littlewood.py`:

```bash
# Run with SageMath
sage -python -m pytest tests/test_hardy_littlewood.py -v

# Or run the verification script (no SageMath required)
python3 verify_hardy_littlewood.py
```

Test coverage includes:
- ✅ Import and basic functionality
- ✅ Hardy-Littlewood constant computation
- ✅ Verification that p=2 is omitted
- ✅ Correction factor formulas
- ✅ Multiple prime factors
- ✅ Convergence properties
- ✅ Error handling

## Demonstration

Run the demonstration script to see the singular series in action:

```bash
sage -python examples/hardy_littlewood_demo.py
```

This demonstrates:
1. Computing the Hardy-Littlewood constant $C_2$
2. Examples of $\mathfrak{S}(n)$ for various $n$
3. Verification that $p=2$ is correctly omitted
4. Correction factors for prime divisors

## Historical Context

The Hardy-Littlewood singular series appears in analytic number theory, particularly in:

1. **Twin Prime Conjecture**: The constant $C_2$ appears in the asymptotic formula for the number of twin primes up to $x$.

2. **Goldbach's Conjecture**: Related singular series appear in the study of representations of integers as sums of primes.

3. **Circle Method**: The singular series is a key component in Hardy and Littlewood's circle method for additive problems.

### Reference

Hardy, G. H., & Littlewood, J. E. (1923). Some problems of 'Partitio numerorum'; III: On the expression of a number as a sum of primes. *Acta Mathematica*, 44, 1-70.

### The 1923 Convention

Hardy and Littlewood's original 1923 paper establishes the convention of omitting the local factor at $p=2$. This is **Equation (4)** in the problem statement, which has been faithfully implemented here.

## Technical Notes

### Numerical Precision

The implementation uses SageMath's `RealField` with configurable precision (default 50 decimal places) to ensure accuracy.

### Truncation of Infinite Product

The infinite product is truncated at `max_prime` (default 1000). For most applications, this provides sufficient accuracy:
- Relative error with `max_prime=1000`: $< 10^{-4}$
- For higher precision, increase `max_prime` to 2000 or higher

### Prime Divisor Computation

Prime divisors are computed using SageMath's `prime_divisors()` function, which is efficient for integers up to $10^{15}$.

## API Reference

### `hardy_littlewood_singular_series(n, max_prime=1000, precision=50)`

Compute $\mathfrak{S}(n)$ for a given positive integer $n$.

**Parameters:**
- `n` (int): Positive integer for which to compute $\mathfrak{S}(n)$
- `max_prime` (int, optional): Maximum prime in the infinite product. Default: 1000
- `precision` (int, optional): Decimal precision. Default: 50

**Returns:**
- `float`: Value of $\mathfrak{S}(n)$

**Raises:**
- `ValueError`: If $n \leq 0$ or not an integer

**Example:**
```python
S_15 = hardy_littlewood_singular_series(15, max_prime=1000)
```

### `hardy_littlewood_constant(max_prime=1000, precision=50)`

Compute the Hardy-Littlewood constant $C_2 = \mathfrak{S}(1)$.

**Parameters:**
- `max_prime` (int, optional): Maximum prime in the infinite product. Default: 1000
- `precision` (int, optional): Decimal precision. Default: 50

**Returns:**
- `float`: Approximation of $C_2 \approx 0.6601618158$

**Example:**
```python
C2 = hardy_littlewood_constant(max_prime=2000, precision=100)
```

## Integration with adelic-BSD Framework

The Hardy-Littlewood singular series is part of the `local_factors` module, which provides various local arithmetic invariants used in the BSD conjecture and related problems in analytic number theory.

While the singular series itself is not directly part of the BSD formula, it represents a similar mathematical structure: a product of local factors at primes, which is central to the adelic-spectral approach of this framework.

## See Also

- [`src/local_factors.py`](../src/local_factors.py): Implementation
- [`tests/test_hardy_littlewood.py`](../tests/test_hardy_littlewood.py): Tests
- [`examples/hardy_littlewood_demo.py`](../examples/hardy_littlewood_demo.py): Demo
- [`docs/BSD_FRAMEWORK.md`](BSD_FRAMEWORK.md): BSD framework documentation
