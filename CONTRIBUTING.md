# Contributing to Algoritmo Espectral

Thank you for your interest in contributing to the Mota Burruezo Spectral BSD Framework!

## How to Contribute

### Reporting Bugs

If you find a bug, please open an issue with:
- A clear description of the problem
- Steps to reproduce
- Expected vs actual behavior
- Your environment (Python version, SageMath version, OS)
- Any error messages or stack traces

### Suggesting Enhancements

We welcome suggestions for new features or improvements:
- Open an issue describing the enhancement
- Explain the use case and benefits
- If possible, provide examples of how it would work

### Pull Requests

1. **Fork the repository** and create a new branch:
   ```bash
   git checkout -b feature/your-feature-name
   ```

2. **Make your changes**:
   - Write clear, documented code
   - Follow the existing code style
   - Add tests for new functionality
   - Update documentation as needed

3. **Test your changes**:
   ```bash
   # Run tests
   pytest tests/
   
   # Run linting
   flake8 src/ tests/ examples/
   ```

4. **Commit your changes**:
   ```bash
   git commit -m "Add feature: brief description"
   ```

5. **Push to your fork**:
   ```bash
   git push origin feature/your-feature-name
   ```

6. **Open a Pull Request**:
   - Provide a clear description of changes
   - Reference any related issues
   - Ensure all tests pass

## Development Setup

### Prerequisites

- Python 3.9 or later
- SageMath 9.5 or later
- Git

### Installation

```bash
# Clone your fork
git clone https://github.com/YOUR-USERNAME/algoritmo.git
cd algoritmo

# Create conda environment
conda env create -f environment.yml
conda activate algoritmo-spectral

# Install in development mode
pip install -e .
```

### Running Tests

```bash
# Run all tests
pytest tests/ -v

# Run specific test
pytest tests/test_finiteness.py::test_11a1_finiteness -v

# Run with coverage
pytest --cov=src tests/
```

### Code Style

- Follow PEP 8 guidelines
- Use meaningful variable and function names
- Add docstrings to all functions and classes
- Keep lines under 100 characters when possible
- Use type hints where appropriate

Example:
```python
def prove_finiteness(self) -> dict:
    """
    Prove finiteness of Ш(E/ℚ).
    
    Returns:
        dict: Proof data including bounds and spectral information
    """
    # Implementation
    pass
```

### Documentation

- Update README.md for user-facing changes
- Update USAGE.md for new features
- Add docstrings to new code
- Include examples in docstrings when helpful

### Commit Messages

Write clear commit messages:
- Use present tense ("Add feature" not "Added feature")
- Keep first line under 50 characters
- Add detailed description if needed

Good examples:
```
Add support for curves with complex multiplication
Fix kernel dimension calculation for supercuspidal case
Update documentation with batch processing examples
```

## Code Organization

```
src/
├── spectral_finiteness.py  # Core implementation
└── __init__.py             # Package exports

tests/
├── test_finiteness.py      # Unit tests
└── __init__.py

examples/
├── quick_demo.py           # Demo scripts
└── __init__.py
```

### Adding New Features

1. **Core functionality**: Add to `src/spectral_finiteness.py`
2. **Tests**: Add to `tests/test_finiteness.py`
3. **Examples**: Add to `examples/` if appropriate
4. **Documentation**: Update README.md and USAGE.md

## Testing Guidelines

### Writing Tests

```python
def test_new_feature():
    """Test description"""
    # Setup
    E = EllipticCurve('11a1')
    prover = SpectralFinitenessProver(E)
    
    # Action
    result = prover.new_feature()
    
    # Assert
    assert result['expected_key'] == expected_value
    print("✓ Test passed")
```

### Test Coverage

- Aim for high test coverage
- Test edge cases
- Test error handling
- Test with various curve types (good/multiplicative/supercuspidal reduction)

## Questions?

- Open an issue for questions
- Check existing issues and pull requests
- Review documentation and examples

## Code of Conduct

- Be respectful and constructive
- Welcome newcomers
- Focus on the mathematics and code
- Help others learn

## License

By contributing, you agree that your contributions will be licensed under the MIT License.

Thank you for contributing to the Spectral BSD Framework!
