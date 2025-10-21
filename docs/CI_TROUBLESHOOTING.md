# CI Troubleshooting Guide / Guía de Solución de Problemas de CI

This guide helps you diagnose and fix CI test failures by reproducing the CI environment locally.

Esta guía le ayuda a diagnosticar y corregir fallos de pruebas CI reproduciendo el entorno CI localmente.

## Quick Diagnosis / Diagnóstico Rápido

### 1. Compare Python Versions / Comparar Versiones de Python

**In CI / En CI:**
CI runs Python 3.9, 3.10, and 3.11 in separate jobs.

**Check Local / Verificar Local:**
```bash
python -V
```

If your local Python version differs, consider using pyenv or conda to match CI versions.
Si su versión local de Python difiere, considere usar pyenv o conda para igualar las versiones de CI.

### 2. Compare Dependencies / Comparar Dependencias

**Download CI frozen packages:**
1. Go to the failed workflow run (e.g., https://github.com/motanova84/adelic-bsd/actions)
2. Download the `frozen-packages-py*.txt` artifacts
3. Compare with local:

```bash
pip freeze > local-frozen.txt
diff local-frozen.txt frozen.txt
```

**Or use the automated comparison script:**
```bash
# Download frozen.txt from CI artifacts, then:
python scripts/compare_dependencies.py frozen.txt

# This will show:
# - Version mismatches between local and CI
# - Packages only in local (may need clean venv)
# - Packages only in CI (may need to update requirements)
```

**Generate frozen packages locally:**
```bash
python -V  # Log Python version
pip freeze > frozen.txt
```

### 3. Reproduce CI Environment Locally / Reproducir Entorno CI Localmente

**Option 1: Using Virtual Environment / Usando Entorno Virtual**

```bash
# Create a clean virtual environment
python -m venv .venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate

# Install CI dependencies
pip install --upgrade pip==23.1.2
pip install -r requirements_ci.txt

# Verify installation
python -V
pip freeze

# Run tests
pytest tests/test_finiteness_basic.py -v
pytest tests/test_basic_functionality.py -v
```

**Option 2: Using Docker (matches CI exactly) / Usando Docker (coincide exactamente con CI)**

```bash
# For basic tests (no SageMath)
docker run -it --rm -v $(pwd):/workspace -w /workspace python:3.11-slim bash
# Inside container:
pip install --upgrade pip==23.1.2
pip install -r requirements_ci.txt
pytest tests/test_finiteness_basic.py -v

# For SageMath tests
docker run -it --rm -v $(pwd):/workspace -w /workspace sagemath/sagemath:9.8 bash
# Inside container:
pip install --upgrade pip==23.1.2
pip install -r requirements.txt
pip install pytest==7.4.0
sage -python -m pytest -q
```

**Option 3: Using act (run GitHub Actions locally) / Usando act (ejecutar GitHub Actions localmente)**

```bash
# Install act: https://github.com/nektos/act
# Then run:
act -j test
```

## Common Issues / Problemas Comunes

### 1. Different Dependencies / Dependencias Diferentes

**Issue:** `pip frozen` output differs between CI and local.

**Solution:**
- Ensure you're using the correct requirements file:
  - `requirements_ci.txt` - for basic CI tests (no SageMath)
  - `requirements.txt` - for full installation with SageMath
  - `requirements-dev.txt` - for local development
- Pin all dependency versions in requirements files
- Use `pip install --no-deps` if you have conflicting dependencies

### 2. Missing Environment Variables / Variables de Entorno Faltantes

**Issue:** Tests fail with missing API keys or configuration.

**Solution:**
- Check `.github/workflows/*.yml` for environment variables
- Add secrets in GitHub repository settings: Settings → Secrets and variables → Actions
- For local testing, create `.env` file (add to `.gitignore`)

### 3. External Services / Network Timeouts / Servicios Externos / Tiempos de Espera de Red

**Issue:** Tests making HTTP calls fail intermittently.

**Solution:**
- Mock external requests using `requests-mock` or `responses`
- Mark flaky tests with `@pytest.mark.flaky`
- Add retries for network operations
- Skip network tests in CI with `@pytest.mark.skipif(os.getenv('CI'))`

### 4. Database Differences or Migrations / Diferencias de Base de Datos o Migraciones

**Issue:** Tests fail due to missing database schema.

**Solution:**
- Add database setup steps in workflow before running tests
- Use in-memory SQLite for CI tests
- Include migration scripts in test setup

### 5. Flaky/Non-deterministic Tests / Pruebas Indeterministas

**Issue:** Tests pass locally but fail intermittently in CI.

**Solution:**
```bash
# Run test repeatedly to catch flakiness
pytest tests/test_name.py -k test_function -vv --maxfail=1 -x

# Fix random seeds
import random
import numpy as np
random.seed(42)
np.random.seed(42)

# Fix dates/times
from unittest.mock import patch
from datetime import datetime
with patch('module.datetime') as mock_date:
    mock_date.now.return_value = datetime(2025, 1, 1)
```

### 6. pytest Configuration Issues / Problemas de Configuración de pytest

**Issue:** Tests work with `python test.py` but fail with `pytest`.

**Solution:**
- Check `pytest.ini` for markers and configuration
- Ensure fixtures are properly defined in `conftest.py`
- Verify test discovery patterns match your file structure
- Check for autouse fixtures that may not work in CI

## Debugging Specific Test Failures / Depuración de Fallas Específicas de Pruebas

### Get Traceback from CI / Obtener Traceback de CI

1. Navigate to failed workflow run: https://github.com/motanova84/adelic-bsd/actions
2. Click on failed job
3. Expand failed step
4. Copy full traceback

### Run Single Test with Full Output / Ejecutar Prueba Única con Salida Completa

```bash
# Run specific test with verbose output
pytest tests/test_file.py::test_function -vv -s

# Run with full traceback
pytest tests/test_file.py::test_function -vv -s --tb=long

# Run with debugging
pytest tests/test_file.py::test_function -vv -s --pdb
```

### Compare CI and Local Output / Comparar Salida CI y Local

```bash
# Local
pytest tests/ -v 2>&1 | tee local-test-output.txt

# Download CI logs from Actions tab
# Compare outputs
diff local-test-output.txt ci-test-output.txt
```

## Requirements Files Overview / Descripción de Archivos de Requisitos

- **`requirements_ci.txt`**: Basic dependencies for CI (without SageMath)
  - Used in `python-tests.yml` and `python-package-conda.yml` basic-tests job
  - Minimal dependencies to ensure fast CI runs
  
- **`requirements.txt`**: Full dependencies including SageMath
  - Used for complete local development
  - Used in `python-package-conda.yml` sage-tests job
  
- **`requirements-dev.txt`**: Development tools (linters, formatters, etc.)
  - Includes everything from `requirements_ci.txt`
  - Adds development tools like black, isort, mypy
  - Use for local development

## Workflow Files / Archivos de Flujo de Trabajo

- **`.github/workflows/python-tests.yml`**: Main test workflow
  - Runs on: push to main/develop, pull requests to main
  - Matrix: Python 3.9, 3.10, 3.11
  - Tests: basic functionality, CI-safe tests, README LaTeX validation
  
- **`.github/workflows/python-package-conda.yml`**: Package tests
  - Runs on: push to main/develop, pull requests to main/develop
  - Two jobs:
    - `basic-tests`: No SageMath (Python 3.9, 3.10, 3.11)
    - `sage-tests`: With SageMath (Docker container)

## Need More Help? / ¿Necesita Más Ayuda?

1. Check existing issues: https://github.com/motanova84/adelic-bsd/issues
2. Create new issue with:
   - Link to failed workflow run
   - Full traceback from CI
   - Local environment details (`python -V`, `pip freeze`)
   - Steps you've tried from this guide
