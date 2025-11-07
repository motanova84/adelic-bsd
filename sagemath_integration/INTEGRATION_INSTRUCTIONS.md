
# INSTRUCCIONES DE INTEGRACIÓN

## Paso 1: Preparar Fork de SageMath
```bash
git clone https://github.com/sagemath/sage.git
cd sage
git checkout -b bsd-spectral-integration
```

## Paso 2: Copiar Archivos
```bash
cp -r sagemath_integration/sage/* sage/src/sage/
cp -r sagemath_integration/doc/* sage/src/doc/
```

## Paso 3: Ejecutar Tests
```bash
./sage -t sage/src/sage/schemes/elliptic_curves/bsd_spectral/
```

## Paso 4: Build Documentation
```bash
cd sage/src/doc
make html
```

## Paso 5: Submit PR

1. Push a tu fork
2. Abrir PR en github.com/sagemath/sage
3. Usar template en PULL_REQUEST_TEMPLATE.md
4. Esperar revisión de maintainers

## Contactos

- Elliptic Curves: @williamstein @jvoisin
- Number Theory: @kedlaya @roed314
