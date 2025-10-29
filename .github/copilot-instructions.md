# GitHub Copilot Instructions for Adelic-BSD Repository

## Workflow Management and Automation

### Production Workflow Updates

- Detecta cuándo los scripts `validate_*` cambian y sugiere actualización del flujo de producción.
- Genera automáticamente nuevos `.yml` en `.github/workflows` para tareas repetitivas.
- Si falta una variable de entorno o secreto, sugiere añadirlo en el repositorio.
- Propón optimizaciones para ejecución paralela (`matrix`, `strategy`) o GPU.

### Python Version Compatibility

- Mantén compatibilidad con Python 3.9-3.13 en todos los workflows.
- Usa Python 3.11 como versión predeterminada para workflows de producción.
- Actualiza automáticamente las matrices de versiones cuando se agreguen nuevas versiones de Python.

### Dependency Management

- Cuando se actualicen `requirements.txt`, `requirements-dev.txt`, o `requirements_ci.txt`, revisa y actualiza los workflows correspondientes.
- Asegúrate de que todas las dependencias estén fijadas con versiones exactas para reproducibilidad.
- Sugiere actualizar los caches de pip cuando cambien los archivos de requisitos.

### GPU Optimization

- Al detectar operaciones matemáticas intensivas, sugiere optimizaciones para GPU.
- Propón configuraciones de matriz que incluyan runners con GPU cuando sea apropiado.
- Sugiere el uso de `strategy.matrix` para paralelizar validaciones en diferentes configuraciones de hardware.

### CI/CD Best Practices

- Mantén permisos mínimos necesarios en todos los workflows (principio de menor privilegio).
- Usa versiones fijadas de las acciones de GitHub (con hashes SHA).
- Sugiere mejoras en tiempo de ejecución mediante cacheo y paralelización.
- Detecta workflows lentos y propón optimizaciones.

### Docker and Containerization

- Actualiza el `Dockerfile` cuando cambien las dependencias o scripts principales.
- Sugiere optimizaciones de capas para reducir el tamaño de la imagen.
- Propón multi-stage builds para separar dependencias de build y runtime.

### Secret Management

- Detecta cuando se necesiten nuevos secretos en workflows.
- Sugiere nombres descriptivos para secretos siguiendo convenciones (ej: `HF_TOKEN`, `DOCKERHUB_TOKEN`).
- Recuerda verificar que los secretos estén configurados antes de hacer merge.

### Testing and Validation

- Cuando se agreguen nuevos módulos en `src/`, sugiere agregar tests correspondientes en `tests/`.
- Actualiza workflows de CI cuando se detecten nuevos tests.
- Propón la ejecución de tests relevantes en paralelo usando matrices.

### Documentation

- Mantén sincronizada la documentación con los cambios en workflows.
- Sugiere actualizar README.md cuando se agreguen nuevos workflows importantes.
- Propón agregar badges de estado para workflows críticos.

### Code Quality

- Sugiere agregar linters y formatters cuando no estén presentes.
- Propón configuraciones de pre-commit hooks para validaciones automáticas.
- Detecta código duplicado en workflows y sugiere extraerlo a acciones reutilizables.

### Mathematical Computations

- Para scripts de validación matemática, sugiere timeouts apropiados basados en complejidad.
- Propón estrategias de cacheo para resultados intermedios costosos.
- Detecta operaciones que puedan beneficiarse de computación paralela.

### Repository Structure

- Mantén consistencia en la estructura de directorios al sugerir nuevos archivos.
- Sigue las convenciones existentes para nombres de archivos y módulos.
- Sugiere ubicaciones apropiadas para nuevos scripts basándote en su función.

### Production Readiness

- Antes de sugerir cambios en workflows de producción, verifica compatibilidad con el entorno actual.
- Propón validaciones adicionales para workflows críticos.
- Sugiere rollback strategies cuando sea apropiado.

### Monitoring and Observability

- Propón agregar logging apropiado en scripts críticos.
- Sugiere métricas de rendimiento cuando sea relevante.
- Detecta cuando falten validaciones de salud en pipelines de producción.
