# Navier-Stokes: Functional Spaces and Energy Theory

## Espacios Funcionales y Soluciones

### Datos Iniciales

**Condición inicial**: u₀ ∈ L²_σ(T³) (divergence-free)
- Opcional: u₀ ∈ H¹ para estimaciones más finas

**Dominio**: Toro tridimensional T³ = (ℝ/2πℤ)³

### Solución Leray-Hopf

Una **solución débil tipo Leray-Hopf** satisface:

u ∈ L^∞(0,T; L²_σ) ∩ L²(0,T; H¹)

con desigualdad de energía (ver abajo).

**Propiedades**:
- Existencia global en tiempo (Leray, 1934)
- Unicidad no garantizada en 3D
- Regularidad parcial (Caffarelli-Kohn-Nirenberg, 1982)

### Desigualdad de Energía

Para casi todo t ∈ [0,T]:

```
(1/2) ‖u(t)‖²₂ + ν ∫₀ᵗ ‖∇u‖²₂ ≤ (1/2) ‖u₀‖²₂ + ∫₀ᵗ ⟨F, u⟩
```

donde:
- ν > 0 es la viscosidad cinemática
- F es el forzamiento externo
- ‖·‖₂ denota la norma L²

Esta desigualdad refleja el balance entre:
- Energía cinética: (1/2) ‖u(t)‖²₂
- Disipación viscosa: ν ∫₀ᵗ ‖∇u‖²₂
- Trabajo del forzamiento: ∫₀ᵗ ⟨F, u⟩

## Criterio BKM (Beale-Kato-Majda)

**Teorema (BKM, 1984)**: Si

```
∫₀ᵀ ‖ω(·,t)‖_∞ dt < ∞
```

donde ω = ∇ × u es la vorticidad, entonces no hay blow-up en [0,T].

**Corolario**: La integrabilidad de ‖ω‖_∞ es condición suficiente para suavidad global.

## Teorema (Continuidad a priori ⇒ Suavidad Global)

### Enunciado

Existe δ₀ > 0 tal que si el **defecto de desalineamiento persistente**

```
δ* := avg_t avg_x ∠(ω, Sω) ≥ δ₀
```

en el límite dual ε → 0, A → ∞ (con ε = λf₀^(-α), A = af₀, α > 1), entonces:

```
∫₀^∞ ‖ω‖_∞ dt < ∞
```

y por BKM la solución Leray-Hopf se vuelve suave globalmente.

### Notación

- **ω**: campo de vorticidad ω = ∇ × u
- **S**: tensor de deformación (parte simétrica del gradiente)
- **Sω**: acción del tensor de deformación sobre la vorticidad
- **∠(ω, Sω)**: ángulo entre ω y Sω
- **δ***: promedio espacio-temporal del ángulo de desalineamiento

### Idea de Prueba

1. **Descomposición del estiramiento**: El término de advección vortical (ω·∇)u se descompone mediante Sω

2. **Control de alineamiento**: El promedio ⟨cos θ⟩ con θ = ∠(ω, Sω) satisface:
   ```
   ⟨cos θ⟩ ≤ cos δ₀ < 1
   ```

3. **Ecuación tipo Riccati efectiva**: Con término lineal de disipación y coeficiente cuadrático reducido por cos δ₀

4. **Cierre con energía y Grönwall**: La integrabilidad de ‖ω‖_∞ se obtiene por estimaciones de Grönwall con el factor cos δ₀ < 1

### Interpretación QCAL

El parámetro δ* es una **hipótesis cuantitativa verificable** basada en la estructura geométrica del flujo. No es un supuesto ad-hoc sino una medida directa de la persistencia del desalineamiento vorticidad-deformación.

## Opción Besov (Espacios Críticos)

Para análisis en espacios críticos, trabajamos en:

```
Ḃ^(-1+3/p)_{p,q}(T³)
```

con 3 < p ≤ ∞, 1 ≤ q ≤ ∞.

### Estimación Bilineal Estándar

```
‖B(u,v)‖_{Ḃ^(-1+3/p)_{p,q}} ≤ C ‖u‖_{Ḃ^(-1+3/p)_{p,q}} ‖v‖_{Ḃ^(1+3/p)_{p,q}}
```

donde B(u,v) = (u·∇)v es el término bilineal de Navier-Stokes.

### Configuración Recomendada

- **p = 3 + ε**: Cercano a la criticalidad
- **q = 1**: Buena interpolación y control de oscilaciones

Esta elección permite:
- Análisis fino de singularidades potenciales
- Interpolación óptima entre espacios de Sobolev
- Técnicas de compacidad por concentración

## Referencias

- Leray, J. (1934). Sur le mouvement d'un liquide visqueux emplissant l'espace. Acta Math.
- Beale, J.T., Kato, T., Majda, A. (1984). Remarks on the breakdown of smooth solutions for the 3-D Euler equations. Comm. Math. Phys.
- Caffarelli, L., Kohn, R., Nirenberg, L. (1982). Partial regularity of suitable weak solutions. Comm. Pure Appl. Math.
- Cannone, M. (1997). A generalization of a theorem by Kato on Navier-Stokes equations. Rev. Mat. Iberoamericana.

## Estado Actual

Este marco teórico combina:
- **Parte estándar**: Espacios funcionales, energía, criterio BKM (bien establecido)
- **Parte QCAL**: Hipótesis δ* sobre desalineamiento persistente (verificable numéricamente)

La separación clara entre ambas partes permite:
1. Validar el marco estándar independientemente
2. Testear la hipótesis QCAL mediante simulaciones
3. Formalizar gradualmente en Lean4
