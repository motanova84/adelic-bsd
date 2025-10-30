# P ≠ NP: Anti-Barriers and Technical Approach

## Sección 2.7 — Anti-barreras

### Contexto

Las tres principales barreras en teoría de la complejidad son:
1. **Relativización** (Baker-Gill-Solovay, 1975)
2. **Natural Proofs** (Razborov-Rudich, 1997)
3. **Algebrización** (Aaronson-Wigderson, 2008)

Nuestro enfoque via **Separator-Information Lower Bounds (SILB)** evita estas tres barreras.

### Por qué no relativiza

Los límites SILB dependen de la estructura de separadores en grafos de incidencias de fórmulas, no de acceso a oráculos. La topología de separación es una propiedad intrínseca de la representación del problema, no un comportamiento de caja negra. Por tanto, el argumento no puede ser trasladado a modelos relativizados donde el acceso al oráculo abstraiga esta estructura.

**Técnicamente**: El ancho de árbol (treewidth) de un grafo de incidencia de fórmulas no puede ser definido consistentemente en presencia de oráculos arbitrarios, ya que la estructura combinatoria depende de la representación explícita.

### Por qué no es "natural" (Razborov-Rudich)

Los predicados usados en SILB no son densos ni constructibles en tiempo polinómico sobre {0,1}^n. En cambio, dependen de:

- Gadgets Tseitin sobre expansores Ramanujan con etiquetas pseudo-aleatorias fijadas
- Información condicional restringida por topología de separación
- Propiedades no-locales de grafos de incidencia

Estos predicados no satisfacen la condición de "naturalidad" de Razborov-Rudich porque no pueden ser evaluados eficientemente en instancias aleatorias sin conocer la estructura global del grafo.

**Técnicamente**: La densidad de funciones satisfaciendo propiedades de separación no es exponencialmente grande en la clase de todas las funciones booleanas; está concentrada en familias con estructura topológica específica.

### Por qué no algebriza

La algebrización permite extender argumentos a modelos algebraicos como A[x]/⟨x^k⟩. Sin embargo, el traspaso a estos modelos rompe la monotonicidad clave de la información en separadores.

**Técnicamente**: La información condicional I(X;Y|Z) en separadores se comporta monotónicamente en grafos discretos, pero esta propiedad no se preserva bajo extensiones algebraicas donde las variables pueden tomar valores en anillos cociente. La transición de estructura combinatoria discreta a estructura algebraica destruye el orden parcial esencial en la jerarquía de separadores.

## Ruta Técnica

### Pipeline completo

```
Treewidth → Protocolo de comunicación → Cota inferior de circuitos
```

1. **Treewidth**: Caracterización del ancho de árbol de grafos de fórmulas vía separadores
2. **Protocolo de comunicación**: Traducción a complejidad de comunicación usando estructura de separadores
3. **Lifting con gadgets G_lift**: Aplicación de gadgets explícitos (parámetros fijados) para amplificar límites
4. **Cota de circuitos**: Traducción final a tamaño de circuitos

### Componentes formales

Los siguientes módulos Lean formalizan los componentes clave:

- `formal/Treewidth/SeparatorInfo.lean`: Lema SILB y flujo de información en separadores
- `formal/Lifting/Gadgets.lean`: Validez del gadget G_lift, construcción de Ramanujan
- `formal/LowerBounds/Circuits.lean`: Traducción a circuitos, familias uniformes, padding estructural

### Pruebas de uniformidad

Las familias de circuitos construidas son **DLOGTIME-uniformes**, garantizando que:
- La descripción del circuito para tamaño n puede ser computada en tiempo O(log n)
- El padding estructural está controlado explícitamente
- No hay dependencias circulares en la construcción

## Referencias

- Baker, T., Gill, J., & Solovay, R. (1975). Relativizations of the P=?NP question. SICOMP.
- Razborov, A. & Rudich, S. (1997). Natural proofs. JCSS.
- Aaronson, S. & Wigderson, A. (2008). Algebrization: A new barrier in complexity theory. STOC.

## Estado actual

Los stubs formales están en su lugar. El desarrollo completo de las pruebas requiere:
1. Formalización de grafos de incidencia y descomposiciones en árbol
2. Teoría de comunicación en Lean (protocolos, límites inferiores)
3. Biblioteca de grafos expansores (Ramanujan, zigzag product)
4. Lifting theorems conectando comunicación y circuitos
