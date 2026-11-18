# Guion: certificados, tamaños y costes en las pruebas de complejidad

Este documento es un guion de apoyo para una presentación informal con el código abierto. Los fragmentos son selecciones del estado actual: se omiten cuerpos y cláusulas cuando interesa enseñar solo la idea. Las rutas llevan al código completo.

## Recorrido sugerido

1. **Objetivo y alcance**: qué necesita una prueba de NP y qué partes están formalizadas.
2. **Certificados cortos**: Set Cover como ejemplo sencillo y CDPC como ejemplo estructural.
3. **Novedades de los dos últimos commits**: tamaños ponderados, contexto y costes de los traits.
4. **Composición de la prueba**: presupuestos, bucles y puente al tamaño exacto de entrada.
5. **Reducciones y cierre**: qué garantiza ya Hitting Set → Set Cover y qué queda para CDPC.

Si hay poco tiempo, mostrar los contratos de `VerifySetCover` y `SetCoverHasShortCertificate`, la fórmula de `CostRepresentation`, el puente `set_cover_input_size_bound_polynomial` y el contrato de la transformación de Hitting Set. CDPC es un buen segundo ejemplo para explicar por qué el tamaño de un certificado no es solo su número de nodos.

## 1. Qué se quiere demostrar

Para un problema de decisión, la estructura habitual de pertenencia a NP es:

* Una instancia positiva tiene **algún certificado de tamaño polinómico** en el tamaño de la instancia.
* Un verificador acepta exactamente los certificados correctos y su trabajo está acotado polinómicamente en el tamaño de la instancia y del certificado. En particular, al sustituir un certificado corto, se obtiene una cota polinómica en la instancia.

Para NP-completitud hace falta además una **reducción** desde un problema NP-difícil: transformación efectiva, equivalencia de respuestas y coste polinómico. En este repositorio se formalizan las definiciones matemáticas, las representaciones, verificadores, transformaciones y cotas que contribuyen a ese argumento.

**Alcance actual:** el contador es un modelo explícito de trabajo ponderado. La realización de sus tarifas en una implementación binaria concreta, el coste de direccionamiento y una conexión completa con una codificación binaria siguen pendientes. Además, la reducción matemática Set Cover → CDPC tiene obligaciones sin cuerpo y falta conectar por completo su construcción instrumentada con el verificador de CDPC. Por tanto, no se debe presentar el proyecto como una prueba acabada de NP-completitud absoluta o de tiempo binario de extremo a extremo.

### Qué aportan los commits

* **`cd42925`, anterior a los dos últimos:** corrección completa de los verificadores y existencia de certificados cortos para Set Cover y CDPC, con sus cotas polinómicas. Después esas pruebas se adaptaron a los tamaños ponderados.
* **`13826e6`, modelo de costes ponderados:** un contador que tiene en cuenta trabajo estructural y tamaños de representación; longitudes binarias; contextos, tarifas y presupuestos comunes; composición de cotas por fases.
* **`91f4b7e`, instancias genéricas y cotas:** instancias con campos nombrados y etiquetas genéricas, pesos explícitos, distinción clara entre tamaño exacto y cotas internas, y generalización de la reducción Hitting Set → Set Cover.

## 2. Modelo matemático, representación y certificado

Mostrar [Problems/SetSystemRepresentation.dfy](Problems/SetSystemRepresentation.dfy) y [Problems/SetCover.dfy](Problems/SetCover.dfy):

```dafny
datatype SetSystemInstance<T(==)> =
  SetSystemInstance(universe:Set<T>, sets:SetSet<T>, k:nat)
{
  ghost function Model():SetSystemModel<T>
  { SetSystemModel(universe.Model(), sets.Model(), k) }
}

ghost predicate SetCoverCertificate<T>(instance:SetCoverModel<T>, cover:set<set<T>>)
{
  cover <= instance.sets && IsCover(instance.universe, cover) && |cover| <= instance.k
}
```

La **instancia instrumentada** contiene colecciones con contratos de costes; `Model()` ofrece la vista matemática que usan las especificaciones. El certificado se pasa por separado: así el mismo predicado describe cuándo una propuesta concreta es correcta. `T` es genérico y su peso se aporta explícitamente a las pruebas de tamaño y coste.

En Set Cover hay una convención de dominio que conviene mencionar: una instancia válida exige que la familia completa cubra el universo; la pregunta es si existe una subfamilia de tamaño a lo sumo `k`. Véase `SetCoverValidInstance` en el mismo archivo.

En CDPC, [Problems/CDPCRepresentation.dfy](Problems/CDPCRepresentation.dfy) separa `CDPCInstance<Q>` de `CDPCModel<Q>`: los umbrales almacenados son pares racionales y el modelo usa sus valores reales exactos. Las multiplicidades se guardan como enteros, sin expandir la población en individuos. Las etiquetas de preguntas pueden ser genéricas; una salida con etiquetas que son conjuntos usa interfaces especializadas y un tamaño de etiqueta compuesto.

## 3. Corrección y certificados cortos

### Set Cover: el caso directo

Mostrar [Verifications/VerificationSetCover.dfy](Verifications/VerificationSetCover.dfy), al principio del archivo:

```dafny
ghost method SetCoverHasShortCertificate<T>(instance:SetSystemInstance<T>)
    returns (certificate:SetSet<T>)
  requires instance.universe.Init() && instance.sets.Init()
  requires SetCoverValidInstance(instance.Model())
  requires SetCover(instance.Model())
  ensures SetCoverCertificate(instance.Model(), certificate.Model())
  ensures forall weight:T -> nat ::
    certificate.Size(weight) <= BudgetSetCoverCertificateSize(instance.Size(weight))
```

Es un método `ghost`: prueba existencia, no es un algoritmo que encuentre la solución. Dada una instancia positiva, el cuerpo elige una cobertura matemática y la envuelve en una colección válida e inicializada. La cota vale uniformemente para cualquier función de peso.

La idea matemática es muy breve: un certificado correcto es un subconjunto de la familia de entrada. Por tanto, su representación exacta ocupa como máximo la de esa familia y, por tanto, como máximo el tamaño de la instancia. El lema `set_cover_certificate_instance_size_bound` lo prueba mediante `size_subset_set`; `BudgetSetCoverCertificateSize(n)` es exactamente `n`. No hace falta acotar el valor numérico de `k`.

El contrato del verificador, en el mismo archivo, conecta esa existencia con un procedimiento:

```dafny
method VerifySetCover<T>(instance:SetSystemInstance<T>,
    certificate:SetSet<T>, ghost weight:T -> nat)
    returns (accepted:bool, ghost counter:nat)
  // ... precondiciones de inicialización y validez ...
  ensures accepted == SetCoverCertificate(instance.Model(), certificate.Model())
  ensures accepted ==> SetCover(instance.Model())
  ensures 0 < counter <= BudgetVerifySetCover(SetCoverInputSize(instance, certificate, weight))
```

La igualdad caracteriza aceptación y rechazo, no solo la corrección de las respuestas positivas. La cota usa la **entrada completa**, incluido el certificado suministrado, también si es incorrecto. El corolario `budget_verify_set_cover_short_input_bound` en [Polynomial/PolynomialSetCover.dfy](Polynomial/PolynomialSetCover.dfy) sustituye el tamaño de un certificado corto y da una cota solo en función de la instancia.

### CDPC: primero nodos, después tamaño representado

Mostrar [Problems/CDPCLemmas.dfy](Problems/CDPCLemmas.dfy), `cdpc_certificate_node_count_bound`, y [Verifications/VerificationCDPC.dfy](Verifications/VerificationCDPC.dfy), `CDPCHasShortCertificate`:

```dafny
lemma cdpc_certificate_node_count_bound<Q(!new)>(instance:CDPCModel<Q>, tree:InterviewModel<Q>)
  requires CDPCValidInstance(instance)
  requires CDPCCertificate(instance, tree)
  ensures InterviewNodes(tree) <=
    2*|instance.fitness.Keys|*|instance.questions|+1
```

Aquí el certificado es un árbol de entrevista binaria. `InterviewFits` limita las preguntas que pueden aparecer en cada camino y evita repetirlas; la semántica hace terminar las ramas sin candidatos. La inducción sobre subárboles usa la partición de los **tipos de candidatos** entre las respuestas, y obtiene una cota cuadrática en número de tipos y preguntas. El recuento incluye las hojas `End` y ambas posiciones hijas. No depende del valor de las multiplicidades.

Pero contar nodos no basta: cada nodo puede llevar una etiqueta larga. La prueba `cdpc_certificate_instance_size_bound` de [Polynomial/PolynomialCDPC.dfy](Polynomial/PolynomialCDPC.dfy) combina la cota de nodos con el hecho de que las preguntas del certificado pertenecen a las de la instancia y, por tanto, sus pesos están acotados. El resultado es `certificate.Size(weight) <= BudgetCDPCCertificateSize(instance.Size(weight))`, con una cota cúbica. La existencia del árbol correcto procede de la propia definición existencial de CDPC; el método ghost lo elige y le aplica estos lemas.

`VerifyCDPC` también comprueba primero el tamaño estructural mediante `CountInterviewBounded`: al superar el límite `2*population*questionCount+1` puede rechazar, porque `cdpc_over_limit_not_certificate` prueba que ese árbol no es un certificado válido. Después comprueba estructura y semántica. La cota pública del contador sigue expresada en el tamaño de la entrada completa, que también tiene en cuenta etiquetas ajenas o largas de certificados rechazados.

## 4. Tres niveles de tamaño

La novedad importante es no confundir cuántos objetos hay, cuánto anidamiento hay y cuánto ocupan sus etiquetas.

| Medida | Significado | Ejemplo |
| --- | --- | --- |
| `Cardinality` | Número de elementos del nivel o camino considerado. | `|S|` y el máximo tamaño de un conjunto miembro. |
| `VolumeBound` | Cota estructural sin pesos, formada con máximos independientes. | Para `SetSet`: `Cardinality() * (1 + Cardinality1())`. |
| `SizeBound(weight)` | Cota de representación del modelo, con estructura y pesos. | `1 + 3*VolumeBound()*LeafBits(weight)`. |
| `UCardinality`, `UVolumeBound`, `USizeBound` | Versiones sobre el universo retenido por el trait. | Permiten acotar estados intermedios aunque cambie `Model()`. |
| `Size_*`, `Size`, `*InputSize` | Tamaños exactos de referencia según el esquema definido en el proyecto. | Incluyen cabeceras, entradas y pesos almacenados. |

En [Foundations/StructuralSizes.dfy](Foundations/StructuralSizes.dfy) aparecen las fórmulas comunes:

```dafny
ghost function StructuralVolumeBound(count:nat, childVolume:nat):nat
{ count*(1+childVolume) }

ghost function RepresentationSizeBound(volume:nat, bits:nat):(size:nat)
  requires 1 <= bits
{ 1+3*volume*bits }
```

Los máximos de los distintos niveles pueden proceder de hijos diferentes: son una envolvente cómoda para la prueba, no un recuento exacto. `LeafBits(weight)` es el máximo de los pesos de las hojas, normalizado a al menos uno. Para números aparecen `NatBits`, `IntBits`, `BoolBits` y `RationalBits`: por ejemplo, un `k` grande en binario se mide por `NatBits(k)`, no por `k`. Los racionales cuentan los campos realmente almacenados, incluso si la fracción no está reducida.

La cota de representación no es el tamaño exacto. El tamaño de referencia de un conjunto, `Size_set` en [Foundations/ExactCollectionSizes.dfy](Foundations/ExactCollectionSizes.dfy), suma la cabecera y las contribuciones de cada elemento y su peso. Es exacto respecto a **esa definición matemática de representación**, no una afirmación de que ya exista una codificación binaria concreta realizada y medida.

## 5. `*InputSize`, `*InputSizeBound` y el puente polinómico

En [Problems/SetSystemRepresentation.dfy](Problems/SetSystemRepresentation.dfy):

```dafny
// En SetSystemInstance<T>
ghost function Size(weight:T -> nat):nat
{ 1+universe.Size(weight)+sets.Size(weight)+NatBits(k) }

ghost function SetCoverInputSize<T>(instance:SetSystemInstance<T>, certificate:SetSet<T>, weight:T -> nat):nat
{ instance.Size(weight)+certificate.Size(weight) }
```

`instance.Size(weight)` mide la instancia de Set Cover o Hitting Set; `SetCoverInputSize` añade **todo** el certificado. La distinción importa: una propuesta incorrecta podría incluir elementos que no aparecen en la instancia, así que su tamaño no se puede ocultar en el de esta.

`instance.SizeBound(weight)` suma las cotas internas de las colecciones, las cabeceras y los campos numéricos. `SetCoverInputSizeBound` añade `certificate.SizeBound(weight)` y `CDPCInputSizeBound` añade `interview.SizeBound(weight)`. Cada componente queda así acotado por una misma `n` en las precondiciones e invariantes.

Pero no basta con demostrar `InputSize <= InputSizeBound`: una cota interna podría ser excesivamente grande. El paso decisivo, en [Polynomial/PolynomialSetCover.dfy](Polynomial/PolynomialSetCover.dfy), es también la desigualdad inversa **polinómica**:

```dafny
lemma set_cover_input_size_bound_polynomial<T>(
    instance:SetSystemInstance<T>, certificate:SetSet<T>, weight:T -> nat)
  ensures var input := SetCoverInputSize(instance, certificate, weight);
    input <= SetCoverInputSizeBound(instance, certificate, weight) <=
      21*NatPower(input+1, 3)
```

Después, `budget_verify_set_cover_input_bound` combina este puente con la cota de las fases y obtiene el presupuesto público en función del tamaño exacto. Para CDPC existe el puente análogo, que también proporciona la cota de bits del máximo de multiplicidad, incluido el caso del mapa vacío.

## 6. Contextos y nueva estructura de `Cost`

Abrir [Foundations/RepresentationCosts.dfy](Foundations/RepresentationCosts.dfy) y [Collections/Set.dfy](Collections/Set.dfy):

```dafny
datatype SetContext<!E> = BitSetCost(ghost weight:E -> nat, ghost bound:nat := 0)

ghost function {:opaque} CostRepresentation(work:nat, size:nat, operandSize:nat):(cost:nat)
{
  var width := 1+size+operandSize;
  // ... prueba de las propiedades del resultado ...
  if work > 0 then work*width*width else 0
}
```

* `work` mide el trabajo estructural de la operación; `size` acota la representación del receptor; `operandSize` tiene en cuenta los operandos externos, no solo el receptor. En una inserción de mapa puede ser necesario contar **clave más valor**.
* El contexto proporciona pesos tipados para las hojas. `MapContext` distingue pesos de clave y valor; `NestedMapContext` incluye los tres tipos de hoja de las formas de mapa anidado. Sus proyecciones mantienen la misma cota auxiliar.
* `bound` es una **escala para la prueba**, no una entrada que cambie la tarifa. Los pesos y los tamaños efectivos alimentan `CostRepresentation`; la cota permite demostrar una garantía condicional común.

En el trait de conjuntos, `Cost(work, operandSize, context)` calcula `size := SizeBound(context.weight)` y devuelve `CostRepresentation(work, size, operandSize)`. Además garantiza:

```dafny
work <= context.bound+1 && SizeBound(context.weight) <= context.bound &&
  operandSize <= context.bound
  ==> cost <= BudgetPrimitiveStep(context.bound)
```

Así, cada operación declara su carga exacta al contador a través del mismo `Cost`, pero escoge el trabajo y el operando apropiados. Ejemplos de `Set<T>`:

```dafny
// Count: acceso de trabajo unitario.
ensures counter_out == counter_in + Cost(1, 0, context)

// Contains: recorrido del receptor y tamaño del elemento buscado.
ensures counter_out == counter_in + Cost(TraversalWork(), context.weight(e), context)

// Equal: trabajo combinado y tamaño del otro conjunto.
ensures counter_out == counter_in + Cost(CombinedTraversalWork(other),
  other.SizeBound(context.weight), context)
```

`TraversalWork()` es `VolumeBound()+1`: incluso una operación sobre una colección vacía tiene coste positivo. Las fábricas también cobran una tarifa propia. `Interview` expone su propio `Cost(context)` para accesos de trabajo unitario. Las operaciones de aritmética usan tarifas según la longitud de sus operandos; todas contribuyen al mismo contador ponderado. Los contextos y contadores `ghost` sirven para razonar y se eliminan de la ejecución compilada.

## 7. De operaciones a presupuesto del algoritmo

La cadena que interesa enseñar es:

```text
CostRepresentation(work, receptor, operandos)
    → Cost del trait y carga exacta del contador
    → BudgetPrimitiveStep(n), si se cumplen sus condiciones
    → Budget de cada bucle, árbol y fase
    → Budget…Phase(InputSizeBound)
    → Budget público(InputSize exacto), por sustitución polinómica
```

`BudgetPrimitiveStep(n)` domina una operación ordinaria cuando trabajo, receptor y operandos están acotados como exige el contrato de `Cost`. Su carácter polinómico está demostrado; para trabajo o operandos excepcionales se puede usar `cost_representation_uniform_bound` con cotas independientes.

Para los bucles, [Foundations/LoopCosts.dfy](Foundations/LoopCosts.dfy) ofrece `LinearLoopBudget(base, step, processed) = base + processed*step`, con lemas para inicializar, avanzar y acotar. En `CheckSetCoverCertificateAdmissible`, en [Verifications/VerificationSetCover.dfy](Verifications/VerificationSetCover.dfy), el invariante dice:

```dafny
invariant remaining.UniverseWithin(certificate)
invariant counter <= LinearLoopBudget(base, step,
  certificate.Cardinality() - remaining.Cardinality())
```

La primera relación preserva validez y una referencia para transportar cotas de universo y tamaño; la segunda acumula el presupuesto de los elementos ya procesados. La asignación inicial `remaining := certificate` es un alias; las operaciones persistentes posteriores mantienen los contratos de la colección original.

En [Polynomial/PolynomialSetCover.dfy](Polynomial/PolynomialSetCover.dfy), `BudgetVerifySetCoverPhase` suma los presupuestos de admisibilidad y núcleo. En [Polynomial/PolynomialCDPC.dfy](Polynomial/PolynomialCDPC.dfy), el presupuesto de verificación combina recuento, comprobación estructural y trabajo sobre el árbol, incluyendo filtros, clasificación, privacidad y aritmética racional. `HasPolynomialBound` fija coeficiente y grado antes de cuantificar sobre las entradas; `IsPolynomial` expresa que existen tales constantes.

Los grados públicos son deliberadamente holgados: por ejemplo, 15 para `BudgetVerifySetCover` y 21 para `BudgetVerifyCDPC`. Son testigos de crecimiento polinómico del contador, no mediciones de rendimiento ni cotas ajustadas. Los `Budget…CertificateSize` y `Budget…OutputSize` acotan el tamaño del resultado nombrado; no son cotas de memoria máxima de ejecución.

## 8. Reducciones y tamaños de construcción

### Hitting Set → Set Cover

Mostrar [Reductions/ReductionHittingSetToSetCover.dfy](Reductions/ReductionHittingSetToSetCover.dfy) y [Transformations/TransformationHittingSetToSetCover.dfy](Transformations/TransformationHittingSetToSetCover.dfy). Si ningún conjunto de la familia fuente es vacío, el universo destino es la familia `S` y para cada elemento `u` se construye su conjunto de incidencias `{ s in S | u in s }`. Así, elegir elementos que intersecten todos los conjuntos equivale a elegir incidencias que cubran `S`.

El caso de un conjunto fuente vacío se trata por separado: se construye una instancia destino válida pero negativa con límite cero. El lema `hitting_set_to_set_cover_correct` demuestra ambas direcciones. El contrato de la transformación instrumentada garantiza, entre otras cosas:

```dafny
ensures r.Model() == HittingSetToSetCover(instance.Model())
ensures SetCoverValidInstance(r.Model())
ensures 0 < counter <= BudgetTransformHittingSetToSetCover(instance.Size(weight))
```

También acota el tamaño exacto de salida por `BudgetHittingSetToSetCoverOutputSize` aplicado al tamaño exacto de la fuente. Las etiquetas destino son conjuntos fuente, por lo que su peso es `member => Size_set(member, weight)`: no se cobran como etiquetas atómicas de tamaño constante.

`HittingSetConstructionSizeBound` aporta la escala para receptores y operandos durante la construcción, incluso cuando las colecciones crecen y no basta una referencia fija. El puente final elimina esa escala interna en favor del tamaño exacto de la instancia fuente.

### Set Cover → CDPC: resultados y trabajo pendiente

La construcción instrumentada en [Transformations/TransformationSetCoverToCDPC.dfy](Transformations/TransformationSetCoverToCDPC.dfy) ya expone cotas polinómicas de contador y tamaño exacto de salida. Usa `CDPCConstructionSizeBound(n, bits)` para acotar representaciones en crecimiento, manteniendo separadas dimensiones estructurales y longitudes; el puente polinómico combina ambas mediante `n+bits`.

En cambio, en [Reductions/ReductionSetCoverToCDPC.dfy](Reductions/ReductionSetCoverToCDPC.dfy) siguen sin cuerpo las dos direcciones principales y otros cuatro lemas auxiliares. Aunque un lema con cuerpo invoque contratos sin cuerpo, esos contratos no son resultados demostrados. Siguen pendientes la equivalencia matemática completa, la correspondencia funcional y validez a nivel del problema de la salida instrumentada, y los adaptadores entre etiquetas compuestas y la representación del verificador. Las cotas de construcción, por sí solas, no cierran la reducción.

## 9. Cierre oral sugerido

> «La idea es separar la lógica del problema de su representación y del coste. Primero demostramos que los certificados son correctos y cortos. Después ponemos precio a operaciones concretas según trabajo y tamaño, componemos presupuestos para los algoritmos y demostramos que las escalas internas están relacionadas polinómicamente con el tamaño exacto de la entrada. Para completar una afirmación de complejidad binaria faltan la realización de ese modelo y las obligaciones de reducción que siguen abiertas».
