# Problema 281 de Erdős — informe de investigación verificable

**Fecha:** 9 de noviembre de 2026 · **Tipo:** nota de investigación + verificación formal (Lean 4 / Mathlib) + comprobaciones numéricas · **Estado:** sin revisión por pares; elaborado con asistencia de IA (Claude Code) a pedido del titular del repositorio.

> **Problema (Erdős–Graham, 1980 [1]).** Sea $n_1 \lt n_2 \lt \cdots$ una sucesión infinita tal que, para toda elección de clases de congruencia $a_i \pmod{n_i}$, el conjunto de enteros que no satisfacen ninguna de las congruencias tiene densidad $0$. ¿Es cierto que para todo $\varepsilon \gt 0$ existe $k$ tal que, para toda elección de clases, la densidad de los enteros que no satisfacen ninguna de las congruencias $a_i \pmod{n_i}$, $1 \le i \le k$, es menor que $\varepsilon$?

## 1. Respuesta corta

**Sí.** La hipótesis (H) implica la conclusión uniforme (C), y de hecho son equivalentes. **[PROBADO]** — verificado aquí por Lean 4 + Mathlib, sin `sorry` y solo con los axiomas estándar; certeza **[ALTA]**, además respaldada por dos demostraciones publicadas en 2026 y una formalización independiente de terceros [2, 5, 6, 17].

**Importante:** el problema **no estaba abierto** al momento de este trabajo: fue resuelto en enero de 2026 (argumento profinito/ergódico de N. Somani con GPT‑5.2 Pro; y Davenport–Erdős 1936 + teorema de Rogers, observado por KoishiChan). Lo que se aporta aquí es (i) una **demostración finitaria nueva** (conteo doble + Markov + lema de König), **formalizada desde cero**; (ii) versiones **más fuertes** verificadas formalmente (hipótesis con densidad inferior; multiplicidad; forma entera bilateral; teorema de Rogers); (iii) la forma óptima del resultado y una extensión a grupos abelianos, con demostración escrita.

## 2. Hallazgos

Las citas [n] remiten a la lista de referencias (Sección 7). Etiquetas: **[PROBADO]** = aceptado por Lean en esta sesión; **[PLAUSIBLE]** = demostración informal completa en [`NOTA.md`](NOTA.md), sin verificación mecánica; **[NUMÉRICO]** = comprobación por cómputo; **[LITERATURA]** = resultado publicado.

1. **Estado del problema [LITERATURA, certeza ALTA].** Resuelto afirmativamente en enero de 2026 por dos vías independientes [2, 5, 17]; existe una formalización en Lean del argumento profinito [6]. El teorema de Rogers aparece en Halberstam–Roth [4] y el de Davenport–Erdős en [3].
2. **Teorema principal, demostración finitaria [PROBADO].** `Erdos281.erdos_281`: (H) ⟹ (C); `erdos_281_converse`: (C) ⟹ (H); `erdos_281_zmod`: forma con clases en `ZMod (n i)`. La demostración (NOTA §3) no usa medida de Haar, teoría ergódica, Davenport–Erdős ni Rogers.
3. **Forma fuerte [PROBADO].** `erdos_281_strong`: si (C) falla al nivel $\varepsilon$, existe una elección explícita $b$ (un "desplazamiento profinito" de una elección extremal) cuyo conjunto no cubierto tiene al menos $(\varepsilon/2)N$ elementos en $[0,N)$ para $N$ arbitrariamente grandes.
4. **Teorema de Rogers [PROBADO].** `Rogers.rogers`: entre todas las elecciones de clases, la homogénea $a = 0$ es la que menos cubre. (Resultado clásico [4, 5]; aquí con demostración formal propia.)
5. **Hipótesis más débil [PROBADO].** `erdos_281_lower`: basta suponer densidad *inferior* cero para toda elección; `erdos_281_strong_lower`: si (C) falla al nivel $\varepsilon$, alguna elección deja sin cubrir al menos $(\varepsilon/2)N$ enteros en $[0,N)$ para **todo** $N$ grande. Usa una desigualdad maximal elemental (`maximal_ineq`). Este enunciado es estrictamente más fuerte que el del problema y que el enunciado formal público [6].
   **Forma entera [PROBADO].** `erdos_281_int`: el mismo teorema para subconjuntos de $\mathbb{Z}$ con densidad bilateral $\#(S \cap [-N,N])/(2N+1)$ y clases en `ZMod (n i)`, es decir, con la forma exacta del enunciado formal de [6].
   **Rogers ⟹ basta $a = 0$ [PROBADO].** `uniform_iff_homogeneous`: (C) equivale a (C) solo para la elección homogénea (los módulos forman una *sucesión de Behrend*).
6. **Forma óptima [PLAUSIBLE; partes PROBADAS].** Para toda sucesión, $\max_a \overline{d}(R(a)) = \max_a \underline{d}(R(a)) = \varepsilon^\ast := \lim_k \max_a d_k(a)$, y en $\mathbb{Z}$ vale $\varepsilon^\ast = 1 - \delta^\ast$ con $\delta^\ast$ la densidad logarítmica del conjunto de múltiplos (NOTA, Teoremas 2 y 3). La hipótesis puede debilitarse a "densidad inferior cero para toda elección" o a "densidad cero para $a = 0$", pero no a "densidad inferior cero para $a=0$".
7. **Multiplicidad [PROBADO].** Bajo (H) y $n_1 \ge 2$, para cada $r$ casi todo entero satisface al menos $r$ de las congruencias, uniformemente en la elección (`erdos_281_multiplicity`, `few_congruences_density_zero`; NOTA, Teorema 4). Las colas de la sucesión heredan la propiedad (`tail_uniform`).
8. **Grupos abelianos [PLAUSIBLE] y contraejemplo [NUMÉRICO + verificación directa].** El enunciado vale para clases laterales de subgrupos de índice finito de cualquier grupo abeliano (NOTA, Teorema 7.1), donde el teorema de Rogers es falso: en $(\mathbb{Z}/2)^2$ tres clases laterales cubren 3 elementos mientras los tres subgrupos cubren 4 (NOTA, Ejemplo 7.2).

## 3. Tabla afirmación–evidencia

(Las columnas "n" y "efecto (IC 95 %)" del formato estándar no aplican a un resultado matemático; se reemplazan por "tipo de evidencia" y "alcance".)

| # | Afirmación | Evidencia | Tipo | Alcance | Certeza |
|---|---|---|---|---|---|
| 1 | El Problema 281 tiene respuesta afirmativa | `Erdos281.erdos_281`, `erdos_281_zmod` (este repo); [2, 5, 6, 17] | Lean + literatura | Sucesiones estrictamente crecientes de módulos positivos; densidad natural en $\mathbb{N}$ | **[PROBADO]**, ALTA |
| 2 | Recíproco: (C) ⟹ (H) | `erdos_281_converse` | Lean | ídem | **[PROBADO]** |
| 3 | Si (C) falla, hay una elección con densidad superior positiva del conjunto no cubierto | `erdos_281_strong` | Lean | ídem | **[PROBADO]** |
| 4 | Teorema de Rogers | `Rogers.rogers`, `Rogers.rogers_uncovered`; [4, 5]; 367 familias exhaustivas | Lean + literatura + numérico | Módulos que dividen a $N$ | **[PROBADO]**, ALTA |
| 5 | Versión para subconjuntos de $\mathbb{Z}$ con densidad bilateral y clases en `ZMod` | `Erdos281.erdos_281_int` | Lean | Mismo formato que el enunciado formal de [6] | **[PROBADO]** |
| 6 | Rogers en forma de densidad: $d_k(a) \le d_k(0)$; (C) ⟺ (C) solo para $a = 0$ | `density_le_homogeneous`, `uniform_of_homogeneous`, `uniform_iff_homogeneous` | Lean | $\mathbb{N}$ | **[PROBADO]** |
| 7 | Multiplicidad uniforme (Teorema 4) y herencia a las colas (Lema 6.1) | `tail_uniform`, `erdos_281_multiplicity`, `erdos_281_multiplicity_of_hyp`, `few_congruences_density_zero` | Lean | $n_1 \ge 2$ | **[PROBADO]** |
| 8 | Basta "densidad inferior cero para toda elección"; si (C) falla, alguna elección tiene densidad *inferior* $\ge \varepsilon/2$ | `maximal_ineq`, `erdos_281_strong_lower`, `erdos_281_lower` | Lean | $\mathbb{N}$; enunciado estrictamente más fuerte que el original | **[PROBADO]** |
| 9 | Valor exacto: $\max_a \overline{d}(R(a)) = \max_a \underline{d}(R(a)) = \varepsilon^\ast$, con densidad natural existente | NOTA §4 (Prop. 4.2); la cota inferior $\varepsilon/2$ sí está formalizada (fila 8) | Demostración informal | Toda sucesión | **[PLAUSIBLE]** |
| 10 | $\overline{d}(R(0)) = 1 - \delta^\ast$ (dirección necesaria de Davenport–Erdős) | NOTA §5.2; [3, 4]; comprobación numérica de la monotonía | Demostración informal + literatura + numérico | $\mathbb{Z}$ | **[PLAUSIBLE]**; el teorema completo es **[LITERATURA]**, ALTA |
| 11 | "Densidad inferior cero solo para $a = 0$" no basta | NOTA §5.3(d); usa [11, 12, 13] | Demostración informal + literatura | Ejemplo por bloques | **[PLAUSIBLE]** (depende de un teorema citado) |
| 12 | Extensión a grupos abelianos | NOTA §7 | Demostración informal | Sucesiones equidistribuidas (p. ej. Følner) | **[PLAUSIBLE]** |
| 13 | Rogers falla en grupos no cíclicos; el atajo $a = 0$ falla en $\mathbb{Z}^2$ | NOTA Ej. 7.2; `verificacion/checks.py` (bloque 3) | Verificación directa + numérico | $(\mathbb{Z}/2)^2$, $\mathbb{Z}^2$ | **[NUMÉRICO]** + cálculo a mano; coincide con [5] |

## 4. Limitaciones y vacíos

- **Novedad limitada del resultado central.** La respuesta al problema ya era conocida [2, 5]. No pude leer directamente el hilo del foro ni la conversación original (el sitio bloquea el acceso automatizado; usé la captura aportada, un espejo parcial y fuentes secundarias). Según esas fuentes, T. Tao publicó una traducción combinatoria del argumento ergódico con la desigualdad maximal de Hardy–Littlewood, que puede solaparse con NOTA §4. La búsqueda bibliográfica (Crossref/FastTrack, Consensus, web) no puede garantizar exhaustividad.
- **Partes sin verificación mecánica.** Las filas [PLAUSIBLE] de la tabla (9–12) tienen demostración escrita completa en `NOTA.md`, pero no están formalizadas.<!-- REVISION_README -->
- **Dependencia de literatura profunda.** La fila 11 usa que la densidad de los enteros con un divisor en $(T, 2T]$ tiende a $0$ [12, 13].
- **Sin versión cuantitativa.** No se obtiene $k$ en función de $\varepsilon$; en general no puede existir sin información aritmética sobre la sucesión. Qué sucesiones cumplen la hipótesis equivale a caracterizar las *sucesiones de Behrend*, un problema clásico y difícil [9].
- **Qué lo resolvería:** formalizar el valor exacto de la Proposición 4.2, la Proposición 5.3 (Davenport–Erdős) y el Teorema 7.1 (grupos); contrastar con el hilo original cuando sea accesible.

## 5. Cómo reproducir

**Lean** (versiones exactas en [`lean/README.md`](lean/README.md)):

```bash
cd Erdos-281/lean
```

```bash
lake exe cache get
```

```bash
lake build
```

**Comprobaciones numéricas** (solo biblioteca estándar de Python 3; ~40 s):

```bash
python3 Erdos-281/verificacion/checks.py
```

## 6. Contenido de la carpeta

- [`NOTA.md`](NOTA.md) — nota matemática completa (enunciados, demostraciones, qué es conocido y qué es nuevo). Versión en PDF: [`NOTA.pdf`](NOTA.pdf).
- [`lean/`](lean/) — proyecto Lean 4 + Mathlib con las formalizaciones y su registro de verificación.
- [`verificacion/`](verificacion/) — `checks.py` y su salida `salida.txt`.

## 7. Referencias

Las referencias con DOI se verificaron contra Crossref en esta sesión. La lista completa y comentada está en [`NOTA.md`](NOTA.md#referencias); las principales:

1. P. Erdős, R. L. Graham, *Old and new problems and results in combinatorial number theory*, Monogr. Enseign. Math. 28, 1980. (Sin DOI; existencia confirmada por la reseña [doi:10.2307/2320942](https://doi.org/10.2307/2320942).)
2. T. F. Bloom (ed.), *Erdős Problem #281*, <https://www.erdosproblems.com/281>, con su hilo de discusión.
3. H. Davenport, P. Erdős, *On sequences of positive integers*, Acta Arith. 2 (1936), 147–151. [doi:10.4064/aa-2-1-147-151](https://doi.org/10.4064/aa-2-1-147-151)
4. H. Halberstam, K. F. Roth, *Sequences*, 2.ª ed., Springer, 1983. [doi:10.1007/978-1-4613-8227-0](https://doi.org/10.1007/978-1-4613-8227-0)
5. T. Tao, *Rogers' theorem on sieving*, 19‑1‑2026, <https://terrytao.wordpress.com/2026/01/19/rogers-theorem-on-sieving/>
6. Enunciado formal (Google DeepMind, *formal-conjectures*): <https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/281.lean>; demostración formal del argumento de Somani: <https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos281.lean>
7. M. Filaseta, K. Ford, S. Konyagin, C. Pomerance, G. Yu, J. Amer. Math. Soc. 20 (2007), 495–517. [doi:10.1090/S0894-0347-06-00549-2](https://doi.org/10.1090/S0894-0347-06-00549-2)
8. R. J. Simpson, Discrete Math. 59 (1986), 181–190. [doi:10.1016/0012-365X(86)90079-8](https://doi.org/10.1016/0012-365X(86)90079-8)
9. R. R. Hall, *Sets of Multiples*, Cambridge Univ. Press, 1996. [doi:10.1017/CBO9780511566011](https://doi.org/10.1017/CBO9780511566011)
10. F. A. Behrend, Bull. Amer. Math. Soc. 54 (1948), 681–684. [doi:10.1090/S0002-9904-1948-09056-5](https://doi.org/10.1090/S0002-9904-1948-09056-5)
11. A. S. Besicovitch, Math. Ann. 110 (1935), 336–341. [doi:10.1007/BF01448032](https://doi.org/10.1007/BF01448032)
12. P. Erdős, *A generalization of a theorem of Besicovitch*, J. London Math. Soc. 11 (1936), 92–98. [doi:10.1112/jlms/s1-11.2.92](https://doi.org/10.1112/jlms/s1-11.2.92)
13. K. Ford, Ann. of Math. 168 (2008), 367–433. [doi:10.4007/annals.2008.168.367](https://doi.org/10.4007/annals.2008.168.367)
14. A. Dymek, S. Kasjan, J. Kułaga‑Przymus, M. Lemańczyk, Trans. Amer. Math. Soc. 370 (2018), 5425–5489. [doi:10.1090/tran/7132](https://doi.org/10.1090/tran/7132)
15. S. Kasjan, G. Keller, M. Lemańczyk, Int. Math. Res. Not. 2019, 2690–2734. [doi:10.1093/imrn/rnx196](https://doi.org/10.1093/imrn/rnx196)
16. E. Lindenstrauss, Invent. Math. 146 (2001), 259–295. [doi:10.1007/s002220100162](https://doi.org/10.1007/s002220100162)
17. T. Tao et al., *AI contributions to Erdős problems* (wiki), <https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems>
18. P. Balister, B. Bollobás, R. Morris, J. Sahasrabudhe, M. Tiba, Invent. Math. 228 (2022), 377–414. [doi:10.1007/s00222-021-01087-5](https://doi.org/10.1007/s00222-021-01087-5)
19. B. Hough, Ann. of Math. 181 (2015), 361–382. [doi:10.4007/annals.2015.181.1.6](https://doi.org/10.4007/annals.2015.181.1.6)

Ninguna de las referencias es un preprint sin revisión, salvo las fuentes web [2, 5, 6, 17], que son páginas, blogs y repositorios (no publicaciones arbitradas).
