# Problema 142 de Erdős (fórmula asintótica para $r_k(N)$)

Informe de investigación con evidencia verificable. Nota sin revisión por pares, elaborada con asistencia de IA (10‑11‑2026).

## 1. Respuesta corta

**El Problema 142 no queda resuelto: sigue abierto, y no está al alcance de las técnicas actuales.** Pide una fórmula asintótica para $r_k(N)$, el mayor tamaño de un subconjunto de $\lbrace1,\dots,N\rbrace$ sin progresión aritmética de $k$ términos; hoy ni siquiera se conoce el orden de magnitud de $r_3(N)$.

Lo que sí se entrega, todo comprobable:

- una **revisión del estado del arte** con cada fuente verificada (§2 de la nota);
- **tres observaciones sobre las formalizaciones públicas** del problema, dos de ellas demostradas en Lean;
- **cuatro teoremas elementales en el régimen de progresiones largas** ($N\le k^2$), los cuatro verificados en Lean 4 (25 teoremas en total, compilación limpia);
- **valores exactos nuevos por ordenador** en $N=k^2$, que además **refutan una conjetura natural** que yo mismo había formulado.

Documento principal: [`NOTA.md`](NOTA.md) ([`NOTA.pdf`](NOTA.pdf)).

## 2. Hallazgos

Notación: $\tau_k(N)=N-r_k(N)$ es el menor tamaño de un conjunto que corta todas las progresiones de $k$ términos de $[1,N]$; $q$ es el menor factor primo de $k$.

**Estado del arte.**

- **[Verificado en la fuente]** Para $k=3$: $N\cdot2^{-(C+o(1))\sqrt{\log_2N}}\le r_3(N)$ con $C=2\sqrt{\log_2(24/7)}\approx2{,}667$ [7], y $r_3(N)\le N\exp(-c(\log N)^{1/6}/\log\log N)$ [15]. Los exponentes de $\log N$ no coinciden, luego no hay fórmula asintótica ni orden de magnitud.
- **[Verificado en la fuente]** Para $k\ge5$ la mejor cota superior publicada es $N\exp(-(\log\log N)^{c_k})$ [12]; un manuscrito de OpenAI de septiembre de 2026 afirma $N\exp(-c_k(\log N)^{\varepsilon_k})$ para todo $k\ge3$ [18]. No lo he verificado.

**Formalizaciones.**

- **[PROBADO]** (A) El enunciado formal `erdos_142` de `google-deepmind/formal-conjectures` es insatisfacible tal como está escrito: pide una sola función `answer` para todos los $k$, y $r_1(N)=N$, $r_2(N)=1$. Lo mismo su variante `isTheta`.
- **[PROBADO, condicional]** (B) La variante `erdos_142.variants.lower` ($r_k(N)=o(N/\log N)$), marcada allí como abierta, se deduce del teorema cuantitativo que `openai/math` declara demostrado.
- **[Comprobado por lectura]** (C) El enunciado Lean de ese teorema, $\exp(-c(\log\log N)^{1+\eta})$, es más débil que la cota del resumen del manuscrito.

**Progresiones largas.**

- **[PROBADO]** Teorema A: $r_k(N)=N-\lfloor N/k\rfloor$ para todo $N\le q(k-1)$.
- **[PROBADO]** Teorema B: ese rango es óptimo para todo $k\ge2$: $r_k(q(k-1)+1)=N-\lfloor N/k\rfloor-1$.
- **[PROBADO]** Teorema C: si $\tau_k(k^2)=k+s$ entonces $k\lt8s^2+8s+4$; es decir, en $N=k^2$ hace falta un exceso de orden $\sqrt k$ sobre la cota trivial.
- **[PROBADO]** Teorema D: $\tau_p(p^2)\le2p-3$ para todo primo $p\ge7$, con un conjunto explícito (además comprobado por fuerza bruta para todos los primos $p\le499$); para $p=5$, $\tau_5(25)=7$ por cálculo exacto **[NUMÉRICO]**.
- **[PLAUSIBLE]** Corolario A.1: $N-r_k(N)\sim N/k$ uniformemente para $N\le(k-k^{0{,}525})(k-1)$ (usa [2]).
- **[PROBADO]** Corolario A.2: $r_p(ip-1)=i(p-1)$ para $p$ primo y $1\le i\le p-1$, el caso $t=1$ de una conjetura de Ahmed–Dybizbański–Snevily [1]; la unicidad del conjunto extremal queda **[PLAUSIBLE + NUMÉRICO]**.

**Cálculos exactos en $N=k^2$.**

- **[NUMÉRICO]** $\tau_k(k^2)=3,4,6,7,9,11,13,15,16$ para $k=2,\dots,10$ (búsqueda exhaustiva), y $17\le\tau_{11}(121)\le18$.
- **[NUMÉRICO]** La conjetura $\tau_p(p^2)=2p-3$ es **falsa** para $p=11,13,17,19,23$ (conjuntos explícitos de $18,21,29,33,41$ elementos, verificados de forma independiente).
- **[CONJETURA]** $\tau_k(k^2)\ge(1+c)k$ para alguna constante $c\gt0$. Lo demostrado es solo $k+c\sqrt k$.

## 3. Tabla afirmación–evidencia

| Afirmación | Evidencia | Certeza |
|---|---|---|
| El Problema 142 sigue abierto | Base de datos de problemas de Erdős y enunciado formal marcado `research open` [20]; brecha entre [7] y [15] | Alta |
| Enunciado formal `erdos_142` insatisfacible | `erdos_142_statement_unsatisfiable` en `lean/Erdos142/FormalConjectures.lean` | **[PROBADO]** |
| `variants.lower` se sigue del teorema de OpenAI | `erdos_142_variants_lower_of_quantitative` (hipótesis: `QuantitativeDensityTheorem`) | **[PROBADO]** condicional |
| $r_k(N)=N-\lfloor N/k\rfloor$ para $N\le q(k-1)$ | `r_eq_of_le_minFac` | **[PROBADO]** |
| El rango anterior es óptimo | `r_first_fail` | **[PROBADO]** |
| $\tau_k(k^2)=k+s\Rightarrow k\lt8s^2+8s+4$ | `card_hitting_sq`, `r_sq_add_lt` | **[PROBADO]** |
| $\tau_p(p^2)\le2p-3$, $p\ge7$ primo | `Hset_hits`, `r_prime_sq_ge`; además `check_Hp.cpp` para los 92 primos $7\le p\le499$ | **[PROBADO]** |
| $\tau_k(k^2)$ para $k\le10$; $17\le\tau_{11}(121)\le18$ | `verificacion/datos/exhaustivo.txt` ($8{,}5\cdot10^9$ nodos para descartar 16); conjuntos en `mejores_conjuntos.txt` | **[NUMÉRICO]** |
| $\tau_p(p^2)=2p-3$ es falsa para $p\ge11$ | Conjuntos explícitos re-verificados por fuerza bruta en `checks.py` | **[NUMÉRICO]** (certificado comprobable) |
| El buscador exhaustivo es correcto | Coincide con OEIS A003002–A003005, con las tablas de [1] (incluido el número de conjuntos extremales en 7 casos) y con una búsqueda independiente en 1160 casos | Alta, no formal |

## 4. Limitaciones y vacíos

- **No hay avance sobre el problema original** ($k$ fijo, $N\to\infty$). Los resultados nuevos viven en otro régimen ($N\le k^2$).
- **Novedad incierta.** El Teorema A es casi con seguridad folclore y otras ejecuciones con IA han anunciado una fórmula exacta de este tipo [21]. No he encontrado los Teoremas B–D ni los valores para $k=10,11$ en [1] ni en OEIS, pero la búsqueda bibliográfica de este régimen no fue exhaustiva.
- **Cotas inferiores por ordenador.** Los valores exactos de §5 de la nota dependen de un programa propio en C++, validado pero no formalizado.
- **$\tau_{11}(121)$ queda sin decidir** entre 17 y 18; descartar 17 exhaustivamente costaría unas 20 veces más cómputo.
- **Resultado de OpenAI.** La observación (B) es condicional a un teorema que no he recompilado ni revisado; la (C) solo compara enunciados.
- **Sitios no consultables.** `erdosproblems.com` y `oeis.org` rechazan el acceso automático; usé sus repositorios públicos de datos en GitHub.

## 5. Contenido de la carpeta

| Ruta | Contenido |
|---|---|
| [`NOTA.md`](NOTA.md), [`NOTA.pdf`](NOTA.pdf) | Nota completa: estado del arte, observaciones, teoremas con demostración, cálculos, preguntas abiertas |
| [`lean/`](lean/) | Proyecto Lean 4 + Mathlib (6 módulos, 25 teoremas) y [`registro_verificacion.txt`](lean/registro_verificacion.txt) |
| [`verificacion/`](verificacion/) | `tau_dfs.cpp` (búsqueda exhaustiva), `sa.cpp` (recocido), `checks.py` y `test_dfs.py` (contrastes), `tabla.py`, y [`datos/`](verificacion/datos/) |
| [`herramientas/build_pdf.py`](herramientas/build_pdf.py) | Generación del PDF |

Para reproducir, véase §8 de la nota y [`lean/README.md`](lean/README.md).

## 6. Referencias

Numeración de [`NOTA.md`](NOTA.md); todas verificadas contra Crossref o arXiv.

1. T. Ahmed, J. Dybizbański, H. Snevily, *Unique sequences containing no $k$-term arithmetic progressions*, Electron. J. Combin. 20(4) (2013), P29. <https://doi.org/10.37236/3007>
2. R. C. Baker, G. Harman, J. Pintz, *The difference between consecutive primes, II*, Proc. London Math. Soc. 83 (2001), 532–562. <https://doi.org/10.1112/plms/83.3.532>
7. C. Elsholtz, Z. Hunter, L. Proske, L. Sauermann, *Improving Behrend's construction: sets without arithmetic progressions in integers and over finite fields*, arXiv:2406.12290 (2024). <https://arxiv.org/abs/2406.12290>
12. J. Leng, A. Sah, M. Sawhney, *Improved bounds for Szemerédi's theorem*, arXiv:2402.17995 (2024). <https://arxiv.org/abs/2402.17995>
15. R. Raghavan, *Improved bounds for 3-progressions*, arXiv:2603.27045 (2026). <https://arxiv.org/abs/2603.27045>
18. OpenAI, *Quasipolynomial bounds for arithmetic progressions*, manuscrito del 23‑9‑2026 y formalización Lean en <https://github.com/openai/math>.
20. Base de datos de problemas de Erdős, <https://github.com/teorth/erdosproblems>, y <https://github.com/google-deepmind/formal-conjectures>.
21. *Erdős Problem a Day*, entrada sobre el problema 142, <https://erdosproblemaday.com/day/142-white-whale>.

La lista completa (21 referencias) está en la nota.
