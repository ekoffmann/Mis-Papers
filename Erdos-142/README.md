# Problema 142 de Erdős (fórmula asintótica para $r_k(N)$)

Informe de investigación con evidencia verificable. Nota sin revisión por pares, elaborada con asistencia de IA (10‑11‑2026).

## 1. Respuesta corta

**El Problema 142 no queda resuelto: sigue abierto, y no está al alcance de las técnicas actuales.** Pide una fórmula asintótica para $r_k(N)$, el mayor tamaño de un subconjunto de $\lbrace1,\dots,N\rbrace$ sin progresión aritmética de $k$ términos; hoy ni siquiera se conoce el orden de magnitud de $r_3(N)$.

Lo que se entrega, todo comprobable:

- una **revisión del estado del arte** con cada fuente verificada;
- **tres observaciones sobre las formalizaciones públicas** del problema, dos de ellas demostradas en Lean;
- **25 teoremas verificados en Lean 4** sobre el régimen de progresiones largas ($N\le k^2$);
- **valores exactos por ordenador** en $N=k^2$ hasta $k=10$, confirmados por dos programas independientes.

**Advertencia sobre la novedad.** Una revisión independiente localizó, al final del trabajo, bibliografía previa sobre ese régimen (Brown–Freedman 1989, Truss 1991, Xu 2013 y una prepublicación de Korsky de 2026) que ya contiene versiones **más fuertes** de dos de mis cuatro teoremas. Lo que queda como aportación propia es modesto: la verificación formal, los datos exactos para $k=9,10$ y la cota para $k=11$, y las observaciones sobre los enunciados formales.

Documento principal: [`NOTA.md`](NOTA.md) ([`NOTA.pdf`](NOTA.pdf)).

## 2. Hallazgos

Notación: $\tau_k(N)=N-r_k(N)$ es el menor tamaño de un conjunto que corta todas las progresiones de $k$ términos de $[1,N]$; $q$ es el menor factor primo de $k$.

**Estado del arte.**

- **[Verificado en la fuente]** Para $k=3$: $N\cdot2^{-(C+o(1))\sqrt{\log_2N}}\le r_3(N)$ con $C=2\sqrt{\log_2(24/7)}\approx2{,}667$ [7], y $r_3(N)\le N\exp(-c(\log N)^{1/6}/\log\log N)$ [15]. Los exponentes de $\log N$ no coinciden, luego no hay fórmula asintótica ni orden de magnitud.
- **[Verificado en la fuente]** Para $k\ge5$ la mejor cota superior publicada es $N\exp(-(\log\log N)^{c_k})$ [12]; un manuscrito de OpenAI de septiembre de 2026 afirma $N\exp(-c_k(\log N)^{\varepsilon_k})$ para todo $k\ge3$ [18]. No lo he verificado.

**Formalizaciones.**

- **[PROBADO]** (A) El enunciado formal `erdos_142` de `google-deepmind/formal-conjectures` es insatisfacible tal como está escrito: pide una sola función `answer` para todos los $k$, y $r_1(N)=N$, $r_2(N)=1$. Lo mismo su variante `isTheta`.
- **[PROBADO, condicional]** (B) La variante `erdos_142.variants.lower` ($r_k(N)=o(N/\log N)$), marcada allí como abierta, se deduce del teorema cuantitativo que `openai/math` declara demostrado.
- **[Comprobado por lectura]** (C) El enunciado Lean de ese teorema, $\exp(-c(\log\log N)^{1+\eta})$, es más débil que la cota del resumen del manuscrito. La documentación de `openai/math` ya lo advierte en lo esencial.

**Progresiones largas** (los cuatro teoremas están verificados en Lean; entre paréntesis, su relación con lo publicado).

- **[PROBADO]** Teorema A: $r_k(N)=N-\lfloor N/k\rfloor$ para todo $N\le q(k-1)$. (Argumento conocido: aparece en Korsky [25]; la cota superior de Truss [23] tiene la misma forma.)
- **[PROBADO]** Teorema B: la fórmula falla en $N=q(k-1)+1$, donde $r_k(N)=N-\lfloor N/k\rfloor-1$. (No lo he visto enunciado; es inmediato.)
- **[PROBADO]** Teorema C: si $\tau_k(k^2)=k+s$ entonces $k\lt8s^2+8s+4$, es decir, exceso de orden $\sqrt k$. (**Más débil** que Truss 1991 [23], y muy inferior a Korsky 2026 [25]: $\tau_n(n^2)\ge n+n^{1-o(1)}$.)
- **[PROBADO]** Teorema D: $\tau_p(p^2)\le2p-3$ para todo primo $p\ge7$, con un conjunto explícito. (Una unidad mejor que Brown–Freedman 1989 [22]; **más débil** que Xu 2013 [24] y Korsky [25] para $p$ grande.)
- **[PROBADO]** Corolario A.2: $r_p(ip-1)=i(p-1)$ para $p$ primo y $1\le i\le p-1$, el caso $t=1$ de una conjetura de Ahmed–Dybizbański–Snevily [1]; la unicidad del conjunto extremal queda **[PLAUSIBLE + NUMÉRICO]**.

**Cálculos exactos en $N=k^2$.**

- **[NUMÉRICO]** $\tau_k(k^2)=3,4,6,7,9,11,13,15,16$ para $k=2,\dots,10$, y $17\le\tau_{11}(121)\le18$. Dos implementaciones independientes coinciden.
- **[NUMÉRICO]** La igualdad $\tau_p(p^2)=2p-3$, que conjeturé a mitad del trabajo, falla ya en $p=11,13,17,19,23$ (conjuntos explícitos verificados). Para $p$ grande esto ya se seguía de [24] y [25].
- **[Abierto, de Korsky [25]]** ¿Es $\tau_n(n^2)\ge(1+\eta)n$? Conjetura de Korsky: $\tau_n(n^2)=(2-o(1))n$. Mis datos son compatibles con ella, sin demostrar nada.

## 3. Tabla afirmación–evidencia

| Afirmación | Evidencia | Certeza |
|---|---|---|
| El Problema 142 sigue abierto | Base de datos de problemas de Erdős y enunciado formal marcado `research open` [20]; brecha entre [7] y [15] | Alta |
| Enunciado formal `erdos_142` insatisfacible | `erdos_142_statement_unsatisfiable` en `lean/Erdos142/FormalConjectures.lean` | **[PROBADO]** |
| `variants.lower` se sigue del teorema de OpenAI | `erdos_142_variants_lower_of_quantitative` (hipótesis: `QuantitativeDensityTheorem`) | **[PROBADO]** condicional |
| $r_k(N)=N-\lfloor N/k\rfloor$ para $N\le q(k-1)$, y fallo en $q(k-1)+1$ | `r_eq_of_le_minFac`, `r_first_fail` | **[PROBADO]** |
| $\tau_k(k^2)=k+s\Rightarrow k\lt8s^2+8s+4$ | `card_hitting_sq`, `r_sq_add_lt` | **[PROBADO]** |
| $\tau_p(p^2)\le2p-3$, $p\ge7$ primo | `Hset_hits`, `r_prime_sq_ge`; además fuerza bruta para los 92 primos $7\le p\le499$ | **[PROBADO]** |
| $\tau_k(k^2)$ para $k\le10$; $17\le\tau_{11}(121)\le18$ | `verificacion/datos/exhaustivo.txt` e `independiente.txt` (dos algoritmos distintos); conjuntos en `mejores_conjuntos.txt` | **[NUMÉRICO]** |
| $\tau_p(p^2)\lt2p-3$ para $p=11,13,17,19,23$ | Conjuntos explícitos re-verificados por fuerza bruta en `checks.py` | **[NUMÉRICO]** (certificado comprobable) |
| Los Teoremas C y D son más débiles que resultados publicados | Introducción de Korsky [25], leída directamente; registros Crossref de [22], [23], [24] | Alta |

## 4. Limitaciones y vacíos

- **No hay avance sobre el problema original** ($k$ fijo, $N\to\infty$). Los resultados viven en otro régimen ($N\le k^2$).
- **Novedad limitada.** La bibliografía de ese régimen ([22]–[25]) se localizó solo en la revisión final. Los Teoremas C y D son redescubrimientos más débiles; el argumento del Teorema A es conocido. No he leído directamente [22], [23], [24] ni [26]: sus resultados se citan según la introducción de [25].
- **Cotas inferiores por ordenador.** Los valores exactos para $k=9,10$ y la cota para $k=11$ dependen de búsquedas exhaustivas no formalizadas (dos programas independientes coinciden).
- **$\tau_{11}(121)$ queda sin decidir** entre 17 y 18; descartar 17 exhaustivamente costaría unas 20 veces más cómputo.
- **Resultado de OpenAI.** La observación (B) es condicional a un teorema que no he recompilado ni revisado.
- **Sitios no consultables.** `erdosproblems.com` y `oeis.org` rechazan el acceso automático; usé sus repositorios públicos de datos en GitHub.

## 5. Contenido de la carpeta

| Ruta | Contenido |
|---|---|
| [`NOTA.md`](NOTA.md), [`NOTA.pdf`](NOTA.pdf) | Nota completa: estado del arte, antecedentes, teoremas con demostración, cálculos, preguntas abiertas |
| [`lean/`](lean/) | Proyecto Lean 4 + Mathlib (6 módulos, 25 teoremas) y [`registro_verificacion.txt`](lean/registro_verificacion.txt) |
| [`verificacion/`](verificacion/) | `tau_dfs.cpp` y `hs_independiente.cpp` (dos búsquedas exhaustivas independientes), `sa.cpp` (recocido), `check_Hp.cpp`, `checks.py` y `test_dfs.py` (contrastes), `tabla.py`, y [`datos/`](verificacion/datos/) |
| [`herramientas/build_pdf.py`](herramientas/build_pdf.py) | Generación del PDF |

Para reproducir, véase §8 de la nota y [`lean/README.md`](lean/README.md).

## 6. Referencias

Numeración de [`NOTA.md`](NOTA.md); todas verificadas contra Crossref o arXiv.

1. T. Ahmed, J. Dybizbański, H. Snevily, *Unique sequences containing no $k$-term arithmetic progressions*, Electron. J. Combin. 20(4) (2013), P29. <https://doi.org/10.37236/3007>
7. C. Elsholtz, Z. Hunter, L. Proske, L. Sauermann, *Improving Behrend's construction: sets without arithmetic progressions in integers and over finite fields*, arXiv:2406.12290 (2024). <https://arxiv.org/abs/2406.12290>
12. J. Leng, A. Sah, M. Sawhney, *Improved bounds for Szemerédi's theorem*, arXiv:2402.17995 (2024). <https://arxiv.org/abs/2402.17995>
15. R. Raghavan, *Improved bounds for 3-progressions*, arXiv:2603.27045 (2026). <https://arxiv.org/abs/2603.27045>
18. OpenAI, *Quasipolynomial bounds for arithmetic progressions*, manuscrito del 23‑9‑2026 y formalización Lean en <https://github.com/openai/math>.
20. Base de datos de problemas de Erdős, <https://github.com/teorth/erdosproblems>, y <https://github.com/google-deepmind/formal-conjectures>.
22. T. C. Brown, A. R. Freedman, *Small sets which meet all the $k(n)$-term arithmetic progressions in the interval $[1,n]$*, J. Combin. Theory Ser. A 51 (1989), 244–249. <https://doi.org/10.1016/0097-3165(89)90049-6>
23. J. K. Truss, *Small sets which meet all the $n$-term arithmetic progressions in the interval $[1,n^2]$*, Bull. London Math. Soc. 23 (1991), 123–127. <https://doi.org/10.1112/blms/23.2.123>
24. X. Xu, *A generalization of sets without long arithmetic progressions based on Szekeres algorithm*, J. Number Theory 133 (2013), 3670–3677. <https://doi.org/10.1016/j.jnt.2013.05.008>
25. S. Korsky, *Hitting arithmetic progressions at the square-root scale*, arXiv:2606.01780 (2026). <https://arxiv.org/abs/2606.01780>
26. Z. Shao, F. Deng, M. Liang, X. Xu, *On sets without $k$-term arithmetic progression*, J. Comput. System Sci. 78 (2012), 610–618. <https://doi.org/10.1016/j.jcss.2011.09.003>

La lista completa (26 referencias) está en la nota.
