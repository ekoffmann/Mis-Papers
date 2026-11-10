# Problema 142 de Erdős: estado del arte verificado y resultados exactos para progresiones largas

**Nota de investigación (sin revisión por pares), elaborada con asistencia de IA. Versión del 10‑11‑2026.**

> **Advertencia.** El Problema 142 de Erdős **sigue abierto** y esta nota **no lo resuelve**. Contiene (i) una revisión del estado del arte con fuentes verificadas, (ii) tres observaciones sobre las formalizaciones públicas del problema y (iii) resultados elementales, varios de ellos verificados en Lean 4, en un régimen **distinto** del que pide el problema (progresiones largas, $N \le k^2$). Etiquetas: **[PROBADO]** = verificado en Lean 4 + Mathlib (compila, sin `sorry`, solo axiomas estándar); **[PLAUSIBLE]** = demostración escrita a mano, no formalizada; **[NUMÉRICO]** = comprobado por ordenador; **[CONJETURA]** = sin demostración.

## 0. Resumen

Sea $r_k(N)$ el mayor tamaño de un subconjunto de $\lbrace 1,\dots,N\rbrace$ sin progresión aritmética (PA) no trivial de $k$ términos. Erdős pidió (10 000 USD) una **fórmula asintótica** para $r_k(N)$ con $k$ fijo y $N\to\infty$.

1. **Estado del arte (§2).** Ni siquiera se conoce el orden de magnitud de $r_3(N)$: las mejores cotas son $N\cdot 2^{-(C+o(1))\sqrt{\log_2 N}}$ por abajo y $N\exp(-c(\log N)^{1/6}/\log\log N)$ por arriba. Los exponentes de $\log N$ ($1/2$ frente a $1/6$) no coinciden, así que una fórmula asintótica está fuera del alcance de las técnicas actuales. Para $k\ge 4$ la distancia es mayor.
2. **Formalizaciones (§3).** (A) El enunciado formal de `erdos_142` en `google-deepmind/formal-conjectures` es insatisfacible tal como está escrito (pide una sola función para todos los $k$) **[PROBADO]**. (B) Su variante `erdos_142.variants.lower` ($r_k(N)=o(N/\log N)$), marcada allí como abierta, se deduce del teorema cuantitativo formalizado por OpenAI **[PROBADO, condicional a ese teorema]**. (C) El enunciado Lean de ese teorema es más débil que el que anuncia el manuscrito.
3. **Progresiones largas (§4).** Con $\tau_k(N)=N-r_k(N)$ y $q$ el menor factor primo de $k$:
   - **Teorema A [PROBADO]:** $r_k(N)=N-\lfloor N/k\rfloor$ para todo $N\le q(k-1)$.
   - **Teorema B [PROBADO]:** el rango es óptimo: $r_k(q(k-1)+1)=N-\lfloor N/k\rfloor-1$.
   - **Teorema C [PROBADO]:** en $N=k^2$ hace falta un exceso de orden $\sqrt{k}$: si $\tau_k(k^2)=k+s$ entonces $k \lt 8s^2+8s+4$.
   - **Teorema D [PLAUSIBLE + NUMÉRICO]:** $\tau_p(p^2)\le 2p-3$ para todo primo $p\ge 5$ (construcción explícita).
4. **Cálculos exactos (§5) [NUMÉRICO].** $\tau_k(k^2)=3,4,6,7,9,11,13,15,16$ para $k=2,\dots,10$ y $17\le\tau_{11}(121)\le 18$. La conjetura natural $\tau_p(p^2)=2p-3$ (cierta para $p=5,7$) es **falsa** para $p=11,13,17,19,23$.
5. **Preguntas abiertas (§6)** y **qué es nuevo y qué no (§7)**.

Nada de lo anterior aporta información sobre la asintótica con $k$ fijo.

## 1. El problema

Una PA de $k$ términos es un conjunto $\lbrace a, a+d, \dots, a+(k-1)d\rbrace$ con $d\ge 1$. Se define

```math
r_k(N)=\max\{\lvert A\rvert : A\subseteq\{1,\dots,N\},\ A \text{ no contiene ninguna PA de } k \text{ términos}\}.
```

**Problema 142 (Erdős).** Demostrar una fórmula asintótica para $r_k(N)$, es decir, hallar $f_k$ con $r_k(N)/f_k(N)\to 1$. La base de datos de problemas de Erdős lo lista como abierto con premio de 10 000 USD [20]; el caso $k=3$ ya es abierto. El problema relacionado n.º 3 (si $\sum_{a\in A}1/a=\infty$ entonces $A$ contiene PAs arbitrariamente largas; 5 000 USD) es el que afirma resolver el manuscrito de OpenAI de septiembre de 2026 [18].

Trabajaremos con el **complemento**: $\tau_k(N)=N-r_k(N)$ es el menor tamaño de un conjunto $H\subseteq\lbrace 1,\dots,N\rbrace$ que corta (interseca) todas las PA de $k$ términos contenidas en $\lbrace 1,\dots,N\rbrace$. Escribimos $[a,b]$ para $\lbrace a,a+1,\dots,b\rbrace$.

## 2. Estado del arte (noviembre de 2026)

Todas las fuentes de esta tabla se comprobaron contra Crossref o arXiv; las constantes citadas se leyeron en el propio texto o resumen de cada trabajo.

| $k$ | Mejor cota inferior conocida | Mejor cota superior conocida |
|---|---|---|
| $3$ | $N\cdot 2^{-(C+o(1))\sqrt{\log_2 N}}$ con $C=2\sqrt{\log_2(24/7)}\approx 2{,}667$ (Elsholtz–Hunter–Proske–Sauermann 2024 [7]); antes $C=2\sqrt2\approx 2{,}828$ (Behrend 1946 [3], con mejoras de orden inferior de Elkin [6]) | $N\exp(-c(\log N)^{1/6}/\log\log N)$ (Raghavan 2026 [15]); antes exponente $1/9$ (Bloom–Sisask 2023 [5]) y $1/12$ (Kelley–Meka 2023 [11]) |
| $4$ | $N\exp(-c(\log N)^{1/2})$ (Rankin 1961 [14]; O'Bryant 2011 [13]) | $N(\log N)^{-c}$ (Green–Tao 2017 [10]); $N\exp(-c(\log N)^{\varepsilon})$ según el manuscrito de OpenAI [18] |
| $\ge 5$ | $N\exp(-c_k(\log N)^{1/n})$ con $n=\lceil\log_2 k\rceil$ (Rankin [14]; O'Bryant [13]) | $N\exp(-(\log\log N)^{c_k})$ (Leng–Sah–Sawhney 2024 [12]); $N\exp(-c_k(\log N)^{\varepsilon_k})$ según el manuscrito de OpenAI [18] |

Hitos anteriores: Erdős–Turán 1936 [8] (definición y conjetura $r_3(N)=o(N)$), Salem–Spencer 1942 [17], Roth 1953 [16] ($r_3(N)\ll N/\log\log N$), Szemerédi 1975 [19] ($r_k(N)=o(N)$), Gowers 2001 [9] ($r_k(N)\ll N(\log\log N)^{-c_k}$), Bloom–Sisask 2020 [4] ($r_3(N)\ll N/(\log N)^{1+c}$).

**Por qué el problema no está al alcance.** Una fórmula asintótica exige conocer $r_k(N)$ salvo un factor $1+o(1)$. Para $k=3$ las cotas actuales difieren en mucho más que una constante: $\exp(-C\sqrt{\log N})$ frente a $\exp(-c(\log N)^{1/6-o(1)})$. Cerrar esa brecha requeriría, como mínimo, decidir si la construcción de tipo Behrend es óptima en el exponente, cosa que nadie sabe hacer. La propia variante «orden de magnitud» (`erdos_142.variants.isTheta`) está abierta para todo $k\ge 3$.

**Sobre el manuscrito de OpenAI [18].** Su resumen afirma, para cada $k\ge 3$ fijo, $r_k(N)\le C_kN\exp(-c_k(\log N)^{\varepsilon_k})$, y de ahí la conjetura de Erdős sobre sumas de recíprocos (Problema 3). El repositorio público incluye una formalización Lean; no la he recompilado ni he revisado la demostración. Véase la observación (C) de §3 sobre qué dice exactamente el enunciado formal. En cualquier caso, una cota superior de ese tipo **no** da una fórmula asintótica: sigue faltando una cota inferior del mismo orden.

## 3. Tres observaciones sobre las formalizaciones

Archivo Lean: [`lean/Erdos142/FormalConjectures.lean`](lean/Erdos142/FormalConjectures.lean). Las definiciones de `formal-conjectures` (commit `1c24583`, 9‑11‑2026) y de `openai/math` (commit `4eaee87`) están copiadas literalmente en los espacios de nombres `FC` y `OAI.Erdos3`.

**(A) El enunciado formal principal es insatisfacible [PROBADO].** En `FormalConjectures/ErdosProblems/142.lean` se lee:

```lean
def erdos_142.answer : ℕ → ℝ := sorry

theorem erdos_142 (k : ℕ) : (fun N => (r k N : ℝ)) ~[atTop] erdos_142.answer := by
  sorry
```

La respuesta `answer` no depende de `k`, pero el teorema se pide para todo `k`. Como allí $r_1(N)=N$ y $r_2(N)=1$, ninguna función sirve:

```lean
theorem erdos_142_statement_unsatisfiable :
    ¬ ∃ f : ℕ → ℝ, ∀ k : ℕ, (fun N => (FC.maxCard k N : ℝ)) ~[atTop] f
```

Lo mismo ocurre con `erdos_142.variants.isTheta` (`erdos_142_isTheta_statement_unsatisfiable`). El docstring deja claro que la intención es «hallar $f_k$»; bastaría declarar `answer : ℕ → ℕ → ℝ` (y, razonablemente, restringir a $k\ge 3$). Es un defecto de la formalización, no información sobre el problema matemático.

**(B) La variante `lower` se deduce del teorema cuantitativo de OpenAI [PROBADO, condicional].** La variante

```lean
theorem erdos_142.variants.lower (k : ℕ) (hk : 1 < k) :
    (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)
```

figura como `research open`. Con las definiciones de `openai/math`,

```lean
theorem erdos_142_variants_lower_of_quantitative
    (h : OAI.Erdos3.QuantitativeDensityTheorem) (k : ℕ) (hk : 1 < k) :
    (fun N => (FC.maxCard k N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ) / (N : ℝ).log)
```

donde `QuantitativeDensityTheorem` es la proposición que `openai/math` declara demostrada (`manuscriptQuantitativeDensityTheorem`). El puente entre las dos definiciones de $r_k(N)$ es `maxCard_eq_extremalNumber` (válido para $k\ge 2$). Para $k=3$ la variante ya era consecuencia de Bloom–Sisask 2020 [4]; para $k\ge 4$ depende del resultado de OpenAI, que yo no he verificado.

**(C) El enunciado Lean de OpenAI es más débil que el del manuscrito [comprobado por lectura].** El resumen del manuscrito anuncia $\exp(-c_k(\log N)^{\varepsilon_k})$; la proposición formal es

```lean
def QuantitativeDensityBound (k : ℕ) : Prop :=
  ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
    ∀ N : ℕ, 3 ≤ N →
      (extremalNumber k N : ℝ) ≤ C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))
```

es decir, $\exp(-c(\log\log N)^{1+\eta})$. Basta para el Problema 3 y para (B), pero no es la cota cuasipolinómica del título. Solo he leído los enunciados (`Model.lean`, `Results/Conclusions.lean`), no las demostraciones.

## 4. Progresiones largas: el régimen $N\le k^2$

Cuando $k$ crece con $N$ el problema cambia de naturaleza: $r_k(N)$ está muy cerca de $N$ y lo interesante es el complemento $\tau_k(N)$. Archivos Lean: [`Exact.lean`](lean/Erdos142/Exact.lean), [`Threshold.lean`](lean/Erdos142/Threshold.lean), [`Sqrt.lean`](lean/Erdos142/Sqrt.lean).

### 4.1. Dos lemas básicos

**Lema 1 (bloques) [PROBADO: `r_add_div_le`].** $\tau_k(N)\ge\lfloor N/k\rfloor$.

*Demostración.* Los bloques $[jk+1,(j+1)k]$, $0\le j\lt\lfloor N/k\rfloor$, son PAs disjuntas de $k$ términos (diferencia 1). $\square$

**Lema 2 (forma de ventanas) [PLAUSIBLE + NUMÉRICO].** Sea $d\ge1$ con $kd\le N$. Un conjunto $H$ corta todas las PA de $k$ términos y diferencia $d$ de $[1,N]$ si y solo si, para todo intervalo $I\subseteq[1,N]$ de $kd$ enteros consecutivos, $H\cap I$ contiene elementos de las $d$ clases de restos módulo $d$.

*Demostración.* En un intervalo de longitud $kd$ cada clase módulo $d$ tiene exactamente $k$ elementos, que forman una PA de $k$ términos y diferencia $d$. Recíprocamente, la PA $a,a+d,\dots,a+(k-1)d$ está contenida en algún intervalo de longitud $kd$ dentro de $[1,N]$ (porque $kd\le N$) y es la clase de $a$ en ese intervalo. $\square$

Así, cortar todas las PA equivale a que $H$ sea «completo módulo $d$» en cada ventana de longitud $kd$, para cada $d$. Para $d=1$ es la condición de bloques; la dificultad está en satisfacer todas las $d$ a la vez.

### 4.2. Fórmula exacta y optimalidad de su rango

**Teorema A [PROBADO: `r_eq_of_le_minFac`, `r_sandwich`].** Sea $k\ge2$ y $q$ su menor factor primo. Para todo $N\le q(k-1)$,

```math
r_k(N)=N-\lfloor N/k\rfloor .
```

Más en general, si $p\le k$ es primo y $N\le p(k-1)$, entonces $N-\lfloor N/p\rfloor\le r_k(N)\le N-\lfloor N/k\rfloor$.

*Demostración.* La cota superior es el Lema 1. Para la inferior basta ver que los múltiplos de $m$ (con $m=k$ o $m=p$) cortan toda PA de $k$ términos de $[1,N]$. Una tal PA tiene diferencia $d\le (N-1)/(k-1)$, luego $d\lt q$ (resp. $d\lt p$) y $\gcd(d,m)=1$: todo factor primo de $k$ es $\ge q\gt d$ (resp. $p$ es primo y $p\gt d$). Entonces los $m\le k$ primeros términos $a,a+d,\dots,a+(m-1)d$ recorren todas las clases módulo $m$; uno de ellos es múltiplo de $m$. $\square$

En particular, para $p$ primo, $r_p(N)=N-\lfloor N/p\rfloor$ para todo $N\le p(p-1)$ (`r_prime_eq`).

**Corolario A.1 (asintótica uniforme) [PLAUSIBLE; usa un teorema externo].** Por Baker–Harman–Pintz [2], para $k$ grande hay un primo en $[k-k^{0{,}525},k]$. Para tales $k$ y todo $N\le (k-k^{0{,}525})(k-1)$,

```math
\Big\lfloor \frac{N}{k}\Big\rfloor \le N-r_k(N)\le \frac{N}{k-k^{0{,}525}} ,
```

de modo que $N-r_k(N)=(1+O(k^{-0{,}475}))N/k+O(1)$. En este rango ($k$ algo mayor que $\sqrt N$) sí hay, pues, una fórmula asintótica para el complemento.

**Corolario A.2 (caso $t=1$ de una conjetura de Ahmed–Dybizbański–Snevily) [PLAUSIBLE + NUMÉRICO].** Para $p$ primo y $1\le i\le p-1$ se tiene $r_p(ip-1)=i(p-1)$, y el conjunto extremal es único: $[1,ip-1]$ menos los múltiplos de $p$.

*Demostración.* El valor es el Teorema A con $N=ip-1\le p(p-1)$. Unicidad: un conjunto de corte $H$ de tamaño $i-1$ tiene exactamente un elemento en cada bloque $[(j-1)p+1,jp]$ y exactamente uno en cada bloque $[jp,(j+1)p-1]$, $1\le j\le i-1$; el $j$-ésimo elemento está en ambos, cuya intersección es $\lbrace jp\rbrace$. $\square$

Es el caso $t=1$ de la «conjetura de unicidad» de [1] (que generaliza la conjetura de Szekeres), cuya tabla de valores exactos para $k=11$ ($n\le109$) queda explicada íntegramente por el Teorema A. Los casos $t\ge2$ de esa conjetura no se tocan aquí.

**Teorema B (el rango es óptimo) [PROBADO: `r_first_fail`].** Para todo $k\ge2$, con $q$ su menor factor primo y $N=q(k-1)+1$,

```math
r_k(N)=q(k-2)+1=N-\lfloor N/k\rfloor-1 .
```

*Demostración.* $\tau_k(N)\le\tau_k(N-1)+1=q$ por el Teorema A. Supongamos que $H$ corta todo y $\lvert H\rvert\le q-1$. Para cada $x\in H$, los bloques de $k$ enteros consecutivos a la izquierda y a la derecha de $x$ dan $\lfloor (x-1)/k\rfloor+1+\lfloor (N-x)/k\rfloor\le \lvert H\rvert\le q-1$ (`card_ge_of_mem`). Escribiendo $x=jk+u$ con $1\le u\le k$, si fuera $u\le k-q+1$ se tendría $N-x\ge (q-1-j)k$ y la suma sería $\ge q$. Luego $u\ge k-q+2$, y como $q$ divide a $k$, $x\equiv u\pmod q$ con $u\in[k-q+2,k]$, cuyos restos módulo $q$ son $2,3,\dots,q-1,0$: nunca $1$. Pero la PA $1,1+q,\dots,1+(k-1)q=N$ está en $[1,N]$ y todos sus términos son $\equiv1\pmod q$: $H$ no la corta. $\square$

Para $k=p$ primo: $r_p(p(p-1)+1)=(p-1)^2$ (`r_prime_succ_range`).

### 4.3. Cota inferior en $N=k^2$

En $N=k^2$ el Lema 1 da $\tau_k(k^2)\ge k$. La relajación lineal no da más:

**Observación (relajación lineal) [PLAUSIBLE + NUMÉRICO].** Si $k$ divide a $N$, el óptimo fraccionario del problema de corte es exactamente $N/k$: el peso constante $1/k$ en cada entero es admisible (cada PA tiene $k$ puntos) y los $N/k$ bloques disjuntos son un empaquetamiento. Todo exceso de $\tau_k(N)$ sobre $N/k$ es, por tanto, un fenómeno entero, invisible para la programación lineal.

**Teorema C [PROBADO: `card_hitting_sq`, `r_sq_add_lt`].** Sea $k\ge2$ y $H\subseteq[1,k^2]$ un conjunto que corta todas las PA de $k$ términos de $[1,k^2]$. Si $\lvert H\rvert=k+s$, entonces

```math
k \lt 8s^2+8s+4 .
```

Equivalentemente, $\tau_k(k^2)\gt k+\tfrac12\big(\sqrt{(k-2)/2}-1\big)$; y si $8s^2+8s+4\le k$ entonces $r_k(k^2)\le k^2-k-s-1$.

*Demostración.* Sea $n=k+s$ y $h_1\lt\dots\lt h_n$ los elementos de $H$.

*(a) Huecos.* $g_i=h_{i+1}-h_i\le k$, $h_1\le k$ y $h_n\ge k^2-k+1$ (PAs de diferencia 1). Los déficits $\delta_i=k-g_i\ge0$ cumplen

```math
\sum_{i=1}^{n-1}\delta_i=(n-1)k-(h_n-h_1)\le (n-1)k-(k^2-2k+1)=k(s+1)-1 .
```

*(b) Clases.* Sea $1\le g\le k$. Cada clase módulo $g$ contiene una PA de $k$ términos de $[1,k^2]$ (la de primer término $a\in[1,g]$ y diferencia $g$ termina en $a+(k-1)g\le kg\le k^2$), así que $H$ toca las $g$ clases. El mayor elemento de $H$ en cada clase no es de la forma $h$ con $h+g\in H$. Por tanto $\#\lbrace h\in H: h+g\in H\rbrace\le n-g$; en particular, a lo sumo $n-g$ huecos valen exactamente $g$. Con $g=k-j$: **a lo sumo $s+j$ huecos tienen déficit $j$**.

*(c) Conteo.* Sea $t=2s+2$. Los huecos con déficit menor que $t$ son a lo sumo $\sum_{j\lt t}(s+j)=4s^2+5s+1$, de modo que al menos $(k+s-1)-(4s^2+5s+1)=k-4s^2-4s-2$ huecos tienen déficit $\ge t$. Si este número es positivo, por (a),

```math
k(s+1)-1\ \ge\ (2s+2)(k-4s^2-4s-2),
```

es decir $(s+1)k+1\le (s+1)(8s^2+8s+4)$, que da $k\lt 8s^2+8s+4$. Si no es positivo, $k\le 4s^2+4s+2$ y no hay nada que probar. $\square$

(La prueba formal evita ordenar $H$: cubre $[1,k^2]$ con las «fibras» de cada $h\in H$, que tienen a lo sumo $k$ elementos, y a lo sumo $k-t$ salvo para pocos $h$.)

**Versión afinada [PLAUSIBLE + NUMÉRICO].** Los pasos (a) y (b) dan más: si $D(k,s)$ es la menor suma posible de $k+s-1$ enteros $\ge0$ en la que el valor $j$ aparece a lo sumo $s+j$ veces, entonces $D(k,s)\le k(s+1)-1$. Llamando $s_{\min}(k)$ al menor $s$ que lo cumple, $\tau_k(k^2)\ge k+s_{\min}(k)$. Numéricamente $s_{\min}(k)/\sqrt k\to c_0\approx0{,}556$ (véase `checks.py`); por ejemplo $s_{\min}(k)=1$ para $3\le k\le9$, $2$ para $10\le k\le22$ y $3$ para $k=23$.

**Consecuencia para $N$ grande.** Como $r_k$ es subaditiva, $\tau_k$ es superaditiva y $\tau_k(N)\ge\lfloor N/k^2\rfloor\,\tau_k(k^2)$: para $N$ múltiplo de $k^2$, $r_k(N)\le N-(1+c/\sqrt k)N/k$. Con los valores exactos de §5, $r_5(N)\le \tfrac{18}{25}N$ y $r_7(N)\le\tfrac{38}{49}N$ para $N$ múltiplo de $25$ y de $49$.

### 4.4. Cota superior en $N=p^2$

La construcción clásica de dígitos da $r_p(p^m)\ge(p-1)^m$ para $p$ primo: los enteros de $[0,p^m)$ sin el dígito $p-1$ en base $p$ no contienen PAs de $p$ términos (si $p^e$ es la mayor potencia de $p$ que divide a $d$, el dígito de posición $e$ de $a+id$ recorre todos los valores módulo $p$ cuando $i=0,\dots,p-1$). Es la observación de Erdős–Turán [8] para $p=3$ y el origen de la conjetura de Szekeres (véase [1]). En $N=p^2$ da $\tau_p(p^2)\le 2p-1$.

**Teorema D [PLAUSIBLE + NUMÉRICO].** Sea $p\ge7$ primo, $W=[2p+3,3p-2]$ y

```math
H_p=\{2,\ p+1,\ 2p-1\}\ \cup\ W\ \cup\ \{jp : 3\le j\le p\}.
```

Entonces $H_p$ corta todas las PA de $p$ términos de $[1,p^2]$ y $\lvert H_p\rvert=2p-3$. Por tanto $r_p(p^2)\ge(p-1)^2+2$. Para $p=5$ también $\tau_5(25)=7=2p-3$, con el conjunto $\lbrace5,10,15,16,17,19,23\rbrace$.

*Demostración.* Sea $P=\lbrace a+id:0\le i\le p-1\rbrace\subseteq[1,p^2]$. Entonces $(p-1)d\le p^2-1$, luego $d\le p+1$.

*(i) $d=p+1$.* Fuerza $a=1$ y $P\ni 1+2(p+1)=2p+3\in W$.

*(ii) $d=p$.* $P$ es una clase módulo $p$ completa. $H_p$ toca todas: la clase $0$ con $3p$; la $1$ con $p+1$; la $2$ con $2$; la $p-1$ con $2p-1$; la clase $c$, $3\le c\le p-2$, con $2p+c\in W$.

*(iii) $1\le d\le p-1$.* Como $\gcd(d,p)=1$, $P$ contiene exactamente un múltiplo de $p$, digamos $mp=a+jd$. Si $m\ge3$, $mp\in H_p$. Quedan dos casos.

*Caso $m=2$.* Si $d=1$: $P$ es un intervalo que contiene a $2p$; si $a\le 2p-1$ contiene a $2p-1$, y si $a=2p$ contiene a $2p+3$. Si $d=2$: los términos son pares; si $a=2$, $2\in H_p$; si $4\le a\le p+1$, $P\ni p+1$; si $a\ge p+3$, el último término es $\ge 3p+1$ y $P\ni 2p+4\in W$ (pues $p\ge 6$). Si $3\le d\le p-2$: $2p$ no es el último término (si lo fuera, $a=2p-(p-1)d\ge1$ daría $d\le2$), luego $P\ni 2p+d\in W$. Si $d=p-1$: $a=2p-j(p-1)\ge1$ da $j\le2$; $j=2$ da $a=2$, $j=1$ da $a=p+1$, y $j=0$ es imposible porque el último término sería $2p+(p-1)^2=p^2+1$.

*Caso $m=1$.* Si $d=1$: $P=[a,a+p-1]\ni p$; si $a\le2$ contiene a $2$, y si $a\ge3$ contiene a $p+1$. Si $d=2$: los términos son los impares de $a$ a $a+2p-2$ con $1\le a\le p$, entre ellos $2p-1$. Si $3\le d\le p-4$: el primer término es $\le p\lt 2p+3$ y el último $\ge1+3(p-1)=3p-2$; el primer término $\ge 2p+3$ es $\le 2p+2+d\le 3p-2$, luego está en $W$. Si $d=p-3$: $j\le1$ (pues $2(p-3)\gt p-1$), así que $P$ contiene a $p+2d=3p-6$ y a $p+3d=4p-9$; si $p\ge11$, $3p-6\in W$, y si $p=7$, $4p-9=19=3p-2\in W$. Si $d=p-2$: $j\le1$; $j=1$ da $a=2\in H_p$ y $j=0$ da $P\ni p+2d=3p-4\in W$ (pues $p\ge7$). Si $d=p-1$: $j\le1$ y $P\ni p+d=2p-1$.

Los tres bloques de $H_p$ son disjuntos y suman $3+(p-4)+(p-2)=2p-3$. $\square$

`checks.py` comprueba por fuerza bruta que $H_p$ corta todas las PA para todos los primos $7\le p\le61$, y que la fórmula falla para $p=5$ (por eso el teorema pide $p\ge7$).

## 5. Cálculos exactos en $N=k^2$

Herramientas (carpeta [`verificacion/`](verificacion/)): un buscador exhaustivo propio en C++ (`tau_dfs.cpp`), un recocido simulado para cotas superiores (`sa.cpp`) y un script de contraste independiente en Python (`checks.py`). Detalles y controles en §8.

| $k$ | $\tau_k(k^2)$ | $2k-\tau_k(k^2)$ | Cota inferior del Teorema C afinado, $k+s_{\min}(k)$ | Estado |
|---|---|---|---|---|
| 2 | 3 | 1 | 2 | exacto |
| 3 | 4 | 2 | 4 | exacto |
| 4 | 6 | 2 | 5 | exacto |
| 5 | 7 | 3 | 6 | exacto |
| 6 | 9 | 3 | 7 | exacto |
| 7 | 11 | 3 | 8 | exacto |
| 8 | 13 | 3 | 9 | exacto |
| 9 | 15 | 3 | 10 | exacto |
| 10 | 16 | 4 | 12 | exacto |
| 11 | 17 o 18 | 5 o 4 | 13 | exhaustivo hasta 16; conjunto de 18 |
| 12 | $\le 20$ | $\ge4$ | 14 | cota superior (recocido) |
| 13 | $\le 21$ | $\ge5$ | 15 | cota superior (recocido) |
| 17 | $\le 29$ | $\ge5$ | 19 | cota superior (recocido) |
| 19 | $\le 33$ | $\ge5$ | 21 | cota superior (recocido) |
| 23 | $\le 41$ | $\ge5$ | 26 | cota superior (recocido) |

Equivalentemente: $r_8(64)=51$, $r_9(81)=66$, $r_{10}(100)=84$ y $103\le r_{11}(121)\le104$.

**La conjetura $\tau_p(p^2)=2p-3$ es falsa.** Los datos de $k=5,\dots,9$ y el Teorema D sugieren $\tau_p(p^2)=2p-3$. No es así: el conjunto

```math
\{6,10,15,26,37,44,48,53,59,67,70,79,81,92,93,96,106,113\}
```

tiene 18 elementos y corta todas las PA de 11 términos de $[1,121]$ (y $2\cdot11-3=19$). Su estructura: la clase $4$ módulo $11$ en las filas centrales ($15,26,\dots,92$) y un elemento de cada una de las otras diez clases repartidos de modo que suplen a los términos que faltan de esa columna en los extremos. Para $p=13$ hay un conjunto de $21\lt23$ elementos formado, salvo cinco puntos, por dos PA de diferencias $11$ y $13$ que se cruzan en $106$. Los conjuntos están en [`verificacion/datos/mejores_conjuntos.txt`](verificacion/datos/mejores_conjuntos.txt).

**Lo que se sabe de $\tau_{11}(121)$.** La búsqueda exhaustiva descarta todo conjunto de 16 elementos ($8{,}5\cdot10^9$ nodos), luego $\tau_{11}(121)\ge17$. El recocido encuentra 18 en un segundo y no encuentra 17 en quince minutos ($3\cdot10^9$ iteraciones), lo que sugiere, sin demostrarlo, que el valor es 18.

**Cerca del umbral.** Los valores exactos justo por encima de $p(p-1)$ muestran que cada entero adicional cuesta al principio un elemento entero más:

| $N$ | 110 | 111 | 112 | 113 | 114 |
|---|---|---|---|---|---|
| $\tau_{11}(N)$ | 10 | 11 | 12 | 13 | 14 |

(análogamente $\tau_5(20..23)=4,5,6,7$ y $\tau_7(42..45)=6,7,8,9$). Tablas completas en [`verificacion/datos/tabla_tau.txt`](verificacion/datos/tabla_tau.txt).

## 6. Preguntas abiertas

1. **El Problema 142** propiamente dicho: fórmula asintótica (o al menos orden de magnitud) de $r_k(N)$ con $k$ fijo. Sigue abierto para todo $k\ge3$.
2. **[Pregunta]** ¿Cuánto vale $\lim \tau_p(p^2)/p$? Se sabe $p+0{,}55\sqrt p\lesssim\tau_p(p^2)\le 2p-3$. Los datos ($2k-\tau_k(k^2)=1,2,2,3,3,3,3,3,4$ para $k=2,\dots,10$) son compatibles con $\tau_k(k^2)=2k-o(k)$, es decir, con que la construcción de dígitos sea asintóticamente óptima en $N=k^2$, pero no lo demuestran. **[CONJETURA]** $\tau_k(k^2)\ge(1+c)k$ para alguna constante $c\gt0$.
3. **[Pregunta]** ¿$\tau_{11}(121)$ es 17 o 18?
4. **[Pregunta]** ¿Es $\tau_p(p(p-1)+j)=p-1+j$ para $0\le j\le j_0(p)$ con $j_0(p)\to\infty$? (El caso $j=1$ es el Teorema B.)

## 7. Qué es nuevo y qué no

- **§2** es una revisión; todos los resultados son de los autores citados.
- **(A), (B), (C)** son observaciones sobre textos formales públicos. No he encontrado que estén señaladas, pero no he revisado las incidencias ni las solicitudes de cambio de esos repositorios. No son progreso matemático.
- **Teorema A.** Es elemental y casi con seguridad folclore. Una página de seguimiento de estos problemas con IA [21] menciona que otros modelos «encontraron y demostraron una fórmula exacta para $r_k(N)$ con $N$ acotado en términos de $k$» (sin enunciarla); puede ser esta misma. En la literatura que pude consultar, [1] da la desigualdad general más débil $r(k,n)\le n-\lfloor m/2\rfloor$ y tablas exactas compatibles. No lo reclamo como nuevo; sí es nueva su verificación formal aquí.
- **Teoremas B, C, D, Corolario A.2 y los valores de §5 para $k=10,11$.** No los he encontrado en [1] ni en las entradas de OEIS A003002–A003005, pero la búsqueda fue limitada (no pude consultar, por ejemplo, las tablas de Shao–Deng–Liang–Xu citadas en OEIS). Son elementales y pueden ser conocidos. Los valores exactos para $k\le7$ coinciden con las tablas de [1] y de OEIS.
- Una conjetura que formulé durante el trabajo ($\tau_p(p^2)=2p-3$) quedó **refutada** por mis propios cálculos; se deja constancia en §5.

## 8. Reproducibilidad

**Lean.** Lean `4.35.0`, Mathlib `v4.35.0` (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`). Desde `Erdos-142/lean`:

```bash
lake exe cache get
```

```bash
lake build
```

Resultado registrado en [`lean/registro_verificacion.txt`](lean/registro_verificacion.txt): código de salida 0, sin `sorry`, y los 21 teoremas dependen solo de `propext`, `Classical.choice` y `Quot.sound`. `Resumen.lean` demuestra además que la función `r` usada aquí coincide con `extremalNumber` de `openai/math` (por definición) y, para $k\ge2$, con `maxCard` de `formal-conjectures`.

**Cálculos.** Desde `Erdos-142/verificacion`:

```bash
g++ -O2 -o tau_dfs tau_dfs.cpp
```

```bash
g++ -O2 -o sa sa.cpp
```

```bash
python3 checks.py
```

```bash
python3 test_dfs.py
```

- `checks.py` (Python puro, independiente del C++): contrasta con OEIS A003002–A003005, comprueba los Teoremas A y B para $k\le9$, el lema de ventanas, la construcción $H_p$ para $p\le61$, la cota del Teorema C, la relajación lineal y vuelve a verificar por fuerza bruta todos los conjuntos guardados. Salida en [`verificacion/salida.txt`](verificacion/salida.txt).
- `test_dfs.py`: compara `tau_dfs` con la búsqueda de `checks.py` en 1160 casos pequeños, con y sin podas; cero discrepancias.
- `tau_dfs k N B` decide si existe un conjunto de corte de tamaño $\le B$. Las podas son condiciones necesarias (explicadas en la cabecera del archivo); como control, $(k,N,B)=(11,121,15)$ da «no existe» tanto con todas las podas ($3{,}9\cdot10^8$ nodos) como sin las podas de simetría y de ventanas ($1{,}1\cdot10^9$ nodos). Registros en [`verificacion/datos/exhaustivo.txt`](verificacion/datos/exhaustivo.txt).
- `sa k N B segundos semilla` busca un conjunto de tamaño $B$; solo puede demostrar existencia. Registros en [`verificacion/datos/recocido.txt`](verificacion/datos/recocido.txt).

**Limitaciones.** Las cotas inferiores de §5 para $k=10,11$ descansan en una búsqueda exhaustiva por ordenador no formalizada (validada como se indica). Los Teoremas D y los corolarios A.1 y A.2 no están formalizados. La revisión bibliográfica del régimen de progresiones largas no es exhaustiva.

## Referencias

Todas verificadas (Crossref para los DOI; página de arXiv para las prepublicaciones).

1. T. Ahmed, J. Dybizbański, H. Snevily, *Unique sequences containing no $k$-term arithmetic progressions*, Electron. J. Combin. 20(4) (2013), P29. <https://doi.org/10.37236/3007>
2. R. C. Baker, G. Harman, J. Pintz, *The difference between consecutive primes, II*, Proc. London Math. Soc. 83 (2001), 532–562. <https://doi.org/10.1112/plms/83.3.532>
3. F. A. Behrend, *On sets of integers which contain no three terms in arithmetical progression*, Proc. Nat. Acad. Sci. USA 32 (1946), 331–332. <https://doi.org/10.1073/pnas.32.12.331>
4. T. F. Bloom, O. Sisask, *Breaking the logarithmic barrier in Roth's theorem on arithmetic progressions*, arXiv:2007.03528 (2020). <https://arxiv.org/abs/2007.03528>
5. T. F. Bloom, O. Sisask, *An improvement to the Kelley–Meka bounds on three-term arithmetic progressions*, arXiv:2309.02353 (2023). <https://arxiv.org/abs/2309.02353>
6. M. Elkin, *An improved construction of progression-free sets*, Israel J. Math. 184 (2011), 93–128. <https://doi.org/10.1007/s11856-011-0061-1>
7. C. Elsholtz, Z. Hunter, L. Proske, L. Sauermann, *Improving Behrend's construction: sets without arithmetic progressions in integers and over finite fields*, arXiv:2406.12290 (2024). <https://arxiv.org/abs/2406.12290>
8. P. Erdős, P. Turán, *On some sequences of integers*, J. London Math. Soc. 11 (1936), 261–264. <https://doi.org/10.1112/jlms/s1-11.4.261>
9. W. T. Gowers, *A new proof of Szemerédi's theorem*, Geom. Funct. Anal. 11 (2001), 465–588. <https://doi.org/10.1007/s00039-001-0332-9>
10. B. Green, T. Tao, *New bounds for Szemerédi's theorem, III: a polylogarithmic bound for $r_4(N)$*, Mathematika 63 (2017), 944–1040. <https://doi.org/10.1112/s0025579317000316>
11. Z. Kelley, R. Meka, *Strong bounds for 3-progressions*, FOCS 2023, 933–973. <https://doi.org/10.1109/focs57990.2023.00059>
12. J. Leng, A. Sah, M. Sawhney, *Improved bounds for Szemerédi's theorem*, arXiv:2402.17995 (2024). <https://arxiv.org/abs/2402.17995>
13. K. O'Bryant, *Sets of integers that do not contain long arithmetic progressions*, Electron. J. Combin. 18(1) (2011), P59. <https://doi.org/10.37236/546>
14. R. A. Rankin, *Sets of integers containing not more than a given number of terms in arithmetical progression*, Proc. Roy. Soc. Edinburgh Sect. A 65 (1961), 332–344. <https://doi.org/10.1017/s0080454100017726>
15. R. Raghavan, *Improved bounds for 3-progressions*, arXiv:2603.27045 (2026). <https://arxiv.org/abs/2603.27045>
16. K. F. Roth, *On certain sets of integers*, J. London Math. Soc. 28 (1953), 104–109. <https://doi.org/10.1112/jlms/s1-28.1.104>
17. R. Salem, D. C. Spencer, *On sets of integers which contain no three terms in arithmetical progression*, Proc. Nat. Acad. Sci. USA 28 (1942), 561–563. <https://doi.org/10.1073/pnas.28.12.561>
18. OpenAI, *Quasipolynomial bounds for arithmetic progressions*, manuscrito del 23‑9‑2026 y formalización Lean en <https://github.com/openai/math> (commit `4eaee87`). Sin revisión por pares conocida; no recompilado aquí.
19. E. Szemerédi, *On sets of integers containing no $k$ elements in arithmetic progression*, Acta Arith. 27 (1975), 199–245. <https://doi.org/10.4064/aa-27-1-199-245>
20. Base de datos de problemas de Erdős, <https://github.com/teorth/erdosproblems> (entrada 142: abierto, 10 000 USD), y enunciado formal en <https://github.com/google-deepmind/formal-conjectures> (commit `1c24583`).
21. *Erdős Problem a Day*, entrada sobre el problema 142, <https://erdosproblemaday.com/day/142-white-whale> (consultada el 10‑11‑2026).
