# El Problema 281 de Erdős: demostración finitaria, forma óptima y extensiones

> **Naturaleza del documento.** Nota de investigación elaborada con asistencia de IA (Claude Code) a pedido del titular del repositorio. No ha pasado revisión por pares. Las etiquetas de certeza siguen el protocolo del repositorio: **[PROBADO]** = verificado por Lean 4 + Mathlib en esta sesión (sin `sorry`, solo axiomas estándar); **[PLAUSIBLE]** = demostración informal completa, escrita aquí, no verificada por Lean; **[NUMÉRICO]** = comprobado por cómputo en casos finitos; **[LITERATURA]** = resultado publicado, citado con referencia verificada.

## 0. Resumen

El **Problema 281** de Erdős–Graham [1, p. 29] pregunta:

> Sea $n_1 \lt n_2 \lt \cdots$ una sucesión infinita tal que, para toda elección de clases de congruencia $a_i \pmod{n_i}$, el conjunto de enteros que no satisfacen ninguna de las congruencias tiene densidad $0$. ¿Es cierto que para todo $\varepsilon \gt 0$ existe $k$ tal que, para toda elección de clases $a_i$, la densidad de los enteros que no satisfacen ninguna de las congruencias $a_i \pmod{n_i}$, $1 \le i \le k$, es menor que $\varepsilon$?

**La respuesta es sí, y el problema ya estaba resuelto antes de esta nota** (enero de 2026): (i) N. Somani, con GPT‑5.2 Pro, dio un argumento con la medida de Haar de los enteros profinitos (formalizado después en Lean por terceros [2, 6]); (ii) KoishiChan observó que se deduce del teorema de Davenport–Erdős de 1936 [3] más un teorema de Rogers publicado en Halberstam–Roth [4, pp. 242–244]; véase también la exposición de Tao [5].

Lo que aporta esta nota:

1. **Una demostración finitaria y autocontenida** (Sección 3): solo conteo doble, la desigualdad de Markov y el lema de König. No usa teoría de la medida, teoría ergódica, el teorema de Davenport–Erdős ni el de Rogers. **Está formalizada y verificada en Lean 4 + Mathlib en esta sesión** (Sección 9).
2. **Forma óptima** (Teoremas 2 y 3): para *cualquier* sucesión de módulos, el supremo sobre todas las elecciones de la densidad superior del conjunto no cubierto es exactamente $\varepsilon^\ast = \lim_k \max_a d_k(a)$, se alcanza, y se alcanza con *densidad natural existente*. En $\mathbb{Z}$, $\varepsilon^\ast = 1 - \delta^\ast$, donde $\delta^\ast$ es la densidad logarítmica del conjunto de múltiplos de los $n_i$. La hipótesis del problema puede debilitarse a "densidad *inferior* cero para toda elección", o a "densidad cero solo para la elección $a = 0$"; pero **no** a "densidad inferior cero solo para $a=0$".
3. **Versión con multiplicidad** (Teorema 4): bajo la hipótesis del problema (y $n_1 \ge 2$), para todo $r$ casi todo entero satisface al menos $r$ de las congruencias, uniformemente en la elección de clases.
4. **Grupos abelianos generales** (Teorema 5): el enunciado de Erdős–Graham sigue siendo cierto para clases laterales de subgrupos de índice finito (p. ej. retículos en $\mathbb{Z}^d$), donde el teorema de Rogers es falso y por tanto el atajo "basta mirar $a=0$" deja de valer (Ejemplo 7.2).
5. Demostraciones cortas y autocontenidas del teorema de Rogers (Teorema 5.1; **verificado en Lean**) y de la dirección necesaria del teorema de Davenport–Erdős (Proposición 5.3).

En la Sección 10 se separa con cuidado lo conocido de lo (posiblemente) nuevo.

---

## 1. Notación y enunciados

Sea $1 \le n_1 \lt n_2 \lt \cdots$ una sucesión infinita de enteros. Una **elección** es una sucesión $a = (a_i)_{i \ge 1}$ con $a_i \in \mathbb{Z}/n_i\mathbb{Z}$. Para $k \ge 0$ definimos el conjunto de enteros **no cubiertos** por las primeras $k$ congruencias y por todas:

```math
R_k(a) = \lbrace m \in \mathbb{Z} : m \not\equiv a_i \pmod{n_i} \text{ para } 1 \le i \le k \rbrace, \qquad R(a) = \bigcap_{k \ge 0} R_k(a).
```

Sea $N_k = \operatorname{mcm}(n_1, \dots, n_k)$ (con $N_0 = 1$). El conjunto $R_k(a)$ es $N_k$‑periódico, así que tiene densidad natural

```math
d_k(a) = \frac{\lvert R_k(a) \cap [1, N_k] \rvert}{N_k}, \qquad \varepsilon_k = \max_a d_k(a), \qquad \varepsilon^\ast = \lim_{k \to \infty} \varepsilon_k .
```

($d_k(a)$ solo depende de $a_1, \dots, a_k$, de modo que el máximo es sobre un conjunto finito; $\varepsilon_k$ es no creciente porque $R_{k+1}(a) \subseteq R_k(a)$.) Para $S \subseteq \mathbb{Z}$ escribimos $\overline{d}(S) = \limsup_L \lvert S \cap [1,L] \rvert / L$, $\underline{d}(S) = \liminf_L \lvert S \cap [1,L] \rvert / L$, y $d(S)$ si coinciden.

- **(H)** Para toda elección $a$, $d(R(a)) = 0$.
- **(C)** $\varepsilon^\ast = 0$; es decir, para todo $\varepsilon \gt 0$ existe $k$ con $d_k(a) \lt \varepsilon$ para toda elección $a$.

El Problema 281 pregunta si (H) implica (C). La implicación (C) ⟹ (H) es inmediata ("claramente suficiente", en palabras de Erdős y Graham): $R(a) \subseteq R_k(a)$, luego $\overline{d}(R(a)) \le d_k(a) \le \varepsilon_k$ para todo $k$.

**Desplazamientos.** Para $t \in \mathbb{Z}$, la elección $a - t := (a_i - t \bmod n_i)_i$ cumple $R_k(a - t) = R_k(a) - t$. Un **desplazamiento profinito** es una sucesión coherente de enteros $\tau = (t_k)_{k \ge 0}$ con $t_{k+1} \equiv t_k \pmod{N_k}$; define la elección $a - \tau$ por $(a - \tau)_i := a_i - t_i \bmod n_i$. Como $n_i \mid N_i \mid N_k$ para $k \ge i$, se tiene $(a-\tau)_i \equiv a_i - t_k \pmod{n_i}$ para todo $k \ge i$, y por tanto

```math
R_k(a - \tau) = R_k(a) - t_k \quad\text{para todo } k, \qquad\text{en particular}\quad d_k(a - \tau) = d_k(a). \qquad\qquad (1.1)
```

> **Teorema 1 (Problema 281).** (H) ⟺ (C).

> **Teorema 2 (forma óptima).** Para toda sucesión $n_1 \lt n_2 \lt \cdots$:
> (a) $\overline{d}(R(a)) \le \varepsilon^\ast$ para toda elección $a$;
> (b) existe una elección $b$ tal que la densidad natural de $R(b)$ existe y vale $\varepsilon^\ast$.
> En consecuencia $\max_a \overline{d}(R(a)) = \max_a \underline{d}(R(a)) = \varepsilon^\ast$, y son equivalentes: (C); (H); y **(H⁻)**: para toda elección $a$, $\underline{d}(R(a)) = 0$.

> **Teorema 3 (caso entero: Rogers + Davenport–Erdős).** Sea $\delta_k$ la densidad del conjunto de enteros divisibles por alguno de $n_1, \dots, n_k$, y $\delta^\ast = \lim_k \delta_k$. Entonces:
> (a) $\varepsilon_k = d_k(0) = 1 - \delta_k$ para todo $k$, luego $\varepsilon^\ast = 1 - \delta^\ast$;
> (b) $\overline{d}(R(0)) = \varepsilon^\ast$: la elección homogénea $a = 0$ alcanza el máximo de la densidad superior;
> (c) son equivalentes: (C); (H); $\delta_k \to 1$; y **(H₀)**: el conjunto de enteros no divisibles por ningún $n_i$ tiene densidad $0$;
> (d) en cambio, "$\underline{d}(R(0)) = 0$" **no** implica (C).

> **Teorema 4 (multiplicidad).** Supongamos (C) (equivalentemente (H)) y $n_1 \ge 2$. Para $m \in \mathbb{Z}$ sea $\nu_{a,k}(m)$ el número de índices $i \le k$ con $m \equiv a_i \pmod{n_i}$. Entonces para todo $r \ge 1$ y todo $\varepsilon \gt 0$ existe $k$ tal que, para toda elección $a$,
> $d(\lbrace m : \nu_{a,k}(m) \lt r \rbrace) \lt \varepsilon$.
> En particular, para toda elección $a$ y todo $r$, el conjunto de enteros que satisfacen menos de $r$ de las congruencias tiene densidad $0$.

> **Teorema 5 (grupos abelianos).** El Teorema 1 y el Teorema 2 (con densidad superior) valen, con la misma demostración, para clases laterales de subgrupos de índice finito $\Lambda_1, \Lambda_2, \dots$ de un grupo abeliano $\Gamma$, midiendo densidades a lo largo de cualquier sucesión de conjuntos finitos $F_1, F_2, \dots \subseteq \Gamma$ que se equidistribuya módulo cada $\Lambda_1 \cap \dots \cap \Lambda_k$ (por ejemplo, $\Gamma = \mathbb{Z}^d$ con cajas). El Teorema 4 también vale. El Teorema 3 **no**: en $\mathbb{Z}^2$ la elección homogénea puede cubrirlo todo mientras otra elección deja densidad positiva sin cubrir.

Los enunciados precisos de los Teoremas 4 y 5 están en las Secciones 6 y 7.

---

## 2. Dos lemas elementales

**Lema 2.1 (ventanas de un período).** Sea $E \subseteq \mathbb{Z}$ un conjunto $N$‑periódico con $e = \lvert E \cap [1,N] \rvert$. Entonces todo intervalo de $N$ enteros consecutivos contiene exactamente $e$ elementos de $E$, y para todo $m \in \mathbb{Z}$, $\lvert \lbrace t \in \mathbb{Z}/N\mathbb{Z} : m + t \in E \rbrace \rvert = e$.

*Demostración.* Un intervalo de $N$ enteros consecutivos es un sistema completo de restos módulo $N$, igual que $m + \mathbb{Z}/N\mathbb{Z}$. ∎

**Lema 2.2 (König).** Sean $T_0, T_1, T_2, \dots$ conjuntos finitos no vacíos y $\pi_k : T_{k+1} \to T_k$ aplicaciones. Entonces existe una sucesión $(x_k)_{k \ge 0}$ con $x_k \in T_k$ y $\pi_k(x_{k+1}) = x_k$ para todo $k$.

*Demostración.* Es el lema de König para el árbol (de ramificación finita y con infinitos nodos) cuyos nodos de profundidad $k$ son las imágenes en $T_k$ de los elementos de niveles superiores. Explícitamente: sea $T_k^{(j)} \subseteq T_k$ la imagen de $T_j$ ($j \ge k$) bajo la composición de las $\pi$. Los $T_k^{(j)}$ son no vacíos, finitos y decrecientes en $j$, luego $T_k^{(\infty)} = \bigcap_j T_k^{(j)}$ es no vacío y $\pi_k$ aplica $T_{k+1}^{(\infty)}$ *sobre* $T_k^{(\infty)}$ (finitud). Se elige $x_0 \in T_0^{(\infty)}$ y recursivamente $x_{k+1} \in T_{k+1}^{(\infty)}$ con $\pi_k(x_{k+1}) = x_k$. ∎

---

## 3. Demostración finitaria del Teorema 1

**Lema 3.1 (compacidad).** Existe una elección $a^\ast$ con $d_k(a^\ast) \ge \varepsilon^\ast$ para todo $k$; de hecho $\lim_k d_k(a^\ast) = \varepsilon^\ast$.

*Demostración.* Llamemos *admisible* a una tupla $(a_1, \dots, a_k) \in \prod_{i \le k} \mathbb{Z}/n_i\mathbb{Z}$ si $d_k(a_1, \dots, a_k) \ge \varepsilon^\ast$. Sea $T_k$ el conjunto (finito) de tuplas admisibles de longitud $k$. Es no vacío: una tupla que realiza $\varepsilon_k \ge \varepsilon^\ast$ es admisible. La truncación $\pi_k : T_{k+1} \to T_k$ está bien definida porque $R_k \supseteq R_{k+1}$ implica $d_k(a_1,\dots,a_k) \ge d_{k+1}(a_1, \dots, a_{k+1})$. El Lema 2.2 da una elección $a^\ast$ cuyas truncaciones son todas admisibles. Finalmente $\varepsilon^\ast \le d_k(a^\ast) \le \varepsilon_k \to \varepsilon^\ast$. ∎

**Proposición 3.2 (clave).** Sea $a^\ast$ una elección cualquiera, $\rho_k = d_k(a^\ast)$ y $\rho = \lim_k \rho_k$. Existen un desplazamiento profinito $\tau$ y enteros $L_1 \lt L_2 \lt \cdots$ tales que la elección $b = a^\ast - \tau$ cumple

```math
\lvert R(b) \cap [1, L_j] \rvert \ \ge\ (\rho - 2^{-j})\, L_j \qquad \text{para todo } j \ge 1 .
```

En particular $\overline{d}(R(b)) = \rho$.

*Demostración.* Escribimos $R_k = R_k(a^\ast)$.

*Paso 0 (parámetros).* Sean $\lambda_j = 2^{-j}$ y $\theta_j = 2^{-j-1}$, de modo que $\sum_{j \ge 1} \theta_j = 1/2$. Como $\rho_k \downarrow \rho$ y $N_k \ge n_k \to \infty$, podemos elegir niveles $\kappa_1 \lt \kappa_2 \lt \cdots$ tales que

```math
\rho_{\kappa_j} - \rho \ \le\ \lambda_j \theta_j \qquad\text{y}\qquad L_j := N_{\kappa_j} \ \text{ es estrictamente creciente.}
```

*Paso 1 (defecto).* Para $k \ge \kappa_j$ sea $E_{j,k} = R_{\kappa_j} \setminus R_k$: es $N_k$‑periódico y, como $R_k \subseteq R_{\kappa_j}$, tiene densidad $\rho_{\kappa_j} - \rho_k \le \rho_{\kappa_j} - \rho \le \lambda_j\theta_j$. Para $t \in \mathbb{Z}$ definimos

```math
D_{j,k}(t) = \lvert \lbrace m \in [1, L_j] : m + t \in E_{j,k} \rbrace \rvert ,
```

que solo depende de $t$ módulo $N_k$.

*Paso 2 (conteo doble y Markov).* Por el Lema 2.1,

```math
\sum_{t \in \mathbb{Z}/N_k\mathbb{Z}} D_{j,k}(t) = \sum_{m=1}^{L_j} \lvert \lbrace t \in \mathbb{Z}/N_k\mathbb{Z} : m + t \in E_{j,k} \rbrace \rvert = L_j \, N_k\, (\rho_{\kappa_j} - \rho_k) \ \le\ L_j N_k \lambda_j \theta_j .
```

Luego el conjunto de restos *$j$‑malos*, $B_{j,k} = \lbrace t \in \mathbb{Z}/N_k\mathbb{Z} : D_{j,k}(t) \gt \lambda_j L_j \rbrace$, cumple $\lvert B_{j,k} \rvert \le \theta_j N_k$.

*Paso 3 (la maldad persiste hacia arriba).* Si $k' \ge k \ge \kappa_j$ entonces $E_{j,k'} \supseteq E_{j,k}$, luego $D_{j,k'}(t) \ge D_{j,k}(t)$ para todo $t \in \mathbb{Z}$. Así, si $t \bmod N_k \in B_{j,k}$ entonces $t \bmod N_{k'} \in B_{j,k'}$.

*Paso 4 (árbol de restos buenos).* Sea $T_k$ el conjunto de $t \in \mathbb{Z}/N_k\mathbb{Z}$ que no pertenecen a $B_{j,k}$ para ningún $j$ con $\kappa_j \le k$. Por el Paso 2, $\lvert T_k \rvert \ge N_k (1 - \sum_j \theta_j) \ge N_k/2 \gt 0$. Por el Paso 3, la reducción módulo $N_k$ aplica $T_{k+1}$ en $T_k$. El Lema 2.2 da enteros $t_0, t_1, t_2, \dots$ con $t_k \bmod N_k \in T_k$ y $t_{k+1} \equiv t_k \pmod{N_k}$: un desplazamiento profinito $\tau$.

*Paso 5 (conteo).* Sea $b = a^\ast - \tau$. Por (1.1), $R_k(b) = R_k - t_k$. Para $k \ge \kappa_j$, como $R_k = R_{\kappa_j} \setminus E_{j,k}$,

```math
\lvert R_k(b) \cap [1, L_j] \rvert = \lvert \lbrace m \in [1,L_j] : m + t_k \in R_{\kappa_j} \rbrace \rvert - D_{j,k}(t_k) = \rho_{\kappa_j} L_j - D_{j,k}(t_k) \ \ge\ (\rho_{\kappa_j} - \lambda_j) L_j ,
```

donde usamos el Lema 2.1 (la ventana $[1,L_j] + t_k$ es exactamente un período $L_j = N_{\kappa_j}$ de $R_{\kappa_j}$) y que $t_k \notin B_{j,k}$.

*Paso 6 (paso al límite, sin trampa).* $R(b) \cap [1,L_j]$ es la intersección de la sucesión decreciente de conjuntos **finitos** $R_k(b) \cap [1,L_j]$, $k \ge \kappa_j$, que por tanto se estabiliza; así $\lvert R(b) \cap [1,L_j] \rvert \ge (\rho_{\kappa_j} - \lambda_j) L_j \ge (\rho - 2^{-j}) L_j$. Como $L_j \to \infty$, $\overline{d}(R(b)) \ge \rho$. Y $\overline{d}(R(b)) \le d_k(b) = \rho_k$ para todo $k$, luego $\overline{d}(R(b)) = \rho$. ∎

*Demostración del Teorema 1.* (C) ⟹ (H) ya se vio. Recíprocamente, si (C) falla, $\varepsilon^\ast \gt 0$; el Lema 3.1 da $a^\ast$ con $\rho = \varepsilon^\ast$ y la Proposición 3.2 da $b$ con $\overline{d}(R(b)) = \varepsilon^\ast \gt 0$, lo que contradice (H). ∎

**Observación 3.3 (dónde está la dificultad).** No basta la compacidad sola: las densidades de los conjuntos $R_k(a^\ast)$ pueden estar todas por encima de $\varepsilon$ y sin embargo $R(a^\ast)$ ser vacío (por ejemplo, enumerando los enteros $m_1, m_2, \dots$ y tomando $a_i = m_i$ con $\sum 1/n_i$ pequeño). La densidad natural no es numerablemente aditiva. Lo que salva el argumento es la libertad de *desplazar*: el Paso 2 promedia sobre desplazamientos y el árbol del Paso 4 selecciona un desplazamiento profinito que es bueno en infinitas escalas a la vez. Es la versión finitaria del paso "medida de Haar positiva ⟹ algún trasladado tiene densidad superior positiva" de la demostración profinita [2, 6].

---

## 4. Existencia de la densidad: demostración del Teorema 2

Para reemplazar "densidad superior" por "densidad" basta cambiar Markov por una desigualdad maximal elemental.

**Lema 4.1 (desigualdad maximal en $\mathbb{Z}/N\mathbb{Z}$).** Sea $E \subseteq \mathbb{Z}$ un conjunto $N$‑periódico, $e = \lvert E \cap [1,N] \rvert$ y $\lambda \gt 0$. Sea

```math
B = \lbrace t \in [1,N] : \text{existe } L \in [1,N] \text{ con } \lvert E \cap [t+1, t+L] \rvert \gt \lambda L \rbrace .
```

Entonces $\lvert B \rvert \le 2e/\lambda$.

*Demostración.* Si $B = \emptyset$ no hay nada que probar. Sea $t_1 = \min B$ con testigo $L_1$ e $I_1 = [t_1 + 1, t_1 + L_1]$. Recursivamente, mientras exista $t \in B$ con $t \ge t_i + L_i$, sea $t_{i+1}$ el mínimo de tales $t$, con testigo $L_{i+1}$, e $I_{i+1} = [t_{i+1}+1, t_{i+1} + L_{i+1}]$. Los intervalos $I_i$ son disjuntos dos a dos y están contenidos en $[2, 2N]$. Además $t + 1 \in \bigcup_i I_i$ para todo $t \in B$: si $i$ es el mayor índice con $t_i \le t$, entonces $t \lt t_i + L_i$ (si no, $t_{i+1}$ existiría y sería $\le t$). Por tanto

```math
\lvert B \rvert \ \le\ \sum_i \lvert I_i \rvert = \sum_i L_i \ \lt\ \frac{1}{\lambda} \sum_i \lvert E \cap I_i \rvert \ \le\ \frac{1}{\lambda} \lvert E \cap [1, 2N] \rvert = \frac{2e}{\lambda}. \qquad ∎
```

**Proposición 4.2.** En la situación de la Proposición 3.2 puede elegirse $\tau$ de modo que $b = a^\ast - \tau$ cumpla $d(R(b)) = \rho$ (la densidad natural existe).

*Demostración.* Repetimos la demostración de la Proposición 3.2 con dos cambios. Elegimos los niveles con $\rho_{\kappa_j} - \rho \le \lambda_j\theta_j/2$, y declaramos $t \in \mathbb{Z}/N_k\mathbb{Z}$ *$j$‑malo* (para $k \ge \kappa_j$) si existe $L \in [1, N_k]$ con $\lvert \lbrace m \in [1,L] : m + t \in E_{j,k} \rbrace \rvert \gt \lambda_j L$. Por el Lema 4.1 (con $N = N_k$, $E = E_{j,k}$, $e = N_k(\rho_{\kappa_j} - \rho_k) \le N_k\lambda_j\theta_j/2$) hay a lo sumo $\theta_j N_k$ restos $j$‑malos. La maldad persiste hacia arriba (las ventanas admisibles $L \le N_k$ lo siguen siendo para $k' \ge k$, y $E_{j,k'} \supseteq E_{j,k}$). El Lema 2.2 da, igual que antes, un desplazamiento profinito $\tau$ tal que $t_k$ no es $j$‑malo para ningún $j$ con $\kappa_j \le k$.

Fijemos $j$ y $L \ge 1$. Tomamos $k \ge \kappa_j$ con $N_k \ge L$ y tal que $R(b) \cap [1,L] = R_k(b) \cap [1,L]$ (estabilización en un conjunto finito). Entonces

```math
\lvert R(b) \cap [1,L] \rvert = \lvert \lbrace m \le L : m + t_k \in R_{\kappa_j} \rbrace \rvert - \lvert \lbrace m \le L : m + t_k \in E_{j,k} \rbrace \rvert \ \ge\ (\rho_{\kappa_j} L - N_{\kappa_j}) - \lambda_j L ,
```

porque una ventana de longitud $L$ contiene $\lfloor L/N_{\kappa_j} \rfloor$ períodos completos de $R_{\kappa_j}$ (Lema 2.1) y $t_k$ no es $j$‑malo. Dividiendo por $L$ y haciendo $L \to \infty$: $\underline{d}(R(b)) \ge \rho_{\kappa_j} - \lambda_j \ge \rho - 2^{-j}$ para todo $j$, es decir $\underline{d}(R(b)) \ge \rho$. Como $\overline{d}(R(b)) \le \rho$, la densidad existe y vale $\rho$. ∎

*Demostración del Teorema 2.* (a) $R(a) \subseteq R_k(a)$ da $\overline{d}(R(a)) \le d_k(a) \le \varepsilon_k$ para todo $k$. (b) Lema 3.1 y Proposición 4.2. Las equivalencias: (C) ⟹ (H) ⟹ (H⁻) son triviales, y si (C) falla, la elección $b$ de (b) tiene $\underline{d}(R(b)) = \varepsilon^\ast \gt 0$, contra (H⁻). ∎

---

## 5. El caso de $\mathbb{Z}$: Rogers y Davenport–Erdős (Teorema 3)

### 5.1 Teorema de Rogers

**Teorema 5.1 (Rogers [4, pp. 242–244]; véase [5]).** Sean $n_1, \dots, n_k \ge 1$, $N$ un múltiplo común y $a_1, \dots, a_k \in \mathbb{Z}$. Entonces

```math
\lvert \lbrace x \in \mathbb{Z}/N\mathbb{Z} : \exists i,\ x \equiv a_i \ (\mathrm{mod}\ n_i) \rbrace \rvert \ \ge\ \lvert \lbrace x \in \mathbb{Z}/N\mathbb{Z} : \exists i,\ n_i \mid x \rbrace \rvert .
```

Equivalentemente, $d_k(a) \le d_k(0)$ para toda elección $a$.

*Demostración.* Inducción sobre $N$, para todas las familias finitas a la vez. Si $N = 1$ ambos lados valen $1$ (o $0$ si la familia es vacía). Si $N \gt 1$, sea $p$ un primo con $N = p^e M$, $e \ge 1$, $p \nmid M$, y escribamos $n_i = p^{e_i} M_i$ con $e_i \le e$, $M_i \mid M$. Por el teorema chino del resto, $x \mapsto (u,v) = (x \bmod p^e, x \bmod M)$ es una biyección $\mathbb{Z}/N \to \mathbb{Z}/p^e \times \mathbb{Z}/M$, y $x \equiv a_i \pmod{n_i}$ equivale a "$u \equiv a_i \pmod{p^{e_i}}$ y $v \equiv a_i \pmod{M_i}$". Para $u \in \mathbb{Z}/p^e$ sea $I_u = \lbrace i : u \equiv a_i \ (\mathrm{mod}\ p^{e_i}) \rbrace$, y para $v \in \mathbb{Z}/M$ sea $J_v = \lbrace i : M_i \mid v \rbrace$. Entonces

```math
\begin{aligned}
\lvert \mathrm{LI} \rvert &= \sum_{u} \lvert \lbrace v : \exists i \in I_u,\ v \equiv a_i \ (M_i) \rbrace \rvert \ \ge\ \sum_{u} \lvert \lbrace v : \exists i \in I_u,\ M_i \mid v \rbrace \rvert && \text{(hipótesis de inducción para } M \lt N\text{)} \\
&= \sum_{v} \lvert \lbrace u : \exists i \in J_v,\ u \equiv a_i \ (p^{e_i}) \rbrace \rvert \ \ge\ \sum_{v} \lvert \lbrace u : \exists i \in J_v,\ p^{e_i} \mid u \rbrace \rvert = \lvert \mathrm{LD} \rvert && \text{(lema de la cadena).}
\end{aligned}
```

*Lema de la cadena:* si $J \ne \emptyset$, sea $i_0 \in J$ con $e_{i_0}$ mínimo. Los subgrupos $p^{e_i}\mathbb{Z}/p^e$ están encajados, así que $\lbrace u : \exists i \in J,\ p^{e_i} \mid u \rbrace = \lbrace u : p^{e_{i_0}} \mid u \rbrace$ tiene $p^{e - e_{i_0}}$ elementos, los mismos que la única clase $\lbrace u \equiv a_{i_0} \ (p^{e_{i_0}}) \rbrace \subseteq \lbrace u : \exists i \in J,\ u \equiv a_i \ (p^{e_i}) \rbrace$. ∎

La estructura de cadena de los subgrupos de un $p$‑grupo cíclico es esencial: el teorema es falso en grupos no cíclicos (Ejemplo 7.2).

### 5.2 La dirección necesaria de Davenport–Erdős, por acoplamiento monótono

Para un conjunto finito $B$ de enteros positivos sea $M(B)$ el conjunto de enteros positivos divisibles por algún elemento de $B$, y

```math
f_B(s) = \sum_{\emptyset \ne J \subseteq B} (-1)^{\lvert J \rvert + 1} \operatorname{mcm}(J)^{-s}, \qquad s \gt 0 .
```

Por inclusión–exclusión, $f_B(1)$ es la densidad de $M(B)$, y para $s \gt 1$, $\sum_{m \in M(B)} m^{-s} = \zeta(s) f_B(s)$.

**Lema 5.2 (monotonía).** $f_B$ es no creciente en $(0, \infty)$. En particular, para $s \gt 1$,

```math
\sum_{m \in M(B)} m^{-s} \ \le\ \zeta(s)\, d(M(B)) .
```

*Demostración.* Sea $P$ el conjunto (finito) de primos que dividen a algún elemento de $B$, y sean $(X_p)_{p \in P}$ variables independientes exponenciales de parámetro $1$. Para $s \gt 0$ sea $G_p(s) = \lfloor X_p / (s \log p) \rfloor$. Entonces $\Pr(G_p(s) \ge j) = p^{-sj}$, así que para todo entero $c$ con factores primos en $P$, $\Pr(\forall p : G_p(s) \ge v_p(c)) = c^{-s}$. Sea $\mathcal{E}(s)$ el suceso "existe $b \in B$ con $G_p(s) \ge v_p(b)$ para todo $p$". Por inclusión–exclusión (la intersección de los sucesos correspondientes a $b \in J$ es el suceso correspondiente a $\operatorname{mcm}(J)$), $\Pr(\mathcal{E}(s)) = f_B(s)$. Pero $G_p(s)$ decrece puntualmente al crecer $s$, luego $\mathcal{E}(s') \subseteq \mathcal{E}(s)$ si $s \le s'$. ∎

**Proposición 5.3 (Davenport–Erdős [3], dirección necesaria).** Sea $A = \lbrace n_1 \lt n_2 \lt \cdots \rbrace$, $\delta_k = d(M(\lbrace n_1,\dots,n_k \rbrace))$, $\delta^\ast = \lim \delta_k$, y $R$ el conjunto de enteros positivos no divisibles por ningún $n_i$. Entonces $\overline{d}(R) \ge 1 - \delta^\ast$.

*Demostración.* Sea $s \gt 1$. Por el Lema 5.2 y convergencia monótona, $\sum_{m \in M(A)} m^{-s} = \lim_k \sum_{m \in M(A_k)} m^{-s} \le \zeta(s)\delta^\ast$, luego

```math
\sum_{m \in R} m^{-s} \ \ge\ (1 - \delta^\ast)\, \zeta(s) \ \ge\ \frac{1 - \delta^\ast}{s - 1}.
```

Sea $\eta \gt \overline{d}(R)$ y $x_0$ tal que $R(x) := \lvert R \cap [1,x] \rvert \le \eta x$ para $x \ge x_0$. Por sumación de Abel,

```math
\sum_{m \in R} m^{-s} = s \int_1^\infty R(x)\, x^{-s-1}\, dx \ \le\ s \int_1^{x_0} x^{-s}\, dx + s\eta \int_{x_0}^\infty x^{-s}\, dx \ \le\ s \log x_0 + \frac{s \eta}{s-1} .
```

Multiplicando por $s - 1$ y haciendo $s \to 1^+$ resulta $1 - \delta^\ast \le \eta$. Como $\eta \gt \overline{d}(R)$ era arbitrario, $1 - \delta^\ast \le \overline{d}(R)$. ∎

(El teorema completo de Davenport–Erdős dice más: la densidad logarítmica de $M(A)$ existe y vale $\delta^\ast = \underline{d}(M(A))$ [3; 4, Cap. V, Teorema 12]. Aquí solo se necesita la desigualdad anterior, que es la dirección "abeliana", fácil.)

### 5.3 Demostración del Teorema 3

(a) Es el Teorema 5.1: $d_k(a) \le d_k(0) = 1 - \delta_k$.

(b) $\overline{d}(R(0)) \le \varepsilon^\ast$ por el Teorema 2(a), y $\overline{d}(R(0)) \ge 1 - \delta^\ast = \varepsilon^\ast$ por la Proposición 5.3 y (a).

(c) (C) ⟺ $\delta_k \to 1$ por (a). (C) ⟹ (H) ⟹ (H₀) son triviales. Y (H₀) dice $\overline{d}(R(0)) = 0$, que por (b) da $\varepsilon^\ast = 0$, es decir (C).

(d) Por un teorema clásico (Besicovitch [11] para el límite inferior, Erdős [12] para el límite; Ford [13] determinó el orden de magnitud exacto), la densidad $\epsilon(T)$ del conjunto de enteros con algún divisor en $(T, 2T]$ tiende a $0$ cuando $T \to \infty$. Luego, para $K$ fijo, la densidad de los enteros con un divisor en $(T, KT]$ también tiende a $0$ (unión de $\lceil \log_2 K \rceil$ bloques diádicos). Elegimos $K_j = j + 1$ y $T_1 \lt T_2 \lt \cdots$ creciendo tan rápido que $T_{j+1} \gt K_j T_j$ y la densidad de los enteros con un divisor en $(T_j, K_j T_j]$ sea menor que $2^{-j-1}$. Sea $A = \bigcup_j (T_j, K_j T_j] \cap \mathbb{Z}$. Entonces $\delta^\ast \le \sum_j 2^{-j-1} = 1/2$, de modo que (C) falla ($\varepsilon^\ast \ge 1/2$); pero todos los enteros de $(T_j, K_jT_j]$ son múltiplos de elementos de $A$, luego $\lvert R(0) \cap [1, K_jT_j] \rvert \le T_j$ y $\underline{d}(R(0)) \le \liminf_j 1/K_j = 0$. ∎

---

## 6. Multiplicidad: demostración del Teorema 4

**Lema 6.1 (las colas heredan (C)).** Supongamos (C) y $n_1 \ge 2$. Para todo $j \ge 0$ y $\varepsilon \gt 0$ existe $k \gt j$ tal que, para toda elección de clases $a_{j+1}, \dots, a_k$, el conjunto

```math
W = \lbrace m \in \mathbb{Z} : m \not\equiv a_i \pmod{n_i} \text{ para } j \lt i \le k \rbrace
```

tiene densidad menor que $\varepsilon$.

*Demostración.* Sea $c_j = \prod_{i \le j} (1 - 1/n_i) \gt 0$. Por (C) existe $k \gt j$ con $d_k(a) \lt \varepsilon c_j$ para toda elección $a$. Fijemos $a_{j+1}, \dots, a_k$ y $W$. Promediando sobre todas las tuplas $(a_1, \dots, a_j) \in \prod_{i \le j} \mathbb{Z}/n_i\mathbb{Z}$ (para cada $x$ fijo, la fracción de tuplas con $x \not\equiv a_i \pmod{n_i}$ para todo $i \le j$ es exactamente $c_j$):

```math
\frac{1}{n_1 \cdots n_j} \sum_{a_1, \dots, a_j} d_k(a_1, \dots, a_k) = c_j \, d(W).
```

Cada sumando es $\lt \varepsilon c_j$, luego $d(W) \lt \varepsilon$. ∎

*Demostración del Teorema 4.* Dados $r$ y $\varepsilon$, aplicamos el Lema 6.1 sucesivamente con $\varepsilon/r$: obtenemos $0 = k_0 \lt k_1 \lt \cdots \lt k_r$ tales que, para toda elección, el conjunto $W_s$ de enteros que no satisfacen ninguna congruencia del bloque $k_{s-1} \lt i \le k_s$ tiene densidad $\lt \varepsilon/r$. Si un entero satisface menos de $r$ de las primeras $k_r$ congruencias, hay un bloque del que no satisface ninguna; así $\lbrace m : \nu_{a,k_r}(m) \lt r \rbrace \subseteq W_1 \cup \dots \cup W_r$, de densidad $\lt \varepsilon$. La última afirmación se sigue porque $\lbrace m : \nu_a(m) \lt r \rbrace \subseteq \lbrace m : \nu_{a,k}(m) \lt r \rbrace$ para todo $k$. ∎

**Observación 6.2 (una trampa).** *No* es cierto que, bajo (H), casi todo entero satisfaga infinitas congruencias: con $n_i$ = el $i$‑ésimo primo y $a = 0$, todo entero no nulo satisface solo un número finito. El Teorema 4 dice que $\nu_a(m) \to \infty$ "en densidad" (para cada $r$ fijo), no puntualmente; la unión numerable de conjuntos de densidad cero puede tener densidad uno. La hipótesis $n_1 \ge 2$ es necesaria: si $n_1 = 1$, (H) se cumple trivialmente y la conclusión puede fallar (p. ej. $n_i = 2^{i}$ para $i \ge 2$).

---

## 7. Grupos abelianos: Teorema 5

**Marco.** Sea $\Gamma$ un grupo abeliano y $\Lambda_1, \Lambda_2, \dots$ subgrupos de índice finito; $\Lambda^{(k)} = \Lambda_1 \cap \dots \cap \Lambda_k$ y $Q_k = [\Gamma : \Lambda^{(k)}]$. Una elección es $a = (a_i)$ con $a_i \in \Gamma/\Lambda_i$; $R_k(a) = \Gamma \setminus \bigcup_{i \le k} (a_i + \Lambda_i)$ es unión de clases de $\Lambda^{(k)}$ y $d_k(a)$ es la proporción de esas clases; $\varepsilon_k$, $\varepsilon^\ast$ como antes. Sea $(F_N)$ una sucesión de subconjuntos finitos no vacíos de $\Gamma$ **equidistribuida**: para todo $k$ y toda clase $c$ de $\Lambda^{(k)}$, $\lvert F_N \cap c \rvert / \lvert F_N \rvert \to 1/Q_k$. (Toda sucesión de Følner lo es; p. ej. $F_N = [1,N]^d$ en $\mathbb{Z}^d$.) Ponemos $\overline{d}_F(S) = \limsup_N \lvert S \cap F_N \rvert / \lvert F_N \rvert$.

**Teorema 7.1.** (i) $\overline{d}_F(R(a)) \le \varepsilon^\ast$ para toda elección $a$. (ii) Existe una elección $b$ con $\overline{d}_F(R(b)) = \varepsilon^\ast$. En particular: [para toda elección $a$, $\overline{d}_F(R(a)) = 0$] ⟺ [$\varepsilon^\ast = 0$]. (iii) Si $\varepsilon^\ast = 0$ y todos los $\Lambda_i \ne \Gamma$, vale la conclusión del Teorema 4.

*Demostración (cambios respecto de las Secciones 3 y 6).* (i) Por equidistribución, $\overline{d}_F(R_k(a)) = d_k(a)$. (ii) El Lema 3.1 no cambia. En la Proposición 3.2, los restos módulo $N_k$ se reemplazan por $\Gamma/\Lambda^{(k)}$ y un desplazamiento profinito es una sucesión coherente $t_k \in \Gamma/\Lambda^{(k)}$. Para cada $j$ se elige, además de $\kappa_j$, un índice $N_j$ (creciente) tal que $\lvert F_{N_j} \cap c \rvert \ge (1 - \lambda_j) \lvert F_{N_j} \rvert / Q_{\kappa_j}$ para toda clase $c$ de $\Lambda^{(\kappa_j)}$, y se define $D_{j,k}(t) = \lvert \lbrace g \in F_{N_j} : g + t \in E_{j,k} \rbrace \rvert$. El conteo doble da $\sum_{t \in \Gamma/\Lambda^{(k)}} D_{j,k}(t) = \lvert F_{N_j} \rvert\, Q_k\, (\rho_{\kappa_j} - \rho_k)$ exactamente (para cada $g$, $g + t$ recorre todas las clases una vez), y Markov, la persistencia y König funcionan igual. En el Paso 5 el término principal es $\lvert \lbrace g \in F_{N_j} : g + t_k \in R_{\kappa_j} \rbrace \rvert \ge \rho_{\kappa_j}(1 - \lambda_j) \lvert F_{N_j} \rvert$, y se concluye $\lvert R(b) \cap F_{N_j} \rvert \ge (\rho_{\kappa_j}(1-\lambda_j) - \lambda_j) \lvert F_{N_j} \rvert$. (iii) El Lema 6.1 y la demostración del Teorema 4 solo usan promedios sobre elecciones, con $c_j = \prod_{i \le j}(1 - 1/[\Gamma:\Lambda_i])$. ∎

**Ejemplo 7.2 (Rogers falla fuera del caso cíclico; el atajo $a = 0$ también).** En $\Gamma = \mathbb{Z}^2$ sean $\Lambda_1 = \lbrace x \text{ par} \rbrace$, $\Lambda_2 = \lbrace y \text{ par} \rbrace$, $\Lambda_3 = \lbrace x + y \text{ par} \rbrace$ y $\Lambda_i = 2^{i-2}\mathbb{Z}^2$ para $i \ge 4$. Con la elección homogénea, $\Lambda_1 \cup \Lambda_2 \cup \Lambda_3 = \mathbb{Z}^2$: **nada** queda sin cubrir. Pero las clases $\Lambda_1$, $(0,1) + \Lambda_2$, $\Lambda_3$ dejan sin cubrir la clase $\lbrace x \text{ impar}, y \text{ par} \rbrace$, de densidad $1/4$, y las clases de $\Lambda_i$, $i \ge 4$, cubren a lo sumo densidad $\sum_{i \ge 4} 4^{-(i-2)} = 1/12$. Luego $\varepsilon_k \ge 1/4 - 1/12 = 1/6$ para todo $k$: (C) falla aunque "(H) para $a = 0$" se cumple de la manera más fuerte posible. En grupos no cíclicos el cuantificador "para toda elección" de Erdős–Graham es indispensable, y la demostración finitaria (o la profinita) es la adecuada.

**Observación 7.3.** La versión con densidad inferior (Proposición 4.2) se extiende a $\mathbb{Z}^d$ con cajas usando la desigualdad maximal de recubrimiento de Vitali en lugar del Lema 4.1; para sucesiones de Følner temperadas en grupos promediables corresponde al teorema ergódico puntual de Lindenstrauss [16]. No lo desarrollamos aquí **[PLAUSIBLE, sin detalles]**.

---

## 8. Observaciones

**8.1 (Las dos observaciones de Erdős–Graham).** El promedio de $d_k(a)$ sobre todas las elecciones es $\prod_{i \le k}(1 - 1/n_i)$, luego $\varepsilon_k \ge \prod_{i \le k} (1 - 1/n_i)$; así (C) con $n_1 \ge 2$ fuerza $\sum 1/n_i = \infty$. Si los $n_i$ son coprimos dos a dos, $d_k(a) = \prod_{i \le k}(1 - 1/n_i)$ para *toda* elección (teorema chino), y (C) ⟺ $\sum 1/n_i = \infty$.

**8.2 (Subsucesión coprima).** Si (C) vale y $n_1 \ge 2$, la sucesión contiene una subsucesión infinita de términos coprimos dos a dos (observado en el foro [2]). En efecto, si no, un subconjunto coprimo dos a dos maximal $C$ es finito; todo $n_i$ comparte un factor primo con algún elemento de $C$, es decir, es divisible por algún primo del conjunto finito $Q$ de primos que dividen a elementos de $C$; entonces $R_k(0)$ contiene a los enteros coprimos con $\prod_{q \in Q} q$ y $d_k(0) \ge \prod_{q \in Q}(1 - 1/q) \gt 0$ para todo $k$.

**8.3 (Elecciones aleatorias frente al peor caso).** Si las clases $a_i$ se eligen al azar, independientes y uniformes, y $\sum 1/n_i = \infty$, entonces casi seguramente *todo* entero queda cubierto (infinitas veces): para $m$ fijo los sucesos $\lbrace a_i \equiv m \rbrace$ son independientes de probabilidad $1/n_i$ (Borel–Cantelli). Por tanto "(H) para casi toda elección" equivale a $\sum 1/n_i = \infty$, que es estrictamente más débil que (H) (ejemplo: $n_i = 2i$, donde $a = 0$ deja sin cubrir a los impares). El peor caso es estructurado, no aleatorio; en $\mathbb{Z}$ es exactamente $a = 0$ (Rogers).

**8.4 (Sucesiones de Behrend).** En la terminología de Hall [9], la condición $\delta_k \to 1$ dice que $\lbrace n_i \rbrace$ es una *sucesión de Behrend*. El Teorema 3(c) dice entonces: *la hipótesis del Problema 281 caracteriza exactamente a las sucesiones de Behrend*. El Lema 6.1 con $a = 0$ recupera el hecho conocido de que las colas de una sucesión de Behrend (sin el $1$) son de Behrend (consecuencia de la desigualdad de Behrend [10]).

**8.5 (Dinámica $\mathcal{B}$‑libre).** Para $a^\ast = 0$, el Teorema 2(b) afirma que para un desplazamiento profinito adecuado $\tau$ el conjunto $\lbrace m : n_i \nmid m + t_i \ \forall i \rbrace$ tiene densidad natural $1 - \delta^\ast$. Esto está emparentado con la existencia de puntos genéricos para la medida de Mirsky en la teoría de sistemas $\mathcal{B}$‑libres [14, 15] (referencias de contexto; no se revisó en esta sesión la correspondencia exacta de enunciados).

---

## 9. Verificación formal (Lean 4 + Mathlib) y numérica

Véanse `lean/README.md` (versiones, comandos, salida de `#print axioms`) y `verificacion/salida.txt`.

**Formalizado en esta sesión** (archivos `lean/Erdos281.lean` y `lean/Rogers.lean`):

| Enunciado en Lean | Corresponde a | Etiqueta |
|---|---|---|
| `Erdos281.erdos_281` | Teorema 1, dirección (H) ⟹ (C), sobre $\mathbb{N}$ con clases representadas por naturales | ver `lean/README.md` |
| `Erdos281.erdos_281_zmod` | Lo mismo con clases en `ZMod (n i)` (forma del enunciado de [6]) | ver `lean/README.md` |
| `Erdos281.erdos_281_converse` | (C) ⟹ (H) | ver `lean/README.md` |
| `Erdos281.erdos_281_strong` | Proposición 3.2 + Lema 3.1 en la forma: si (C) falla al nivel $\varepsilon$, existe $b$ con $\lvert R(b) \cap [0,N) \rvert \ge (\varepsilon/2) N$ para $N$ arbitrariamente grandes | ver `lean/README.md` |
| `Rogers.rogers`, `Rogers.rogers_uncovered` | Teorema 5.1 | ver `lean/README.md` |

Diferencias de formulación (inofensivas): en Lean las densidades se miden en $[0,N)$ en vez de $[1,N]$; el período usado es $\prod_{i \lt k} n_i$ en lugar del mínimo común múltiplo; los índices empiezan en $0$.

**No formalizado** (queda **[PLAUSIBLE]** con demostración completa en esta nota): Proposición 4.2 y Teorema 2(b) con densidad natural; Proposición 5.3; Teorema 3(b)–(d) (el punto (d) depende además del teorema de Erdős–Ford citado); Teorema 4; Teorema 7.1.

**Comprobaciones numéricas [NUMÉRICO]** (`verificacion/checks.py`): Rogers exhaustivo sobre 367 familias aleatorias de módulos (todas las elecciones); monotonía de $f_B$ y $f_B(1) = d(M(B))$ en 300 conjuntos; fallo de Rogers en $(\mathbb{Z}/2)^2$ ($3 \lt 4$); identidad de promedio del Lema 6.1 (exacta, con fracciones); desigualdad maximal del Lema 4.1 en 300 casos; tabla de multiplicidad para módulos primos.

---

## 10. Qué es conocido y qué es (posiblemente) nuevo

**Conocido** (no se reclama novedad):
- La respuesta afirmativa al Problema 281 y sus dos demostraciones: profinita/ergódica (Somani + GPT‑5.2 Pro; formalizada en Lean por Aristotle, Gemini 3 Flash y colaboradores [6]) y Davenport–Erdős + Rogers (KoishiChan) [2, 5]. Según fuentes secundarias, T. Tao tradujo además el argumento ergódico a lenguaje combinatorio usando la desigualdad maximal de Hardy–Littlewood; **no pude leer ese comentario directamente** (el sitio bloquea el acceso automatizado), así que la Sección 4 puede coincidir en lo esencial con él.
- El teorema de Rogers [4, 5] (y su redescubrimiento por Simpson [8], según [5]) y el teorema de Davenport–Erdős [3, 4]; que la cyclicidad es esencial para Rogers [5]; las observaciones 8.1 y 8.2.

**Posiblemente nuevo** (no lo encontré en las fuentes consultadas; la búsqueda no puede ser exhaustiva):
- La presentación finitaria con *solo Markov + König* para el enunciado original (Sección 3), y su formalización en Lean, independiente de la existente.
- La fórmula exacta $\max_a \overline{d}(R(a)) = \max_a \underline{d}(R(a)) = \varepsilon^\ast$ ($= 1 - \delta^\ast$ en $\mathbb{Z}$) con el cuadro completo de qué debilitamientos de la hipótesis bastan y cuál no (Teoremas 2 y 3).
- El Teorema 4 (multiplicidad uniforme) y su demostración por promedio sobre las primeras clases.
- El Teorema 7.1 (grupos abelianos) junto con el Ejemplo 7.2, que muestra que allí el problema no se reduce a la elección homogénea.
- La demostración por acoplamiento monótono del Lema 5.2 es probablemente folclore.

**Limitaciones.** (1) No pude acceder al hilo original del foro ni a la conversación de ChatGPT; el estado del arte se reconstruyó con fuentes secundarias [5, 6, 17] y un espejo parcial del hilo. (2) Las partes no formalizadas no tienen verificación mecánica. (3) El Teorema 3(d) usa un teorema profundo citado, no demostrado aquí. (4) No se obtuvo ninguna versión cuantitativa (dependencia de $k$ respecto de $\varepsilon$), que en general no puede existir sin información sobre la sucesión.

---

## Referencias

Las referencias con DOI fueron verificadas contra Crossref en esta sesión (título, autores, año, revista, páginas).

1. P. Erdős, R. L. Graham, *Old and new problems and results in combinatorial number theory*, Monographies de L'Enseignement Mathématique 28, Ginebra, 1980. (Sin DOI; existencia confirmada por la reseña en Amer. Math. Monthly 89 (1982), [doi:10.2307/2320942](https://doi.org/10.2307/2320942). El enunciado del problema se tomó de [2].)
2. T. F. Bloom (ed.), *Erdős Problem #281*, <https://www.erdosproblems.com/281> y su hilo de discusión <https://www.erdosproblems.com/forum/thread/281> (consultados el 9‑11‑2026 mediante la captura aportada por el usuario y un espejo parcial; acceso directo bloqueado).
3. H. Davenport, P. Erdős, *On sequences of positive integers*, Acta Arith. 2 (1936), 147–151. [doi:10.4064/aa-2-1-147-151](https://doi.org/10.4064/aa-2-1-147-151)
4. H. Halberstam, K. F. Roth, *Sequences*, Oxford Univ. Press, 1966; 2.ª ed. Springer, 1983. [doi:10.1007/978-1-4613-8227-0](https://doi.org/10.1007/978-1-4613-8227-0) (Cap. V: teorema de Rogers, pp. 242–244; Teorema 12, p. 258, según [2, 5].)
5. T. Tao, *Rogers' theorem on sieving*, blog *What's new*, 19‑1‑2026. <https://terrytao.wordpress.com/2026/01/19/rogers-theorem-on-sieving/>
6. Enunciado formal: Google DeepMind, *formal-conjectures*, `FormalConjectures/ErdosProblems/281.lean`, <https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/281.lean>; demostración formal del argumento de Somani: <https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos281.lean>.
7. M. Filaseta, K. Ford, S. Konyagin, C. Pomerance, G. Yu, *Sieving by large integers and covering systems of congruences*, J. Amer. Math. Soc. 20 (2007), 495–517. [doi:10.1090/S0894-0347-06-00549-2](https://doi.org/10.1090/S0894-0347-06-00549-2)
8. R. J. Simpson, *Exact coverings of the integers by arithmetic progressions*, Discrete Math. 59 (1986), 181–190. [doi:10.1016/0012-365X(86)90079-8](https://doi.org/10.1016/0012-365X(86)90079-8) (Atribución del redescubrimiento del teorema de Rogers según [5]; no revisé el artículo.)
9. R. R. Hall, *Sets of Multiples*, Cambridge Tracts in Math. 118, Cambridge Univ. Press, 1996. [doi:10.1017/CBO9780511566011](https://doi.org/10.1017/CBO9780511566011)
10. F. A. Behrend, *Generalization of an inequality of Heilbronn and Rohrbach*, Bull. Amer. Math. Soc. 54 (1948), 681–684. [doi:10.1090/S0002-9904-1948-09056-5](https://doi.org/10.1090/S0002-9904-1948-09056-5)
11. A. S. Besicovitch, *On the density of certain sequences of integers*, Math. Ann. 110 (1935), 336–341. [doi:10.1007/BF01448032](https://doi.org/10.1007/BF01448032)
12. P. Erdős, *A generalization of a theorem of Besicovitch*, J. London Math. Soc. 11 (1936), 92–98. [doi:10.1112/jlms/s1-11.2.92](https://doi.org/10.1112/jlms/s1-11.2.92) (Existencia verificada; la atribución del enunciado $\epsilon(T) \to 0$ a este artículo es de memoria, no revisé el texto. El enunciado en sí se sigue de [13].)
13. K. Ford, *The distribution of integers with a divisor in a given interval*, Ann. of Math. 168 (2008), 367–433. [doi:10.4007/annals.2008.168.367](https://doi.org/10.4007/annals.2008.168.367)
14. A. Dymek, S. Kasjan, J. Kułaga‑Przymus, M. Lemańczyk, *$\mathcal{B}$‑free sets and dynamics*, Trans. Amer. Math. Soc. 370 (2018), 5425–5489. [doi:10.1090/tran/7132](https://doi.org/10.1090/tran/7132)
15. S. Kasjan, G. Keller, M. Lemańczyk, *Dynamics of $\mathcal{B}$‑free sets: a view through the window*, Int. Math. Res. Not. 2019, 2690–2734. [doi:10.1093/imrn/rnx196](https://doi.org/10.1093/imrn/rnx196)
16. E. Lindenstrauss, *Pointwise theorems for amenable groups*, Invent. Math. 146 (2001), 259–295. [doi:10.1007/s002220100162](https://doi.org/10.1007/s002220100162)
17. T. Tao et al., *AI contributions to Erdős problems* (wiki), <https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems> (entrada del problema 281: solución con GPT‑5.2 Pro el 17‑1‑2026; literatura previa hallada el 18‑1‑2026; formalización el 19‑1‑2026).
18. P. Balister, B. Bollobás, R. Morris, J. Sahasrabudhe, M. Tiba, *On the Erdős covering problem: the density of the uncovered set*, Invent. Math. 228 (2022), 377–414. [doi:10.1007/s00222-021-01087-5](https://doi.org/10.1007/s00222-021-01087-5) (Contexto: densidad del conjunto no cubierto en sistemas finitos.)
19. B. Hough, *Solution of the minimum modulus problem for covering systems*, Ann. of Math. 181 (2015), 361–382. [doi:10.4007/annals.2015.181.1.6](https://doi.org/10.4007/annals.2015.181.1.6) (Contexto.)
