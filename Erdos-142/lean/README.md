# Verificación formal (Lean 4 + Mathlib) — en torno al Problema 142 de Erdős

**Estos archivos no demuestran el Problema 142, que sigue abierto.** Formalizan resultados elementales sobre $r_k(N)$ para progresiones largas y dos hechos sobre los enunciados formales públicos del problema.

Protocolo: un enunciado lleva **[PROBADO]** solo si (1) el archivo compila con código de salida 0, (2) no contiene `sorry`, y (3) `#print axioms` muestra únicamente `propext`, `Classical.choice` y `Quot.sound`.

## Versiones

- Lean `4.35.0` (`leanprover/lean4:v4.35.0`, ver `lean-toolchain`).
- Mathlib `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (ver `lake-manifest.json`).

## Cómo reproducir

```bash
cd Erdos-142/lean
```

```bash
lake exe cache get
```

```bash
lake build
```

`lake build` compila todos los módulos (`Erdos142.lean` los importa a todos) e imprime la salida de `#print axioms` de cada teorema.

## Archivos y enunciados

| Archivo | Teoremas principales | Contenido |
|---|---|---|
| `Erdos142/Exact.lean` (346 líneas) | `r_add_div_le`, `le_r_of_coprime`, `r_eq_of_le_minFac`, `r_prime_eq`, `r_sandwich`, `r_succ_range_le`, `r_prime_succ_range` | Definición de `r k N`; cota de bloques; fórmula exacta $r_k(N)=N-\lfloor N/k\rfloor$ para $N\le q(k-1)$ (Teorema A de la nota). Solo `import Mathlib`. |
| `Erdos142/Threshold.lean` (190) | `card_ge_of_mem`, `r_first_fail` | La fórmula exacta falla en $N=q(k-1)+1$ para todo $k\ge2$ (Teorema B): $q(k-1)$ es el mayor $M$ tal que vale para todo $N\le M$. |
| `Erdos142/Sqrt.lean` (376) | `card_hitting_sq`, `r_sq_add_lt` | Cota inferior en $N=k^2$: exceso de orden $\sqrt k$ (Teorema C). |
| `Erdos142/Construccion.lean` (269) | `Hset_hits`, `r_prime_sq_ge` | Conjunto de corte explícito de $2p-3$ elementos en $N=p^2$, $p\ge7$ primo (Teorema D): $r_p(p^2)\ge(p-1)^2+2$. |
| `Erdos142/FormalConjectures.lean` (341) | `maxCard_one`, `maxCard_two`, `erdos_142_statement_unsatisfiable`, `erdos_142_isTheta_statement_unsatisfiable`, `maxCard_eq_extremalNumber`, `erdos_142_variants_lower_of_quantitative` | Observaciones (A) y (B) de la nota sobre los enunciados de `formal-conjectures` y `openai/math` (definiciones copiadas literalmente). |
| `Erdos142/Resumen.lean` (119) | `r_eq_extremalNumber`, `r_eq_maxCard`, `r_prime_mul_sub_one`, `resumen_rango`, `resumen_cuadrado`, `resumen_primo_cuadrado` | Identifica `r` con las definiciones de los otros repositorios, demuestra $r_p(ip-1)=i(p-1)$ (Corolario A.2), resume y reimprime los axiomas de los 25 teoremas. |

Enunciados principales, tal como compilan:

```lean
def HasAP (A : Set ℕ) (k : ℕ) : Prop := ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A
def APFree (A : Set ℕ) (k : ℕ) : Prop := ¬ HasAP A k
noncomputable def r (k N : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 N).powerset).filter fun S : Finset ℕ ↦ APFree (S : Set ℕ) k).sup
    Finset.card

theorem r_eq_of_le_minFac (k N : ℕ) (hk : 2 ≤ k) (hN : N ≤ Nat.minFac k * (k - 1)) :
    r k N = N - N / k

theorem r_sandwich (k N p : ℕ) (hp : p.Prime) (hpk : p ≤ k) (hN : N ≤ p * (k - 1)) :
    N - N / p ≤ r k N ∧ r k N ≤ N - N / k

theorem r_first_fail (k : ℕ) (hk : 2 ≤ k) :
    r k (Nat.minFac k * (k - 1) + 1) = Nat.minFac k * (k - 2) + 1

theorem card_hitting_sq (k s : ℕ) (hk : 2 ≤ k) (H : Finset ℕ) (hH : H ⊆ Finset.Icc 1 (k ^ 2))
    (hit : ∀ a d : ℕ, 1 ≤ a → 0 < d → a + (k - 1) * d ≤ k ^ 2 → ∃ i, i < k ∧ a + i * d ∈ H)
    (hcard : H.card = k + s) : k < 8 * s ^ 2 + 8 * s + 4

theorem r_sq_add_lt (k s : ℕ) (hk : 2 ≤ k) (hs : 8 * s ^ 2 + 8 * s + 4 ≤ k) :
    r k (k ^ 2) + k + s < k ^ 2

theorem r_prime_sq_ge (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : (p - 1) ^ 2 + 2 ≤ r p (p ^ 2)

theorem erdos_142_statement_unsatisfiable :
    ¬ ∃ f : ℕ → ℝ, ∀ k : ℕ, (fun N => (FC.maxCard k N : ℝ)) ~[atTop] f

theorem erdos_142_variants_lower_of_quantitative
    (h : OAI.Erdos3.QuantitativeDensityTheorem) (k : ℕ) (hk : 1 < k) :
    (fun N => (FC.maxCard k N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ) / (N : ℝ).log)
```

## Correspondencia enunciado informal ↔ enunciado Lean

| Informal | Lean |
|---|---|
| PA de $k$ términos $a, a+d, \dots, a+(k-1)d$ con $d\ge1$ | `∃ a d, 0 < d ∧ ∀ i < k, a + i * d ∈ A` |
| $r_k(N)$ | `r k N`: supremo de los cardinales de los `S ⊆ Finset.Icc 1 N` con `APFree S k` |
| $\lfloor N/k\rfloor$ | `N / k` (división natural) |
| menor factor primo de $k$ | `Nat.minFac k` |
| $H$ corta todas las PA de $k$ términos de $[1,k^2]$ | `∀ a d, 1 ≤ a → 0 < d → a + (k - 1) * d ≤ k ^ 2 → ∃ i, i < k ∧ a + i * d ∈ H` |
| $\tau_k(N)=N-r_k(N)\ge m$ | se enuncia sin resta: `r k N + m ≤ N` |

Trampas revisadas: la resta natural truncada solo aparece en `N - N / k`, `k - 1`, `k - 2` con $k\ge2$ y en `N - N / p`, donde no trunca (siempre $N/k\le N$); `k - 1` en la hipótesis `hit` es exacto porque $k\ge2$; para $k=1$ y $k=0$ las definiciones degeneran y los teoremas piden $k\ge2$ donde hace falta; `r` coincide por definición con `OAI.Erdos3.extremalNumber` y, para $k\ge2$, con `Set.IsAPOfLengthFree.maxCard` de `formal-conjectures` (`r_eq_extremalNumber`, `r_eq_maxCard`).

## Registro de verificación

Compilación limpia de todo el proyecto (`lake build`) el 10‑11‑2026: **código de salida 0**, sin `sorry`, y los 25 teoremas dependen únicamente de `[propext, Classical.choice, Quot.sound]`. Registro completo (versiones, sha256 de cada fuente, auditoría de palabras prohibidas y salida de `#print axioms`) en [`registro_verificacion.txt`](registro_verificacion.txt).

Etiqueta resultante: **[PROBADO]** para los enunciados de la tabla. **No** están formalizados (quedan **[PLAUSIBLE]** o **[NUMÉRICO]** en `../NOTA.md`): el Corolario A.1, la unicidad del Corolario A.2, el lema de ventanas, la versión afinada del Teorema C y todos los valores exactos de §5. El teorema (B) es **condicional**: toma como hipótesis `OAI.Erdos3.QuantitativeDensityTheorem`, que el repositorio `openai/math` declara demostrado y que aquí no se ha recompilado. Un lema probado no es el teorema grande: ninguno de estos enunciados es el Problema 142. Además, verificar no es descubrir: los Teoremas C y D son versiones más débiles de resultados ya publicados (Truss 1991; Brown–Freedman 1989; Xu 2013; Korsky 2026), y el argumento del Teorema A es conocido; véase §4.0 y §7 de la nota.

Las advertencias que emite `lake build` son solo de estilo (cabecera de copyright, uso de `show`) y no afectan a la corrección.
