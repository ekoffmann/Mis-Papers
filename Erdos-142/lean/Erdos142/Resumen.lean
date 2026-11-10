import Erdos142.Exact
import Erdos142.Threshold
import Erdos142.Sqrt
import Erdos142.Construccion
import Erdos142.FormalConjectures

/-!
# Problema 142 de Erdős — resumen de los enunciados verificados

Este archivo no demuestra el Problema 142 (que sigue abierto).  Reúne los enunciados verificados
en los demás módulos y vuelve a imprimir los axiomas de los que depende cada uno.

* `Erdos142.r_eq_extremalNumber`, `Erdos142.r_eq_maxCard` : la función `r` usada aquí es la misma
  que `OAI.Erdos3.extremalNumber` (openai/math) y, para `k ≥ 2`, que
  `Set.IsAPOfLengthFree.maxCard` (google-deepmind/formal-conjectures).
* `Erdos142.resumen_rango` : fórmula exacta `r_k(N) = N - ⌊N/k⌋` para `N ≤ q (k - 1)` (con `q` el
  menor factor primo de `k`) y fallo de la fórmula en `N = q (k - 1) + 1`.
* `Erdos142.resumen_cuadrado` : en `N = k²`, `r_k(k²) ≤ k² - k - s - 1` si `8 s² + 8 s + 4 ≤ k`.
* `Erdos142.resumen_primo_cuadrado` : para `p ≥ 7` primo,
  `(p - 1)² + 2 ≤ r_p(p²) ≤ p² - p - 1`.
-/

namespace Erdos142

/-- La función `r` de `Erdos142.Exact` coincide (por definición) con `extremalNumber` de
openai/math. -/
theorem r_eq_extremalNumber (k N : ℕ) : r k N = OAI.Erdos3.extremalNumber k N := rfl

/-- ... y, para `k ≥ 2`, con `maxCard` de formal-conjectures. -/
theorem r_eq_maxCard (k N : ℕ) (hk : 2 ≤ k) : r k N = FC.maxCard k N := by
  rw [maxCard_eq_extremalNumber k N hk]
  rfl

/-- **Fórmula exacta y optimalidad de su rango.** Sea `q` el menor factor primo de `k ≥ 2`.
Entonces `r_k(N) = N - ⌊N/k⌋` para todo `N ≤ q (k - 1)`, y en `N = q (k - 1) + 1` la fórmula
falla: `r_k(N) = q (k - 2) + 1 = N - ⌊N/k⌋ - 1`. -/
theorem resumen_rango (k : ℕ) (hk : 2 ≤ k) :
    (∀ N, N ≤ Nat.minFac k * (k - 1) → r k N = N - N / k) ∧
      r k (Nat.minFac k * (k - 1) + 1) = Nat.minFac k * (k - 2) + 1 :=
  ⟨fun N hN => r_eq_of_le_minFac k N hk hN, r_first_fail k hk⟩

/-- **En `N = k²`.** Siempre `r_k(k²) ≤ k² - k`; y si `8 s² + 8 s + 4 ≤ k` entonces
`r_k(k²) ≤ k² - k - s - 1`. -/
theorem resumen_cuadrado (k s : ℕ) (hk : 2 ≤ k) (hs : 8 * s ^ 2 + 8 * s + 4 ≤ k) :
    r k (k ^ 2) + k ≤ k ^ 2 ∧ r k (k ^ 2) + k + s < k ^ 2 := by
  refine ⟨?_, r_sq_add_lt k s hk hs⟩
  have h := r_add_div_le k (k ^ 2) (by omega)
  have h3 : k ^ 2 / k = k := by
    rw [pow_two]
    exact Nat.mul_div_cancel_left k (by omega)
  omega

/-- **En `N = p²`, `p ≥ 7` primo.** `(p - 1)² + 2 ≤ r_p(p²)` (construcción explícita con
`2p - 3` puntos eliminados) y `r_p(p²) + p + 1 ≤ p²` (hace falta al menos un punto más que los
`p` de la cota de bloques). -/
theorem resumen_primo_cuadrado (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p - 1) ^ 2 + 2 ≤ r p (p ^ 2) ∧ r p (p ^ 2) + p + 1 ≤ p ^ 2 := by
  refine ⟨r_prime_sq_ge p hp hp7, ?_⟩
  have h := r_sq_add_lt p 0 (by omega) (by omega)
  omega

end Erdos142

#print axioms Erdos142.r_add_div_le
#print axioms Erdos142.le_r_of_coprime
#print axioms Erdos142.r_eq_of_le_minFac
#print axioms Erdos142.r_prime_eq
#print axioms Erdos142.r_sandwich
#print axioms Erdos142.r_succ_range_le
#print axioms Erdos142.r_prime_succ_range
#print axioms Erdos142.card_ge_of_mem
#print axioms Erdos142.r_first_fail
#print axioms Erdos142.card_hitting_sq
#print axioms Erdos142.r_sq_add_lt
#print axioms Erdos142.Hset_hits
#print axioms Erdos142.r_prime_sq_ge
#print axioms Erdos142.maxCard_one
#print axioms Erdos142.maxCard_two
#print axioms Erdos142.erdos_142_statement_unsatisfiable
#print axioms Erdos142.erdos_142_isTheta_statement_unsatisfiable
#print axioms Erdos142.maxCard_eq_extremalNumber
#print axioms Erdos142.erdos_142_variants_lower_of_quantitative
#print axioms Erdos142.r_eq_extremalNumber
#print axioms Erdos142.r_eq_maxCard
#print axioms Erdos142.resumen_rango
#print axioms Erdos142.resumen_cuadrado
#print axioms Erdos142.resumen_primo_cuadrado
