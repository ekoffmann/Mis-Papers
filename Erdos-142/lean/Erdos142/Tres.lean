import Erdos142.Exact

/-!
# El caso `k = 3`: lo que Mathlib ya demuestra, trasladado a `r 3 N`

Este archivo no demuestra nada nuevo sobre el Problema 142.  Identifica la función `r 3 N` de
`Erdos142.Exact` con el número de Roth `rothNumberNat N` de Mathlib y traslada los dos teoremas
de Mathlib sobre conjuntos sin progresiones aritméticas de tres términos:

* `behrend_r_three` : la cota inferior de Behrend, `N * exp (-4 √(log N)) ≤ r_3(N)`
  (`Behrend.roth_lower_bound`, `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean`);
* `r_three_isLittleO` : el teorema de Roth en la forma `r_3(N) = o(N)`
  (`rothNumberNat_isLittleO_id`, `Mathlib/Combinatorics/Additive/Corner/Roth.lean`).

Como consecuencia (`answer_three_isLittleO`), toda función `f` con `r_3 ~ f`, es decir, toda
respuesta admisible al caso `k = 3` del Problema 142, es `o(N)`.
-/

namespace Erdos142

/-- Para `k = 3`, la noción de «sin progresión aritmética» de `Erdos142.Exact` coincide con
`ThreeAPFree` de Mathlib. -/
lemma apFree_three_iff (S : Set ℕ) : APFree S 3 ↔ ThreeAPFree S := by
  constructor
  · intro hfree a ha b hb c hc habc
    by_contra hne
    apply hfree
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · -- `a < b`: la progresión es `a, b, c` con diferencia `b - a`
      refine ⟨a, b - a, by omega, ?_⟩
      intro i hi
      interval_cases i
      · have e : a + 0 * (b - a) = a := by omega
        rw [e]
        exact ha
      · have e : a + 1 * (b - a) = b := by omega
        rw [e]
        exact hb
      · have e : a + 2 * (b - a) = c := by omega
        rw [e]
        exact hc
    · -- `b < a`: entonces `c < b` y la progresión es `c, b, a` con diferencia `b - c`
      refine ⟨c, b - c, by omega, ?_⟩
      intro i hi
      interval_cases i
      · have e : c + 0 * (b - c) = c := by omega
        rw [e]
        exact hc
      · have e : c + 1 * (b - c) = b := by omega
        rw [e]
        exact hb
      · have e : c + 2 * (b - c) = a := by omega
        rw [e]
        exact ha
  · rintro h3 ⟨a, d, hd, hmem⟩
    have h0 := hmem 0 (by norm_num)
    have h1 := hmem 1 (by norm_num)
    have h2 := hmem 2 (by norm_num)
    have heq : a + 0 * d + (a + 2 * d) = a + 1 * d + (a + 1 * d) := by ring
    have := h3 h0 h1 h2 heq
    omega

/-- Nuestra `r 3 N` es el número de Roth de Mathlib. -/
theorem r_three_eq_rothNumberNat (N : ℕ) : r 3 N = rothNumberNat N := by
  have hroth : addRothNumber (Finset.Icc 1 N) = rothNumberNat N := by
    rw [← Finset.Ico_add_one_right_eq_Icc 1 N, addRothNumber_Ico, Nat.add_sub_cancel]
  rw [← hroth]
  apply le_antisymm
  · apply r_le
    intro S hS hfree
    exact ((apFree_three_iff _).1 hfree).le_addRothNumber hS
  · obtain ⟨t, hts, hcard, hfree⟩ := addRothNumber_spec (Finset.Icc 1 N)
    rw [← hcard]
    exact card_le_r hts ((apFree_three_iff _).2 hfree)

/-- Cota inferior de Behrend para `r_3(N)` (teorema de Mathlib, trasladado). -/
theorem behrend_r_three (N : ℕ) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤ r 3 N := by
  rw [r_three_eq_rothNumberNat]
  exact Behrend.roth_lower_bound

/-- Teorema de Roth en la forma `r_3(N) = o(N)` (teorema de Mathlib, trasladado). -/
theorem r_three_isLittleO :
    (fun N : ℕ => (r 3 N : ℝ)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
  have h : (fun N : ℕ => (r 3 N : ℝ)) = fun N : ℕ => (rothNumberNat N : ℝ) := by
    funext N
    rw [r_three_eq_rothNumberNat]
  rw [h]
  exact rothNumberNat_isLittleO_id

/-- Toda `f` con `r_3 ~ f` (es decir, toda respuesta admisible al caso `k = 3` del Problema 142)
es `o(N)`. -/
theorem answer_three_isLittleO (f : ℕ → ℝ)
    (hf : Asymptotics.IsEquivalent Filter.atTop (fun N : ℕ => (r 3 N : ℝ)) f) :
    f =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) :=
  hf.symm.isBigO.trans_isLittleO r_three_isLittleO

end Erdos142

#print axioms Erdos142.r_three_eq_rothNumberNat
#print axioms Erdos142.behrend_r_three
#print axioms Erdos142.r_three_isLittleO
#print axioms Erdos142.answer_three_isLittleO
