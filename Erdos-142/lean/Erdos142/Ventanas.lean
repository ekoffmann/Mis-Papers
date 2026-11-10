import Mathlib

/-!
# Forma de ventanas (Lema 2 de la nota)

Un conjunto `H` corta todas las progresiones aritméticas de `k` términos y diferencia `d`
contenidas en `{1, …, N}` si y solo si, en todo intervalo de `k * d` enteros consecutivos contenido
en `{1, …, N}`, `H` tiene elementos de las `d` clases de restos módulo `d` (siempre que
`k * d ≤ N`).

Idea: en un intervalo de `k * d` enteros consecutivos cada clase módulo `d` tiene exactamente `k`
elementos, que forman una progresión de `k` términos y diferencia `d`; recíprocamente, toda
progresión de ese tipo está contenida en uno de esos intervalos.
-/

namespace Erdos142

/-- Lema de ventanas.  Sea `1 ≤ k`, `1 ≤ d` y `k * d ≤ N`.  Un conjunto `H` corta todas las
progresiones de `k` términos y diferencia `d` contenidas en `{1, …, N}` si y solo si, en todo
intervalo `{b, …, b + k*d - 1} ⊆ {1, …, N}` de `k * d` enteros consecutivos, `H` tiene elementos de
las `d` clases de restos módulo `d`. -/
theorem window_iff (k N d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hkd : k * d ≤ N) (H : Finset ℕ) :
    (∀ a : ℕ, 1 ≤ a → a + (k - 1) * d ≤ N → ∃ i, i < k ∧ a + i * d ∈ H) ↔
      (∀ b : ℕ, 1 ≤ b → b + k * d ≤ N + 1 → ∀ ρ : ℕ, ρ < d →
        ∃ x, x ∈ H ∧ b ≤ x ∧ x < b + k * d ∧ x % d = ρ) := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hqd : (q + 1) * d = q * d + d := by ring
  constructor
  · -- progresiones ⟹ ventanas
    intro h b hb hbN ρ hρ
    -- el menor entero `a ≥ b` con `a % d = ρ`
    obtain ⟨a, hab, habd, hamod⟩ : ∃ a, b ≤ a ∧ a < b + d ∧ a % d = ρ := by
      obtain ⟨r, hr⟩ : ∃ r, r = b % d := ⟨_, rfl⟩
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = d * (b / d) := ⟨_, rfl⟩
      have hbm : r < d := by rw [hr]; exact Nat.mod_lt _ (by omega)
      have hdm : Q + r = b := by rw [hr, hQ]; exact Nat.div_add_mod b d
      rcases Nat.lt_or_ge ρ r with hlt | hle
      · refine ⟨b + (d - r) + ρ, by omega, by omega, ?_⟩
        have e1 : d * (b / d + 1) = d * (b / d) + d := by ring
        have e : b + (d - r) + ρ = ρ + d * (b / d + 1) := by rw [e1, ← hQ]; omega
        rw [e, Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hρ
      · refine ⟨b + (ρ - r), by omega, by omega, ?_⟩
        have e : b + (ρ - r) = ρ + d * (b / d) := by rw [← hQ]; omega
        rw [e, Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hρ
    obtain ⟨i, hi, hmem⟩ := h a (by omega) (by omega)
    have hid : i * d ≤ q * d := Nat.mul_le_mul_right d (by omega)
    refine ⟨a + i * d, hmem, by omega, by omega, ?_⟩
    rw [Nat.add_mul_mod_self_right]
    exact hamod
  · -- ventanas ⟹ progresiones
    intro h a ha haN
    -- una ventana `[b, b + k d)` contenida en `[1, N]` que contiene a la progresión
    obtain ⟨b, hb1, hbN, hba, hlast⟩ : ∃ b, 1 ≤ b ∧ b + (q + 1) * d ≤ N + 1 ∧ b ≤ a ∧
        a + q * d < b + (q + 1) * d := by
      rcases Nat.lt_or_ge (N + 1) (a + (q + 1) * d) with hc | hc
      · exact ⟨N + 1 - (q + 1) * d, by omega, by omega, by omega, by omega⟩
      · exact ⟨a, ha, hc, le_rfl, by omega⟩
    obtain ⟨x, hxH, hbx, hxlt, hxmod⟩ := h b hb1 hbN (a % d) (Nat.mod_lt _ (by omega))
    rcases Nat.lt_or_ge x a with hxa | hax
    · -- `x < a` es imposible: `a - x` sería un múltiplo positivo de `d` menor que `d`
      exfalso
      have hdvd : d ∣ a - x := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hxmod.symm)
      obtain ⟨i, hi⟩ := hdvd
      have hi1 : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · rw [Nat.mul_zero] at hi
          omega
        · exact hpos
      have h2 : d * 1 ≤ d * i := Nat.mul_le_mul_left d hi1
      rw [Nat.mul_one] at h2
      omega
    · -- `x = a + i d` con `i < k`
      have hdvd : d ∣ x - a := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hxmod)
      obtain ⟨i, hi⟩ := hdvd
      refine ⟨i, ?_, ?_⟩
      · have hcomm : d * (q + 1) = (q + 1) * d := Nat.mul_comm _ _
        have h1 : d * i < d * (q + 1) := by omega
        exact Nat.lt_of_mul_lt_mul_left h1
      · have hcomm : i * d = d * i := Nat.mul_comm _ _
        have e : a + i * d = x := by omega
        rw [e]
        exact hxH

end Erdos142

#print axioms Erdos142.window_iff
