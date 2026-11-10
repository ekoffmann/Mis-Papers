import Erdos142.Exact

/-!
# An explicit hitting set of size `2p - 3` at `N = p²` (Teorema D)

For a prime `p ≥ 7` the set

`Hset p = {2, p + 1, 2p - 1} ∪ [2p + 3, 3p - 2] ∪ {j p : 3 ≤ j ≤ p}`

meets every `p`-term arithmetic progression contained in `{1, …, p²}` (`Hset_hits`).  It has at
most `2p - 3` elements, hence `r_p(p²) ≥ p² - (2p - 3) = (p - 1)² + 2` (`r_prime_sq_ge`).

Proof of `Hset_hits`.  Let the progression be `a, a + d, …, a + (p - 1) d ≤ p²`.  Then
`d ≤ p + 1`.  If `d = p + 1` then `a = 1` and the third term is `2p + 3`.  If `d = p` the
progression is a full residue class mod `p`, and `Hset p` meets every class.  If `d < p` the
progression contains exactly one multiple `m p` of `p`; if `m ≥ 3` it lies in `Hset p`, and the
cases `m = 2` (`hits_two`) and `m = 1` (`hits_one`) are handled by a case analysis on `d`.
-/

namespace Erdos142

/-- El conjunto de corte explícito de la nota (Teorema D). -/
def Hset (p : ℕ) : Finset ℕ :=
  {2, p + 1, 2 * p - 1} ∪ Finset.Icc (2 * p + 3) (3 * p - 2) ∪
    (Finset.Icc 3 p).image (fun j => j * p)

/-- Membership in the first two blocks of `Hset p`. -/
lemma mem_Hset_of {p x : ℕ}
    (h : x = 2 ∨ x = p + 1 ∨ x = 2 * p - 1 ∨ (2 * p + 3 ≤ x ∧ x ≤ 3 * p - 2)) :
    x ∈ Hset p := by
  unfold Hset
  apply Finset.mem_union_left
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc]
  omega

/-- Membership in the third block of `Hset p`: the multiples `m p` with `3 ≤ m ≤ p`. -/
lemma mem_Hset_mul {p m : ℕ} (h1 : 3 ≤ m) (h2 : m ≤ p) : m * p ∈ Hset p := by
  unfold Hset
  apply Finset.mem_union_right
  exact Finset.mem_image.2 ⟨m, Finset.mem_Icc.2 ⟨h1, h2⟩, rfl⟩

/-- Difference `d = p + 1`: the progression is `1, p + 2, 2p + 3, …`. -/
lemma hits_succ (p : ℕ) (hp7 : 7 ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (hlast : a + (p - 1) * (p + 1) ≤ p ^ 2) : ∃ i, i < p ∧ a + i * (p + 1) ∈ Hset p := by
  have h3 : (p - 1) * (p + 1) + 1 = p ^ 2 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  exact ⟨2, by omega, mem_Hset_of (by omega)⟩

/-- Difference `d = p`: the progression is a full residue class mod `p`. -/
lemma hits_self (p : ℕ) (hp7 : 7 ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (hlast : a + (p - 1) * p ≤ p ^ 2) : ∃ i, i < p ∧ a + i * p ∈ Hset p := by
  have h3 : (p - 1) * p + p = p ^ 2 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hc : a = 1 ∨ a = 2 ∨ (3 ≤ a ∧ a + 2 ≤ p) ∨ a + 1 = p ∨ a = p := by omega
  rcases hc with hc | hc | hc | hc | hc
  · exact ⟨1, by omega, mem_Hset_of (by omega)⟩
  · exact ⟨0, by omega, mem_Hset_of (by omega)⟩
  · exact ⟨2, by omega, mem_Hset_of (by omega)⟩
  · exact ⟨1, by omega, mem_Hset_of (by omega)⟩
  · refine ⟨2, by omega, ?_⟩
    have e : a + 2 * p = 3 * p := by omega
    rw [e]
    exact mem_Hset_mul (by omega) (by omega)

/-- Difference `d < p`, and the multiple of `p` in the progression is `2p`. -/
lemma hits_two (p : ℕ) (hp7 : 7 ≤ p) (hodd : p % 2 = 1) (a d j : ℕ) (ha : 1 ≤ a)
    (hd : 0 < d) (hdp : d + 1 ≤ p) (hj : j < p) (hlast : a + (p - 1) * d ≤ p ^ 2)
    (h : a + j * d = 2 * p) : ∃ i, i < p ∧ a + i * d ∈ Hset p := by
  have hcases : d = 1 ∨ d = 2 ∨ (3 ≤ d ∧ d + 2 ≤ p) ∨ d + 1 = p := by omega
  rcases hcases with rfl | rfl | ⟨hd3, hd2⟩ | hd1
  · -- `d = 1`
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact ⟨3, by omega, mem_Hset_of (by omega)⟩
    · exact ⟨j - 1, by omega, mem_Hset_of (by omega)⟩
  · -- `d = 2`
    have hc : j + 2 ≤ p - 1 ∨ j = p - 1 ∨ j = p - 2 := by omega
    rcases hc with hc | hc | hc
    · exact ⟨j + 2, by omega, mem_Hset_of (by omega)⟩
    · exact ⟨0, by omega, mem_Hset_of (by omega)⟩
    · exact ⟨(p - 3) / 2, by omega, mem_Hset_of (by omega)⟩
  · -- `3 ≤ d ≤ p - 2`: the term after `2p` is `2p + d`
    have hjle : j + 2 ≤ p := by
      by_contra hcon
      have hjeq : j = p - 1 := by omega
      subst hjeq
      have h3 : (p - 1) * 3 ≤ (p - 1) * d := Nat.mul_le_mul_left _ hd3
      omega
    have e : (j + 1) * d = j * d + d := by ring
    exact ⟨j + 1, by omega, mem_Hset_of (by omega)⟩
  · -- `d = p - 1`
    obtain rfl : d = p - 1 := by omega
    have hj2 : j ≤ 2 := by
      by_contra hcon
      have h3 : 3 * (p - 1) ≤ j * (p - 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    have hsq : (p - 1) * (p - 1) + 2 * p = p ^ 2 + 1 := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exfalso
      omega
    · exact ⟨0, by omega, mem_Hset_of (by omega)⟩
    · exact ⟨0, by omega, mem_Hset_of (by omega)⟩

/-- Difference `d < p`, and the multiple of `p` in the progression is `p` itself. -/
lemma hits_one (p : ℕ) (hp7 : 7 ≤ p) (hodd : p % 2 = 1) (a d j : ℕ) (ha : 1 ≤ a)
    (hd : 0 < d) (hdp : d + 1 ≤ p) (hj : j < p) (h : a + j * d = p) :
    ∃ i, i < p ∧ a + i * d ∈ Hset p := by
  have hcases : d = 1 ∨ d = 2 ∨ (3 ≤ d ∧ d + 4 ≤ p) ∨ d + 3 = p ∨ d + 2 = p ∨ d + 1 = p := by
    omega
  rcases hcases with rfl | rfl | ⟨hd3, hd4⟩ | hd3 | hd2 | hd1
  · -- `d = 1`
    have hc : a = 1 ∨ a = 2 ∨ 3 ≤ a := by omega
    rcases hc with hc | hc | hc
    · exact ⟨1, by omega, mem_Hset_of (by omega)⟩
    · exact ⟨0, by omega, mem_Hset_of (by omega)⟩
    · exact ⟨j + 1, by omega, mem_Hset_of (by omega)⟩
  · -- `d = 2`: the odd numbers from `a` on contain `2p - 1`
    exact ⟨j + (p - 1) / 2, by omega, mem_Hset_of (by omega)⟩
  · -- `3 ≤ d ≤ p - 4`: the progression cannot jump over the window `[2p + 3, 3p - 2]`
    have hbig : 2 * p + 3 ≤ a + (p - 1) * d := by
      have h3 : (p - 1) * 3 ≤ (p - 1) * d := Nat.mul_le_mul_left _ hd3
      omega
    have hex : ∃ i, 2 * p + 3 ≤ a + i * d := ⟨p - 1, hbig⟩
    obtain ⟨i, hi, hmin⟩ :
        ∃ i, 2 * p + 3 ≤ a + i * d ∧ ∀ k, k < i → ¬ (2 * p + 3 ≤ a + k * d) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
    have hip : i < p := by
      by_contra hcon
      exact hmin (p - 1) (by omega) hbig
    have hi0 : i ≠ 0 := by
      rintro rfl
      omega
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk := hmin k (by omega)
    have e : (k + 1) * d = k * d + d := by ring
    exact ⟨k + 1, hip, mem_Hset_of (by omega)⟩
  · -- `d = p - 3`
    obtain rfl : d = p - 3 := by omega
    have hj1 : j ≤ 1 := by
      by_contra hcon
      have h3 : 2 * (p - 3) ≤ j * (p - 3) := Nat.mul_le_mul_right _ (by omega)
      omega
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rcases Nat.lt_or_ge p 9 with h9 | h9
      · exact ⟨3, by omega, mem_Hset_of (by omega)⟩
      · exact ⟨2, by omega, mem_Hset_of (by omega)⟩
    · rcases Nat.lt_or_ge p 9 with h9 | h9
      · exact ⟨4, by omega, mem_Hset_of (by omega)⟩
      · exact ⟨3, by omega, mem_Hset_of (by omega)⟩
  · -- `d = p - 2`
    obtain rfl : d = p - 2 := by omega
    have hj1 : j ≤ 1 := by
      by_contra hcon
      have h3 : 2 * (p - 2) ≤ j * (p - 2) := Nat.mul_le_mul_right _ (by omega)
      omega
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact ⟨2, by omega, mem_Hset_of (by omega)⟩
    · exact ⟨0, by omega, mem_Hset_of (by omega)⟩
  · -- `d = p - 1`
    obtain rfl : d = p - 1 := by omega
    have hj1 : j ≤ 1 := by
      by_contra hcon
      have h3 : 2 * (p - 1) ≤ j * (p - 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact ⟨1, by omega, mem_Hset_of (by omega)⟩
    · exact ⟨2, by omega, mem_Hset_of (by omega)⟩

/-- `Hset p` corta toda progresión de `p` términos contenida en `{1, …, p²}`. -/
theorem Hset_hits (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (a d : ℕ) (ha : 1 ≤ a) (hd : 0 < d)
    (hlast : a + (p - 1) * d ≤ p ^ 2) : ∃ i, i < p ∧ a + i * d ∈ Hset p := by
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  -- the common difference is at most `p + 1`
  have hdle : d ≤ p + 1 := by
    by_contra hcon
    have h1 : p + 2 ≤ d := by omega
    have h2 : (p - 1) * (p + 2) ≤ (p - 1) * d := Nat.mul_le_mul_left _ h1
    have h3 : (p - 1) * (p + 2) + 2 = p ^ 2 + p := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega
  have hc : d = p + 1 ∨ d = p ∨ d + 1 ≤ p := by omega
  rcases hc with hd1 | hd2 | hdp
  · subst hd1
    exact hits_succ p hp7 a ha hlast
  · rw [hd2] at hlast ⊢
    exact hits_self p hp7 a ha hlast
  · -- `d < p`: the progression contains exactly one multiple of `p`
    have hcop : Nat.Coprime d p :=
      Nat.coprime_comm.1
        ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hd (by omega)))
    obtain ⟨j, hj, m, hm⟩ := exists_dvd_term a (by omega : 1 ≤ p) hcop
    have hjd : j * d ≤ (p - 1) * d := Nat.mul_le_mul_right d (by omega)
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · omega
      · exact hpos
    have hmp : m ≤ p := by
      have h1 : p * m ≤ p * p := by
        have := pow_two p
        omega
      exact Nat.le_of_mul_le_mul_left h1 (by omega)
    rcases (by omega : m = 1 ∨ m = 2 ∨ 3 ≤ m) with rfl | rfl | hm3
    · exact hits_one p hp7 hodd a d j ha hd hdp hj (by omega)
    · exact hits_two p hp7 hodd a d j ha hd hdp hj hlast (by omega)
    · refine ⟨j, hj, ?_⟩
      rw [hm, Nat.mul_comm p m]
      exact mem_Hset_mul hm3 hmp

/-- `Hset p` has at most `2p - 3` elements. -/
lemma card_Hset_le (p : ℕ) (hp7 : 7 ≤ p) : (Hset p).card ≤ 2 * p - 3 := by
  unfold Hset
  have h1 := Finset.card_union_le
    (({2, p + 1, 2 * p - 1} : Finset ℕ) ∪ Finset.Icc (2 * p + 3) (3 * p - 2))
    ((Finset.Icc 3 p).image (fun j => j * p))
  have h2 := Finset.card_union_le ({2, p + 1, 2 * p - 1} : Finset ℕ)
    (Finset.Icc (2 * p + 3) (3 * p - 2))
  have h3 : ({2, p + 1, 2 * p - 1} : Finset ℕ).card ≤ 3 := Finset.card_le_three
  have h4 : (Finset.Icc (2 * p + 3) (3 * p - 2)).card = p - 4 := by
    rw [Nat.card_Icc]
    omega
  have h5 : ((Finset.Icc 3 p).image (fun j => j * p)).card ≤ p - 2 := by
    refine le_trans Finset.card_image_le ?_
    rw [Nat.card_Icc]
    omega
  omega

/-- Teorema D: `r_p(p²) ≥ (p-1)² + 2` para todo primo `p ≥ 7`. -/
theorem r_prime_sq_ge (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : (p - 1) ^ 2 + 2 ≤ r p (p ^ 2) := by
  have hsub : Finset.Icc 1 (p ^ 2) \ Hset p ⊆ Finset.Icc 1 (p ^ 2) := Finset.sdiff_subset
  -- the complement of `Hset p` contains no `p`-term progression
  have hfree : APFree ((Finset.Icc 1 (p ^ 2) \ Hset p : Finset ℕ) : Set ℕ) p := by
    rintro ⟨a, d, hd, h⟩
    have h0 := h 0 (by omega)
    have hl := h (p - 1) (by omega)
    rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_Icc] at h0 hl
    obtain ⟨i, hi, hmem⟩ := Hset_hits p hp hp7 a d (by omega) hd hl.1.2
    have hi' := h i hi
    rw [Finset.mem_coe, Finset.mem_sdiff] at hi'
    exact hi'.2 hmem
  -- cardinality of the complement
  have hcardS : p ^ 2 - (2 * p - 3) ≤ (Finset.Icc 1 (p ^ 2) \ Hset p).card := by
    have h1 := Finset.le_card_sdiff (Hset p) (Finset.Icc 1 (p ^ 2))
    rw [Nat.card_Icc] at h1
    have h2 := card_Hset_le p hp7
    omega
  have halg : (p - 1) ^ 2 + 2 = p ^ 2 - (2 * p - 3) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have e : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    omega
  calc (p - 1) ^ 2 + 2 = p ^ 2 - (2 * p - 3) := halg
    _ ≤ (Finset.Icc 1 (p ^ 2) \ Hset p).card := hcardS
    _ ≤ r p (p ^ 2) := card_le_r hsub hfree

end Erdos142

#print axioms Erdos142.Hset_hits
#print axioms Erdos142.r_prime_sq_ge
