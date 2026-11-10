import Mathlib

/-!
# Exact values of `r_k(N)` for long progressions

`r k N` is the largest size of a subset of `{1, …, N}` containing no `k`-term arithmetic
progression (with positive common difference).  This file proves:

* `r_add_div_le` : `r_k(N) ≤ N - ⌊N/k⌋` (disjoint blocks of `k` consecutive integers);
* `le_r_of_coprime` : if `1 ≤ m ≤ k` and every admissible common difference is coprime to `m`,
  then `N - ⌊N/m⌋ ≤ r_k(N)` (delete the multiples of `m`);
* `r_eq_of_le_minFac` : `r_k(N) = N - ⌊N/k⌋` for `N ≤ minFac k * (k - 1)`;
* `r_prime_eq` : `r_p(N) = N - ⌊N/p⌋` for `p` prime and `N ≤ p (p - 1)`;
* `r_sandwich` : `N - ⌊N/p⌋ ≤ r_k(N) ≤ N - ⌊N/k⌋` for a prime `p ≤ k` and `N ≤ p (k - 1)`;
* `r_succ_range_le` : `r_k(k(k-1)+1) ≤ (k-1)^2`;
* `r_prime_succ_range` : `r_p(p(p-1)+1) = (p-1)^2` for `p` prime.
-/

namespace Erdos142

/-- `A` contains a `k`-term arithmetic progression with positive common difference. -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- `A` contains no `k`-term arithmetic progression with positive common difference. -/
def APFree (A : Set ℕ) (k : ℕ) : Prop := ¬ HasAP A k

/-- `r k N`: the largest size of a subset of `{1, …, N}` with no `k`-term arithmetic progression
(the same definition as `OAI.Erdos3.extremalNumber` in the openai/math Lean library). -/
noncomputable def r (k N : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 N).powerset).filter fun S : Finset ℕ ↦ APFree (S : Set ℕ) k).sup
    Finset.card

/-! ### Basic facts about `r` -/

/-- Any `k`-AP-free subset of `{1,…,N}` has at most `r k N` elements. -/
lemma card_le_r {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hfree : APFree (S : Set ℕ) k) : S.card ≤ r k N := by
  classical
  unfold r
  apply Finset.le_sup (f := Finset.card)
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hS, hfree⟩

/-- To bound `r k N` above it suffices to bound every `k`-AP-free subset of `{1,…,N}`. -/
lemma r_le {k N B : ℕ}
    (h : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → APFree (S : Set ℕ) k → S.card ≤ B) :
    r k N ≤ B := by
  classical
  unfold r
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact h S hS.1 hS.2

/-- `r k N` is monotone in `N`. -/
lemma r_mono (k : ℕ) {N N' : ℕ} (h : N ≤ N') : r k N ≤ r k N' := by
  apply r_le
  intro S hS hfree
  exact card_le_r (hS.trans (Finset.Icc_subset_Icc_right h)) hfree

/-- A `k`-AP-free finite set misses a term of every `k`-term progression. -/
lemma exists_not_mem_of_APFree {S : Finset ℕ} {k : ℕ} (hfree : APFree (S : Set ℕ) k)
    (a d : ℕ) (hd : 0 < d) : ∃ i, i < k ∧ a + i * d ∉ S := by
  by_contra hcon
  push Not at hcon
  exact hfree ⟨a, d, hd, fun i hi => Finset.mem_coe.2 (hcon i hi)⟩

/-- Uniqueness of quotient and remainder, in the form used below. -/
lemma block_unique {c j j' u u' : ℕ} (hu : u < c) (hu' : u' < c)
    (h : j * c + u = j' * c + u') : j = j' ∧ u = u' := by
  have hc : 0 < c := by omega
  have h1 : (j * c + u) / c = j := by
    rw [Nat.mul_comm, Nat.mul_add_div hc, Nat.div_eq_of_lt hu, Nat.add_zero]
  have h2 : (j' * c + u') / c = j' := by
    rw [Nat.mul_comm, Nat.mul_add_div hc, Nat.div_eq_of_lt hu', Nat.add_zero]
  have hj : j = j' := by
    calc j = (j * c + u) / c := h1.symm
      _ = (j' * c + u') / c := by rw [h]
      _ = j' := h2
  subst hj
  exact ⟨rfl, by omega⟩

/-! ### The trivial upper bound -/

/-- Trivial upper bound: each of the `⌊N/k⌋` disjoint blocks of `k` consecutive integers must
lose a point.  So `r_k(N) ≤ N - ⌊N/k⌋`. -/
theorem r_add_div_le (k N : ℕ) (hk : 1 ≤ k) : r k N + N / k ≤ N := by
  have _ : 0 < k := hk
  have hle : r k N ≤ N - N / k := by
    apply r_le
    intro S hS hfree
    classical
    have hex : ∀ j : ℕ, ∃ i, i < k ∧ j * k + 1 + i * 1 ∉ S :=
      fun j => exists_not_mem_of_APFree hfree (j * k + 1) 1 one_pos
    choose f hf using hex
    simp only [mul_one] at hf
    have hinj : Set.InjOn (fun j => j * k + 1 + f j) (Finset.range (N / k) : Set ℕ) := by
      intro j _ j' _ h
      dsimp only at h
      exact (block_unique (c := k) (hf j).1 (hf j').1 (by omega)).1
    have hmaps : ∀ j ∈ Finset.range (N / k),
        (fun j => j * k + 1 + f j) j ∈ Finset.Icc 1 N \ S := by
      intro j hj
      rw [Finset.mem_range] at hj
      have h1 := (hf j).1
      have h2 : (j + 1) * k ≤ N / k * k := Nat.mul_le_mul_right k hj
      have h3 : N / k * k ≤ N := Nat.div_mul_le_self N k
      have h4 : (j + 1) * k = j * k + k := by ring
      rw [Finset.mem_sdiff, Finset.mem_Icc]
      exact ⟨⟨by dsimp only; omega, by dsimp only; omega⟩, (hf j).2⟩
    have hcard : (Finset.range (N / k)).card ≤ (Finset.Icc 1 N \ S).card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    have hsd := Finset.card_sdiff_add_card_eq_card hS
    rw [Nat.card_Icc] at hsd
    rw [Finset.card_range] at hcard
    omega
  have hdiv : N / k ≤ N := Nat.div_le_self N k
  omega

/-! ### The construction: deleting the multiples of `m` -/

/-- If `d` is coprime to `m ≥ 1`, the progression `a, a + d, a + 2d, …` hits a multiple of `m`
within its first `m` terms. -/
lemma exists_dvd_term {m d : ℕ} (a : ℕ) (hm : 1 ≤ m) (hcop : Nat.Coprime d m) :
    ∃ i, i < m ∧ m ∣ a + i * d := by
  have : NeZero m := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod m)ˣ, (u : ZMod m) = (d : ZMod m) :=
    ⟨ZMod.unitOfCoprime d hcop, ZMod.coe_unitOfCoprime d hcop⟩
  refine ⟨((-(a : ZMod m)) * ((u⁻¹ : (ZMod m)ˣ) : ZMod m)).val, ZMod.val_lt _, ?_⟩
  rw [← CharP.cast_eq_zero_iff (ZMod m) m]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [← hu, mul_assoc, Units.inv_mul]
  ring

/-- The number of non-multiples of `m` in `{1,…,N}`. -/
lemma card_filter_not_dvd (N m : ℕ) :
    ((Finset.Icc 1 N).filter (fun x => ¬ m ∣ x)).card = N - N / m := by
  have h1 : ((Finset.Icc 1 N).filter (fun x => m ∣ x)).card = N / m := by
    rw [show Finset.Icc 1 N = Finset.Ioc 0 N from Finset.Icc_add_one_left_eq_Ioc 0 N]
    exact Nat.Ioc_filter_dvd_card_eq_div N m
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 N) (fun x => m ∣ x)
  rw [h1, Nat.card_Icc] at h2
  omega

/-- Construction: if `1 ≤ m ≤ k` and every admissible common difference `d` (`0 < d` and
`d * (k - 1) < N`) is coprime to `m`, then deleting the multiples of `m` from `{1,…,N}` leaves a
`k`-AP-free set, so `N - ⌊N/m⌋ ≤ r_k(N)`. -/
theorem le_r_of_coprime (k N m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k)
    (hcop : ∀ d : ℕ, 0 < d → d * (k - 1) < N → Nat.Coprime d m) : N - N / m ≤ r k N := by
  classical
  have hSsub : (Finset.Icc 1 N).filter (fun x => ¬ m ∣ x) ⊆ Finset.Icc 1 N :=
    Finset.filter_subset _ _
  have hfree : APFree (((Finset.Icc 1 N).filter (fun x => ¬ m ∣ x) : Finset ℕ) : Set ℕ) k := by
    rintro ⟨a, d, hd, h⟩
    have hk : 1 ≤ k := le_trans hm hmk
    have h0 := h 0 (by omega)
    have hlast := h (k - 1) (by omega)
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at h0 hlast
    have hdk : d * (k - 1) < N := by
      have h1 := hlast.1.2
      have h2 := h0.1.1
      have h3 : d * (k - 1) = (k - 1) * d := Nat.mul_comm _ _
      omega
    have hc := hcop d hd hdk
    obtain ⟨i, hi, hdvd⟩ := exists_dvd_term a hm hc
    have hmem := h i (lt_of_lt_of_le hi hmk)
    rw [Finset.mem_coe, Finset.mem_filter] at hmem
    exact hmem.2 hdvd
  calc N - N / m = ((Finset.Icc 1 N).filter (fun x => ¬ m ∣ x)).card :=
        (card_filter_not_dvd N m).symm
    _ ≤ r k N := card_le_r hSsub hfree

/-! ### Exact formula -/

/-- **Exact formula for long progressions.** If `k ≥ 2` and `N ≤ minFac k * (k - 1)` then
`r_k(N) = N - ⌊N/k⌋`. -/
theorem r_eq_of_le_minFac (k N : ℕ) (hk : 2 ≤ k) (hN : N ≤ Nat.minFac k * (k - 1)) :
    r k N = N - N / k := by
  apply le_antisymm
  · have := r_add_div_le k N (by omega)
    omega
  · apply le_r_of_coprime k N k (by omega) le_rfl
    intro d hd hdN
    have hlt : d < Nat.minFac k := by
      by_contra hge
      push Not at hge
      have := Nat.mul_le_mul_right (k - 1) hge
      omega
    by_contra hnc
    obtain ⟨q, hq, hqd, hqk⟩ := Nat.Prime.not_coprime_iff_dvd.1 hnc
    have h1 : Nat.minFac k ≤ q := Nat.minFac_le_of_dvd hq.two_le hqk
    have h2 : q ≤ d := Nat.le_of_dvd hd hqd
    omega

/-- Prime case: for `p` prime and `N ≤ p (p - 1)`, `r_p(N) = N - ⌊N/p⌋`. -/
theorem r_prime_eq (p N : ℕ) (hp : p.Prime) (hN : N ≤ p * (p - 1)) : r p N = N - N / p :=
  r_eq_of_le_minFac p N hp.two_le (by rw [hp.minFac_eq]; exact hN)

/-- Sandwich with a prime `p ≤ k`: for `N ≤ p (k - 1)`, `N - ⌊N/p⌋ ≤ r_k(N) ≤ N - ⌊N/k⌋`. -/
theorem r_sandwich (k N p : ℕ) (hp : p.Prime) (hpk : p ≤ k) (hN : N ≤ p * (k - 1)) :
    N - N / p ≤ r k N ∧ r k N ≤ N - N / k := by
  have hp2 := hp.two_le
  refine ⟨?_, ?_⟩
  · apply le_r_of_coprime k N p (by omega) hpk
    intro d hd hdN
    have hlt : d < p := by
      by_contra hge
      push Not at hge
      have := Nat.mul_le_mul_right (k - 1) hge
      omega
    exact Nat.coprime_comm.1
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hd hlt))
  · have := r_add_div_le k N (by omega)
    omega

/-! ### The first value beyond the range -/

/-- Auxiliary form of `r_succ_range_le` with `k = q + 1`. -/
lemma r_succ_range_le_aux (q : ℕ) (hq : 1 ≤ q) : r (q + 1) ((q + 1) * q + 1) ≤ q ^ 2 := by
  classical
  apply r_le
  intro S hS hfree
  by_contra hcon
  push Not at hcon
  have hN : (q + 1) * q + 1 = q * (q + 1) + 1 := by ring
  rw [hN] at hS
  have hsq : q * (q + 1) = q ^ 2 + q := by ring
  -- in each block of `q + 1` consecutive integers, `S` misses a point
  have hex : ∀ j : ℕ, ∃ i, i < q + 1 ∧ j * (q + 1) + 1 + i * 1 ∉ S :=
    fun j => exists_not_mem_of_APFree hfree (j * (q + 1) + 1) 1 one_pos
  choose f hf using hex
  simp only [mul_one] at hf
  have hmul : ∀ j, j + 1 ≤ q → j * (q + 1) + (q + 1) ≤ q * (q + 1) := by
    intro j hj
    have h := Nat.mul_le_mul_right (q + 1) hj
    rwa [Nat.add_mul, Nat.one_mul] at h
  -- the complement has at most `q` points
  have hHcard : (Finset.Icc 1 (q * (q + 1) + 1) \ S).card ≤ q := by
    have hsd := Finset.card_sdiff_add_card_eq_card hS
    rw [Nat.card_Icc] at hsd
    omega
  have he_mem : ∀ j ∈ Finset.range q,
      j * (q + 1) + 1 + f j ∈ Finset.Icc 1 (q * (q + 1) + 1) \ S := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 := (hf j).1
    have h2 := hmul j (by omega)
    rw [Finset.mem_sdiff, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, (hf j).2⟩
  have he_inj : Set.InjOn (fun j => j * (q + 1) + 1 + f j) (Finset.range q : Set ℕ) := by
    intro j _ j' _ h
    dsimp only at h
    exact (block_unique (c := q + 1) (hf j).1 (hf j').1 (by omega)).1
  have himg : (Finset.range q).image (fun j => j * (q + 1) + 1 + f j)
      = Finset.Icc 1 (q * (q + 1) + 1) \ S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact he_mem j hj
    · rw [Finset.card_image_of_injOn he_inj, Finset.card_range]
      exact hHcard
  -- every missing point is one of the chosen ones
  have hmiss : ∀ x, 1 ≤ x → x ≤ q * (q + 1) + 1 → x ∉ S →
      ∃ j, j < q ∧ x = j * (q + 1) + 1 + f j := by
    intro x hx1 hx2 hxS
    have hxH : x ∈ Finset.Icc 1 (q * (q + 1) + 1) \ S := by
      rw [Finset.mem_sdiff, Finset.mem_Icc]
      exact ⟨⟨hx1, hx2⟩, hxS⟩
    rw [← himg, Finset.mem_image] at hxH
    obtain ⟨j, hj, hjx⟩ := hxH
    exact ⟨j, Finset.mem_range.1 hj, hjx.symm⟩
  -- the last point `N` belongs to `S`
  have hNS : q * (q + 1) + 1 ∈ S := by
    by_contra hNS
    obtain ⟨j, hj, hjx⟩ := hmiss _ (by omega) le_rfl hNS
    have h := block_unique (c := q + 1) (j := q) (j' := j) (u := 0) (u' := f j)
      (by omega) (hf j).1 (by omega)
    omega
  -- the progression `1, 1 + (q+1), …, 1 + q (q+1) = N` forces some block to miss its first point
  obtain ⟨i, hi, hiS⟩ := exists_not_mem_of_APFree hfree 1 (q + 1) (by omega)
  have hi_le : i * (q + 1) ≤ q * (q + 1) := Nat.mul_le_mul_right (q + 1) (by omega)
  obtain ⟨j0, hj0, hj0x⟩ := hmiss _ (by omega) (by omega) hiS
  have hf0 : f j0 = 0 := by
    have h := block_unique (c := q + 1) (j := i) (j' := j0) (u := 0) (u' := f j0)
      (by omega) (hf j0).1 (by omega)
    omega
  -- propagation: if block `j` misses its first point, so does block `j + 1`
  have step : ∀ j, j < q → f j = 0 → j + 1 < q ∧ f (j + 1) = 0 := by
    intro j hj hfj
    obtain ⟨t, ht, htS⟩ := exists_not_mem_of_APFree hfree (j * (q + 1) + 2) 1 one_pos
    rw [mul_one] at htS
    have h2 := hmul j (by omega)
    obtain ⟨j', hj', hx⟩ := hmiss _ (by omega) (by omega) htS
    rcases Nat.lt_or_ge t q with htq | htq
    · exfalso
      have h := block_unique (c := q + 1) (j := j) (j' := j') (u := 1 + t) (u' := f j')
        (by omega) (hf j').1 (by omega)
      obtain ⟨hjj, h3⟩ := h
      rw [← hjj] at h3
      omega
    · have h := block_unique (c := q + 1) (j := j + 1) (j' := j') (u := 0) (u' := f j')
        (by omega) (hf j').1 (by rw [Nat.add_mul, Nat.one_mul]; omega)
      obtain ⟨hjj, h3⟩ := h
      rw [← hjj] at h3 hj'
      exact ⟨hj', h3.symm⟩
  have all : ∀ n, j0 + n < q ∧ f (j0 + n) = 0 := by
    intro n
    induction n with
    | zero => exact ⟨hj0, hf0⟩
    | succ n ih => exact step (j0 + n) ih.1 ih.2
  have hfin := (all q).1
  omega

/-- First value beyond the range: `r_k(k(k-1)+1) ≤ (k-1)^2` for every `k ≥ 2`. -/
theorem r_succ_range_le (k : ℕ) (hk : 2 ≤ k) : r k (k * (k - 1) + 1) ≤ (k - 1) ^ 2 := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  have hq : 1 ≤ q := by omega
  simpa using r_succ_range_le_aux q hq

/-- ... with equality when `k = p` is prime: `r_p(p(p-1)+1) = (p-1)^2`.  In particular the formula
`N - ⌊N/p⌋` fails at `N = p(p-1)+1`. -/
theorem r_prime_succ_range (p : ℕ) (hp : p.Prime) : r p (p * (p - 1) + 1) = (p - 1) ^ 2 := by
  apply le_antisymm (r_succ_range_le p hp.two_le)
  have h1 : r p (p * (p - 1)) = p * (p - 1) - p * (p - 1) / p := r_prime_eq p _ hp le_rfl
  rw [Nat.mul_div_cancel_left _ hp.pos] at h1
  have h2 : p * (p - 1) - (p - 1) = (p - 1) ^ 2 := by
    have hp2 := hp.two_le
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [hq, Nat.add_sub_cancel]
    have h3 : (q + 1) * q = q ^ 2 + q := by ring
    omega
  calc (p - 1) ^ 2 = r p (p * (p - 1)) := by rw [h1, h2]
    _ ≤ r p (p * (p - 1) + 1) := r_mono p (Nat.le_succ _)

end Erdos142

#print axioms Erdos142.r_add_div_le
#print axioms Erdos142.le_r_of_coprime
#print axioms Erdos142.r_eq_of_le_minFac
#print axioms Erdos142.r_prime_eq
#print axioms Erdos142.r_sandwich
#print axioms Erdos142.r_succ_range_le
#print axioms Erdos142.r_prime_succ_range
