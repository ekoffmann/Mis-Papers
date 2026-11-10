import Erdos142.Exact

/-!
# The range of the exact formula is sharp for every `k`

`Erdos142.r_eq_of_le_minFac` shows `r_k(N) = N - ⌊N/k⌋` for `N ≤ q (k - 1)`, where `q` is the
least prime factor of `k`.  This file shows that the range cannot be extended by one:

* `card_ge_of_mem` : if `S ⊆ {1,…,N}` has no `k`-term progression and `x ∈ {1,…,N}` is not in
  `S`, then the complement of `S` has at least `⌊(x-1)/k⌋ + 1 + ⌊(N-x)/k⌋` points
  (disjoint blocks of `k` consecutive integers to the left and to the right of `x`);
* `r_first_fail` : `r_k(q (k - 1) + 1) = q (k - 2) + 1 = N - ⌊N/k⌋ - 1` for every `k ≥ 2`.
-/

namespace Erdos142

/-- In any interval `{a+1, …, a+M}` of `M` consecutive integers, a `k`-AP-free set misses at
least `⌊M/k⌋` points (one in each of the disjoint blocks of `k` consecutive integers). -/
lemma card_Icc_sdiff_ge {k : ℕ} {S : Finset ℕ} (hfree : APFree (S : Set ℕ) k) (a M : ℕ) :
    M / k ≤ (Finset.Icc (a + 1) (a + M) \ S).card := by
  classical
  have hex : ∀ j : ℕ, ∃ i, i < k ∧ a + 1 + j * k + i * 1 ∉ S :=
    fun j => exists_not_mem_of_APFree hfree (a + 1 + j * k) 1 one_pos
  choose f hf using hex
  simp only [mul_one] at hf
  have hinj : Set.InjOn (fun j => a + 1 + j * k + f j) (Finset.range (M / k) : Set ℕ) := by
    intro j _ j' _ h
    dsimp only at h
    exact (block_unique (c := k) (hf j).1 (hf j').1 (by omega)).1
  have hmaps : ∀ j ∈ Finset.range (M / k),
      (fun j => a + 1 + j * k + f j) j ∈ Finset.Icc (a + 1) (a + M) \ S := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 := (hf j).1
    have h2 : (j + 1) * k ≤ M / k * k := Nat.mul_le_mul_right k hj
    have h3 : M / k * k ≤ M := Nat.div_mul_le_self M k
    have h4 : (j + 1) * k = j * k + k := by ring
    rw [Finset.mem_sdiff, Finset.mem_Icc]
    exact ⟨⟨by dsimp only; omega, by dsimp only; omega⟩, (hf j).2⟩
  have hcard : (Finset.range (M / k)).card ≤ (Finset.Icc (a + 1) (a + M) \ S).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  rwa [Finset.card_range] at hcard

/-- If `S ⊆ {1,…,N}` has no `k`-term progression and `x ∈ {1,…,N}` is not in `S`, then the
complement of `S` in `{1,…,N}` has at least `⌊(x-1)/k⌋ + 1 + ⌊(N-x)/k⌋` elements (disjoint blocks
to the left and to the right of `x`, plus `x` itself). -/
theorem card_ge_of_mem (k N : ℕ) (hk : 1 ≤ k) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 N)
    (hfree : APFree (S : Set ℕ) k) (x : ℕ) (hx1 : 1 ≤ x) (hxN : x ≤ N) (hxS : x ∉ S) :
    S.card + (x - 1) / k + 1 + (N - x) / k ≤ N := by
  classical
  have _ : 0 < k := hk
  have hL : (x - 1) / k ≤ (Finset.Icc 1 (x - 1) \ S).card := by
    have h := card_Icc_sdiff_ge hfree 0 (x - 1)
    simpa only [Nat.zero_add] using h
  have hR : (N - x) / k ≤ (Finset.Icc (x + 1) N \ S).card := by
    have h := card_Icc_sdiff_ge hfree x (N - x)
    have e : x + (N - x) = N := by omega
    rwa [e] at h
  have hsub : (Finset.Icc 1 (x - 1) \ S) ∪ {x} ∪ (Finset.Icc (x + 1) N \ S)
      ⊆ Finset.Icc 1 N \ S := by
    intro y hy
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_singleton] at hy
    rw [Finset.mem_sdiff, Finset.mem_Icc]
    rcases hy with (hy | hy) | hy
    · rw [Finset.mem_sdiff, Finset.mem_Icc] at hy
      exact ⟨⟨hy.1.1, by omega⟩, hy.2⟩
    · subst hy
      exact ⟨⟨hx1, hxN⟩, hxS⟩
    · rw [Finset.mem_sdiff, Finset.mem_Icc] at hy
      exact ⟨⟨by omega, hy.1.2⟩, hy.2⟩
  have hdisj1 : Disjoint (Finset.Icc 1 (x - 1) \ S) {x} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_sdiff, Finset.mem_Icc]
    omega
  have hdisj2 : Disjoint ((Finset.Icc 1 (x - 1) \ S) ∪ {x}) (Finset.Icc (x + 1) N \ S) := by
    rw [Finset.disjoint_left]
    intro y hy hyR
    rw [Finset.mem_union, Finset.mem_singleton] at hy
    rw [Finset.mem_sdiff, Finset.mem_Icc] at hyR
    rcases hy with hy | hy
    · rw [Finset.mem_sdiff, Finset.mem_Icc] at hy
      omega
    · omega
  have hcard : ((Finset.Icc 1 (x - 1) \ S) ∪ {x} ∪ (Finset.Icc (x + 1) N \ S)).card
      = (Finset.Icc 1 (x - 1) \ S).card + 1 + (Finset.Icc (x + 1) N \ S).card := by
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
      Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  have hsd := Finset.card_sdiff_add_card_eq_card hS
  rw [Nat.card_Icc] at hsd
  omega

/-- Upper bound at the first value beyond the range, for any divisor `q ≥ 2` of `k`:
`r_k(q (k - 1) + 1) ≤ q (k - 2) + 1`. -/
lemma r_first_fail_le (k q : ℕ) (hk : 2 ≤ k) (hq2 : 2 ≤ q) (hqk : q ∣ k) :
    r k (q * (k - 1) + 1) ≤ q * (k - 2) + 1 := by
  classical
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 2 := ⟨k - 2, by omega⟩
  have hk1 : K + 2 - 1 = K + 1 := by omega
  have hk2 : K + 2 - 2 = K := by omega
  rw [hk1, hk2]
  apply r_le
  intro S hS hfree
  by_contra hcon
  have hcon' : q * K + 1 < S.card := not_le.mp hcon
  -- the progression `1, 1 + q, …, 1 + (K + 1) q = N` has a term outside `S`
  obtain ⟨i, hi, hiS⟩ := exists_not_mem_of_APFree hfree 1 q (by omega)
  have hiq : i * q ≤ (K + 1) * q := Nat.mul_le_mul_right q (by omega)
  have hcomm : (K + 1) * q = q * (K + 1) := Nat.mul_comm _ _
  have hqK : q * (K + 1) = q * K + q := by ring
  have hx1 : 1 ≤ 1 + i * q := by omega
  have hxN : 1 + i * q ≤ q * (K + 1) + 1 := by omega
  have hcg := card_ge_of_mem (K + 2) (q * (K + 1) + 1) (by omega) S hS hfree (1 + i * q)
    hx1 hxN hiS
  have hxm : 1 + i * q - 1 = i * q := by omega
  rw [hxm] at hcg
  -- quotient and remainder of `x - 1 = i q` by `k = K + 2`
  have hdm : (K + 2) * (i * q / (K + 2)) + i * q % (K + 2) = i * q :=
    Nat.div_add_mod (i * q) (K + 2)
  have hult : i * q % (K + 2) < K + 2 := Nat.mod_lt _ (by omega)
  have hqu : q ∣ i * q % (K + 2) := (Nat.dvd_mod_iff hqk).2 (Dvd.intro_left i rfl)
  obtain ⟨j, hj⟩ : ∃ j, j = i * q / (K + 2) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = i * q % (K + 2) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (q * (K + 1) + 1 - (1 + i * q)) / (K + 2) := ⟨_, rfl⟩
  rw [← hj, ← hD] at hcg
  rw [← hj] at hdm
  rw [← hu] at hdm hult hqu
  -- the complement has at most `q - 1` points
  have hsum : j + D + 2 ≤ q := by omega
  -- hence the remainder is large: `u + 1 ≥ k - q + 2`
  have hclaim : K + 3 ≤ u + q := by
    by_contra hlt
    have hlt' : u + q < K + 3 := not_le.mp hlt
    obtain ⟨t, ht⟩ : ∃ t, q = j + t + 2 := ⟨q - j - 2, by omega⟩
    have hdiv : t + 1 ≤ D := by
      rw [hD, Nat.le_div_iff_mul_le (by omega)]
      have e1 : (t + 1) * (K + 2) = t * K + 2 * t + K + 2 := by ring
      have e2 : (K + 2) * j = j * K + 2 * j := by ring
      have e3 : q * (K + 1) = j * K + t * K + 2 * K + j + t + 2 := by rw [ht]; ring
      omega
    omega
  -- but `u` is a multiple of `q` lying strictly between `k - q` and `k`, and `q ∣ k`
  obtain ⟨w, hw⟩ := hqu
  obtain ⟨m, hm⟩ := hqk
  have hwm : w < m := by
    apply Nat.lt_of_mul_lt_mul_left (a := q)
    rw [← hw, ← hm]
    exact hult
  have h5 : q * (w + 1) ≤ q * m := Nat.mul_le_mul_left q hwm
  have h6 : q * (w + 1) = q * w + q := by ring
  omega

/-- Arithmetic behind the lower bound: `⌊q (k - 1) / k⌋ = q - 1` and
`q (k - 1) - (q - 1) = q (k - 2) + 1` for `1 ≤ q ≤ k`, `k ≥ 2`. -/
lemma first_fail_arith (k q : ℕ) (hk : 2 ≤ k) (hq : 1 ≤ q) (hqk : q ≤ k) :
    q * (k - 1) / k = q - 1 ∧ q * (k - 1) - (q - 1) = q * (k - 2) + 1 := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 2 := ⟨k - 2, by omega⟩
  obtain ⟨Q, rfl⟩ : ∃ Q, q = Q + 1 := ⟨q - 1, by omega⟩
  have hk1 : K + 2 - 1 = K + 1 := by omega
  have hk2 : K + 2 - 2 = K := by omega
  have hq1 : Q + 1 - 1 = Q := by omega
  rw [hk1, hk2, hq1]
  have a1 : Q * (K + 2) = Q * K + 2 * Q := by ring
  have a2 : (Q + 1) * (K + 1) = Q * K + Q + K + 1 := by ring
  have a3 : (Q + 1) * (K + 2) = Q * K + 2 * Q + K + 2 := by ring
  have a4 : (Q + 1) * K = Q * K + K := by ring
  constructor
  · apply Nat.div_eq_of_lt_le
    · omega
    · omega
  · omega

/-- **The range of the exact formula is sharp for every `k ≥ 2`.**  With `q` the least prime
factor of `k` and `N = q (k - 1) + 1`, one has `r_k(N) = q (k - 2) + 1 = N - ⌊N/k⌋ - 1`. -/
theorem r_first_fail (k : ℕ) (hk : 2 ≤ k) :
    r k (Nat.minFac k * (k - 1) + 1) = Nat.minFac k * (k - 2) + 1 := by
  have hq : (Nat.minFac k).Prime := Nat.minFac_prime (by omega)
  have hqdvd : Nat.minFac k ∣ k := Nat.minFac_dvd k
  have hqle : Nat.minFac k ≤ k := Nat.minFac_le (by omega)
  apply le_antisymm (r_first_fail_le k (Nat.minFac k) hk hq.two_le hqdvd)
  have h1 : r k (Nat.minFac k * (k - 1))
      = Nat.minFac k * (k - 1) - Nat.minFac k * (k - 1) / k :=
    r_eq_of_le_minFac k _ hk le_rfl
  obtain ⟨h2, h3⟩ := first_fail_arith k (Nat.minFac k) hk hq.one_lt.le hqle
  calc Nat.minFac k * (k - 2) + 1 = r k (Nat.minFac k * (k - 1)) := by rw [h1, h2, h3]
    _ ≤ r k (Nat.minFac k * (k - 1) + 1) := r_mono k (Nat.le_succ _)

end Erdos142

#print axioms Erdos142.card_ge_of_mem
#print axioms Erdos142.r_first_fail
