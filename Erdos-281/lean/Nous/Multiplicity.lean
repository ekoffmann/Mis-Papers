import Nous.Erdos281

/-!
# Erdős Problem 281 with multiplicity

Under the uniform covering property (C) of Problem 281 and `n 0 ≥ 2`, for every `r` almost every
natural number satisfies at least `r` of the congruences, uniformly in the choice of residues.

Route:
* `sum_remove_class` / `exists_remove_class`: averaging over the residue of ONE modulus `q`:
  `∑_{r<q} #(S minus the class r mod q) = (q - 1) · #S`, so some class removes at most a
  fraction `1/q` of `S`.
* `lift_tail`: iterating over the moduli `n 0, …, n (j-1)`, every tail set
  `Tail n a j k` (no congruence with index in `[j,k)` satisfied) contains, up to the factor
  `∏_{i<j} (1 - 1/n i)`, a full uncovered set `Unc n a' k`.
* `tail_uniform`: tails inherit (C).
* `mult_general` / `erdos_281_multiplicity`: block + pigeonhole argument, by induction on `r`.
-/

open Filter Topology

namespace Erdos281

/-- `mult n a k m` = number of indices `i < k` with `m ≡ a i (mod n i)`. -/
def mult (n a : ℕ → ℕ) (k m : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => m ≡ a i [MOD n i])).card

/-! ## Auxiliary definitions and density facts -/

/-- Tail set: naturals satisfying none of the congruences with index in `[j, k)`. -/
def Tail (n a : ℕ → ℕ) (j k : ℕ) : Set ℕ := {m | ∀ i, j ≤ i → i < k → ¬ m ≡ a i [MOD n i]}

/-- Number of indices `i ∈ [j, k)` with `m ≡ a i (mod n i)`. -/
def multFrom (n a : ℕ → ℕ) (j k m : ℕ) : ℕ :=
  ((Finset.Ico j k).filter (fun i => m ≡ a i [MOD n i])).card

lemma mult_eq_multFrom (n a : ℕ → ℕ) (k m : ℕ) : mult n a k m = multFrom n a 0 k m := by
  unfold mult multFrom
  rw [Finset.range_eq_Ico]

/-- A set with a density which is periodic has density (count per period)/(period). -/
lemma dens_per_eq {S : Set ℕ} {p : ℕ} (hp : 0 < p) (hper : PerSet S p) {d : ℝ}
    (h : HasNatDensity S d) : d = (W S 0 p : ℝ) / p := by
  have h' := density_of_periodic hp hper
  unfold HasNatDensity at h h'
  exact tendsto_nhds_unique h h'

lemma hasNatDensity_empty : HasNatDensity (∅ : Set ℕ) 0 := by
  unfold HasNatDensity
  simp

lemma W_le_of_subset_union {A B C : Set ℕ} (h : A ⊆ B ∪ C) (s L : ℕ) :
    W A s L ≤ W B s L + W C s L := by
  classical
  unfold W
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hA : x + s ∈ A
  · rcases h hA with hB | hC
    · simp [hA, hB]
    · simp [hA, hC]
  · simp [hA]

/-- If `A ⊆ B ∪ C`, all three periodic with a common period, then `A` has a density which is at
most the sum of the densities of `B` and `C`. -/
lemma dens_union_bound {A B C : Set ℕ} {p : ℕ} (hp : 0 < p) (hA : PerSet A p) (hB : PerSet B p)
    (hC : PerSet C p) (h : A ⊆ B ∪ C) {dB dC : ℝ} (hdB : HasNatDensity B dB)
    (hdC : HasNatDensity C dC) : ∃ d : ℝ, d ≤ dB + dC ∧ HasNatDensity A d := by
  refine ⟨(W A 0 p : ℝ) / p, ?_, density_of_periodic hp hA⟩
  have eB := dens_per_eq hp hB hdB
  have eC := dens_per_eq hp hC hdC
  have hW : (W A 0 p : ℝ) ≤ (W B 0 p : ℝ) + (W C 0 p : ℝ) := by
    exact_mod_cast W_le_of_subset_union h 0 p
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  rw [eB, eC, ← add_div]
  exact div_le_div_of_nonneg_right hW hpr.le

/-- If `S` is contained in sets of arbitrarily small density, then `S` has density `0`. -/
lemma density_zero_of_subsets {S : Set ℕ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ T : Set ℕ, S ⊆ T ∧ ∃ d : ℝ, d < ε ∧ HasNatDensity T d) :
    HasNatDensity S 0 := by
  unfold HasNatDensity
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hST, d, hd, hdens⟩ := h ε hε
  unfold HasNatDensity at hdens
  have hev : ∀ᶠ N : ℕ in atTop, ((T ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) < ε :=
    (tendsto_order.1 hdens).2 ε hd
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  refine ⟨N₁, fun N hN => ?_⟩
  have h1 := hN₁ N hN
  have hsub : (S ∩ Set.Iio N).ncard ≤ (T ∩ Set.Iio N).ncard :=
    Set.ncard_le_ncard (Set.inter_subset_inter_left _ hST)
      ((Set.finite_Iio N).inter_of_right _)
  have h2 : ((S ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) ≤ ((T ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hsub) (Nat.cast_nonneg N)
  have h3 : 0 ≤ ((S ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h3]
  linarith

/-! ## Periodicity -/

lemma modEq_add_P (n : ℕ → ℕ) {i k : ℕ} (h : i < k) (m c : ℕ) :
    m + P n k ≡ c [MOD n i] ↔ m ≡ c [MOD n i] := by
  have h1 : m + P n k ≡ m [MOD n i] := by
    simpa using (Nat.modEq_zero_iff_dvd.2 (n_dvd_P n h)).add_left m
  exact ⟨fun hc => h1.symm.trans hc, fun hc => h1.trans hc⟩

lemma tail_per (n a : ℕ → ℕ) (j : ℕ) {k k' : ℕ} (h : k ≤ k') :
    PerSet (Tail n a j k) (P n k') := by
  intro m
  constructor
  · intro hm i hji hik hc
    exact hm i hji hik ((modEq_add_P n (lt_of_lt_of_le hik h) m (a i)).2 hc)
  · intro hm i hji hik hc
    exact hm i hji hik ((modEq_add_P n (lt_of_lt_of_le hik h) m (a i)).1 hc)

lemma multFrom_per (n a : ℕ → ℕ) (j : ℕ) {k k' : ℕ} (h : k ≤ k') (m : ℕ) :
    multFrom n a j k (m + P n k') = multFrom n a j k m := by
  unfold multFrom
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro i hi
  exact modEq_add_P n (lt_of_lt_of_le (Finset.mem_Ico.1 hi).2 h) m (a i)

lemma multLt_per (n a : ℕ → ℕ) (j : ℕ) {k k' : ℕ} (h : k ≤ k') (r : ℕ) :
    PerSet {m : ℕ | multFrom n a j k m < r} (P n k') := by
  intro m
  change multFrom n a j k (m + P n k') < r ↔ multFrom n a j k m < r
  rw [multFrom_per n a j h m]

lemma multFrom_split (n a : ℕ → ℕ) {j k₁ k₂ : ℕ} (h1 : j ≤ k₁) (h2 : k₁ ≤ k₂) (m : ℕ) :
    multFrom n a j k₂ m = multFrom n a j k₁ m + multFrom n a k₁ k₂ m := by
  unfold multFrom
  simp only [Finset.card_filter]
  exact (Finset.sum_Ico_consecutive _ h1 h2).symm

lemma one_le_multFrom_of_not_mem_tail (n a : ℕ → ℕ) {k₁ k₂ m : ℕ} (h : m ∉ Tail n a k₁ k₂) :
    1 ≤ multFrom n a k₁ k₂ m := by
  have h' : ¬ ∀ i, k₁ ≤ i → i < k₂ → ¬ m ≡ a i [MOD n i] := h
  push Not at h'
  obtain ⟨i, hi1, hi2, hi3⟩ := h'
  unfold multFrom
  exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hi1, hi2⟩, hi3⟩⟩

/-! ## Averaging over the residue of one modulus -/

/-- `∑_{r<q} #{x < L : x ∈ S, x ≢ r (mod q)} = (q - 1) · #{x < L : x ∈ S}`. -/
lemma sum_remove_class (S : Set ℕ) (q : ℕ) (hq : 0 < q) (L : ℕ) :
    ∑ r ∈ Finset.range q, W {m | m ∈ S ∧ ¬ m ≡ r [MOD q]} 0 L = (q - 1) * W S 0 L := by
  classical
  unfold W
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  generalize x + 0 = y
  by_cases hy : y ∈ S
  · -- exactly one residue `r < q` (namely `y % q`) has `y ≡ r (mod q)`
    have hr0 : y % q ∈ Finset.range q := Finset.mem_range.2 (Nat.mod_lt y hq)
    rw [ite_eq_left hy, mul_one, ← Finset.add_sum_erase _ _ hr0]
    rw [ite_eq_right (fun h : y ∈ {m | m ∈ S ∧ ¬ m ≡ y % q [MOD q]} =>
      h.2 (Nat.mod_modEq y q).symm), zero_add]
    have hone : ∀ r ∈ (Finset.range q).erase (y % q),
        y ∈ {m | m ∈ S ∧ ¬ m ≡ r [MOD q]} := by
      intro r hr
      refine ⟨hy, fun hc => (Finset.mem_erase.1 hr).1 ?_⟩
      have h1 : y % q = r % q := hc
      rw [h1, Nat.mod_eq_of_lt (Finset.mem_range.1 (Finset.mem_erase.1 hr).2)]
    have hsum1 : ∀ r ∈ (Finset.range q).erase (y % q),
        @ite ℕ (y ∈ {m | m ∈ S ∧ ¬ m ≡ r [MOD q]}) (Classical.propDecidable _) 1 0 = 1 :=
      fun r hr => ite_eq_left (hone r hr)
    rw [Finset.sum_congr rfl hsum1, Finset.sum_const, Finset.card_erase_of_mem hr0,
      Finset.card_range, smul_eq_mul, mul_one]
  · rw [ite_eq_right hy, mul_zero]
    exact Finset.sum_eq_zero (fun r _ => ite_eq_right (fun h => hy h.1))

/-- Pigeonhole: some residue class mod `q` removes at most a fraction `1/q` of `S ∩ [0,L)`. -/
lemma exists_remove_class (S : Set ℕ) (q : ℕ) (hq : 0 < q) (L : ℕ) :
    ∃ r, (q - 1) * W S 0 L ≤ q * W {m | m ∈ S ∧ ¬ m ≡ r [MOD q]} 0 L := by
  have hsum := sum_remove_class S q hq L
  have hne : (Finset.range q).Nonempty := ⟨0, Finset.mem_range.2 hq⟩
  have h : ∑ _r ∈ Finset.range q, (q - 1) * W S 0 L
      ≤ ∑ r ∈ Finset.range q, q * W {m | m ∈ S ∧ ¬ m ≡ r [MOD q]} 0 L := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum, hsum]
  obtain ⟨r, _, hr⟩ := Finset.exists_le_of_sum_le hne h
  exact ⟨r, hr⟩

/-- Lifting a tail set to a full uncovered set: for every choice `a` there is a choice `a'` with
`#(Tail n a j k ∩ [0,L)) · ∏_{i<j} (n i - 1) ≤ #(Unc n a' k ∩ [0,L)) · ∏_{i<j} n i`. -/
lemma lift_tail (n : ℕ → ℕ) (hpos : ∀ i, 0 < n i) (k L : ℕ) :
    ∀ j : ℕ, ∀ a : ℕ → ℕ, ∃ a' : ℕ → ℕ,
      W (Tail n a j k) 0 L * ∏ i ∈ Finset.range j, (n i - 1)
        ≤ W (Unc n a' k) 0 L * ∏ i ∈ Finset.range j, n i := by
  intro j
  induction j with
  | zero =>
    intro a
    refine ⟨a, ?_⟩
    simp only [Finset.range_zero, Finset.prod_empty, mul_one]
    have hsub0 : Tail n a 0 k ⊆ Unc n a k := fun m hm i hi => hm i (Nat.zero_le i) hi
    exact W_mono hsub0 0 L
  | succ j ih =>
    intro a
    obtain ⟨r, hr⟩ := exists_remove_class (Tail n a (j + 1) k) (n j) (hpos j) L
    obtain ⟨a', ha'⟩ := ih (Function.update a j r)
    refine ⟨a', ?_⟩
    have hsub : {m | m ∈ Tail n a (j + 1) k ∧ ¬ m ≡ r [MOD n j]}
        ⊆ Tail n (Function.update a j r) j k := by
      intro m hm i hji hik
      rcases Nat.eq_or_lt_of_le hji with h | h
      · subst h
        rw [Function.update_self]
        exact hm.2
      · rw [Function.update_of_ne (Nat.ne_of_gt h)]
        exact hm.1 i h hik
    have h1 := W_mono hsub 0 L
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    calc W (Tail n a (j + 1) k) 0 L * ((∏ i ∈ Finset.range j, (n i - 1)) * (n j - 1))
        = ((n j - 1) * W (Tail n a (j + 1) k) 0 L) * ∏ i ∈ Finset.range j, (n i - 1) := by ring
      _ ≤ (n j * W {m | m ∈ Tail n a (j + 1) k ∧ ¬ m ≡ r [MOD n j]} 0 L)
            * ∏ i ∈ Finset.range j, (n i - 1) := Nat.mul_le_mul_right _ hr
      _ ≤ (n j * W (Tail n (Function.update a j r) j k) 0 L)
            * ∏ i ∈ Finset.range j, (n i - 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      _ = n j * (W (Tail n (Function.update a j r) j k) 0 L
            * ∏ i ∈ Finset.range j, (n i - 1)) := by ring
      _ ≤ n j * (W (Unc n a' k) 0 L * ∏ i ∈ Finset.range j, n i) := Nat.mul_le_mul_left _ ha'
      _ = W (Unc n a' k) 0 L * ((∏ i ∈ Finset.range j, n i) * n j) := by ring

/-! ## Main theorems -/

/-- Tails inherit the uniform covering property: for every `j` and `ε` there is `k > j` such that
for every choice of residues, the set of naturals satisfying none of the congruences with
`j ≤ i < k` has density `< ε`. -/
theorem tail_uniform (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 2 ≤ n 0)
    (C : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d) :
    ∀ j : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, j < k ∧ ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧
      HasNatDensity {m : ℕ | ∀ i, j ≤ i → i < k → ¬ m ≡ a i [MOD n i]} d := by
  intro j ε hε
  have h2 : ∀ i, 2 ≤ n i := fun i => hn0.trans (hn.monotone (Nat.zero_le i))
  have hpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (by norm_num) (h2 i)
  have hApos : 0 < ∏ i ∈ Finset.range j, n i := Finset.prod_pos (fun i _ => hpos i)
  have hBpos : 0 < ∏ i ∈ Finset.range j, (n i - 1) :=
    Finset.prod_pos (fun i _ => by have := h2 i; omega)
  have hAr : (0 : ℝ) < ((∏ i ∈ Finset.range j, n i : ℕ) : ℝ) := by exact_mod_cast hApos
  have hBr : (0 : ℝ) < ((∏ i ∈ Finset.range j, (n i - 1) : ℕ) : ℝ) := by exact_mod_cast hBpos
  obtain ⟨k₀, hk₀⟩ := C (ε * (((∏ i ∈ Finset.range j, (n i - 1) : ℕ) : ℝ)
    / ((∏ i ∈ Finset.range j, n i : ℕ) : ℝ))) (by positivity)
  refine ⟨max k₀ (j + 1), lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _), fun a => ?_⟩
  have hPk : 0 < P n (max k₀ (j + 1)) := P_pos hpos _
  have hPr : (0 : ℝ) < (P n (max k₀ (j + 1)) : ℝ) := by exact_mod_cast hPk
  -- uniform bound at the level `max k₀ (j+1)`
  have hbound : ∀ a' : ℕ → ℕ, (cU n a' (max k₀ (j + 1)) : ℝ) / P n (max k₀ (j + 1))
      < ε * (((∏ i ∈ Finset.range j, (n i - 1) : ℕ) : ℝ)
        / ((∏ i ∈ Finset.range j, n i : ℕ) : ℝ)) := by
    intro a'
    obtain ⟨d, hd, hdens⟩ := hk₀ a'
    have hd_eq : d = (cU n a' k₀ : ℝ) / P n k₀ :=
      dens_per_eq (P_pos hpos k₀) (unc_per n a' le_rfl) hdens
    calc (cU n a' (max k₀ (j + 1)) : ℝ) / P n (max k₀ (j + 1))
        ≤ (cU n a' k₀ : ℝ) / P n k₀ := rho_anti hpos a' (le_max_left _ _)
      _ = d := hd_eq.symm
      _ < _ := hd
  have hper : PerSet (Tail n a j (max k₀ (j + 1))) (P n (max k₀ (j + 1))) :=
    tail_per n a j le_rfl
  refine ⟨(W (Tail n a j (max k₀ (j + 1))) 0 (P n (max k₀ (j + 1))) : ℝ)
    / P n (max k₀ (j + 1)), ?_, density_of_periodic hPk hper⟩
  obtain ⟨a', ha'⟩ := lift_tail n hpos (max k₀ (j + 1)) (P n (max k₀ (j + 1))) j a
  have h1 := hbound a'
  rw [div_lt_iff₀ hPr] at h1 ⊢
  have h3 : (W (Tail n a j (max k₀ (j + 1))) 0 (P n (max k₀ (j + 1))) : ℝ)
      * ((∏ i ∈ Finset.range j, (n i - 1) : ℕ) : ℝ)
      ≤ (cU n a' (max k₀ (j + 1)) : ℝ) * ((∏ i ∈ Finset.range j, n i : ℕ) : ℝ) := by
    have h3' : W (Tail n a j (max k₀ (j + 1))) 0 (P n (max k₀ (j + 1)))
        * ∏ i ∈ Finset.range j, (n i - 1)
        ≤ cU n a' (max k₀ (j + 1)) * ∏ i ∈ Finset.range j, n i := ha'
    exact_mod_cast h3'
  have h4 : (cU n a' (max k₀ (j + 1)) : ℝ) * ((∏ i ∈ Finset.range j, n i : ℕ) : ℝ)
      < ε * (((∏ i ∈ Finset.range j, (n i - 1) : ℕ) : ℝ)
        / ((∏ i ∈ Finset.range j, n i : ℕ) : ℝ)) * P n (max k₀ (j + 1))
        * ((∏ i ∈ Finset.range j, n i : ℕ) : ℝ) := mul_lt_mul_of_pos_right h1 hAr
  have h5 : ε * (((∏ i ∈ Finset.range j, (n i - 1) : ℕ) : ℝ)
        / ((∏ i ∈ Finset.range j, n i : ℕ) : ℝ)) * P n (max k₀ (j + 1))
        * ((∏ i ∈ Finset.range j, n i : ℕ) : ℝ)
      = ε * P n (max k₀ (j + 1)) * ((∏ i ∈ Finset.range j, (n i - 1) : ℕ) : ℝ) := by
    field_simp
  have h6 : (W (Tail n a j (max k₀ (j + 1))) 0 (P n (max k₀ (j + 1))) : ℝ)
      * ((∏ i ∈ Finset.range j, (n i - 1) : ℕ) : ℝ)
      < ε * P n (max k₀ (j + 1)) * ((∏ i ∈ Finset.range j, (n i - 1) : ℕ) : ℝ) := by
    linarith
  exact lt_of_mul_lt_mul_right h6 hBr.le

/-- General block statement, by induction on `r`: for every starting index `j` there is `k ≥ j`
such that, for every choice, all but density `< ε` of the naturals satisfy at least `r` of the
congruences with index in `[j, k)`. -/
lemma mult_general (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 2 ≤ n 0)
    (C : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d) :
    ∀ r : ℕ, ∀ j : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, j ≤ k ∧ ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧
      HasNatDensity {m : ℕ | multFrom n a j k m < r} d := by
  have h2 : ∀ i, 2 ≤ n i := fun i => hn0.trans (hn.monotone (Nat.zero_le i))
  have hpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (by norm_num) (h2 i)
  intro r
  induction r with
  | zero =>
    intro j ε hε
    refine ⟨j, le_rfl, fun a => ⟨0, hε, ?_⟩⟩
    have hempty : {m : ℕ | multFrom n a j j m < 0} = ∅ := by
      ext m
      constructor
      · intro h
        exact absurd h (Nat.not_lt_zero _)
      · intro h
        exact absurd h (Set.notMem_empty m)
    rw [hempty]
    exact hasNatDensity_empty
  | succ r ih =>
    intro j ε hε
    obtain ⟨k₁, hjk₁, h₁⟩ := ih j (ε / 2) (by positivity)
    obtain ⟨k₂, hk₁₂, h₂⟩ := tail_uniform n hn hn0 C k₁ (ε / 2) (by positivity)
    refine ⟨k₂, hjk₁.trans hk₁₂.le, fun a => ?_⟩
    obtain ⟨d₁, hd₁, hdens₁⟩ := h₁ a
    obtain ⟨d₂, hd₂, hdens₂⟩ := h₂ a
    have hp : 0 < P n k₂ := P_pos hpos k₂
    have hsub : {m : ℕ | multFrom n a j k₂ m < r + 1}
        ⊆ {m : ℕ | multFrom n a j k₁ m < r} ∪ Tail n a k₁ k₂ := by
      intro m hm
      by_contra hcon
      have hm' : multFrom n a j k₂ m < r + 1 := hm
      have hnot1 : ¬ multFrom n a j k₁ m < r := fun h => hcon (Or.inl h)
      have hnot2 : m ∉ Tail n a k₁ k₂ := fun h => hcon (Or.inr h)
      have h3 := one_le_multFrom_of_not_mem_tail n a hnot2
      have h4 := multFrom_split n a hjk₁ hk₁₂.le m
      omega
    obtain ⟨d, hd, hdens⟩ := dens_union_bound hp (multLt_per n a j le_rfl (r + 1))
      (multLt_per n a j hk₁₂.le r) (tail_per n a k₁ le_rfl) hsub hdens₁ hdens₂
    exact ⟨d, by linarith, hdens⟩

/-- Multiplicity version of Problem 281: under the uniform covering property (C) and `n 0 ≥ 2`,
for every `r`, all but density `< ε` of the naturals satisfy at least `r` of the first `k`
congruences, uniformly in the choice of residues. -/
theorem erdos_281_multiplicity (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 2 ≤ n 0)
    (C : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d) :
    ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧
      HasNatDensity {m : ℕ | mult n a k m < r} d := by
  intro r ε hε
  obtain ⟨k, _, hk⟩ := mult_general n hn hn0 C r 0 ε hε
  refine ⟨k, fun a => ?_⟩
  obtain ⟨d, hd, hdens⟩ := hk a
  refine ⟨d, hd, ?_⟩
  have e : {m : ℕ | mult n a k m < r} = {m : ℕ | multFrom n a 0 k m < r} := by
    simp only [mult_eq_multFrom]
  rw [e]
  exact hdens

/-- Same conclusion from the original hypothesis (H) of Problem 281. -/
theorem erdos_281_multiplicity_of_hyp (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 2 ≤ n 0)
    (H : ∀ a : ℕ → ℕ, HasNatDensity (UncInf n a) 0) :
    ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧
      HasNatDensity {m : ℕ | mult n a k m < r} d :=
  erdos_281_multiplicity n hn hn0 (erdos_281 n hn (lt_of_lt_of_le (by norm_num) hn0) H)

/-- Infinite form: for every choice and every `r`, the set of naturals satisfying fewer than `r`
of ALL the congruences has natural density `0`. -/
theorem few_congruences_density_zero (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 2 ≤ n 0)
    (H : ∀ a : ℕ → ℕ, HasNatDensity (UncInf n a) 0) (a : ℕ → ℕ) (r : ℕ) :
    HasNatDensity {m : ℕ | ∀ k, mult n a k m < r} 0 := by
  apply density_zero_of_subsets
  intro ε hε
  obtain ⟨k, hk⟩ := erdos_281_multiplicity_of_hyp n hn hn0 H r ε hε
  obtain ⟨d, hd, hdens⟩ := hk a
  exact ⟨{m : ℕ | mult n a k m < r}, fun m hm => hm k, d, hd, hdens⟩

end Erdos281

#print axioms Erdos281.tail_uniform
#print axioms Erdos281.erdos_281_multiplicity
#print axioms Erdos281.erdos_281_multiplicity_of_hyp
#print axioms Erdos281.few_congruences_density_zero
