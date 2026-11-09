import Mathlib

/-!
# Erdős Problem 281 — a finitary proof

Let `n 0 < n 1 < ⋯` be positive integers such that for every choice of residues `a i (mod n i)`
the set of naturals satisfying none of the congruences `m ≡ a i (mod n i)` has natural density `0`.
Then for every `ε > 0` there is `k` such that for every choice of residues the set of naturals
satisfying none of the first `k` congruences has density `< ε`.

The proof is finitary: König's lemma (twice), double counting, Markov's inequality and
full-period windows.  No ergodic theory, no Davenport–Erdős, no Rogers.
-/

open Filter Topology

namespace Erdos281

/-- `S ⊆ ℕ` has natural density `d`:  #(S ∩ [0,N)) / N → d. -/
def HasNatDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ((S ∩ Set.Iio N).ncard : ℝ) / (N : ℝ)) atTop (𝓝 d)

/-- naturals satisfying none of the first `k` congruences `m ≡ a i (mod n i)`, `i < k`. -/
def Unc (n a : ℕ → ℕ) (k : ℕ) : Set ℕ := {m | ∀ i, i < k → ¬ m ≡ a i [MOD n i]}

/-- naturals satisfying none of the congruences `m ≡ a i (mod n i)`. -/
def UncInf (n a : ℕ → ℕ) : Set ℕ := {m | ∀ i, ¬ m ≡ a i [MOD n i]}

/-! ## Window counts -/

section Counting

open Classical in
/-- `W S s L` is the number of `x < L` with `x + s ∈ S` (points of `S` in the window `[s, s+L)`). -/
noncomputable def W (S : Set ℕ) (s L : ℕ) : ℕ :=
  ∑ x ∈ Finset.range L, if x + s ∈ S then 1 else 0

lemma W_mono {S T : Set ℕ} (h : S ⊆ T) (s L : ℕ) : W S s L ≤ W T s L := by
  classical
  unfold W
  apply Finset.sum_le_sum
  intro x _
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h h1) h2
  · exact Nat.zero_le _
  · exact le_rfl

lemma W_le (S : Set ℕ) (s L : ℕ) : W S s L ≤ L := by
  classical
  unfold W
  calc ∑ x ∈ Finset.range L, (if x + s ∈ S then 1 else 0)
      ≤ ∑ x ∈ Finset.range L, 1 :=
        Finset.sum_le_sum (fun x _ => by split_ifs <;> simp)
    _ = L := by simp

lemma W_diff {S T : Set ℕ} (h : T ⊆ S) (s L : ℕ) : W (S \ T) s L + W T s L = W S s L := by
  classical
  unfold W
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hT : x + s ∈ T
  · have hS : x + s ∈ S := h hT
    simp [hT, hS]
  · by_cases hS : x + s ∈ S <;> simp [hT, hS]

/-- `S` is periodic with period `p`. -/
def PerSet (S : Set ℕ) (p : ℕ) : Prop := ∀ m, m + p ∈ S ↔ m ∈ S

lemma W_succ_shift {S : Set ℕ} {p : ℕ} (hper : PerSet S p) (s : ℕ) :
    W S (s + 1) p = W S s p := by
  classical
  unfold W
  have h1 := Finset.sum_range_succ (fun x => if x + s ∈ S then 1 else 0) p
  have h2 := Finset.sum_range_succ' (fun x => if x + s ∈ S then 1 else 0) p
  have h3 : (if p + s ∈ S then 1 else 0 : ℕ) = if 0 + s ∈ S then 1 else 0 := by
    have : p + s ∈ S ↔ 0 + s ∈ S := by
      rw [add_comm p s, zero_add]; exact hper s
    simp only [this]
  have h4 : ∀ x, (x + 1) + s = x + (s + 1) := fun x => by ring
  simp only [h4] at h2
  rw [h1, h3] at h2
  exact Nat.add_right_cancel h2.symm

lemma W_per {S : Set ℕ} {p : ℕ} (hper : PerSet S p) (s : ℕ) : W S s p = W S 0 p := by
  induction s with
  | zero => rfl
  | succ s ih => rw [W_succ_shift hper, ih]

lemma per_mul {S : Set ℕ} {p : ℕ} (hper : PerSet S p) (q m : ℕ) : m + q * p ∈ S ↔ m ∈ S := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : m + (q + 1) * p = (m + q * p) + p := by ring
    rw [this, hper, ih]

lemma cnt_add_period {S : Set ℕ} {p : ℕ} (hper : PerSet S p) (q r : ℕ) :
    W S 0 (q * p + r) = q * W S 0 p + W S 0 r := by
  classical
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : (q + 1) * p + r = p + (q * p + r) := by ring
    rw [h1]
    unfold W at *
    rw [Finset.sum_range_add]
    have h2 : ∀ x, (p + x) + 0 ∈ S ↔ x + 0 ∈ S := fun x => by
      rw [add_zero, add_zero, add_comm]; exact hper x
    simp only [h2]
    rw [ih]; ring

lemma ncard_inter_Iio (S : Set ℕ) (N : ℕ) : (S ∩ Set.Iio N).ncard = W S 0 N := by
  classical
  have h : S ∩ Set.Iio N = ↑((Finset.range N).filter (fun x => x ∈ S)) := by
    ext m; simp [and_comm]
  rw [h, Set.ncard_coe_finset, Finset.card_filter]
  unfold W
  simp

lemma sum_windows {S : Set ℕ} {p : ℕ} (hper : PerSet S p) (L : ℕ) :
    ∑ t ∈ Finset.range p, W S t L = L * W S 0 p := by
  classical
  calc ∑ t ∈ Finset.range p, W S t L
      = ∑ t ∈ Finset.range p, ∑ x ∈ Finset.range L, (if x + t ∈ S then 1 else 0) := rfl
    _ = ∑ x ∈ Finset.range L, ∑ t ∈ Finset.range p, (if x + t ∈ S then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ x ∈ Finset.range L, W S x p := by
        apply Finset.sum_congr rfl
        intro x _
        unfold W
        apply Finset.sum_congr rfl
        intro t _
        rw [add_comm]
    _ = ∑ x ∈ Finset.range L, W S 0 p := by
        apply Finset.sum_congr rfl
        intro x _
        exact W_per hper x
    _ = L * W S 0 p := by simp

/-- Double counting + Markov: for a `p`-periodic set `S`, the number of shifts `t < p` whose
window `[t, t+L)` contains more than `lam * L` points of `S` is at most `#(S ∩ [0,p)) / lam`. -/
lemma markov_shifts {S : Set ℕ} {p : ℕ} (hper : PerSet S p) (L : ℕ) (hL : 0 < L) (lam : ℝ) :
    (((Finset.range p).filter (fun t => lam * (L : ℝ) < (W S t L : ℝ))).card : ℝ) * lam
      ≤ (W S 0 p : ℝ) := by
  classical
  set B := (Finset.range p).filter (fun t => lam * (L : ℝ) < (W S t L : ℝ)) with hB
  have hsum : ∑ t ∈ Finset.range p, W S t L = L * W S 0 p := sum_windows hper L
  have h1 : (B.card : ℝ) * (lam * L) ≤ ∑ t ∈ B, (W S t L : ℝ) := by
    rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro t ht
    exact (Finset.mem_filter.1 ht).2.le
  have h2 : ∑ t ∈ B, (W S t L : ℝ) ≤ ∑ t ∈ Finset.range p, (W S t L : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.cast_nonneg _)
  have h3 : ∑ t ∈ Finset.range p, (W S t L : ℝ) = (L : ℝ) * (W S 0 p : ℝ) := by
    exact_mod_cast hsum
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have h4 : (B.card : ℝ) * lam * L ≤ (W S 0 p : ℝ) * L := by
    calc (B.card : ℝ) * lam * L = (B.card : ℝ) * (lam * L) := by ring
      _ ≤ ∑ t ∈ Finset.range p, (W S t L : ℝ) := h1.trans h2
      _ = (W S 0 p : ℝ) * L := by rw [h3]; ring
  exact le_of_mul_le_mul_right h4 hLr

/-- A periodic set has a natural density, namely (count in one period) / (period). -/
lemma density_of_periodic {S : Set ℕ} {p : ℕ} (hp : 0 < p) (hper : PerSet S p) :
    HasNatDensity S ((W S 0 p : ℝ) / p) := by
  unfold HasNatDensity
  simp only [ncard_inter_Iio]
  have hc : W S 0 p ≤ p := W_le _ _ _
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have main : ∀ N : ℕ, 0 < N →
      (W S 0 p : ℝ) / p - p / N ≤ (W S 0 N : ℝ) / N ∧
      (W S 0 N : ℝ) / N ≤ (W S 0 p : ℝ) / p + p / N := by
    intro N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hdecomp : W S 0 N = (N / p) * W S 0 p + W S 0 (N % p) := by
      have := cnt_add_period hper (N / p) (N % p)
      rwa [Nat.div_add_mod'] at this
    have hNd : N = (N / p) * p + N % p := (Nat.div_add_mod' N p).symm
    have hr : N % p < p := Nat.mod_lt _ hp
    have hwr : W S 0 (N % p) ≤ N % p := W_le _ _ _
    have hcr : W S 0 p * (N % p) ≤ p * p := Nat.mul_le_mul hc hr.le
    have hwp : p * W S 0 (N % p) ≤ p * p := Nat.mul_le_mul_left p (hwr.trans hr.le)
    have e1 : W S 0 p * N ≤ (W S 0 N + p) * p := by
      calc W S 0 p * N = W S 0 p * ((N / p) * p + N % p) := by rw [← hNd]
        _ = (N / p) * W S 0 p * p + W S 0 p * (N % p) := by ring
        _ ≤ (N / p) * W S 0 p * p + p * p := Nat.add_le_add_left hcr _
        _ ≤ ((N / p) * W S 0 p + W S 0 (N % p) + p) * p := by nlinarith
        _ = (W S 0 N + p) * p := by rw [hdecomp]
    have e2 : W S 0 N * p ≤ W S 0 p * N + p * p := by
      calc W S 0 N * p = ((N / p) * W S 0 p + W S 0 (N % p)) * p := by rw [hdecomp]
        _ = W S 0 p * ((N / p) * p) + p * W S 0 (N % p) := by ring
        _ ≤ W S 0 p * ((N / p) * p) + p * p := Nat.add_le_add_left hwp _
        _ ≤ W S 0 p * ((N / p) * p + N % p) + p * p := by nlinarith
        _ = W S 0 p * N + p * p := by rw [← hNd]
    have e1r : (W S 0 p : ℝ) * N ≤ ((W S 0 N : ℝ) + p) * p := by exact_mod_cast e1
    have e2r : (W S 0 N : ℝ) * p ≤ (W S 0 p : ℝ) * N + p * p := by exact_mod_cast e2
    constructor
    · rw [sub_le_iff_le_add, ← add_div, div_le_div_iff₀ hpr hNr]
      exact e1r
    · rw [← sub_le_iff_le_add, ← sub_div, div_le_div_iff₀ hNr hpr]
      linarith
  have h0 : Tendsto (fun N : ℕ => (p : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (p : ℝ)
  have hlow : Tendsto (fun N : ℕ => (W S 0 p : ℝ) / p - p / N) atTop
      (𝓝 ((W S 0 p : ℝ) / p)) := by
    simpa using tendsto_const_nhds.sub h0
  have hup : Tendsto (fun N : ℕ => (W S 0 p : ℝ) / p + p / N) atTop
      (𝓝 ((W S 0 p : ℝ) / p)) := by
    simpa using tendsto_const_nhds.add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN using (main N hN).1
  · filter_upwards [eventually_gt_atTop 0] with N hN using (main N hN).2

end Counting


/-! ## Periods and uncovered sets -/

section Periods

/-- A common period of the first `k` congruences: `P n k = n 0 * ⋯ * n (k-1)`. -/
def P (n : ℕ → ℕ) (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, n i

lemma P_pos {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (k : ℕ) : 0 < P n k :=
  Finset.prod_pos (fun i _ => hpos i)

lemma P_dvd (n : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : P n i ∣ P n j :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_subset_range.2 h)

lemma n_dvd_P (n : ℕ → ℕ) {i k : ℕ} (h : i < k) : n i ∣ P n k :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.2 h)

lemma succ_le_n {n : ℕ → ℕ} (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ) : k + 1 ≤ n k := by
  induction k with
  | zero => exact hn0
  | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hn (Nat.lt_succ_self k)))

lemma le_P {n : ℕ → ℕ} (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ) : k ≤ P n k := by
  have hpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (Nat.succ_pos i) (succ_le_n hn hn0 i)
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    have h1 : n k ≤ P n (k + 1) :=
      Nat.le_of_dvd (P_pos hpos _) (n_dvd_P n (Nat.lt_succ_self k))
    exact (succ_le_n hn hn0 k).trans h1

lemma unc_congr (n a : ℕ → ℕ) {k m m' : ℕ} (h : m ≡ m' [MOD P n k]) :
    m ∈ Unc n a k ↔ m' ∈ Unc n a k := by
  unfold Unc
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hm i hi hc
    exact hm i hi ((h.of_dvd (n_dvd_P n hi)).trans hc)
  · intro hm i hi hc
    exact hm i hi ((h.of_dvd (n_dvd_P n hi)).symm.trans hc)

lemma unc_per (n a : ℕ → ℕ) {k j : ℕ} (h : k ≤ j) : PerSet (Unc n a k) (P n j) := by
  intro m
  apply unc_congr
  have h1 : P n j ≡ 0 [MOD P n k] := Nat.modEq_zero_iff_dvd.2 (P_dvd n h)
  simpa using h1.add_left m

lemma unc_anti (n a : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : Unc n a j ⊆ Unc n a i :=
  fun _ hm l hl => hm l (lt_of_lt_of_le hl h)

lemma uncInf_sub (n a : ℕ → ℕ) (k : ℕ) : UncInf n a ⊆ Unc n a k :=
  fun _ hm l _ => hm l

lemma unc_congr_choice (n : ℕ → ℕ) {a a' : ℕ → ℕ} {k : ℕ}
    (h : ∀ i, i < k → a i ≡ a' i [MOD n i]) : Unc n a k = Unc n a' k := by
  ext m
  constructor
  · intro hm i hi hc; exact hm i hi (hc.trans (h i hi).symm)
  · intro hm i hi hc; exact hm i hi (hc.trans (h i hi))

/-- number of residues mod `P n k` uncovered by the first `k` congruences. -/
noncomputable def cU (n a : ℕ → ℕ) (k : ℕ) : ℕ := W (Unc n a k) 0 (P n k)

lemma density_unc {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (a : ℕ → ℕ) (k : ℕ) :
    HasNatDensity (Unc n a k) ((cU n a k : ℝ) / P n k) :=
  density_of_periodic (P_pos hpos k) (unc_per n a le_rfl)

lemma cnt_unc_period {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (a : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) :
    (W (Unc n a i) 0 (P n j) : ℝ) = (P n j : ℝ) * ((cU n a i : ℝ) / P n i) := by
  obtain ⟨q, hq⟩ := P_dvd n h
  have h1 := cnt_add_period (unc_per n a (le_refl i)) q 0
  have h2 : W (Unc n a i) 0 (P n j) = q * cU n a i := by
    have h3 : W (Unc n a i) 0 0 = 0 := by simp [W]
    rw [hq, mul_comm (P n i) q]
    rw [add_zero, h3, add_zero] at h1
    exact h1
  have hne : (P n i : ℝ) ≠ 0 := by exact_mod_cast (P_pos hpos i).ne'
  rw [h2, hq]
  push_cast
  field_simp

lemma rho_anti {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (a : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) :
    (cU n a j : ℝ) / P n j ≤ (cU n a i : ℝ) / P n i := by
  have h1 : cU n a j ≤ W (Unc n a i) 0 (P n j) := W_mono (unc_anti n a h) 0 _
  have h2 := cnt_unc_period hpos a h
  have hPj : (0 : ℝ) < P n j := by exact_mod_cast P_pos hpos j
  rw [div_le_iff₀ hPj]
  calc (cU n a j : ℝ) ≤ W (Unc n a i) 0 (P n j) := by exact_mod_cast h1
    _ = (cU n a i : ℝ) / P n i * P n j := by rw [h2]; ring

end Periods


/-! ## Step 1: a single choice that is bad at every level (König's lemma) -/

section StepOne

/-- extension of a tuple of residues to a choice function -/
def extT (n : ℕ → ℕ) (k : ℕ) (f : (i : Fin k) → Fin (n i)) : ℕ → ℕ :=
  fun i => if h : i < k then (f ⟨i, h⟩ : ℕ) else 0

/-- tuples of residues `(a 0, …, a (k-1))` whose uncovered density is at least `ε`. -/
abbrev GoodT (n : ℕ → ℕ) (ε : ℝ) (k : ℕ) : Type :=
  {f : (i : Fin k) → Fin (n i) // ε * (P n k : ℝ) ≤ (cU n (extT n k f) k : ℝ)}

/-- restriction of a tuple to its first `i` coordinates -/
def restrT (n : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) (f : (l : Fin j) → Fin (n l)) :
    (l : Fin i) → Fin (n l) :=
  fun l => f ⟨l, lt_of_lt_of_le l.2 h⟩

lemma extT_restr (n : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) (f : (l : Fin j) → Fin (n l)) (l : ℕ)
    (hl : l < i) : extT n i (restrT n h f) l = extT n j f l := by
  unfold extT restrT
  rw [dite_eq_left hl, dite_eq_left (lt_of_lt_of_le hl h)]

lemma exists_uniform_choice (n : ℕ → ℕ) (hpos : ∀ i, 0 < n i) (ε : ℝ)
    (h : ∀ k, ∃ a : ℕ → ℕ, ε * (P n k : ℝ) ≤ (cU n a k : ℝ)) :
    ∃ a : ℕ → ℕ, ∀ k, ε * (P n k : ℝ) ≤ (cU n a k : ℝ) := by
  have : ∀ k, Nonempty (GoodT n ε k) := by
    intro k
    obtain ⟨a, ha⟩ := h k
    refine ⟨⟨fun l => ⟨a l % n l, Nat.mod_lt _ (hpos l)⟩, ?_⟩⟩
    have e : Unc n (extT n k (fun l => ⟨a l % n l, Nat.mod_lt _ (hpos l)⟩)) k = Unc n a k := by
      apply unc_congr_choice
      intro i hi
      unfold extT
      rw [dite_eq_left hi]
      exact Nat.mod_modEq _ _
    unfold cU
    rw [e]
    exact ha
  let π : {i j : ℕ} → i ≤ j → GoodT n ε j → GoodT n ε i := fun {i j} hij x =>
    ⟨restrT n hij x.1, by
      have e : Unc n (extT n i (restrT n hij x.1)) i = Unc n (extT n j x.1) i :=
        unc_congr_choice n (fun l hl => by rw [extT_restr n hij x.1 l hl])
      have hx := x.2
      have hPi : (0 : ℝ) < P n i := by exact_mod_cast P_pos hpos i
      have hPj : (0 : ℝ) < P n j := by exact_mod_cast P_pos hpos j
      have h1 : ε ≤ (cU n (extT n j x.1) j : ℝ) / P n j := (le_div_iff₀ hPj).2 hx
      have h2 := rho_anti hpos (extT n j x.1) hij
      have h3 : cU n (extT n i (restrT n hij x.1)) i = cU n (extT n j x.1) i := by
        unfold cU; rw [e]
      rw [h3]
      exact (le_div_iff₀ hPi).1 (h1.trans h2)⟩
  obtain ⟨g, hg⟩ := exists_seq_forall_proj_of_forall_finite (α := GoodT n ε) π
    (fun i x => rfl) (fun i j k hij hjk x => rfl) (fun i x => Set.toFinite _)
  refine ⟨fun i => ((g (i + 1)).1 ⟨i, Nat.lt_succ_self i⟩ : ℕ), fun k => ?_⟩
  have e : Unc n (fun i => ((g (i + 1)).1 ⟨i, Nat.lt_succ_self i⟩ : ℕ)) k
      = Unc n (extT n k (g k).1) k := by
    apply unc_congr_choice
    intro l hl
    have h1 := hg (Nat.succ_le_of_lt hl)
    have h2 : ((g (l + 1)).1 ⟨l, Nat.lt_succ_self l⟩ : ℕ) = ((g k).1 ⟨l, hl⟩ : ℕ) := by
      rw [← h1]
      rfl
    unfold extT
    rw [dite_eq_left hl, h2]
  unfold cU
  rw [e]
  exact (g k).2

end StepOne


/-! ## Step 2: a coherent sequence of shifts avoiding all bad sets -/

section StepTwo

lemma exists_kappa (ρ : ℕ → ℝ) (hanti : Antitone ρ) (hbdd : ∀ k, 0 ≤ ρ k) (η : ℕ → ℝ)
    (hη : ∀ j, 0 < η j) :
    ∃ κ : ℕ → ℕ, (∀ j, j ≤ κ j) ∧ ∀ j k, κ j ≤ k → ρ (κ j) - ρ k ≤ η j := by
  have hb : BddBelow (Set.range ρ) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hbdd k⟩
  have key : ∀ j, ∃ K, j ≤ K ∧ ∀ k, K ≤ k → ρ K - ρ k ≤ η j := by
    intro j
    have h1 : (⨅ k, ρ k) < (⨅ k, ρ k) + η j := lt_add_of_pos_right _ (hη j)
    obtain ⟨K, hK⟩ := exists_lt_of_ciInf_lt h1
    refine ⟨max K j, le_max_right _ _, fun k _ => ?_⟩
    have h2 : ρ (max K j) ≤ ρ K := hanti (le_max_left _ _)
    have h3 : (⨅ k, ρ k) ≤ ρ k := ciInf_le hb k
    linarith
  choose κ h1 h2 using key
  exact ⟨κ, h1, h2⟩

/-- points uncovered at level `c` but covered at level `k`. -/
def Dset (n a : ℕ → ℕ) (c k : ℕ) : Set ℕ := Unc n a c \ Unc n a k

lemma Dset_per (n a : ℕ → ℕ) {c k : ℕ} (h : c ≤ k) : PerSet (Dset n a c k) (P n k) := by
  intro m
  simp only [Dset, Set.mem_sdiff]
  rw [unc_per n a h m, unc_per n a le_rfl m]

/-- the shift `t` is `j`-bad at depth `k`: the window `[t, t + P n (κ j))` contains more than
`lam j * P n (κ j)` points uncovered at level `κ j` but covered at level `k`. -/
def Bad (n a κ : ℕ → ℕ) (lam : ℕ → ℝ) (j k t : ℕ) : Prop :=
  lam j * (P n (κ j) : ℝ) < (W (Dset n a (κ j) k) t (P n (κ j)) : ℝ)

/-- the shift `t` is good at depth `k`. -/
def Good (n a κ : ℕ → ℕ) (lam : ℕ → ℝ) (k t : ℕ) : Prop :=
  ∀ j, κ j ≤ k → ¬ Bad n a κ lam j k t

lemma bad_persist (n a κ : ℕ → ℕ) (lam : ℕ → ℝ) {j k k' t : ℕ} (hk : κ j ≤ k) (hkk : k ≤ k')
    (h : Bad n a κ lam j k (t % P n k)) : Bad n a κ lam j k' t := by
  classical
  unfold Bad at *
  have hle : W (Dset n a (κ j) k) (t % P n k) (P n (κ j))
      ≤ W (Dset n a (κ j) k') t (P n (κ j)) := by
    unfold W
    apply Finset.sum_le_sum
    intro x _
    have h1 : x + t % P n k ≡ x + t [MOD P n k] := (Nat.mod_modEq t _).add_left x
    have hA : x + t % P n k ∈ Unc n a (κ j) ↔ x + t ∈ Unc n a (κ j) :=
      unc_congr n a (h1.of_dvd (P_dvd n hk))
    have hB : x + t % P n k ∈ Unc n a k ↔ x + t ∈ Unc n a k := unc_congr n a h1
    have hsub : x + t % P n k ∈ Dset n a (κ j) k → x + t ∈ Dset n a (κ j) k' := by
      intro hx
      exact ⟨hA.1 hx.1, fun hc => hx.2 (hB.2 (unc_anti n a hkk hc))⟩
    split_ifs with h2 h3 h3
    · exact le_rfl
    · exact absurd (hsub h2) h3
    · exact Nat.zero_le _
    · exact le_rfl
  have hc : (W (Dset n a (κ j) k) (t % P n k) (P n (κ j)) : ℝ)
      ≤ W (Dset n a (κ j) k') t (P n (κ j)) := by exact_mod_cast hle
  linarith

lemma good_parent (n a κ : ℕ → ℕ) (lam : ℕ → ℝ) {i k t : ℕ} (hik : i ≤ k)
    (h : Good n a κ lam k t) : Good n a κ lam i (t % P n i) :=
  fun j hj hbad => h j (hj.trans hik) (bad_persist n a κ lam hj hik hbad)

lemma bad_card_le {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (a κ : ℕ → ℕ) (lam : ℕ → ℝ) {j k : ℕ}
    (hlam : 0 < lam j) (hk : κ j ≤ k) (th : ℝ)
    (hρ : (cU n a (κ j) : ℝ) / P n (κ j) - (cU n a k : ℝ) / P n k ≤ lam j * th) :
    ∀ F : Finset ℕ, (∀ t ∈ F, t < P n k ∧ Bad n a κ lam j k t) →
      (F.card : ℝ) ≤ th * P n k := by
  classical
  intro F hF
  have hper : PerSet (Dset n a (κ j) k) (P n k) := Dset_per n a hk
  have hM := markov_shifts hper (P n (κ j)) (P_pos hpos _) (lam j)
  have hsub : F ⊆ (Finset.range (P n k)).filter
      (fun t => lam j * (P n (κ j) : ℝ) < (W (Dset n a (κ j) k) t (P n (κ j)) : ℝ)) := by
    intro t ht
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hF t ht).1, (hF t ht).2⟩
  have hcard : (F.card : ℝ) ≤ (((Finset.range (P n k)).filter
      (fun t => lam j * (P n (κ j) : ℝ) < (W (Dset n a (κ j) k) t (P n (κ j)) : ℝ))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hPk : (0 : ℝ) < P n k := by exact_mod_cast P_pos hpos k
  have hD : (W (Dset n a (κ j) k) 0 (P n k) : ℝ)
      = (P n k : ℝ) * ((cU n a (κ j) : ℝ) / P n (κ j) - (cU n a k : ℝ) / P n k) := by
    have h1 : W (Dset n a (κ j) k) 0 (P n k) + W (Unc n a k) 0 (P n k)
        = W (Unc n a (κ j)) 0 (P n k) := W_diff (unc_anti n a hk) 0 (P n k)
    have h2 := cnt_unc_period hpos a hk
    have h3 : (W (Dset n a (κ j) k) 0 (P n k) : ℝ) + (cU n a k : ℝ)
        = W (Unc n a (κ j)) 0 (P n k) := by exact_mod_cast h1
    rw [h2] at h3
    have h4 : (P n k : ℝ) * ((cU n a k : ℝ) / P n k) = cU n a k := by
      field_simp
    rw [mul_sub, h4]
    linarith
  have hmain : (F.card : ℝ) * lam j ≤ (th * P n k) * lam j := by
    calc (F.card : ℝ) * lam j
        ≤ (((Finset.range (P n k)).filter
            (fun t => lam j * (P n (κ j) : ℝ) < (W (Dset n a (κ j) k) t (P n (κ j)) : ℝ))).card : ℝ)
            * lam j := mul_le_mul_of_nonneg_right hcard hlam.le
      _ ≤ (W (Dset n a (κ j) k) 0 (P n k) : ℝ) := hM
      _ = (P n k : ℝ) * ((cU n a (κ j) : ℝ) / P n (κ j) - (cU n a k : ℝ) / P n k) := hD
      _ ≤ (P n k : ℝ) * (lam j * th) := mul_le_mul_of_nonneg_left hρ hPk.le
      _ = (th * P n k) * lam j := by ring
  exact le_of_mul_le_mul_right hmain hlam

lemma good_exists {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (a κ : ℕ → ℕ) (lam th : ℕ → ℝ)
    (hκ : ∀ j, j ≤ κ j) (hlam : ∀ j, 0 < lam j) (hth0 : ∀ j, 0 ≤ th j)
    (hth : ∀ K, ∑ j ∈ Finset.range K, th j < 1)
    (hρ : ∀ j k, κ j ≤ k →
      (cU n a (κ j) : ℝ) / P n (κ j) - (cU n a k : ℝ) / P n k ≤ lam j * th j) (k : ℕ) :
    ∃ t, t < P n k ∧ Good n a κ lam k t := by
  classical
  by_contra hcon
  push Not at hcon
  have hPk : (0 : ℝ) < P n k := by exact_mod_cast P_pos hpos k
  have hcover : Finset.range (P n k) ⊆ (Finset.range (k + 1)).biUnion
      (fun j => (Finset.range (P n k)).filter (fun t => κ j ≤ k ∧ Bad n a κ lam j k t)) := by
    intro t ht
    have ht' := Finset.mem_range.1 ht
    have hng := hcon t ht'
    unfold Good at hng
    push Not at hng
    obtain ⟨j, hj, hbad⟩ := hng
    refine Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le ((hκ j).trans hj)), ?_⟩
    exact Finset.mem_filter.2 ⟨ht, hj, hbad⟩
  have hcard := Finset.card_le_card hcover
  have h2 := Finset.card_biUnion_le (s := Finset.range (k + 1))
      (t := fun j => (Finset.range (P n k)).filter (fun t => κ j ≤ k ∧ Bad n a κ lam j k t))
  have h3 : ∀ j ∈ Finset.range (k + 1),
      (((Finset.range (P n k)).filter (fun t => κ j ≤ k ∧ Bad n a κ lam j k t)).card : ℝ)
        ≤ th j * P n k := by
    intro j _
    by_cases hj : κ j ≤ k
    · apply bad_card_le hpos a κ lam (hlam j) hj (th j) (hρ j k hj)
      intro t ht
      have ht' := Finset.mem_filter.1 ht
      exact ⟨Finset.mem_range.1 ht'.1, ht'.2.2⟩
    · have hempty : (Finset.range (P n k)).filter (fun t => κ j ≤ k ∧ Bad n a κ lam j k t) = ∅ := by
        apply Finset.filter_eq_empty_iff.2
        intro t _ hh
        exact hj hh.1
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (hth0 j) hPk.le
  have hlt : (P n k : ℝ) < P n k := by
    calc (P n k : ℝ) = ((Finset.range (P n k)).card : ℝ) := by simp
      _ ≤ (((Finset.range (k + 1)).biUnion
            (fun j => (Finset.range (P n k)).filter
              (fun t => κ j ≤ k ∧ Bad n a κ lam j k t))).card : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ j ∈ Finset.range (k + 1),
            (((Finset.range (P n k)).filter
              (fun t => κ j ≤ k ∧ Bad n a κ lam j k t)).card : ℝ) := by exact_mod_cast h2
      _ ≤ ∑ j ∈ Finset.range (k + 1), th j * P n k := Finset.sum_le_sum h3
      _ = (∑ j ∈ Finset.range (k + 1), th j) * P n k := by rw [Finset.sum_mul]
      _ < 1 * P n k := mul_lt_mul_of_pos_right (hth (k + 1)) hPk
      _ = P n k := one_mul _
  exact lt_irrefl _ hlt

/-- good shifts at depth `k`. -/
abbrev GoodNode (n a κ : ℕ → ℕ) (lam : ℕ → ℝ) (k : ℕ) : Type :=
  {t : ℕ // t < P n k ∧ Good n a κ lam k t}

instance (n a κ : ℕ → ℕ) (lam : ℕ → ℝ) (k : ℕ) : Finite (GoodNode n a κ lam k) :=
  Finite.of_injective (fun x : GoodNode n a κ lam k => (⟨x.1, x.2.1⟩ : Fin (P n k)))
    (fun _ _ h => Subtype.ext (congrArg Fin.val h))

lemma coherent_shifts {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (a κ : ℕ → ℕ) (lam : ℕ → ℝ)
    (hex : ∀ k, ∃ t, t < P n k ∧ Good n a κ lam k t) :
    ∃ τ : ℕ → ℕ, (∀ k, Good n a κ lam k (τ k)) ∧ ∀ i j, i ≤ j → τ j % P n i = τ i := by
  have : ∀ k, Nonempty (GoodNode n a κ lam k) := fun k => by
    obtain ⟨t, h1, h2⟩ := hex k
    exact ⟨⟨t, h1, h2⟩⟩
  let π : {i j : ℕ} → i ≤ j → GoodNode n a κ lam j → GoodNode n a κ lam i :=
    fun {i _} h x => ⟨x.1 % P n i, Nat.mod_lt _ (P_pos hpos i), good_parent n a κ lam h x.2.2⟩
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite (α := GoodNode n a κ lam) π
    (fun i x => Subtype.ext (Nat.mod_eq_of_lt x.2.1))
    (fun i j k hij hjk x => Subtype.ext (Nat.mod_mod_of_dvd _ (P_dvd n hij)))
    (fun i x => Set.toFinite _)
  refine ⟨fun k => (f k).1, fun k => (f k).2.2, fun i j hij => ?_⟩
  exact congrArg Subtype.val (hf hij)

lemma shift_mem (n a τ : ℕ → ℕ) (hpos : ∀ i, 0 < n i)
    (hτ : ∀ i j, i ≤ j → τ j % P n i = τ i) (k m : ℕ) :
    m ∈ Unc n (fun i => a i + (n i - 1) * τ (i + 1)) k ↔ m + τ k ∈ Unc n a k := by
  unfold Unc
  simp only [Set.mem_ofPred_eq]
  have key : ∀ i, i < k →
      (m ≡ a i + (n i - 1) * τ (i + 1) [MOD n i] ↔ m + τ k ≡ a i [MOD n i]) := by
    intro i hi
    have h1 : τ k ≡ τ (i + 1) [MOD n i] := by
      have h := hτ (i + 1) k (Nat.succ_le_of_lt hi)
      have h' : τ k % P n (i + 1) ≡ τ k [MOD P n (i + 1)] := Nat.mod_modEq _ _
      rw [h] at h'
      exact (h'.of_dvd (n_dvd_P n (Nat.lt_succ_self i))).symm
    have h2 : a i + (n i - 1) * τ (i + 1) + τ (i + 1) ≡ a i [MOD n i] := by
      have e : a i + (n i - 1) * τ (i + 1) + τ (i + 1) = a i + n i * τ (i + 1) := by
        obtain ⟨c, hc⟩ : ∃ c, n i = c + 1 := ⟨n i - 1, by have := hpos i; omega⟩
        rw [hc, Nat.add_sub_cancel]
        ring
      rw [e]
      unfold Nat.ModEq
      exact Nat.add_mul_mod_self_left _ _ _
    constructor
    · intro h
      exact ((h1.add_left m).trans (h.add_right _)).trans h2
    · intro h
      have h3 : m + τ (i + 1) ≡ a i + (n i - 1) * τ (i + 1) + τ (i + 1) [MOD n i] :=
        ((h1.symm.add_left m).trans h).trans h2.symm
      exact Nat.ModEq.add_right_cancel' _ h3
  constructor
  · intro h i hi hc; exact h i hi ((key i hi).2 hc)
  · intro h i hi hc; exact h i hi ((key i hi).1 hc)

lemma stabilize (n b : ℕ → ℕ) (N : ℕ) :
    ∃ K, ∀ k, K ≤ k → W (UncInf n b) 0 N = W (Unc n b k) 0 N := by
  classical
  have h : ∀ m, ∃ i, m ∉ UncInf n b → m ≡ b i [MOD n i] := by
    intro m
    by_cases hm : m ∈ UncInf n b
    · exact ⟨0, fun h => absurd hm h⟩
    · unfold UncInf at hm
      simp only [Set.mem_ofPred_eq, not_forall, not_not] at hm
      obtain ⟨i, hi⟩ := hm
      exact ⟨i, fun _ => hi⟩
  choose f hf using h
  refine ⟨(Finset.range N).sup (fun m => f m + 1), fun k hk => ?_⟩
  unfold W
  apply Finset.sum_congr rfl
  intro x hx
  have hiff : x + 0 ∈ UncInf n b ↔ x + 0 ∈ Unc n b k := by
    rw [add_zero]
    constructor
    · exact fun h => uncInf_sub n b k h
    · intro h
      by_contra hnot
      have h1 := hf x hnot
      have h2 : f x + 1 ≤ (Finset.range N).sup (fun m => f m + 1) :=
        Finset.le_sup (f := fun m => f m + 1) hx
      exact h (f x) (by omega) h1
  simp only [hiff]

lemma geom_half (K : ℕ) :
    ∑ j ∈ Finset.range K, (1 : ℝ) / 2 ^ (j + 2) = 1 / 2 - 1 / 2 ^ (K + 1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have h : (2 : ℝ) ^ (K + 1 + 1) = 2 * 2 ^ (K + 1) := by ring
    rw [h]
    field_simp
    ring

lemma exists_bad_choice {n : ℕ → ℕ} (hn : StrictMono n) (hn0 : 0 < n 0) (ε : ℝ) (hε : 0 < ε)
    (a : ℕ → ℕ) (ha : ∀ k, ε * (P n k : ℝ) ≤ (cU n a k : ℝ)) :
    ∃ b : ℕ → ℕ, ∀ j : ℕ, ∃ L : ℕ, j ≤ L ∧ (ε / 2) * (L : ℝ) ≤ (W (UncInf n b) 0 L : ℝ) := by
  have hpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (Nat.succ_pos i) (succ_le_n hn hn0 i)
  have hanti : Antitone (fun k => (cU n a k : ℝ) / P n k) := fun i j h => rho_anti hpos a h
  have hnonneg : ∀ k, 0 ≤ (cU n a k : ℝ) / P n k := fun k => by positivity
  have hlam : ∀ j : ℕ, 0 < ε / 2 ^ (j + 2) := fun j => by positivity
  have hth0 : ∀ j : ℕ, (0 : ℝ) ≤ 1 / 2 ^ (j + 2) := fun j => by positivity
  have hth : ∀ K, ∑ j ∈ Finset.range K, (1 : ℝ) / 2 ^ (j + 2) < 1 := by
    intro K
    rw [geom_half]
    have : (0 : ℝ) < 1 / 2 ^ (K + 1) := by positivity
    linarith
  obtain ⟨κ, hκ1, hκ2⟩ := exists_kappa (fun k => (cU n a k : ℝ) / P n k) hanti hnonneg
    (fun j => ε / 2 ^ (j + 2) * (1 / 2 ^ (j + 2)))
    (fun j => mul_pos (hlam j) (by positivity))
  have hex := good_exists hpos a κ (fun j => ε / 2 ^ (j + 2)) (fun j => 1 / 2 ^ (j + 2))
    hκ1 hlam hth0 hth hκ2
  obtain ⟨τ, hτ1, hτ2⟩ := coherent_shifts hpos a κ (fun j => ε / 2 ^ (j + 2)) hex
  refine ⟨fun i => a i + (n i - 1) * τ (i + 1), fun j => ?_⟩
  refine ⟨P n (κ j), (hκ1 j).trans (le_P hn hn0 _), ?_⟩
  obtain ⟨K, hK⟩ := stabilize n (fun i => a i + (n i - 1) * τ (i + 1)) (P n (κ j))
  have hk1 : K ≤ max K (κ j) := le_max_left _ _
  have hk2 : κ j ≤ max K (κ j) := le_max_right _ _
  rw [hK _ hk1]
  have e1 : W (Unc n (fun i => a i + (n i - 1) * τ (i + 1)) (max K (κ j))) 0 (P n (κ j))
      = W (Unc n a (max K (κ j))) (τ (max K (κ j))) (P n (κ j)) := by
    classical
    unfold W
    apply Finset.sum_congr rfl
    intro x _
    have := shift_mem n a τ hpos hτ2 (max K (κ j)) x
    rw [add_zero]
    simp only [this]
  have e2 : W (Dset n a (κ j) (max K (κ j))) (τ (max K (κ j))) (P n (κ j))
      + W (Unc n a (max K (κ j))) (τ (max K (κ j))) (P n (κ j))
      = W (Unc n a (κ j)) (τ (max K (κ j))) (P n (κ j)) :=
    W_diff (unc_anti n a hk2) _ _
  have e3 : W (Unc n a (κ j)) (τ (max K (κ j))) (P n (κ j)) = cU n a (κ j) :=
    W_per (unc_per n a le_rfl) _
  have e4 : (W (Dset n a (κ j) (max K (κ j))) (τ (max K (κ j))) (P n (κ j)) : ℝ)
      ≤ ε / 2 ^ (j + 2) * (P n (κ j) : ℝ) := by
    have h := hτ1 (max K (κ j)) j hk2
    unfold Bad at h
    exact not_lt.1 h
  have e5 : ε / 2 ^ (j + 2) ≤ ε / 2 := by
    apply div_le_div_of_nonneg_left hε.le (by norm_num)
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have e6 := ha (κ j)
  have e7 : (W (Dset n a (κ j) (max K (κ j))) (τ (max K (κ j))) (P n (κ j)) : ℝ)
      + (W (Unc n a (max K (κ j))) (τ (max K (κ j))) (P n (κ j)) : ℝ) = (cU n a (κ j) : ℝ) := by
    rw [← e3]
    exact_mod_cast e2
  have hLr : (0 : ℝ) ≤ P n (κ j) := Nat.cast_nonneg _
  have e8 : ε / 2 ^ (j + 2) * (P n (κ j) : ℝ) ≤ ε / 2 * (P n (κ j) : ℝ) :=
    mul_le_mul_of_nonneg_right e5 hLr
  rw [e1]
  linarith

end StepTwo


/-! ## Main theorems -/

/-- Strong (upper-density) form: if the uniform conclusion fails at level ε, some choice `b`
    has uncovered set with upper density ≥ ε/2 (so it does not have density 0). -/
theorem erdos_281_strong (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (ε : ℝ) (hε : 0 < ε)
    (hfail : ∀ k : ℕ, ∃ a : ℕ → ℕ, ∀ d : ℝ, HasNatDensity (Unc n a k) d → ε ≤ d) :
    ∃ b : ℕ → ℕ, ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      (ε / 2) * (N : ℝ) ≤ ((UncInf n b ∩ Set.Iio N).ncard : ℝ) := by
  have hpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (Nat.succ_pos i) (succ_le_n hn hn0 i)
  have h1 : ∀ k, ∃ a : ℕ → ℕ, ε * (P n k : ℝ) ≤ (cU n a k : ℝ) := by
    intro k
    obtain ⟨a, ha⟩ := hfail k
    refine ⟨a, ?_⟩
    have h := ha _ (density_unc hpos a k)
    have hP : (0 : ℝ) < P n k := by exact_mod_cast P_pos hpos k
    exact (le_div_iff₀ hP).1 h
  obtain ⟨a, ha⟩ := exists_uniform_choice n hpos ε h1
  obtain ⟨b, hb⟩ := exists_bad_choice hn hn0 ε hε a ha
  refine ⟨b, fun N₀ => ?_⟩
  obtain ⟨L, hL1, hL2⟩ := hb N₀
  exact ⟨L, hL1, by rw [ncard_inter_Iio]; exact hL2⟩

/-- Erdős Problem 281. -/
theorem erdos_281 (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0)
    (H : ∀ a : ℕ → ℕ, HasNatDensity (UncInf n a) 0) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  have hfail : ∀ k : ℕ, ∃ a : ℕ → ℕ, ∀ d : ℝ, HasNatDensity (Unc n a k) d → ε ≤ d := by
    intro k
    obtain ⟨a, ha⟩ := hcon k
    exact ⟨a, fun d hd => not_lt.1 (fun hlt => ha d hlt hd)⟩
  obtain ⟨b, hb⟩ := erdos_281_strong n hn hn0 ε hε hfail
  have hH := H b
  unfold HasNatDensity at hH
  have hev : ∀ᶠ N : ℕ in atTop, ((UncInf n b ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) < ε / 2 :=
    (tendsto_order.1 hH).2 (ε / 2) (by positivity)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  obtain ⟨N, hN, hle⟩ := hb (max N₁ 1)
  have hNpos : (0 : ℝ) < N := by
    have h1 : 1 ≤ N := (le_max_right _ _).trans hN
    exact_mod_cast h1
  have h2 := hN₁ N ((le_max_left _ _).trans hN)
  rw [div_lt_iff₀ hNpos] at h2
  linarith

set_option linter.unusedVariables false in
/-- The easy converse ("clearly sufficient"). -/
theorem erdos_281_converse (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0)
    (C : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d) :
    ∀ a : ℕ → ℕ, HasNatDensity (UncInf n a) 0 := by
  intro a
  unfold HasNatDensity
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := C ε hε
  obtain ⟨d, hd, hdens⟩ := hk a
  have hev : ∀ᶠ N : ℕ in atTop, ((Unc n a k ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) < ε :=
    (tendsto_order.1 hdens).2 ε hd
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  refine ⟨N₁, fun N hN => ?_⟩
  have h1 := hN₁ N hN
  have hsub : (UncInf n a ∩ Set.Iio N).ncard ≤ (Unc n a k ∩ Set.Iio N).ncard :=
    Set.ncard_le_ncard (Set.inter_subset_inter_left _ (uncInf_sub n a k))
      ((Set.finite_Iio N).inter_of_right _)
  have h2 : ((UncInf n a ∩ Set.Iio N).ncard : ℝ) / (N : ℝ)
      ≤ ((Unc n a k ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hsub) (Nat.cast_nonneg N)
  have h3 : 0 ≤ ((UncInf n a ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h3]
  linarith

/-- Version with genuine residue classes (elements of ZMod (n i)). -/
theorem erdos_281_zmod (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0)
    (H : ∀ a : (i : ℕ) → ZMod (n i), HasNatDensity {m : ℕ | ∀ i, (m : ZMod (n i)) ≠ a i} 0) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : (i : ℕ) → ZMod (n i),
      ∃ d : ℝ, d < ε ∧ HasNatDensity {m : ℕ | ∀ i, i < k → (m : ZMod (n i)) ≠ a i} d := by
  have hpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (Nat.succ_pos i) (succ_le_n hn hn0 i)
  have H' : ∀ a : ℕ → ℕ, HasNatDensity (UncInf n a) 0 := by
    intro a
    have h := H (fun i => (a i : ZMod (n i)))
    have e : {m : ℕ | ∀ i, (m : ZMod (n i)) ≠ ((a i : ℕ) : ZMod (n i))} = UncInf n a := by
      ext m
      simp only [UncInf, Set.mem_ofPred_eq, ne_eq, ZMod.natCast_eq_natCast_iff]
    rwa [e] at h
  intro ε hε
  obtain ⟨k, hk⟩ := erdos_281 n hn hn0 H' ε hε
  refine ⟨k, fun a => ?_⟩
  obtain ⟨d, hd, hdens⟩ := hk (fun i => (a i).val)
  refine ⟨d, hd, ?_⟩
  have e : {m : ℕ | ∀ i, i < k → (m : ZMod (n i)) ≠ a i} = Unc n (fun i => (a i).val) k := by
    ext m
    simp only [Unc, Set.mem_ofPred_eq, ne_eq]
    constructor
    · intro h i hi hc
      have : NeZero (n i) := ⟨(hpos i).ne'⟩
      apply h i hi
      have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).2 hc
      rwa [ZMod.natCast_zmod_val] at h1
    · intro h i hi hc
      have : NeZero (n i) := ⟨(hpos i).ne'⟩
      apply h i hi
      apply (ZMod.natCast_eq_natCast_iff _ _ _).1
      rw [ZMod.natCast_zmod_val]
      exact hc
  rw [e]
  exact hdens

end Erdos281

#print axioms Erdos281.erdos_281
#print axioms Erdos281.erdos_281_converse
#print axioms Erdos281.erdos_281_strong
#print axioms Erdos281.erdos_281_zmod
