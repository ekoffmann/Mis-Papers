import Nous.Erdos281

/-!
# Erdős Problem 281 for sets of integers (two-sided density)

`Nous.Erdos281` proves the theorem for sets of naturals with the one-sided natural density.
Here we transfer it to sets of **integers** with the symmetric density
`#(S ∩ [-N, N]) / (2N+1)`, with residue classes given as elements of `ZMod (n i)`; this is the
shape of the statement in google-deepmind/formal-conjectures (`ErdosProblems/281.lean`).

Route: a set of integers is split into its non-negative part `natPos S` and its negative part
`natNeg S` (via `x ↦ -(x+1)`), both sets of naturals.  For the sets in question both parts are
periodic with the same period and (by the reflection `x ↦ p - 1 - x`) the same count per period.
-/

open Filter Topology

namespace Erdos281

/-- Two-sided natural density of a set of integers: #(S ∩ [-N, N]) / (2N+1) → d. -/
def HasIntDensity (S : Set ℤ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) / (2 * (N : ℝ) + 1)) atTop (𝓝 d)

/-- The non-negative part of `S ⊆ ℤ`, as a set of naturals. -/
def natPos (S : Set ℤ) : Set ℕ := {m : ℕ | (m : ℤ) ∈ S}

/-- The negative part of `S ⊆ ℤ`, as a set of naturals via `x ↦ -(x+1)`. -/
def natNeg (S : Set ℤ) : Set ℕ := {x : ℕ | -((x : ℤ) + 1) ∈ S}

/-! ## Splitting the symmetric window -/

/-- `#(S ∩ [-N, N]) = #(natPos S ∩ [0, N]) + #(natNeg S ∩ [0, N))`. -/
lemma ncard_Icc_split (S : Set ℤ) (N : ℕ) :
    (S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard =
      (natPos S ∩ Set.Iio (N + 1)).ncard + (natNeg S ∩ Set.Iio N).ncard := by
  have hinj : Function.Injective (fun x : ℕ => -((x : ℤ) + 1)) := by
    intro x y h
    have h' : -((x : ℤ) + 1) = -((y : ℤ) + 1) := h
    omega
  have hA : (S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)) =
      ((fun m : ℕ => (m : ℤ)) '' (natPos S ∩ Set.Iio (N + 1))) ∪
      ((fun x : ℕ => -((x : ℤ) + 1)) '' (natNeg S ∩ Set.Iio N)) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_union, Set.mem_image, Set.mem_Iio,
      natPos, natNeg, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hz, h1, h2⟩
      rcases le_or_gt 0 z with h0 | h0
      · left
        have e : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h0
        refine ⟨z.toNat, ⟨?_, ?_⟩, e⟩
        · rw [e]; exact hz
        · omega
      · right
        have e : (((-z - 1).toNat : ℕ) : ℤ) = -z - 1 := Int.toNat_of_nonneg (by omega)
        have e2 : -((((-z - 1).toNat : ℕ) : ℤ) + 1) = z := by rw [e]; ring
        refine ⟨(-z - 1).toNat, ⟨?_, ?_⟩, e2⟩
        · rw [e2]; exact hz
        · omega
    · rintro (⟨m, ⟨hm, hlt⟩, rfl⟩ | ⟨x, ⟨hx, hlt⟩, rfl⟩)
      · exact ⟨hm, by omega, by omega⟩
      · exact ⟨hx, by omega, by omega⟩
  have hfin1 : ((fun m : ℕ => (m : ℤ)) '' (natPos S ∩ Set.Iio (N + 1))).Finite :=
    ((Set.finite_Iio (N + 1)).inter_of_right _).image _
  have hfin2 : ((fun x : ℕ => -((x : ℤ) + 1)) '' (natNeg S ∩ Set.Iio N)).Finite :=
    ((Set.finite_Iio N).inter_of_right _).image _
  have hdisj : Disjoint ((fun m : ℕ => (m : ℤ)) '' (natPos S ∩ Set.Iio (N + 1)))
      ((fun x : ℕ => -((x : ℤ) + 1)) '' (natNeg S ∩ Set.Iio N)) := by
    rw [Set.disjoint_left]
    rintro z ⟨m, _, hm⟩ ⟨x, _, hx⟩
    have h1 : (m : ℤ) = z := hm
    have h2 : -((x : ℤ) + 1) = z := hx
    omega
  rw [hA, Set.ncard_union_eq hdisj hfin1 hfin2,
    Set.ncard_image_of_injective _ Nat.cast_injective,
    Set.ncard_image_of_injective _ hinj]

/-! ## Quantitative counting for periodic sets of naturals -/

/-- Two-sided bound for the count of a `p`-periodic set in `[0, N)`. -/
lemma W_bounds {S : Set ℕ} {p : ℕ} (hp : 0 < p) (hper : PerSet S p) (N : ℕ) :
    W S 0 p * N ≤ (W S 0 N + p) * p ∧ W S 0 N * p ≤ W S 0 p * N + p * p := by
  have hc : W S 0 p ≤ p := W_le _ _ _
  have hdecomp : W S 0 N = (N / p) * W S 0 p + W S 0 (N % p) := by
    have := cnt_add_period hper (N / p) (N % p)
    rwa [Nat.div_add_mod'] at this
  have hNd : N = (N / p) * p + N % p := (Nat.div_add_mod' N p).symm
  have hr : N % p < p := Nat.mod_lt _ hp
  have hwr : W S 0 (N % p) ≤ N % p := W_le _ _ _
  have hcr : W S 0 p * (N % p) ≤ p * p := Nat.mul_le_mul hc hr.le
  have hwp : p * W S 0 (N % p) ≤ p * p := Nat.mul_le_mul_left p (hwr.trans hr.le)
  constructor
  · calc W S 0 p * N = W S 0 p * ((N / p) * p + N % p) := by rw [← hNd]
      _ = (N / p) * W S 0 p * p + W S 0 p * (N % p) := by ring
      _ ≤ (N / p) * W S 0 p * p + p * p := Nat.add_le_add_left hcr _
      _ ≤ ((N / p) * W S 0 p + W S 0 (N % p) + p) * p := by nlinarith
      _ = (W S 0 N + p) * p := by rw [hdecomp]
  · calc W S 0 N * p = ((N / p) * W S 0 p + W S 0 (N % p)) * p := by rw [hdecomp]
      _ = W S 0 p * ((N / p) * p) + p * W S 0 (N % p) := by ring
      _ ≤ W S 0 p * ((N / p) * p) + p * p := Nat.add_le_add_left hwp _
      _ ≤ W S 0 p * ((N / p) * p + N % p) + p * p := by nlinarith
      _ = W S 0 p * N + p * p := by rw [← hNd]

/-- Reflection `x ↦ p - 1 - x` preserves the count in `[0, p)`. -/
lemma W_reflect {A B : Set ℕ} {p : ℕ} (h : ∀ x, x < p → (x ∈ A ↔ (p - 1 - x) ∈ B)) :
    W A 0 p = W B 0 p := by
  classical
  have h2 := Finset.sum_range_reflect (fun x => (if x + 0 ∈ B then 1 else 0 : ℕ)) p
  have h1 : W A 0 p = ∑ j ∈ Finset.range p, (if (p - 1 - j) + 0 ∈ B then 1 else 0 : ℕ) := by
    unfold W
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Finset.mem_range.1 hx
    by_cases hA : x ∈ A
    · have hB : (p - 1 - x) + 0 ∈ B := by rw [add_zero]; exact (h x hx').1 hA
      have hA' : x + 0 ∈ A := by rw [add_zero]; exact hA
      rw [ite_eq_left hA', ite_eq_left hB]
    · have hB : ¬ ((p - 1 - x) + 0 ∈ B) := by
        rw [add_zero]; exact fun hB => hA ((h x hx').2 hB)
      have hA' : ¬ (x + 0 ∈ A) := by rw [add_zero]; exact hA
      rw [ite_eq_right hA', ite_eq_right hB]
  have h3 : W B 0 p = ∑ j ∈ Finset.range p, (if j + 0 ∈ B then 1 else 0 : ℕ) := by
    unfold W
    apply Finset.sum_congr rfl
    intro x _
    by_cases hB : x + 0 ∈ B
    · simp only [ite_eq_left hB]
    · simp only [ite_eq_right hB]
  rw [h1, h3]
  exact h2

/-! ## Two-sided density of a set of integers with periodic parts -/

/-- If the non-negative and negative parts of `S ⊆ ℤ` are `p`-periodic with the same count per
period, then `S` has two-sided density `count / p`. -/
lemma int_density_of_periodic (S : Set ℤ) (p : ℕ) (hp : 0 < p)
    (hpos : PerSet (natPos S) p) (hneg : PerSet (natNeg S) p)
    (hc : W (natNeg S) 0 p = W (natPos S) 0 p) :
    HasIntDensity S ((W (natPos S) 0 p : ℝ) / p) := by
  unfold HasIntDensity
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have main : ∀ N : ℕ,
      (W (natPos S) 0 p : ℝ) / p - 2 * (p : ℝ) / (2 * (N : ℝ) + 1) ≤
        ((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) / (2 * (N : ℝ) + 1) ∧
      ((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) / (2 * (N : ℝ) + 1) ≤
        (W (natPos S) 0 p : ℝ) / p + 2 * (p : ℝ) / (2 * (N : ℝ) + 1) := by
    intro N
    have hsplit := ncard_Icc_split S N
    rw [ncard_inter_Iio, ncard_inter_Iio] at hsplit
    obtain ⟨a1, a2⟩ := W_bounds hp hpos (N + 1)
    obtain ⟨b1, b2⟩ := W_bounds hp hneg N
    rw [hc] at b1 b2
    have hT : ((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) =
        (W (natPos S) 0 (N + 1) : ℝ) + (W (natNeg S) 0 N : ℝ) := by
      rw [hsplit]; push_cast; ring
    have a1r : (W (natPos S) 0 p : ℝ) * ((N : ℝ) + 1) ≤
        ((W (natPos S) 0 (N + 1) : ℝ) + p) * p := by exact_mod_cast a1
    have a2r : (W (natPos S) 0 (N + 1) : ℝ) * p ≤
        (W (natPos S) 0 p : ℝ) * ((N : ℝ) + 1) + (p : ℝ) * p := by exact_mod_cast a2
    have b1r : (W (natPos S) 0 p : ℝ) * (N : ℝ) ≤
        ((W (natNeg S) 0 N : ℝ) + p) * p := by exact_mod_cast b1
    have b2r : (W (natNeg S) 0 N : ℝ) * p ≤
        (W (natPos S) 0 p : ℝ) * (N : ℝ) + (p : ℝ) * p := by exact_mod_cast b2
    have hden : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
    rw [hT]
    constructor
    · rw [sub_le_iff_le_add, ← add_div, div_le_div_iff₀ hpr hden]
      nlinarith
    · rw [← sub_le_iff_le_add, ← sub_div, div_le_div_iff₀ hden hpr]
      nlinarith
  have hinf : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have h0 : Tendsto (fun N : ℕ => 2 * (p : ℝ) / (2 * (N : ℝ) + 1)) atTop (𝓝 0) :=
    hinf.const_div_atTop (2 * (p : ℝ))
  have hlow : Tendsto (fun N : ℕ => (W (natPos S) 0 p : ℝ) / p - 2 * (p : ℝ) / (2 * (N : ℝ) + 1))
      atTop (𝓝 ((W (natPos S) 0 p : ℝ) / p)) := by
    simpa using tendsto_const_nhds.sub h0
  have hup : Tendsto (fun N : ℕ => (W (natPos S) 0 p : ℝ) / p + 2 * (p : ℝ) / (2 * (N : ℝ) + 1))
      atTop (𝓝 ((W (natPos S) 0 p : ℝ) / p)) := by
    simpa using tendsto_const_nhds.add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup
    (fun N => (main N).1) (fun N => (main N).2)

/-- Two-sided density `0` for `S ⊆ ℤ` forces one-sided density `0` for its non-negative part. -/
lemma nat_density_zero_of_int {S : Set ℤ} (h : HasIntDensity S 0) :
    HasNatDensity (natPos S) 0 := by
  unfold HasNatDensity
  unfold HasIntDensity at h
  have h3 : Tendsto (fun N : ℕ =>
      3 * (((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) / (2 * (N : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using h.const_mul 3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3 ?_ ?_
  · exact Eventually.of_forall (fun N => by positivity)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hsplit := ncard_Icc_split S N
    have hle : (natPos S ∩ Set.Iio N).ncard ≤ (S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard := by
      rw [hsplit]
      have hsub : (natPos S ∩ Set.Iio N).ncard ≤ (natPos S ∩ Set.Iio (N + 1)).ncard :=
        Set.ncard_le_ncard (Set.inter_subset_inter_right _ (Set.Iio_subset_Iio (Nat.le_succ N)))
          ((Set.finite_Iio _).inter_of_right _)
      omega
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < N := by linarith
    have hden : (0 : ℝ) < 2 * (N : ℝ) + 1 := by linarith
    have hc : ((natPos S ∩ Set.Iio N).ncard : ℝ) ≤
        ((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) := by exact_mod_cast hle
    have hB0 : (0 : ℝ) ≤ ((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) := Nat.cast_nonneg _
    have h1 : (1 : ℝ) ≤ 3 * (N : ℝ) / (2 * (N : ℝ) + 1) := by
      rw [le_div_iff₀ hden]; linarith
    have key : ((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) ≤
        3 * (((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) / (2 * (N : ℝ) + 1)) * (N : ℝ) := by
      have e : 3 * (((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) / (2 * (N : ℝ) + 1)) * (N : ℝ)
          = ((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) * (3 * (N : ℝ) / (2 * (N : ℝ) + 1)) := by
        ring
      rw [e]
      calc ((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ)
          = ((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) * 1 := by ring
        _ ≤ ((S ∩ Set.Icc (-(N : ℤ)) (N : ℤ)).ncard : ℝ) * (3 * (N : ℝ) / (2 * (N : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left h1 hB0
    rw [div_le_iff₀ hNpos]
    linarith

/-! ## The sets of Problem 281 -/

/-- Integers avoiding the first `k` residue classes `a i ∈ ZMod (n i)`. -/
abbrev IntUnc (n : ℕ → ℕ) (a : (i : ℕ) → ZMod (n i)) (k : ℕ) : Set ℤ :=
  {m : ℤ | ∀ i : ℕ, i < k → (m : ZMod (n i)) ≠ a i}

lemma intUnc_congr (n : ℕ → ℕ) (a : (i : ℕ) → ZMod (n i)) (k : ℕ) {z z' : ℤ}
    (h : (P n k : ℤ) ∣ z' - z) : z ∈ IntUnc n a k ↔ z' ∈ IntUnc n a k := by
  have hcast : ∀ i, i < k → (z : ZMod (n i)) = (z' : ZMod (n i)) := by
    intro i hi
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact dvd_trans (Int.natCast_dvd_natCast.2 (n_dvd_P n hi)) h
  constructor
  · exact fun hz i hi hc => hz i hi ((hcast i hi).trans hc)
  · exact fun hz i hi hc => hz i hi ((hcast i hi).symm.trans hc)

lemma natPos_per (n : ℕ → ℕ) (a : (i : ℕ) → ZMod (n i)) (k : ℕ) :
    PerSet (natPos (IntUnc n a k)) (P n k) := by
  intro m
  show (((m + P n k : ℕ) : ℤ) ∈ IntUnc n a k) ↔ ((m : ℤ) ∈ IntUnc n a k)
  apply intUnc_congr
  exact ⟨-1, by push_cast; ring⟩

lemma natNeg_per (n : ℕ → ℕ) (a : (i : ℕ) → ZMod (n i)) (k : ℕ) :
    PerSet (natNeg (IntUnc n a k)) (P n k) := by
  intro x
  show (-(((x + P n k : ℕ) : ℤ) + 1) ∈ IntUnc n a k) ↔ (-((x : ℤ) + 1) ∈ IntUnc n a k)
  apply intUnc_congr
  exact ⟨1, by push_cast; ring⟩

lemma natNeg_count (n : ℕ → ℕ) (a : (i : ℕ) → ZMod (n i)) (k : ℕ) :
    W (natNeg (IntUnc n a k)) 0 (P n k) = W (natPos (IntUnc n a k)) 0 (P n k) := by
  apply W_reflect
  intro x hx
  show (-((x : ℤ) + 1) ∈ IntUnc n a k) ↔ (((P n k - 1 - x : ℕ) : ℤ) ∈ IntUnc n a k)
  apply intUnc_congr
  refine ⟨1, ?_⟩
  omega

lemma natPos_intUnc (n : ℕ → ℕ) (a : (i : ℕ) → ZMod (n i)) (k : ℕ) :
    natPos (IntUnc n a k) = {m : ℕ | ∀ i, i < k → (m : ZMod (n i)) ≠ a i} := by
  ext m
  simp only [natPos, Set.mem_ofPred_eq, Int.cast_natCast]

/-! ## Main theorem -/

/-- Erdős Problem 281 for sets of integers, two-sided density, residue classes in `ZMod (n i)`. -/
theorem erdos_281_int (n : ℕ → ℕ) (hn : StrictMono n) (hpos : ∀ i, 0 < n i)
    (H : ∀ a : (i : ℕ) → ZMod (n i), HasIntDensity {m : ℤ | ∀ i : ℕ, (m : ZMod (n i)) ≠ a i} 0) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : (i : ℕ) → ZMod (n i),
      ∃ d : ℝ, HasIntDensity {m : ℤ | ∀ i : ℕ, i < k → (m : ZMod (n i)) ≠ a i} d ∧ d < ε := by
  have H' : ∀ a : (i : ℕ) → ZMod (n i),
      HasNatDensity {m : ℕ | ∀ i, (m : ZMod (n i)) ≠ a i} 0 := by
    intro a
    have h := nat_density_zero_of_int (H a)
    have e : natPos {m : ℤ | ∀ i : ℕ, (m : ZMod (n i)) ≠ a i} =
        {m : ℕ | ∀ i, (m : ZMod (n i)) ≠ a i} := by
      ext m
      simp only [natPos, Set.mem_ofPred_eq, Int.cast_natCast]
    rwa [e] at h
  intro ε hε
  obtain ⟨k, hk⟩ := erdos_281_zmod n hn (hpos 0) H' ε hε
  refine ⟨k, fun a => ?_⟩
  obtain ⟨d, hd, hdens⟩ := hk a
  have hp : 0 < P n k := P_pos hpos k
  have hper := natPos_per n a k
  have hdens' : HasNatDensity (natPos (IntUnc n a k)) d := by
    rw [natPos_intUnc]; exact hdens
  have hd_eq : d = (W (natPos (IntUnc n a k)) 0 (P n k) : ℝ) / P n k :=
    tendsto_nhds_unique hdens' (density_of_periodic hp hper)
  refine ⟨d, ?_, hd⟩
  rw [hd_eq]
  exact int_density_of_periodic (IntUnc n a k) (P n k) hp hper (natNeg_per n a k)
    (natNeg_count n a k)

end Erdos281

#print axioms Erdos281.erdos_281_int
