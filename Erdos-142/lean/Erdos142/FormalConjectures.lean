import Mathlib

/-!
# Two facts about the formal statement of Erdős Problem 142

This file concerns the *formal* statement of Erdős Problem 142 in
google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/142.lean`, commit 1c24583):

* (A) `Erdos142.erdos_142_statement_unsatisfiable`: the main statement `erdos_142` asks for a
  single function `answer : ℕ → ℝ`, independent of `k`, with `r_k ~ answer` for every `k`.
  No such function exists (compare `k = 1`, where `r_1(N) = N` in the formal-conjectures
  convention, and `k = 2`, where `r_2(N) = 1`).
  The same holds for `erdos_142.variants.isTheta`
  (`Erdos142.erdos_142_isTheta_statement_unsatisfiable`).
* (B) `Erdos142.erdos_142_variants_lower_of_quantitative`: the variant
  `erdos_142.variants.lower` (`r_k(N) = o(N / log N)` for `k > 1`) follows from the
  `QuantitativeDensityTheorem` formalized in openai/math
  (`lean/OAI/Combinatorics/Progressions/Model.lean`, commit 4eaee87).

The definitions below are verbatim copies of the upstream ones, only moved into the namespaces
`FC` and `OAI.Erdos3`.
-/

open Filter Asymptotics

/-! Verbatim copies of the definitions of google-deepmind/formal-conjectures
(FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean, commit 1c24583), in namespace `FC`. -/
namespace FC
variable {α : Type*} [AddCommMonoid α]

def IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, IsAPOfLengthWith s l a d

def IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, IsAPOfLength t l → l ≤ 1

noncomputable def maxCard (k : ℕ) (N : ℕ) : ℕ :=
  sSup {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N) (_ : IsAPOfLengthFree (S : Set ℕ) k)}
end FC

/-! Verbatim copies of the definitions of openai/math
(lean/OAI/Combinatorics/Progressions/Model.lean, commit 4eaee87). -/
namespace OAI.Erdos3
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A
def APFree (A : Set ℕ) (k : ℕ) : Prop := ¬ HasAP A k
noncomputable def extremalNumber (k N : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 N).powerset).filter fun S : Finset ℕ ↦ APFree (S : Set ℕ) k).sup
    Finset.card
def QuantitativeDensityBound (k : ℕ) : Prop :=
  ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
    ∀ N : ℕ, 3 ≤ N →
      (extremalNumber k N : ℝ) ≤
        C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))
def QuantitativeDensityTheorem : Prop :=
  ∀ k : ℕ, 3 ≤ k → QuantitativeDensityBound k
end OAI.Erdos3

namespace Erdos142

/-! ### Basic facts about `FC.maxCard` -/

/-- The family of cardinalities defining `FC.maxCard k N` is bounded above by `N`. -/
lemma maxCard_set_bddAbove (k N : ℕ) :
    BddAbove {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
      (_ : FC.IsAPOfLengthFree (S : Set ℕ) k)} := by
  refine ⟨N, ?_⟩
  rintro n ⟨S, hS, _, rfl⟩
  exact (Finset.card_le_card hS).trans (by simp)

/-- Every member of the family defining `FC.maxCard k N` is at most `FC.maxCard k N`. -/
lemma card_le_maxCard {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hfree : FC.IsAPOfLengthFree (S : Set ℕ) k) : S.card ≤ FC.maxCard k N :=
  le_csSup (maxCard_set_bddAbove k N) ⟨S, hS, hfree, rfl⟩

/-- `r_1(N) = N` in the formal-conjectures convention (APs of length ≤ 1 are trivial). -/
theorem maxCard_one (N : ℕ) : FC.maxCard 1 N = N := by
  unfold FC.maxCard
  apply IsGreatest.csSup_eq
  refine ⟨⟨Finset.Icc 1 N, subset_rfl, ?_, by simp⟩, ?_⟩
  · intro t _ _
    simp
  · rintro n ⟨S, hS, _, rfl⟩
    exact (Finset.card_le_card hS).trans (by simp)

/-- A two-element set of naturals is an arithmetic progression of length `2`. -/
lemma isAPOfLength_pair {a b : ℕ} (hab : a < b) :
    FC.IsAPOfLength ({a, b} : Set ℕ) ((2 : ℕ) : ℕ∞) := by
  refine ⟨a, b - a, ?_, ?_⟩
  · change ({a, b} : Set ℕ).encard = ((2 : ℕ) : ℕ∞)
    rw [Set.encard_pair hab.ne]
    rfl
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      have hn' : n < 2 := by exact_mod_cast hn
      interval_cases n
      · left; simp
      · right; omega

/-- `r_2(N) = 1` for `N ≥ 1`. -/
theorem maxCard_two (N : ℕ) (hN : 1 ≤ N) : FC.maxCard 2 N = 1 := by
  unfold FC.maxCard
  apply IsGreatest.csSup_eq
  refine ⟨⟨{1}, ?_, ?_, by simp⟩, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_Icc.2 ⟨le_rfl, hN⟩
  · -- `{1}` has no subset of cardinality `2`
    rintro t hts ⟨a, d, hcard, -⟩
    have h1 : t.encard ≤ ({1} : Set ℕ).encard := Set.encard_le_encard (by simpa using hts)
    rw [Set.encard_singleton] at h1
    have h2 : t.encard = ((2 : ℕ) : ℕ∞) := hcard
    rw [h2] at h1
    exact h1
  · rintro n ⟨S, hS, hfree, rfl⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcon
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · have hsub : ({a, b} : Set ℕ) ⊆ (S : Set ℕ) := by
        intro x hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hb
      have := hfree _ hsub (isAPOfLength_pair hlt)
      exact absurd this (by norm_num)
    · have hsub : ({b, a} : Set ℕ) ⊆ (S : Set ℕ) := by
        intro x hx
        rcases hx with rfl | rfl
        · exact hb
        · exact ha
      have := hfree _ hsub (isAPOfLength_pair hlt)
      exact absurd this (by norm_num)

/-! ### (A) The formal statement `erdos_142` is unsatisfiable -/

/-- (A) The formal statement `erdos_142` of formal-conjectures asks for ONE function `answer`
with `r_k ~ answer` for EVERY `k`; no such function exists (compare `k = 1` and `k = 2`). -/
theorem erdos_142_statement_unsatisfiable :
    ¬ ∃ f : ℕ → ℝ, ∀ k : ℕ, (fun N => (FC.maxCard k N : ℝ)) ~[atTop] f := by
  rintro ⟨f, hf⟩
  have h1 : (fun N : ℕ => (N : ℝ)) ~[atTop] f := by
    have := hf 1
    simpa [maxCard_one] using this
  have h2 : (fun _ : ℕ => (1 : ℝ)) ~[atTop] f := by
    refine (hf 2).congr_left ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp [maxCard_two N hN]
  have h3 : (fun _ : ℕ => (1 : ℝ)) ~[atTop] (fun N : ℕ => (N : ℝ)) := h2.trans h1.symm
  have h4 : Tendsto (fun N : ℕ => (N : ℝ)) atTop (nhds 1) := h3.tendsto_nhds tendsto_const_nhds
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_natCast_atTop_atTop 1 h4

/-- (A') The same defect affects `erdos_142.variants.isTheta` (whose `answer` is also independent
of `k`): no single function is `Θ` of `r_k` for every `k`. -/
theorem erdos_142_isTheta_statement_unsatisfiable :
    ¬ ∃ f : ℕ → ℝ, ∀ k : ℕ, (fun N => (FC.maxCard k N : ℝ)) =Θ[atTop] f := by
  rintro ⟨f, hf⟩
  have h1 : (fun N : ℕ => (N : ℝ)) =Θ[atTop] f := by
    have := hf 1
    simpa [maxCard_one] using this
  have he : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop] (fun N => (FC.maxCard 2 N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp [maxCard_two N hN]
  have h2 : (fun _ : ℕ => (1 : ℝ)) =Θ[atTop] f := he.trans_isTheta (hf 2)
  have h3 : (fun N : ℕ => (N : ℝ)) =Θ[atTop] (fun _ : ℕ => (1 : ℝ)) := h1.trans h2.symm
  obtain ⟨c, hc⟩ := h3.1.bound
  have hgt : ∀ᶠ N : ℕ in atTop, c < (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop c
  obtain ⟨N, hN1, hN2⟩ := (hc.and hgt).exists
  simp only [Real.norm_natCast, norm_one, mul_one] at hN1
  linarith

/-! ### Bridge between the two definitions of `r_k(N)` -/

/-- The set `{a + n • d | n < k}` as the image of `Finset.range k`. -/
lemma apSet_eq_image (a d k : ℕ) :
    {a + n • d | (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞))} =
      (fun n => a + n * d) '' ((Finset.range k : Finset ℕ) : Set ℕ) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio, Nat.cast_lt,
    smul_eq_mul, exists_prop]

/-- For `k ≥ 2`, the formal-conjectures notion of `k`-AP-freeness agrees with the openai/math
one. -/
lemma isAPOfLengthFree_iff_apFree (S : Set ℕ) (k : ℕ) (hk : 2 ≤ k) :
    FC.IsAPOfLengthFree S (k : ℕ∞) ↔ OAI.Erdos3.APFree S k := by
  constructor
  · rintro hfree ⟨a, d, hd, hmem⟩
    set t : Set ℕ := {a + n • d | (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞))} with ht
    have hts : t ⊆ S := by
      rintro x ⟨n, hn, rfl⟩
      have hn' : n < k := by exact_mod_cast hn
      simpa [smul_eq_mul] using hmem n hn'
    have hinj : Set.InjOn (fun n => a + n * d) ((Finset.range k : Finset ℕ) : Set ℕ) := by
      intro n _ m _ hnm
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hnm)
    have hcard : ENat.card t = (k : ℕ∞) := by
      change t.encard = (k : ℕ∞)
      rw [ht, apSet_eq_image, hinj.encard_image, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_range]
    have hle : (k : ℕ∞) ≤ 1 := hfree t hts ⟨a, d, hcard, rfl⟩
    have hle' : k ≤ 1 := by exact_mod_cast hle
    omega
  · intro hfree t hts ⟨a, d, hcard, heq⟩
    rcases Nat.eq_zero_or_pos d with hd | hd
    · have hsub : t ⊆ {a} := by
        rw [heq]
        rintro x ⟨n, -, rfl⟩
        simp [hd]
      calc (k : ℕ∞) = t.encard := hcard.symm
        _ ≤ ({a} : Set ℕ).encard := Set.encard_le_encard hsub
        _ = 1 := Set.encard_singleton a
    · refine absurd ⟨a, d, hd, fun i hi => hts ?_⟩ hfree
      rw [heq]
      exact ⟨i, by exact_mod_cast hi, by simp [smul_eq_mul]⟩

/-- Bridge: for `k ≥ 2` the two definitions of `r_k(N)` agree. -/
theorem maxCard_eq_extremalNumber (k N : ℕ) (hk : 2 ≤ k) :
    FC.maxCard k N = OAI.Erdos3.extremalNumber k N := by
  classical
  unfold OAI.Erdos3.extremalNumber
  apply le_antisymm
  · unfold FC.maxCard
    apply csSup_le
    · refine ⟨0, ∅, Finset.empty_subset _, ?_, Finset.card_empty⟩
      rw [isAPOfLengthFree_iff_apFree _ k hk]
      rintro ⟨a, d, -, hmem⟩
      simpa using hmem 0 (by omega)
    · rintro n ⟨S, hS, hfree, rfl⟩
      refine Finset.le_sup (f := Finset.card) ?_
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hS, (isAPOfLengthFree_iff_apFree _ k hk).1 hfree⟩
  · apply Finset.sup_le
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    exact card_le_maxCard hS.1 ((isAPOfLengthFree_iff_apFree _ k hk).2 hS.2)

/-! ### (B) `erdos_142.variants.lower` from the quantitative density theorem -/

/-- If `|u N| ≤ N * ψ N` eventually and `ψ N * log N → 0`, then `u = o(N / log N)`. -/
lemma isLittleO_div_log_of_bound {u ψ : ℕ → ℝ}
    (hu : ∀ᶠ N : ℕ in atTop, |u N| ≤ (N : ℝ) * ψ N)
    (hψ : Tendsto (fun N : ℕ => ψ N * Real.log N) atTop (nhds 0)) :
    u =o[atTop] (fun N : ℕ => (N : ℝ) / Real.log N) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have h1 : ∀ᶠ N : ℕ in atTop, ψ N * Real.log N < c := hψ.eventually (gt_mem_nhds hc)
  filter_upwards [hu, h1, eventually_ge_atTop 3] with N hN1 hN2 hN3
  have hN : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hpos : 0 ≤ (N : ℝ) / Real.log N := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  calc |u N| ≤ (N : ℝ) * ψ N := hN1
    _ = (N : ℝ) / Real.log N * (ψ N * Real.log N) := by field_simp
    _ ≤ (N : ℝ) / Real.log N * c := mul_le_mul_of_nonneg_left hN2.le hpos
    _ = c * ((N : ℝ) / Real.log N) := by ring

/-- `z - c * z ^ (1 + η) → -∞` as `z → ∞`. -/
lemma tendsto_sub_rpow_atBot (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    Tendsto (fun z : ℝ => z - c * z ^ (1 + η)) atTop atBot := by
  have ha : Tendsto (fun z : ℝ => z ^ η) atTop atTop := tendsto_rpow_atTop hη
  have hb : Tendsto (fun z : ℝ => c * z ^ η + (-1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (ha.const_mul_atTop hc)
  have hc' : Tendsto (fun z : ℝ => z * (c * z ^ η + (-1))) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ hb
  have hd : Tendsto (fun z : ℝ => -(z * (c * z ^ η + (-1)))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hc'
  refine hd.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with z hz
  rw [Real.rpow_add hz, Real.rpow_one]
  ring

/-- `C * exp(-c (log log N)^(1+η)) * log N → 0`. -/
lemma tendsto_quantitative_factor (C c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    Tendsto (fun N : ℕ =>
      C * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) * Real.log N) atTop (nhds 0) := by
  have h1 := tendsto_sub_rpow_atBot c η hc hη
  have h2 : Tendsto (fun z : ℝ => C * Real.exp (z - c * z ^ (1 + η))) atTop (nhds 0) := by
    have := (Real.tendsto_exp_atBot.comp h1).const_mul C
    simpa using this
  have h3 : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have h4 := h2.comp h3
  have h5 : Tendsto (fun x : ℝ =>
      C * Real.exp (-c * (Real.log (Real.log x)) ^ (1 + η)) * Real.log x) atTop (nhds 0) := by
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    simp only [Function.comp_apply]
    rw [neg_mul, sub_eq_add_neg, Real.exp_add, Real.exp_log hlog]
    ring
  exact h5.comp tendsto_natCast_atTop_atTop

/-- (B) `erdos_142.variants.lower` (formal-conjectures): `r_k(N) = o(N / log N)` for `k > 1`,
assuming the quantitative density theorem formalized in openai/math. -/
theorem erdos_142_variants_lower_of_quantitative
    (h : OAI.Erdos3.QuantitativeDensityTheorem) (k : ℕ) (hk : 1 < k) :
    (fun N => (FC.maxCard k N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ) / (N : ℝ).log) := by
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · -- `k = 2`: `r_2(N) = 1`
    have hk2 : k = 2 := by omega
    subst hk2
    refine isLittleO_div_log_of_bound (ψ := fun N : ℕ => 1 / (N : ℝ)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      rw [maxCard_two N hN]
      simp only [Nat.cast_one, abs_one]
      rw [mul_one_div, div_self hNpos.ne']
    · have h0 : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (nhds 0) :=
        (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
      refine h0.congr (fun N => ?_)
      ring
  · -- `k ≥ 3`: the quantitative density bound
    obtain ⟨C, c, η, -, hc, hη, hbound⟩ := h k hk3
    refine isLittleO_div_log_of_bound
      (ψ := fun N : ℕ => C * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))) ?_ ?_
    · filter_upwards [eventually_ge_atTop 3] with N hN
      rw [abs_of_nonneg (Nat.cast_nonneg _), maxCard_eq_extremalNumber k N (by omega)]
      calc (OAI.Erdos3.extremalNumber k N : ℝ)
          ≤ C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) := hbound N hN
        _ = (N : ℝ) * (C * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))) := by ring
    · exact tendsto_quantitative_factor C c η hc hη

end Erdos142

#print axioms Erdos142.maxCard_one
#print axioms Erdos142.maxCard_two
#print axioms Erdos142.erdos_142_statement_unsatisfiable
#print axioms Erdos142.erdos_142_isTheta_statement_unsatisfiable
#print axioms Erdos142.maxCard_eq_extremalNumber
#print axioms Erdos142.erdos_142_variants_lower_of_quantitative
