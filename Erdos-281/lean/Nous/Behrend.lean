import Nous.Erdos281
import Nous.Rogers

/-!
# Rogers' theorem in density form, and "the homogeneous choice controls all choices"

Combines the finite Rogers theorem (`Rogers.rogers_uncovered`) with the density lemma for
periodic sets from `Nous.Erdos281`:

* `Erdos281.density_le_homogeneous`: for every choice of residues `a`, the density of the set
  uncovered by the first `k` congruences is at most the density for the homogeneous choice `a = 0`.
* `Erdos281.uniform_of_homogeneous`: if the uncovered densities of the homogeneous choice tend to
  `0` (the moduli form a Behrend sequence), the uniform conclusion of Erdős Problem 281 holds.
-/

open Filter Topology

namespace Erdos281

/-- `cU n a k` (number of uncovered residues mod `P n k`) as the cardinality of a filter. -/
lemma cU_eq_card (n a : ℕ → ℕ) (k : ℕ) :
    cU n a k =
      ((Finset.range (P n k)).filter (fun m => ∀ i, i < k → ¬ m ≡ a i [MOD n i])).card := by
  unfold cU W
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _
  have hiff : (x + 0 ∈ Unc n a k) ↔ (∀ i, i < k → ¬ x ≡ a i [MOD n i]) := by
    rw [add_zero]; rfl
  by_cases h : ∀ i, i < k → ¬ x ≡ a i [MOD n i]
  · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h (hiff.1 hc)), ite_eq_right h]

/-- Rogers' theorem for the counts `cU`: the homogeneous choice leaves the most uncovered. -/
lemma cU_le_homogeneous (n : ℕ → ℕ) (hpos : ∀ i, 0 < n i) (a : ℕ → ℕ) (k : ℕ) :
    cU n a k ≤ cU n (fun _ => 0) k := by
  rw [cU_eq_card, cU_eq_card]
  have h := Rogers.rogers_uncovered k n a (P n k) (P_pos hpos k) (fun i hi => n_dvd_P n hi)
  have e : (Finset.range (P n k)).filter
        (fun m => ∀ i, i < k → ¬ m ≡ (fun _ => 0) i [MOD n i]) =
      (Finset.range (P n k)).filter (fun m => ∀ i, i < k → ¬ n i ∣ m) := by
    apply Finset.filter_congr
    intro m _
    constructor
    · intro h i hi hd; exact h i hi (Nat.modEq_zero_iff_dvd.2 hd)
    · intro h i hi hc; exact h i hi (Nat.modEq_zero_iff_dvd.1 hc)
  rw [e]
  exact h

/-- Rogers in density form: every choice leaves at most as much uncovered as the homogeneous one. -/
theorem density_le_homogeneous (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (a : ℕ → ℕ) (k : ℕ)
    (d d₀ : ℝ) (hd : HasNatDensity (Unc n a k) d) (hd₀ : HasNatDensity (Unc n (fun _ => 0) k) d₀) :
    d ≤ d₀ := by
  have hpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (Nat.succ_pos i) (succ_le_n hn hn0 i)
  have h1 : d = (cU n a k : ℝ) / P n k := tendsto_nhds_unique hd (density_unc hpos a k)
  have h2 : d₀ = (cU n (fun _ => 0) k : ℝ) / P n k :=
    tendsto_nhds_unique hd₀ (density_unc hpos _ k)
  rw [h1, h2]
  have hP : (0 : ℝ) < P n k := by exact_mod_cast P_pos hpos k
  apply div_le_div_of_nonneg_right _ hP.le
  exact_mod_cast cU_le_homogeneous n hpos a k

/-- If the finite-level uncovered densities of the homogeneous choice `a = 0` tend to `0`
(i.e. the moduli form a Behrend sequence), then the uniform conclusion of Problem 281 holds. -/
theorem uniform_of_homogeneous (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n (fun _ => 0) k) d) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d := by
  have hpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (Nat.succ_pos i) (succ_le_n hn hn0 i)
  intro ε hε
  obtain ⟨k, d₀, hd₀, hdens₀⟩ := hB ε hε
  refine ⟨k, fun a => ⟨(cU n a k : ℝ) / P n k, ?_, density_unc hpos a k⟩⟩
  exact lt_of_le_of_lt
    (density_le_homogeneous n hn hn0 a k _ d₀ (density_unc hpos a k) hdens₀) hd₀

end Erdos281

#print axioms Erdos281.density_le_homogeneous
#print axioms Erdos281.uniform_of_homogeneous
