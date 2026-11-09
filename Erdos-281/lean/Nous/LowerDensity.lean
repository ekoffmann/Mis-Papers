import Nous.Erdos281

/-!
# Erdős Problem 281 — lower-density strengthening

If the uniform conclusion of Problem 281 fails, then some choice of residues leaves uncovered a
set of positive LOWER density.  Hence the hypothesis of the problem can be weakened to
"for every choice of residues the uncovered set has lower density `0`".

The proof repeats the finitary argument of `Nous.Erdos281`, with Markov's inequality replaced by
an elementary one-sided maximal inequality on a period (`maximal_ineq`), proved by a greedy
covering argument.
-/

open Filter Topology

namespace Erdos281

/-! ## Window additivity -/

/-- Additivity of window counts: `[s, s+L₁+L₂) = [s, s+L₁) ⊔ [s+L₁, s+L₁+L₂)`. -/
lemma W_add (S : Set ℕ) (s L₁ L₂ : ℕ) : W S s (L₁ + L₂) = W S s L₁ + W S (s + L₁) L₂ := by
  classical
  unfold W
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have e : L₁ + x + s = x + (s + L₁) := by ring
  rw [e]

/-- A window made of `m` full periods contains `m` times the per-period count. -/
lemma W_mul_period {S : Set ℕ} {q : ℕ} (hper : PerSet S q) (s m : ℕ) :
    W S s (m * q) = m * W S 0 q := by
  induction m with
  | zero => simp [W]
  | succ m ih =>
    have e : (m + 1) * q = m * q + q := by ring
    rw [e, W_add, ih, W_per hper (s + m * q)]
    ring

/-- Lower bound for the count of a `q`-periodic set in an arbitrary window of length `N`. -/
lemma W_lower {S : Set ℕ} {q : ℕ} (hq : 0 < q) (hper : PerSet S q) (s N : ℕ) :
    (W S 0 q : ℝ) / q * N - q ≤ (W S s N : ℝ) := by
  have h1 : (N / q) * W S 0 q ≤ W S s N := by
    have e : N = (N / q) * q + N % q := (Nat.div_add_mod' N q).symm
    calc (N / q) * W S 0 q = W S s ((N / q) * q) := (W_mul_period hper s _).symm
      _ ≤ W S s ((N / q) * q) + W S (s + (N / q) * q) (N % q) := Nat.le_add_right _ _
      _ = W S s ((N / q) * q + N % q) := (W_add S s _ _).symm
      _ = W S s N := by rw [← e]
  have hc : W S 0 q ≤ q := W_le _ _ _
  have h2 : N < (N / q + 1) * q := by
    have e := Nat.div_add_mod' N q
    have hlt := Nat.mod_lt N hq
    nlinarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have h1r : ((N / q : ℕ) : ℝ) * (W S 0 q : ℝ) ≤ W S s N := by exact_mod_cast h1
  have h2r : (N : ℝ) < (((N / q : ℕ) : ℝ) + 1) * q := by exact_mod_cast h2
  have hcr : (W S 0 q : ℝ) ≤ q := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ W S 0 q := Nat.cast_nonneg _
  have h3 : (W S 0 q : ℝ) / q * N ≤ (W S 0 q : ℝ) / q * ((((N / q : ℕ) : ℝ) + 1) * q) :=
    mul_le_mul_of_nonneg_left h2r.le (by positivity)
  have e2 : (W S 0 q : ℝ) / q * ((((N / q : ℕ) : ℝ) + 1) * q)
      = (W S 0 q : ℝ) * (((N / q : ℕ) : ℝ) + 1) := by
    field_simp
  rw [e2] at h3
  nlinarith

/-! ## The maximal inequality -/

open Classical in
lemma card_filter_Ico_le (B : ℕ → Prop) {s s' p : ℕ} :
    ((Finset.Ico s p).filter B).card ≤ (s' - s) + ((Finset.Ico s' p).filter B).card := by
  have hsub : (Finset.Ico s p).filter B ⊆ Finset.Ico s s' ∪ (Finset.Ico s' p).filter B := by
    intro t ht
    have ht' := Finset.mem_filter.1 ht
    have ht1 := Finset.mem_Ico.1 ht'.1
    by_cases h : t < s'
    · exact Finset.mem_union_left _ (Finset.mem_Ico.2 ⟨ht1.1, h⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨not_lt.1 h, ht1.2⟩, ht'.2⟩)
  calc ((Finset.Ico s p).filter B).card
      ≤ (Finset.Ico s s' ∪ (Finset.Ico s' p).filter B).card := Finset.card_le_card hsub
    _ ≤ (Finset.Ico s s').card + ((Finset.Ico s' p).filter B).card := Finset.card_union_le _ _
    _ = (s' - s) + ((Finset.Ico s' p).filter B).card := by rw [Nat.card_Ico]

open Classical in
lemma card_filter_Ico_of_not (B : ℕ → Prop) {s p : ℕ} (h : ¬ B s) :
    ((Finset.Ico s p).filter B).card ≤ ((Finset.Ico (s + 1) p).filter B).card := by
  apply Finset.card_le_card
  intro t ht
  have ht' := Finset.mem_filter.1 ht
  have ht1 := Finset.mem_Ico.1 ht'.1
  have hne : t ≠ s := fun e => h (e ▸ ht'.2)
  exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨by omega, ht1.2⟩, ht'.2⟩

open Classical in
/-- Greedy covering: for `s + d = p`, the bad shifts in `[s, p)` are paid for by the points of `E`
in the window `[s, 2p)`. -/
lemma maximal_aux {E : Set ℕ} {p : ℕ} (lam : ℝ) (hlam : 0 < lam) :
    ∀ d s : ℕ, s + d = p →
      lam * (((Finset.Ico s p).filter
        (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ))).card : ℝ)
        ≤ (W E s (p + d) : ℝ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro s hs
    rcases Nat.eq_zero_or_pos d with hd | hd
    · have hsp : s = p := by omega
      rw [hsp]
      simp
    · by_cases hBs : ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E s L : ℝ)
      · obtain ⟨L, hL1, hLp, hLW⟩ := hBs
        by_cases hcase : d ≤ L
        · -- the witness window reaches `p`
          have hcard : ((Finset.Ico s p).filter
              (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ))).card ≤ L := by
            calc ((Finset.Ico s p).filter
                  (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ))).card
                ≤ (Finset.Ico s p).card := Finset.card_filter_le _ _
              _ = p - s := Nat.card_Ico _ _
              _ ≤ L := by omega
          have hW : W E s L ≤ W E s (p + d) := by
            have e : p + d = L + (p + d - L) := by omega
            rw [e, W_add E s L (p + d - L)]
            exact Nat.le_add_right _ _
          have hcardr : (((Finset.Ico s p).filter
              (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ))).card : ℝ)
              ≤ (L : ℝ) := by exact_mod_cast hcard
          have hWr : (W E s L : ℝ) ≤ (W E s (p + d) : ℝ) := by exact_mod_cast hW
          have h1 := mul_le_mul_of_nonneg_left hcardr hlam.le
          linarith
        · -- the witness window ends before `p`: recurse at `s + L`
          have hLd : L < d := not_le.1 hcase
          have hih := ih (d - L) (by omega) (s + L) (by omega)
          have hcard := card_filter_Ico_le
            (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ))
            (s := s) (s' := s + L) (p := p)
          have e : p + d = L + (p + (d - L)) := by omega
          have hW : W E s (p + d) = W E s L + W E (s + L) (p + (d - L)) := by
            rw [e, W_add E s L (p + (d - L))]
          have hsub : s + L - s = L := by omega
          rw [hsub] at hcard
          have hcardr : (((Finset.Ico s p).filter
              (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ))).card : ℝ)
              ≤ (L : ℝ) + (((Finset.Ico (s + L) p).filter
              (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ))).card : ℝ) := by
            exact_mod_cast hcard
          have h1 := mul_le_mul_of_nonneg_left hcardr hlam.le
          rw [hW]
          push_cast
          linarith
      · -- `s` is not bad: drop it
        have hih := ih (d - 1) (by omega) (s + 1) (by omega)
        have hcard := card_filter_Ico_of_not
          (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ)) (p := p) hBs
        have e : p + d = 1 + (p + (d - 1)) := by omega
        have hW : W E (s + 1) (p + (d - 1)) ≤ W E s (p + d) := by
          rw [e, W_add E s 1 (p + (d - 1))]
          exact Nat.le_add_left _ _
        have hcardr : (((Finset.Ico s p).filter
            (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ))).card : ℝ)
            ≤ (((Finset.Ico (s + 1) p).filter
            (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ))).card : ℝ) := by
          exact_mod_cast hcard
        have hWr : (W E (s + 1) (p + (d - 1)) : ℝ) ≤ (W E s (p + d) : ℝ) := by exact_mod_cast hW
        have h1 := mul_le_mul_of_nonneg_left hcardr hlam.le
        linarith

set_option linter.unusedVariables false in
open Classical in
/-- Elementary one-sided maximal inequality on a period: if `E` is `p`-periodic, the number of
shifts `t < p` for which SOME window length `1 ≤ L ≤ p` has more than `lam * L` points of `E`
in `[t, t+L)` is at most `(number of points of E in two periods) / lam`. -/
theorem maximal_ineq {E : Set ℕ} {p : ℕ} (hp : 0 < p) (hper : PerSet E p) (lam : ℝ) (hlam : 0 < lam) :
    lam * (((Finset.range p).filter
        (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ))).card : ℝ)
      ≤ 2 * (W E 0 p : ℝ) := by
  have h := maximal_aux (E := E) (p := p) lam hlam p 0 (by omega)
  rw [Finset.range_eq_Ico]
  have h2 : W E 0 (p + p) = 2 * W E 0 p := by
    have h3 := cnt_add_period hper 2 0
    have h0 : W E 0 0 = 0 := by simp [W]
    rw [add_zero, h0, add_zero] at h3
    rw [← h3]
    congr 1
    ring
  rw [h2] at h
  push_cast at h
  exact h

/-- Instance-free form of the maximal inequality. -/
lemma maximal_card {E : Set ℕ} {p : ℕ} (hp : 0 < p) (hper : PerSet E p) (lam : ℝ) (hlam : 0 < lam)
    (F : Finset ℕ)
    (hF : ∀ t ∈ F, t < p ∧ ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ)) :
    lam * (F.card : ℝ) ≤ 2 * (W E 0 p : ℝ) := by
  classical
  have hM := maximal_ineq hp hper lam hlam
  have hsub : F ⊆ (Finset.range p).filter
      (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ)) := by
    intro t ht
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hF t ht).1, (hF t ht).2⟩
  have hcard : (F.card : ℝ) ≤ (((Finset.range p).filter
      (fun t => ∃ L : ℕ, 1 ≤ L ∧ L ≤ p ∧ lam * (L : ℝ) < (W E t L : ℝ))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h1 := mul_le_mul_of_nonneg_left hcard hlam.le
  exact h1.trans hM

/-! ## Bad shifts for the maximal version (a single level `κ`) -/

/-- the shift `t` is bad at depth `k`: SOME window `[t, t+L)`, `1 ≤ L ≤ P n k`, contains more
than `lam * L` points uncovered at level `κ` but covered at level `k`. -/
def BadM (n a : ℕ → ℕ) (κ : ℕ) (lam : ℝ) (k t : ℕ) : Prop :=
  ∃ L : ℕ, 1 ≤ L ∧ L ≤ P n k ∧ lam * (L : ℝ) < (W (Dset n a κ k) t L : ℝ)

/-- the shift `t` is good at depth `k`. -/
def GoodM (n a : ℕ → ℕ) (κ : ℕ) (lam : ℝ) (k t : ℕ) : Prop :=
  κ ≤ k → ¬ BadM n a κ lam k t

lemma badM_persist {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (a : ℕ → ℕ) (κ : ℕ) (lam : ℝ)
    {k k' t : ℕ} (hk : κ ≤ k) (hkk : k ≤ k')
    (h : BadM n a κ lam k (t % P n k)) : BadM n a κ lam k' t := by
  classical
  obtain ⟨L, hL1, hLp, hLW⟩ := h
  refine ⟨L, hL1, hLp.trans (Nat.le_of_dvd (P_pos hpos k') (P_dvd n hkk)), ?_⟩
  have hle : W (Dset n a κ k) (t % P n k) L ≤ W (Dset n a κ k') t L := by
    unfold W
    apply Finset.sum_le_sum
    intro x _
    have h1 : x + t % P n k ≡ x + t [MOD P n k] := (Nat.mod_modEq t _).add_left x
    have hA : x + t % P n k ∈ Unc n a κ ↔ x + t ∈ Unc n a κ :=
      unc_congr n a (h1.of_dvd (P_dvd n hk))
    have hB : x + t % P n k ∈ Unc n a k ↔ x + t ∈ Unc n a k := unc_congr n a h1
    have hsub : x + t % P n k ∈ Dset n a κ k → x + t ∈ Dset n a κ k' := by
      intro hx
      exact ⟨hA.1 hx.1, fun hc => hx.2 (hB.2 (unc_anti n a hkk hc))⟩
    split_ifs with h2 h3 h3
    · exact le_rfl
    · exact absurd (hsub h2) h3
    · exact Nat.zero_le _
    · exact le_rfl
  have hc : (W (Dset n a κ k) (t % P n k) L : ℝ) ≤ W (Dset n a κ k') t L := by
    exact_mod_cast hle
  linarith

lemma goodM_parent {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (a : ℕ → ℕ) (κ : ℕ) (lam : ℝ)
    {i k t : ℕ} (hik : i ≤ k) (h : GoodM n a κ lam k t) : GoodM n a κ lam i (t % P n i) :=
  fun hi hbad => h (hi.trans hik) (badM_persist hpos a κ lam hi hik hbad)

lemma Dset_count {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (a : ℕ → ℕ) {c k : ℕ} (hk : c ≤ k) :
    (W (Dset n a c k) 0 (P n k) : ℝ)
      = (P n k : ℝ) * ((cU n a c : ℝ) / P n c - (cU n a k : ℝ) / P n k) := by
  have hPk : (0 : ℝ) < P n k := by exact_mod_cast P_pos hpos k
  have h1 : W (Dset n a c k) 0 (P n k) + W (Unc n a k) 0 (P n k)
      = W (Unc n a c) 0 (P n k) := W_diff (unc_anti n a hk) 0 (P n k)
  have h2 := cnt_unc_period hpos a hk
  have h3 : (W (Dset n a c k) 0 (P n k) : ℝ) + (cU n a k : ℝ)
      = W (Unc n a c) 0 (P n k) := by exact_mod_cast h1
  rw [h2] at h3
  have h4 : (P n k : ℝ) * ((cU n a k : ℝ) / P n k) = cU n a k := by
    field_simp
  rw [mul_sub, h4]
  linarith

lemma goodM_exists {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (a : ℕ → ℕ) (κ : ℕ) (lam : ℝ)
    (hlam : 0 < lam)
    (hρ : ∀ k, κ ≤ k → (cU n a κ : ℝ) / P n κ - (cU n a k : ℝ) / P n k ≤ lam / 4) (k : ℕ) :
    ∃ t, t < P n k ∧ GoodM n a κ lam k t := by
  by_cases hk : κ ≤ k
  · by_contra hcon
    push Not at hcon
    have hall : ∀ t ∈ Finset.range (P n k), t < P n k ∧
        ∃ L : ℕ, 1 ≤ L ∧ L ≤ P n k ∧ lam * (L : ℝ) < (W (Dset n a κ k) t L : ℝ) := by
      intro t ht
      have ht' := Finset.mem_range.1 ht
      have hng := hcon t ht'
      unfold GoodM at hng
      push Not at hng
      exact ⟨ht', hng.2⟩
    have hM := maximal_card (P_pos hpos k) (Dset_per n a hk) lam hlam (Finset.range (P n k)) hall
    rw [Finset.card_range, Dset_count hpos a hk] at hM
    have hPk : (0 : ℝ) < P n k := by exact_mod_cast P_pos hpos k
    have h1 := hρ k hk
    have h2 : (P n k : ℝ) * ((cU n a κ : ℝ) / P n κ - (cU n a k : ℝ) / P n k)
        ≤ (P n k : ℝ) * (lam / 4) := mul_le_mul_of_nonneg_left h1 hPk.le
    have h3 : 0 < lam * (P n k : ℝ) := mul_pos hlam hPk
    nlinarith
  · exact ⟨0, P_pos hpos k, fun h => absurd h hk⟩

/-- good shifts at depth `k` (maximal version). -/
abbrev GoodNodeM (n a : ℕ → ℕ) (κ : ℕ) (lam : ℝ) (k : ℕ) : Type :=
  {t : ℕ // t < P n k ∧ GoodM n a κ lam k t}

instance (n a : ℕ → ℕ) (κ : ℕ) (lam : ℝ) (k : ℕ) : Finite (GoodNodeM n a κ lam k) :=
  Finite.of_injective (fun x : GoodNodeM n a κ lam k => (⟨x.1, x.2.1⟩ : Fin (P n k)))
    (fun _ _ h => Subtype.ext (congrArg Fin.val h))

lemma coherent_shiftsM {n : ℕ → ℕ} (hpos : ∀ i, 0 < n i) (a : ℕ → ℕ) (κ : ℕ) (lam : ℝ)
    (hex : ∀ k, ∃ t, t < P n k ∧ GoodM n a κ lam k t) :
    ∃ τ : ℕ → ℕ, (∀ k, GoodM n a κ lam k (τ k)) ∧ ∀ i j, i ≤ j → τ j % P n i = τ i := by
  have : ∀ k, Nonempty (GoodNodeM n a κ lam k) := fun k => by
    obtain ⟨t, h1, h2⟩ := hex k
    exact ⟨⟨t, h1, h2⟩⟩
  let π : {i j : ℕ} → i ≤ j → GoodNodeM n a κ lam j → GoodNodeM n a κ lam i :=
    fun {i _} h x => ⟨x.1 % P n i, Nat.mod_lt _ (P_pos hpos i), goodM_parent hpos a κ lam h x.2.2⟩
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite (α := GoodNodeM n a κ lam) π
    (fun i x => Subtype.ext (Nat.mod_eq_of_lt x.2.1))
    (fun i j k hij hjk x => Subtype.ext (Nat.mod_mod_of_dvd _ (P_dvd n hij)))
    (fun i x => Set.toFinite _)
  refine ⟨fun k => (f k).1, fun k => (f k).2.2, fun i j hij => ?_⟩
  exact congrArg Subtype.val (hf hij)

/-! ## The choice with positive lower density -/

lemma exists_bad_choice_lower {n : ℕ → ℕ} (hn : StrictMono n) (hn0 : 0 < n 0) (ε : ℝ) (hε : 0 < ε)
    (a : ℕ → ℕ) (ha : ∀ k, ε * (P n k : ℝ) ≤ (cU n a k : ℝ)) :
    ∃ b : ℕ → ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (ε / 2) * (N : ℝ) ≤ (W (UncInf n b) 0 N : ℝ) := by
  have hpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (Nat.succ_pos i) (succ_le_n hn hn0 i)
  have hanti : Antitone (fun k => (cU n a k : ℝ) / P n k) := fun i j h => rho_anti hpos a h
  have hnonneg : ∀ k, 0 ≤ (cU n a k : ℝ) / P n k := fun k => by positivity
  have hlam : 0 < ε / 4 := by positivity
  obtain ⟨κ', -, hκ2⟩ := exists_kappa (fun k => (cU n a k : ℝ) / P n k) hanti hnonneg
    (fun _ => ε / 4 / 4) (fun _ => by positivity)
  set κ := κ' 0 with hκdef
  have hρ : ∀ k, κ ≤ k → (cU n a κ : ℝ) / P n κ - (cU n a k : ℝ) / P n k ≤ ε / 4 / 4 :=
    fun k hk => hκ2 0 k hk
  have hex := goodM_exists hpos a κ (ε / 4) hlam hρ
  obtain ⟨τ, hτ1, hτ2⟩ := coherent_shiftsM hpos a κ (ε / 4) hex
  have hPκ : (0 : ℝ) < P n κ := by exact_mod_cast P_pos hpos κ
  have hρκ : ε ≤ (cU n a κ : ℝ) / P n κ := (le_div_iff₀ hPκ).2 (ha κ)
  refine ⟨fun i => a i + (n i - 1) * τ (i + 1), ⌈4 * (P n κ : ℝ) / ε⌉₊ + 1, fun N hN => ?_⟩
  -- size conditions on `N`
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hN
  have hNr : 4 * (P n κ : ℝ) / ε ≤ (N : ℝ) := by
    have h1 : 4 * (P n κ : ℝ) / ε ≤ (⌈4 * (P n κ : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈4 * (P n κ : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast at h2
    linarith
  have hNε : 4 * (P n κ : ℝ) ≤ (N : ℝ) * ε := (div_le_iff₀ hε).1 hNr
  -- stabilise the infinite system on `[0, N)` and pick a deep level `k`
  obtain ⟨K, hK⟩ := stabilize n (fun i => a i + (n i - 1) * τ (i + 1)) N
  set k := max K (max κ N) with hkdef
  have hk1 : K ≤ k := le_max_left _ _
  have hk2 : κ ≤ k := (le_max_left _ _).trans (le_max_right _ _)
  have hk3 : N ≤ P n k := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_P hn hn0 k)
  rw [hK k hk1]
  have e1 : W (Unc n (fun i => a i + (n i - 1) * τ (i + 1)) k) 0 N
      = W (Unc n a k) (τ k) N := by
    classical
    unfold W
    apply Finset.sum_congr rfl
    intro x _
    have := shift_mem n a τ hpos hτ2 k x
    rw [add_zero]
    simp only [this]
  have e2 : W (Dset n a κ k) (τ k) N + W (Unc n a k) (τ k) N = W (Unc n a κ) (τ k) N :=
    W_diff (unc_anti n a hk2) _ _
  have e3 : (cU n a κ : ℝ) / P n κ * N - P n κ ≤ (W (Unc n a κ) (τ k) N : ℝ) :=
    W_lower (P_pos hpos κ) (unc_per n a le_rfl) (τ k) N
  have e4 : (W (Dset n a κ k) (τ k) N : ℝ) ≤ ε / 4 * (N : ℝ) := by
    have h := hτ1 k hk2
    unfold BadM at h
    push Not at h
    exact h N hN1 hk3
  have e5 : (W (Dset n a κ k) (τ k) N : ℝ) + (W (Unc n a k) (τ k) N : ℝ)
      = (W (Unc n a κ) (τ k) N : ℝ) := by exact_mod_cast e2
  have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have e6 : ε * (N : ℝ) ≤ (cU n a κ : ℝ) / P n κ * N := mul_le_mul_of_nonneg_right hρκ hNnn
  rw [e1]
  linarith

/-! ## Main theorems -/

/-- Strong lower-density form: if the uniform conclusion fails at level ε, some choice `b` has an
uncovered set of LOWER density ≥ ε/2: for ALL sufficiently large `N`, at least `(ε/2)·N` of the
naturals below `N` satisfy none of the congruences. -/
theorem erdos_281_strong_lower (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (ε : ℝ) (hε : 0 < ε)
    (hfail : ∀ k : ℕ, ∃ a : ℕ → ℕ, ∀ d : ℝ, HasNatDensity (Unc n a k) d → ε ≤ d) :
    ∃ b : ℕ → ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
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
  obtain ⟨b, N₀, hb⟩ := exists_bad_choice_lower hn hn0 ε hε a ha
  refine ⟨b, N₀, fun N hN => ?_⟩
  rw [ncard_inter_Iio]
  exact hb N hN

/-- Erdős Problem 281 with the hypothesis weakened to LOWER density zero: it suffices that for
every choice of residues, every `c > 0` and every `N₀` there is `N ≥ N₀` with fewer than `c·N`
uncovered naturals below `N`. -/
theorem erdos_281_lower (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0)
    (H : ∀ a : ℕ → ℕ, ∀ c : ℝ, 0 < c → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ((UncInf n a ∩ Set.Iio N).ncard : ℝ) < c * (N : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  have hfail : ∀ k : ℕ, ∃ a : ℕ → ℕ, ∀ d : ℝ, HasNatDensity (Unc n a k) d → ε ≤ d := by
    intro k
    obtain ⟨a, ha⟩ := hcon k
    exact ⟨a, fun d hd => not_lt.1 (fun hlt => ha d hlt hd)⟩
  obtain ⟨b, N₀, hb⟩ := erdos_281_strong_lower n hn hn0 ε hε hfail
  obtain ⟨N, hN, hlt⟩ := H b (ε / 2) (by positivity) N₀
  have h := hb N hN
  linarith

end Erdos281

#print axioms Erdos281.maximal_ineq
#print axioms Erdos281.erdos_281_strong_lower
#print axioms Erdos281.erdos_281_lower
