import Erdos142.Exact

/-!
# A lower bound at `N = k²`

Let `H ⊆ {1, …, k²}` meet every `k`-term arithmetic progression contained in `{1, …, k²}`.
The trivial bound is `|H| ≥ k` (disjoint blocks of `k` consecutive integers).  This file proves
that the excess `s = |H| - k` satisfies `k < 8 s² + 8 s + 4`, i.e. `s ≳ √(k/8)`:

* `card_hitting_sq` : if `|H| = k + s` then `k < 8 s² + 8 s + 4`;
* `r_sq_add_lt` : if `8 s² + 8 s + 4 ≤ k` then `r_k(k²) + k + s < k²`.

Idea of the proof.  For `1 ≤ g ≤ k`, every residue class mod `g` contains a `k`-term progression
of `{1, …, k²}`, so `H` meets all `g` classes; the largest element of `H` in each class is not of
the form `h` with `h + g ∈ H`, hence `#{h ∈ H : h + g ∈ H} ≤ |H| - g` (`card_shift_add_le`).
On the other hand `{1, …, k²}` is covered by the initial segment below `min H` (at most `k - 1`
integers) and by the "fibers" `fiber H (k²) h` (the integers whose largest element of `H` below
them is `h`), each with at most `k` elements.  A fiber with more than `k - t` elements forces
`h + (k - j) ∈ H` for some `j < t` (or `h = max H`), and there are at most
`1 + ∑_{j<t} (s + j)` such `h`.  Taking `t = 2 s + 2` gives the inequality.
-/

namespace Erdos142

/-- (Class count.) If `H` meets every `k`-term progression of `{1, …, k²}` and `1 ≤ g ≤ k`, then
the number of `h ∈ H` with `h + g ∈ H` is at most `|H| - g`. -/
lemma card_shift_add_le (k g : ℕ) (hg1 : 1 ≤ g) (hgk : g ≤ k) (H : Finset ℕ)
    (hit : ∀ a d : ℕ, 1 ≤ a → 0 < d → a + (k - 1) * d ≤ k ^ 2 → ∃ i, i < k ∧ a + i * d ∈ H) :
    (H.filter (fun h => h + g ∈ H)).card + g ≤ H.card := by
  classical
  have hk1 : 1 ≤ k := le_trans hg1 hgk
  have h2 : (k - 1) * g + g = k * g := by
    obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have h3 : k * g ≤ k ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_left k hgk
  have hBsub : H.filter (fun h => h + g ∈ H) ⊆ H := Finset.filter_subset _ _
  -- every residue class mod `g` has an element of `H` outside the filtered set
  have key : ∀ ρ ∈ Finset.range g,
      ∃ h, h ∈ H \ H.filter (fun h => h + g ∈ H) ∧ h % g = ρ := by
    intro ρ hρ
    rw [Finset.mem_range] at hρ
    have hex : ∃ h ∈ H, h % g = ρ := by
      rcases Nat.eq_zero_or_pos ρ with h0 | hpos
      · obtain ⟨i, _, hmem⟩ := hit g g hg1 (by omega) (by omega)
        refine ⟨_, hmem, ?_⟩
        rw [Nat.add_mul_mod_self_right, Nat.mod_self, h0]
      · obtain ⟨i, _, hmem⟩ := hit ρ g hpos (by omega) (by omega)
        refine ⟨_, hmem, ?_⟩
        rw [Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt hρ
    obtain ⟨h₁, h₁H, h₁res⟩ := hex
    have hne : (H.filter (fun h => h % g = ρ)).Nonempty :=
      ⟨h₁, Finset.mem_filter.2 ⟨h₁H, h₁res⟩⟩
    have hmm := Finset.mem_filter.1 (Finset.max'_mem _ hne)
    refine ⟨(H.filter (fun h => h % g = ρ)).max' hne, ?_, hmm.2⟩
    rw [Finset.mem_sdiff]
    refine ⟨hmm.1, ?_⟩
    intro hin
    have hin' : (H.filter (fun h => h % g = ρ)).max' hne + g ∈ H := (Finset.mem_filter.1 hin).2
    have hres : ((H.filter (fun h => h % g = ρ)).max' hne + g) % g = ρ := by
      rw [Nat.add_mod_right]
      exact hmm.2
    have hin2 : (H.filter (fun h => h % g = ρ)).max' hne + g ∈ H.filter (fun h => h % g = ρ) :=
      Finset.mem_filter.2 ⟨hin', hres⟩
    have := Finset.le_max' _ _ hin2
    omega
  choose! f hf using key
  have hmaps : ∀ ρ ∈ Finset.range g, f ρ ∈ H \ H.filter (fun h => h + g ∈ H) :=
    fun ρ hρ => (hf ρ hρ).1
  have hinj : Set.InjOn f (Finset.range g : Set ℕ) := by
    intro a ha b hb hab
    have h1 := (hf a (Finset.mem_coe.1 ha)).2
    have h2 := (hf b (Finset.mem_coe.1 hb)).2
    rw [← h1, ← h2, hab]
  have hcard : (Finset.range g).card ≤ (H \ H.filter (fun h => h + g ∈ H)).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hcard
  have := Finset.card_sdiff_add_card_eq_card hBsub
  omega

/-- The integers of `{1, …, N}` whose largest element of `H` below them (or equal) is `h`. -/
noncomputable def fiber (H : Finset ℕ) (N h : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun x => h ≤ x ∧ ∀ y ∈ H, y ≤ x → y ≤ h)

lemma mem_fiber {H : Finset ℕ} {N h x : ℕ} :
    x ∈ fiber H N h ↔ (1 ≤ x ∧ x ≤ N) ∧ h ≤ x ∧ ∀ y ∈ H, y ≤ x → y ≤ h := by
  classical
  unfold fiber
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- Every fiber has at most `k` elements (blocks of `k` consecutive integers meet `H`). -/
lemma fiber_card_le (k : ℕ) (hk1 : 1 ≤ k) (H : Finset ℕ)
    (hit : ∀ a d : ℕ, 1 ≤ a → 0 < d → a + (k - 1) * d ≤ k ^ 2 → ∃ i, i < k ∧ a + i * d ∈ H)
    (h : ℕ) : (fiber H (k ^ 2) h).card ≤ k := by
  have hsub : fiber H (k ^ 2) h ⊆ Finset.Ico h (h + k) := by
    intro x hx
    rw [mem_fiber] at hx
    obtain ⟨⟨_, hx2⟩, hhx, hmax⟩ := hx
    rw [Finset.mem_Ico]
    refine ⟨hhx, ?_⟩
    by_contra hcon
    have hge : h + k ≤ x := Nat.le_of_not_lt hcon
    obtain ⟨i, hi, hmem⟩ := hit (h + 1) 1 (by omega) one_pos (by rw [Nat.mul_one]; omega)
    rw [Nat.mul_one] at hmem
    have := hmax _ hmem (by omega)
    omega
  calc (fiber H (k ^ 2) h).card ≤ (Finset.Ico h (h + k)).card := Finset.card_le_card hsub
    _ = k := by rw [Nat.card_Ico]; omega

/-- A fiber over `h` has at most `k - t` elements unless `h` is the largest element of `H` or
`h + (k - j) ∈ H` for some `j < t`. -/
lemma fiber_card_le_small (k t : ℕ) (htk : t ≤ k) (H : Finset ℕ)
    (hH : H ⊆ Finset.Icc 1 (k ^ 2))
    (hit : ∀ a d : ℕ, 1 ≤ a → 0 < d → a + (k - 1) * d ≤ k ^ 2 → ∃ i, i < k ∧ a + i * d ∈ H)
    (h : ℕ) (hlt : ∃ y ∈ H, h < y) (hno : ∀ j, j < t → h + (k - j) ∉ H) :
    (fiber H (k ^ 2) h).card ≤ k - t := by
  classical
  have hsub : fiber H (k ^ 2) h ⊆ Finset.Ico h (h + (k - t)) := by
    intro x hx
    rw [mem_fiber] at hx
    obtain ⟨⟨_, _⟩, hhx, hmax⟩ := hx
    rw [Finset.mem_Ico]
    refine ⟨hhx, ?_⟩
    by_contra hcon
    have hge : h + (k - t) ≤ x := Nat.le_of_not_lt hcon
    -- the least element `h'` of `H` above `h`
    have hne : (H.filter (fun y => h < y)).Nonempty := by
      obtain ⟨y, hy, hhy⟩ := hlt
      exact ⟨y, Finset.mem_filter.2 ⟨hy, hhy⟩⟩
    have hmm := Finset.mem_filter.1 (Finset.min'_mem _ hne)
    have hex : ∃ h', h' ∈ H ∧ h < h' ∧ ∀ y ∈ H, h < y → h' ≤ y :=
      ⟨(H.filter (fun y => h < y)).min' hne, hmm.1, hmm.2,
        fun y hy hhy => Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hy, hhy⟩)⟩
    obtain ⟨h', hh'H, hh'lt, hh'min⟩ := hex
    have hh'le : h' ≤ k ^ 2 := (Finset.mem_Icc.1 (hH hh'H)).2
    -- the gap `h' - h` is at most `k`
    have hgap : h' ≤ h + k := by
      by_contra hc
      have hc' : h + k < h' := Nat.lt_of_not_le hc
      obtain ⟨i, hi, hmem⟩ := hit (h + 1) 1 (by omega) one_pos (by rw [Nat.mul_one]; omega)
      rw [Nat.mul_one] at hmem
      have := hh'min _ hmem (by omega)
      omega
    -- ... and in fact at most `k - t`
    have hgap2 : h' ≤ h + (k - t) := by
      by_contra hc
      have hc' : h + (k - t) < h' := Nat.lt_of_not_le hc
      apply hno (k - (h' - h)) (by omega)
      have : h + (k - (k - (h' - h))) = h' := by omega
      rw [this]
      exact hh'H
    have := hmax h' hh'H (le_trans hgap2 hge)
    omega
  calc (fiber H (k ^ 2) h).card ≤ (Finset.Ico h (h + (k - t))).card := Finset.card_le_card hsub
    _ = k - t := by rw [Nat.card_Ico]; omega

/-- The integers below every element of `H` are among `1, …, k - 1`. -/
lemma card_lo_le (k : ℕ) (hk1 : 1 ≤ k) (H : Finset ℕ)
    (hit : ∀ a d : ℕ, 1 ≤ a → 0 < d → a + (k - 1) * d ≤ k ^ 2 → ∃ i, i < k ∧ a + i * d ∈ H) :
    ((Finset.Icc 1 (k ^ 2)).filter (fun x => ∀ y ∈ H, x < y)).card ≤ k - 1 := by
  classical
  have hkk : k ≤ k ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_self k
  have hsub : (Finset.Icc 1 (k ^ 2)).filter (fun x => ∀ y ∈ H, x < y) ⊆ Finset.Ico 1 k := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hx1, _⟩, hlt⟩ := hx
    obtain ⟨i, hi, hmem⟩ := hit 1 1 le_rfl one_pos (by rw [Nat.mul_one]; omega)
    rw [Nat.mul_one] at hmem
    have := hlt _ hmem
    rw [Finset.mem_Ico]
    omega
  calc ((Finset.Icc 1 (k ^ 2)).filter (fun x => ∀ y ∈ H, x < y)).card
      ≤ (Finset.Ico 1 k).card := Finset.card_le_card hsub
    _ = k - 1 := by rw [Nat.card_Ico]

/-- Covering bound: `{1, …, k²}` is covered by the integers below `min H` and by the fibers. -/
lemma cover_bound (k t m : ℕ) (hkm : k = t + m) (hk1 : 1 ≤ k) (H Big : Finset ℕ)
    (hH : H ⊆ Finset.Icc 1 (k ^ 2))
    (hit : ∀ a d : ℕ, 1 ≤ a → 0 < d → a + (k - 1) * d ≤ k ^ 2 → ∃ i, i < k ∧ a + i * d ∈ H)
    (hsmall : ∀ h ∈ H, h ∉ Big → (∃ y ∈ H, h < y) ∧ ∀ j, j < t → h + (k - j) ∉ H) :
    k ^ 2 + 1 ≤ k + Big.card * k + (H \ Big).card * m := by
  classical
  have hcov : Finset.Icc 1 (k ^ 2) ⊆
      ((Finset.Icc 1 (k ^ 2)).filter (fun x => ∀ y ∈ H, x < y) ∪
          Big.biUnion (fiber H (k ^ 2))) ∪ (H \ Big).biUnion (fiber H (k ^ 2)) := by
    intro x hx
    by_cases hlo : ∀ y ∈ H, x < y
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx, hlo⟩))
    · have hex : ∃ y ∈ H, y ≤ x := by
        by_contra hc
        apply hlo
        intro y hy
        by_contra hyx
        exact hc ⟨y, hy, Nat.le_of_not_lt hyx⟩
      obtain ⟨y, hy, hyx⟩ := hex
      have hne : (H.filter (fun y => y ≤ x)).Nonempty := ⟨y, Finset.mem_filter.2 ⟨hy, hyx⟩⟩
      have hmm := Finset.mem_filter.1 (Finset.max'_mem _ hne)
      have hfib : x ∈ fiber H (k ^ 2) ((H.filter (fun y => y ≤ x)).max' hne) := by
        rw [mem_fiber]
        exact ⟨Finset.mem_Icc.1 hx, hmm.2,
          fun z hz hzx => Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hz, hzx⟩)⟩
      by_cases hb : (H.filter (fun y => y ≤ x)).max' hne ∈ Big
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hb, hfib⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.2 ⟨_, Finset.mem_sdiff.2 ⟨hmm.1, hb⟩, hfib⟩)
  have h1 := Finset.card_le_card hcov
  rw [Nat.card_Icc] at h1
  have h2 := card_lo_le k hk1 H hit
  have h3 : (Big.biUnion (fiber H (k ^ 2))).card ≤ Big.card * k :=
    Finset.card_biUnion_le_card_mul _ _ _ (fun h _ => fiber_card_le k hk1 H hit h)
  have h4 : ((H \ Big).biUnion (fiber H (k ^ 2))).card ≤ (H \ Big).card * m := by
    apply Finset.card_biUnion_le_card_mul
    intro h hh
    rw [Finset.mem_sdiff] at hh
    obtain ⟨hy, hno⟩ := hsmall h hh.1 hh.2
    have := fiber_card_le_small k t (by omega) H hH hit h hy hno
    omega
  have h5 := Finset.card_union_le
    ((Finset.Icc 1 (k ^ 2)).filter (fun x => ∀ y ∈ H, x < y) ∪ Big.biUnion (fiber H (k ^ 2)))
    ((H \ Big).biUnion (fiber H (k ^ 2)))
  have h6 := Finset.card_union_le
    ((Finset.Icc 1 (k ^ 2)).filter (fun x => ∀ y ∈ H, x < y)) (Big.biUnion (fiber H (k ^ 2)))
  omega

/-- `∑_{j < 2s+2} (s + j) = 4 s² + 5 s + 1`. -/
lemma sum_range_shift (s : ℕ) :
    ∑ j ∈ Finset.range (2 * s + 2), (s + j) = 4 * s ^ 2 + 5 * s + 1 := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h1 := Finset.sum_range_id_mul_two (2 * s + 2)
  have h2 : (2 * s + 2) * (2 * s + 2 - 1) = 4 * s ^ 2 + 6 * s + 2 := by
    have : 2 * s + 2 - 1 = 2 * s + 1 := by omega
    rw [this]
    ring
  have h3 : (2 * s + 2) * s = 2 * s ^ 2 + 2 * s := by ring
  omega

/-- **Lower bound at `N = k²`.** If `H ⊆ {1, …, k²}` meets every `k`-term arithmetic progression
contained in `{1, …, k²}` and `|H| = k + s`, then `k < 8 s² + 8 s + 4`. -/
theorem card_hitting_sq (k s : ℕ) (hk : 2 ≤ k) (H : Finset ℕ) (hH : H ⊆ Finset.Icc 1 (k ^ 2))
    (hit : ∀ a d : ℕ, 1 ≤ a → 0 < d → a + (k - 1) * d ≤ k ^ 2 → ∃ i, i < k ∧ a + i * d ∈ H)
    (hcard : H.card = k + s) : k < 8 * s ^ 2 + 8 * s + 4 := by
  classical
  by_contra hcon
  have hge : 8 * s ^ 2 + 8 * s + 4 ≤ k := Nat.le_of_not_lt hcon
  have hk1 : 1 ≤ k := by omega
  obtain ⟨m, hm⟩ : ∃ m, k = (2 * s + 2) + m := ⟨k - (2 * s + 2), by omega⟩
  -- the "big" elements: `h + (k - j) ∈ H` for some `j < 2s+2`, or `h = max H`
  obtain ⟨Big, hBigdef⟩ : ∃ Big : Finset ℕ, Big =
      H.filter (fun h => (∃ j, j < 2 * s + 2 ∧ h + (k - j) ∈ H) ∨ ∀ y ∈ H, y ≤ h) := ⟨_, rfl⟩
  have hmemBig : ∀ h, h ∈ Big ↔
      h ∈ H ∧ ((∃ j, j < 2 * s + 2 ∧ h + (k - j) ∈ H) ∨ ∀ y ∈ H, y ≤ h) := by
    intro h
    rw [hBigdef, Finset.mem_filter]
  have hBigsub : Big ⊆ H := fun h hh => ((hmemBig h).1 hh).1
  -- there are few big elements
  have hBig : Big.card ≤ 4 * s ^ 2 + 5 * s + 2 := by
    have hsub : Big ⊆
        ((Finset.range (2 * s + 2)).biUnion fun j => H.filter (fun h => h + (k - j) ∈ H)) ∪
          H.filter (fun h => ∀ y ∈ H, y ≤ h) := by
      intro h hh
      obtain ⟨hhH, hp⟩ := (hmemBig h).1 hh
      rw [Finset.mem_union]
      rcases hp with ⟨j, hj, hmem⟩ | hmax
      · left
        rw [Finset.mem_biUnion]
        exact ⟨j, Finset.mem_range.2 hj, Finset.mem_filter.2 ⟨hhH, hmem⟩⟩
      · right
        exact Finset.mem_filter.2 ⟨hhH, hmax⟩
    have h1 : ((Finset.range (2 * s + 2)).biUnion
        fun j => H.filter (fun h => h + (k - j) ∈ H)).card ≤
        ∑ j ∈ Finset.range (2 * s + 2), (s + j) := by
      refine le_trans Finset.card_biUnion_le ?_
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      have := card_shift_add_le k (k - j) (by omega) (by omega) H hit
      show (H.filter (fun h => h + (k - j) ∈ H)).card ≤ s + j
      omega
    have h2 : (H.filter (fun h => ∀ y ∈ H, y ≤ h)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      exact le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)
    have h3 := sum_range_shift s
    have h4 := Finset.card_le_card hsub
    have h5 := Finset.card_union_le
      ((Finset.range (2 * s + 2)).biUnion fun j => H.filter (fun h => h + (k - j) ∈ H))
      (H.filter (fun h => ∀ y ∈ H, y ≤ h))
    omega
  -- covering bound
  have hcov := cover_bound k (2 * s + 2) m hm hk1 H Big hH hit (by
    intro h hh hnot
    have hnot' : ¬((∃ j, j < 2 * s + 2 ∧ h + (k - j) ∈ H) ∨ ∀ y ∈ H, y ≤ h) :=
      fun hp => hnot ((hmemBig h).2 ⟨hh, hp⟩)
    rw [not_or] at hnot'
    obtain ⟨hn1, hn2⟩ := hnot'
    refine ⟨?_, ?_⟩
    · by_contra hc
      apply hn2
      intro y hy
      by_contra hyh
      exact hc ⟨y, hy, Nat.lt_of_not_le hyh⟩
    · intro j hj hmem
      exact hn1 ⟨j, hj, hmem⟩)
  have hsd := Finset.card_sdiff_add_card_eq_card hBigsub
  -- arithmetic
  have hce : (H \ Big).card + Big.card = k + s := by omega
  have e1 : Big.card * k + (H \ Big).card * m =
      Big.card * (2 * s + 2) + (k + s) * m := by
    calc Big.card * k + (H \ Big).card * m
        = Big.card * (2 * s + 2 + m) + (H \ Big).card * m := by rw [← hm]
      _ = Big.card * (2 * s + 2) + ((H \ Big).card + Big.card) * m := by ring
      _ = Big.card * (2 * s + 2) + (k + s) * m := by rw [hce]
  have e2 : Big.card * (2 * s + 2) ≤ (4 * s ^ 2 + 5 * s + 2) * (2 * s + 2) :=
    Nat.mul_le_mul_right _ hBig
  have hmge : 8 * s ^ 2 + 6 * s + 2 ≤ m := by omega
  have e4 : (s + 1) * (8 * s ^ 2 + 6 * s + 2) ≤ (s + 1) * m := Nat.mul_le_mul_left _ hmge
  have fin : (2 * s + 2 + m) ^ 2 + 1 ≤
      (2 * s + 2 + m) + (4 * s ^ 2 + 5 * s + 2) * (2 * s + 2) + (2 * s + 2 + m + s) * m := by
    rw [← hm]
    omega
  nlinarith [fin, e4]

/-- **Consequence for `r_k(k²)`.** If `8 s² + 8 s + 4 ≤ k` then `r_k(k²) ≤ k² - k - s - 1`. -/
theorem r_sq_add_lt (k s : ℕ) (hk : 2 ≤ k) (hs : 8 * s ^ 2 + 8 * s + 4 ≤ k) :
    r k (k ^ 2) + k + s < k ^ 2 := by
  classical
  have hk2 : 2 * k ≤ k ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right k hk
  have hsk : s + 1 < k := by omega
  have hle : r k (k ^ 2) ≤ k ^ 2 - (k + s + 1) := by
    apply r_le
    intro S hS hfree
    by_contra hcon
    have hcon' : k ^ 2 - (k + s + 1) < S.card := Nat.lt_of_not_le hcon
    have hsd := Finset.card_sdiff_add_card_eq_card hS
    rw [Nat.card_Icc] at hsd
    -- the complement meets every progression
    have hit : ∀ a d : ℕ, 1 ≤ a → 0 < d → a + (k - 1) * d ≤ k ^ 2 →
        ∃ i, i < k ∧ a + i * d ∈ Finset.Icc 1 (k ^ 2) \ S := by
      intro a d ha hd hlast
      obtain ⟨i, hi, hiS⟩ := exists_not_mem_of_APFree hfree a d hd
      refine ⟨i, hi, ?_⟩
      rw [Finset.mem_sdiff, Finset.mem_Icc]
      have h1 : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
      exact ⟨⟨by omega, by omega⟩, hiS⟩
    -- the complement has at least `k` elements
    have hlow : S.card + k ≤ k ^ 2 := by
      have h1 := card_le_r hS hfree
      have h2 := r_add_div_le k (k ^ 2) (by omega)
      have h3 : k ^ 2 / k = k := by
        rw [pow_two]
        exact Nat.mul_div_cancel_left k (by omega)
      omega
    obtain ⟨s', hs'⟩ : ∃ s', (Finset.Icc 1 (k ^ 2) \ S).card = k + s' :=
      ⟨(Finset.Icc 1 (k ^ 2) \ S).card - k, by omega⟩
    have hs's : s' ≤ s := by omega
    have hmain := card_hitting_sq k s' hk (Finset.Icc 1 (k ^ 2) \ S) Finset.sdiff_subset hit hs'
    have hmono : 8 * s' ^ 2 + 8 * s' + 4 ≤ 8 * s ^ 2 + 8 * s + 4 := by
      have : s' ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hs's 2
      omega
    omega
  omega

end Erdos142

#print axioms Erdos142.card_hitting_sq
#print axioms Erdos142.r_sq_add_lt
