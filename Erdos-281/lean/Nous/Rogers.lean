import Mathlib

/-!
# Rogers' theorem on covering by residue classes (finite cyclic case)

For moduli `n i ∣ N` and arbitrary residues `a i`, the union of the classes `a i (mod n i)`
inside `ℤ/N` has at least as many elements as the union of the classes `0 (mod n i)`.

The proof is by strong induction on `N`: pick a prime `p ∣ N`, write `N = p ^ e * M` with
`p ∤ M`, use the Chinese remainder bijection `m ↦ (m % p ^ e, m % M)`, apply the induction
hypothesis (for `M`) on the fibres over `u ∈ ℤ/p^e`, swap the order of counting, and apply the
"chain lemma" in `ℤ/p^e` (divisors of `p ^ e` are totally ordered by divisibility) on the fibres
over `v ∈ ℤ/M`.
-/

namespace Rogers

open Finset

/-- Number of residues `m < N` lying in at least one class `a i (mod n i)`, `i ∈ I`. -/
def cnt (N : ℕ) (I : Finset ℕ) (n a : ℕ → ℕ) : ℕ :=
  ((range N).filter (fun m => ∃ i ∈ I, m ≡ a i [MOD n i])).card

/-- The "mixed" covering predicate on pairs `(u, v)`. -/
def Q (I : Finset ℕ) (d c a b : ℕ → ℕ) (u v : ℕ) : Prop :=
  ∃ i ∈ I, u ≡ a i [MOD d i] ∧ v ≡ b i [MOD c i]

instance (I : Finset ℕ) (d c a b : ℕ → ℕ) (u v : ℕ) : Decidable (Q I d c a b u v) := by
  unfold Q; infer_instance

/-- Number of pairs `(u, v) ∈ [0,A) × [0,B)` with `u ≡ a i (mod d i)` and `v ≡ b i (mod c i)`
for some `i ∈ I`. -/
def mixed (A B : ℕ) (I : Finset ℕ) (d c a b : ℕ → ℕ) : ℕ :=
  ((range A ×ˢ range B).filter (fun uv : ℕ × ℕ => Q I d c a b uv.1 uv.2)).card

/-! ### Counting via the Chinese remainder theorem -/

/-- CRT counting: for coprime `A`, `B`, a predicate of `(m % A, m % B)` has as many solutions
`m < A * B` as the corresponding predicate on pairs `(u, v) ∈ [0,A) × [0,B)`. -/
lemma card_filter_crt (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (hc : Nat.Coprime A B)
    (P : ℕ → ℕ → Prop) [∀ u v, Decidable (P u v)] :
    ((range (A * B)).filter (fun m => P (m % A) (m % B))).card =
      ((range A ×ˢ range B).filter (fun uv : ℕ × ℕ => P uv.1 uv.2)).card := by
  apply Finset.card_bij (fun m _ => (m % A, m % B))
  · intro m hm
    simp only [mem_filter, mem_range, mem_product] at hm ⊢
    exact ⟨⟨Nat.mod_lt _ hA, Nat.mod_lt _ hB⟩, hm.2⟩
  · intro m hm m' hm' h
    simp only [mem_filter, mem_range] at hm hm'
    have h1 : m % A = m' % A := congrArg Prod.fst h
    have h2 : m % B = m' % B := congrArg Prod.snd h
    have h3 : m ≡ m' [MOD A * B] := (Nat.modEq_and_modEq_iff_modEq_mul hc).1 ⟨h1, h2⟩
    exact Nat.ModEq.eq_of_lt_of_lt h3 hm.1 hm'.1
  · rintro ⟨u, v⟩ huv
    simp only [mem_filter, mem_range, mem_product] at huv
    obtain ⟨⟨hu, hv⟩, hP⟩ := huv
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hc u v
    have e1 : k % (A * B) % A = u := by
      rw [Nat.mod_mul_right_mod]
      have : k % A = u % A := hk1
      rw [this, Nat.mod_eq_of_lt hu]
    have e2 : k % (A * B) % B = v := by
      rw [Nat.mod_mul_left_mod]
      have : k % B = v % B := hk2
      rw [this, Nat.mod_eq_of_lt hv]
    refine ⟨k % (A * B), ?_, ?_⟩
    · simp only [mem_filter, mem_range]
      refine ⟨Nat.mod_lt _ (Nat.mul_pos hA hB), ?_⟩
      rw [e1, e2]; exact hP
    · rw [e1, e2]

/-- Splitting a congruence modulo `n ∣ A * B` (with `A`, `B` coprime) into its `A`-part and
its `B`-part. -/
lemma modEq_split {A B n : ℕ} (hc : Nat.Coprime A B) (hn : n ∣ A * B) (m a : ℕ) :
    m ≡ a [MOD n] ↔ m % A ≡ a [MOD Nat.gcd n A] ∧ m % B ≡ a [MOD Nat.gcd n B] := by
  have hmul : Nat.gcd n A * Nat.gcd n B = n := by
    rw [← Nat.Coprime.gcd_mul n hc]; exact Nat.gcd_eq_left hn
  have hcop : Nat.Coprime (Nat.gcd n A) (Nat.gcd n B) :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right n A)
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right n B) hc)
  have hA : m % A ≡ m [MOD Nat.gcd n A] := (Nat.mod_modEq m A).of_dvd (Nat.gcd_dvd_right n A)
  have hB : m % B ≡ m [MOD Nat.gcd n B] := (Nat.mod_modEq m B).of_dvd (Nat.gcd_dvd_right n B)
  constructor
  · intro h
    have h' : m ≡ a [MOD Nat.gcd n A * Nat.gcd n B] := by rw [hmul]; exact h
    have h'' := (Nat.modEq_and_modEq_iff_modEq_mul hcop).2 h'
    exact ⟨hA.trans h''.1, hB.trans h''.2⟩
  · rintro ⟨h1, h2⟩
    have h' := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hA.symm.trans h1, hB.symm.trans h2⟩
    rw [hmul] at h'
    exact h'

/-- CRT form of the count: for coprime `A`, `B` and moduli `n i ∣ A * B`. -/
lemma crt_count (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (hc : Nat.Coprime A B)
    (I : Finset ℕ) (n a : ℕ → ℕ) (hdvd : ∀ i ∈ I, n i ∣ A * B) :
    cnt (A * B) I n a =
      mixed A B I (fun i => Nat.gcd (n i) A) (fun i => Nat.gcd (n i) B) a a := by
  unfold cnt mixed
  rw [← card_filter_crt A B hA hB hc
    (Q I (fun i => Nat.gcd (n i) A) (fun i => Nat.gcd (n i) B) a a)]
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro m _
  unfold Q
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, (modEq_split hc (hdvd i hi) m (a i)).1 h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, (modEq_split hc (hdvd i hi) m (a i)).2 h⟩

/-! ### Fibre decompositions of the mixed count -/

lemma mixed_eq_sum_left (A B : ℕ) (I : Finset ℕ) (d c a b : ℕ → ℕ) :
    mixed A B I d c a b =
      ∑ u ∈ range A, ((range B).filter (fun v => Q I d c a b u v)).card := by
  unfold mixed
  simp only [Finset.card_filter, Finset.sum_product]

lemma mixed_eq_sum_right (A B : ℕ) (I : Finset ℕ) (d c a b : ℕ → ℕ) :
    mixed A B I d c a b =
      ∑ v ∈ range B, ((range A).filter (fun u => Q I d c a b u v)).card := by
  unfold mixed
  simp only [Finset.card_filter, Finset.sum_product_right]

lemma inner_left (B : ℕ) (I : Finset ℕ) (d c a b : ℕ → ℕ) (u : ℕ) :
    ((range B).filter (fun v => Q I d c a b u v)).card =
      cnt B (I.filter (fun i => u ≡ a i [MOD d i])) c b := by
  unfold cnt
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro v _
  unfold Q
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, Finset.mem_filter.2 ⟨hi, h1⟩, h2⟩
  · rintro ⟨i, hi, h2⟩
    obtain ⟨hi', h1⟩ := Finset.mem_filter.1 hi
    exact ⟨i, hi', h1, h2⟩

lemma inner_right (A : ℕ) (I : Finset ℕ) (d c a b : ℕ → ℕ) (v : ℕ) :
    ((range A).filter (fun u => Q I d c a b u v)).card =
      cnt A (I.filter (fun i => v ≡ b i [MOD c i])) d a := by
  unfold cnt
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro u _
  unfold Q
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, Finset.mem_filter.2 ⟨hi, h2⟩, h1⟩
  · rintro ⟨i, hi, h1⟩
    obtain ⟨hi', h2⟩ := Finset.mem_filter.1 hi
    exact ⟨i, hi', h1, h2⟩

/-! ### The chain lemma in `ℤ/p^e` -/

/-- A residue class modulo `d ∣ A` has exactly `A / d` elements in `[0, A)`. -/
lemma card_class (A d v : ℕ) (hd : d ∣ A) (hdpos : 0 < d) :
    ((range A).filter (fun u => u ≡ v [MOD d])).card = A / d := by
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card A hdpos v,
    Nat.mod_eq_zero_of_dvd hd]
  simp

/-- **Chain lemma.** In `ℤ/p^e` the homogeneous classes cover the least, because the divisors
of `p ^ e` are totally ordered by divisibility. -/
lemma chain (p e : ℕ) (hp : p.Prime) (J : Finset ℕ) (d a : ℕ → ℕ)
    (hd : ∀ i ∈ J, d i ∣ p ^ e) :
    cnt (p ^ e) J d (fun _ => 0) ≤ cnt (p ^ e) J d a := by
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · simp [cnt]
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image J d hJ
  have hdvd : ∀ i ∈ J, d i₀ ∣ d i := by
    intro i hi
    obtain ⟨s, _, hs'⟩ := (Nat.dvd_prime_pow hp).1 (hd i₀ hi₀)
    obtain ⟨t, _, ht'⟩ := (Nat.dvd_prime_pow hp).1 (hd i hi)
    have hle := hmin i hi
    rw [hs', ht'] at hle ⊢
    exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).1 hle)
  have hpos : 0 < d i₀ := Nat.pos_of_dvd_of_pos (hd i₀ hi₀) (pow_pos hp.pos e)
  calc cnt (p ^ e) J d (fun _ => 0)
      ≤ ((range (p ^ e)).filter (fun u => u ≡ 0 [MOD d i₀])).card := by
        unfold cnt
        apply Finset.card_le_card
        intro u hu
        simp only [mem_filter] at hu ⊢
        obtain ⟨hur, i, hi, hui⟩ := hu
        exact ⟨hur, Nat.modEq_zero_iff_dvd.2
          ((hdvd i hi).trans (Nat.modEq_zero_iff_dvd.1 hui))⟩
    _ = p ^ e / d i₀ := card_class (p ^ e) (d i₀) 0 (hd i₀ hi₀) hpos
    _ = ((range (p ^ e)).filter (fun u => u ≡ a i₀ [MOD d i₀])).card :=
        (card_class (p ^ e) (d i₀) (a i₀) (hd i₀ hi₀) hpos).symm
    _ ≤ cnt (p ^ e) J d a := by
        unfold cnt
        apply Finset.card_le_card
        intro u hu
        simp only [mem_filter] at hu ⊢
        exact ⟨hu.1, i₀, hi₀, hu.2⟩

/-! ### The two comparison steps -/

/-- Step 1: replace the `B`-residues by `0`, using Rogers' theorem for the modulus `B`
on each fibre over `u`. -/
lemma step1 (A B : ℕ) (I : Finset ℕ) (d c a : ℕ → ℕ)
    (ihB : ∀ (I' : Finset ℕ) (a' : ℕ → ℕ), (∀ i ∈ I', c i ∣ B) →
      cnt B I' c (fun _ => 0) ≤ cnt B I' c a')
    (hc : ∀ i ∈ I, c i ∣ B) :
    mixed A B I d c a (fun _ => 0) ≤ mixed A B I d c a a := by
  rw [mixed_eq_sum_left, mixed_eq_sum_left]
  apply Finset.sum_le_sum
  intro u _
  rw [inner_left, inner_left]
  exact ihB _ _ (fun i hi => hc i (Finset.mem_of_mem_filter i hi))

/-- Step 2: replace the `A`-residues by `0` when `A = p ^ e`, using the chain lemma on each
fibre over `v`. -/
lemma step2 (p e B : ℕ) (hp : p.Prime) (I : Finset ℕ) (d c a : ℕ → ℕ)
    (hd : ∀ i ∈ I, d i ∣ p ^ e) :
    mixed (p ^ e) B I d c (fun _ => 0) (fun _ => 0) ≤ mixed (p ^ e) B I d c a (fun _ => 0) := by
  rw [mixed_eq_sum_right, mixed_eq_sum_right]
  apply Finset.sum_le_sum
  intro v _
  rw [inner_right, inner_right]
  exact chain p e hp _ d a (fun i hi => hd i (Finset.mem_of_mem_filter i hi))

/-! ### Rogers' theorem -/

/-- Rogers' theorem, general form over an arbitrary finite index set. -/
theorem rogers_general : ∀ N : ℕ, 0 < N → ∀ (I : Finset ℕ) (n a : ℕ → ℕ),
    (∀ i ∈ I, n i ∣ N) → cnt N I n (fun _ => 0) ≤ cnt N I n a := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN I n a hdvd
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hN) with h1 | h1
    · -- `N = 1`: every modulus is `1`
      have hN1 : N = 1 := h1.symm
      subst hN1
      apply le_of_eq
      unfold cnt
      refine congrArg Finset.card (Finset.filter_congr ?_)
      intro m _
      constructor
      · rintro ⟨i, hi, _⟩
        exact ⟨i, hi, by rw [Nat.dvd_one.1 (hdvd i hi)]; exact Nat.modEq_one⟩
      · rintro ⟨i, hi, _⟩
        exact ⟨i, hi, by rw [Nat.dvd_one.1 (hdvd i hi)]; exact Nat.modEq_one⟩
    · -- `N > 1`: split off a prime power
      obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd (ne_of_gt h1)
      obtain ⟨e, M, hpM, hNeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.ne_one
      have he : e ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hNeq
        exact hpM (hNeq ▸ hpN)
      have hMpos : 0 < M := by
        rcases Nat.eq_zero_or_pos M with h0 | h0
        · rw [h0, mul_zero] at hNeq; omega
        · exact h0
      have hApos : 0 < p ^ e := pow_pos hp.pos e
      have hA1 : 1 < p ^ e := Nat.one_lt_pow he hp.one_lt
      have hMlt : M < N := by
        rw [hNeq]
        exact lt_mul_of_one_lt_left hMpos hA1
      have hcop : Nat.Coprime (p ^ e) M :=
        Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
      subst hNeq
      have key1 := crt_count (p ^ e) M hApos hMpos hcop I n a hdvd
      have key0 := crt_count (p ^ e) M hApos hMpos hcop I n (fun _ => 0) hdvd
      have s1 : mixed (p ^ e) M I (fun i => Nat.gcd (n i) (p ^ e)) (fun i => Nat.gcd (n i) M)
            a (fun _ => 0) ≤
          mixed (p ^ e) M I (fun i => Nat.gcd (n i) (p ^ e)) (fun i => Nat.gcd (n i) M) a a :=
        step1 (p ^ e) M I _ _ a
          (fun I' a' h' => ih M hMlt hMpos I' _ a' h')
          (fun i _ => Nat.gcd_dvd_right (n i) M)
      have s2 : mixed (p ^ e) M I (fun i => Nat.gcd (n i) (p ^ e)) (fun i => Nat.gcd (n i) M)
            (fun _ => 0) (fun _ => 0) ≤
          mixed (p ^ e) M I (fun i => Nat.gcd (n i) (p ^ e)) (fun i => Nat.gcd (n i) M)
            a (fun _ => 0) :=
        step2 p e M hp I _ _ a (fun i _ => Nat.gcd_dvd_right (n i) (p ^ e))
      rw [key0, key1]
      exact s2.trans s1

/-- **Rogers' theorem.** Let `n i ∣ N` for `i < k`, `N > 0`. For any residues `a i`, the number of
residues `m < N` lying in at least one class `a i (mod n i)` is at least the number of `m < N`
divisible by at least one `n i`.  (So the homogeneous choice `a = 0` covers the least.) -/
theorem rogers (k : ℕ) (n a : ℕ → ℕ) (N : ℕ) (hN : 0 < N) (hdvd : ∀ i, i < k → n i ∣ N) :
    ((Finset.range N).filter (fun m => ∃ i, i < k ∧ n i ∣ m)).card ≤
      ((Finset.range N).filter (fun m => ∃ i, i < k ∧ m ≡ a i [MOD n i])).card := by
  have h := rogers_general N hN (Finset.range k) n a
    (fun i hi => hdvd i (Finset.mem_range.1 hi))
  unfold cnt at h
  have e1 : (Finset.range N).filter (fun m => ∃ i, i < k ∧ n i ∣ m) =
      (Finset.range N).filter (fun m => ∃ i ∈ Finset.range k, m ≡ 0 [MOD n i]) := by
    apply Finset.filter_congr
    intro m _
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨i, Finset.mem_range.2 hi, Nat.modEq_zero_iff_dvd.2 h⟩
    · rintro ⟨i, hi, h⟩
      exact ⟨i, Finset.mem_range.1 hi, Nat.modEq_zero_iff_dvd.1 h⟩
  have e2 : (Finset.range N).filter (fun m => ∃ i, i < k ∧ m ≡ a i [MOD n i]) =
      (Finset.range N).filter (fun m => ∃ i ∈ Finset.range k, m ≡ a i [MOD n i]) := by
    apply Finset.filter_congr
    intro m _
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨i, Finset.mem_range.2 hi, h⟩
    · rintro ⟨i, hi, h⟩
      exact ⟨i, Finset.mem_range.1 hi, h⟩
  rw [e1, e2]
  exact h

/-- Complement form: the homogeneous choice leaves the most residues uncovered. -/
theorem rogers_uncovered (k : ℕ) (n a : ℕ → ℕ) (N : ℕ) (hN : 0 < N)
    (hdvd : ∀ i, i < k → n i ∣ N) :
    ((Finset.range N).filter (fun m => ∀ i, i < k → ¬ m ≡ a i [MOD n i])).card ≤
      ((Finset.range N).filter (fun m => ∀ i, i < k → ¬ n i ∣ m)).card := by
  have h := rogers k n a N hN hdvd
  have c1 := Finset.card_filter_add_card_filter_not (s := Finset.range N)
    (fun m => ∃ i, i < k ∧ m ≡ a i [MOD n i])
  have c2 := Finset.card_filter_add_card_filter_not (s := Finset.range N)
    (fun m => ∃ i, i < k ∧ n i ∣ m)
  have e1 : (Finset.range N).filter (fun m => ∀ i, i < k → ¬ m ≡ a i [MOD n i]) =
      (Finset.range N).filter (fun m => ¬ ∃ i, i < k ∧ m ≡ a i [MOD n i]) := by
    apply Finset.filter_congr
    intro m _
    constructor
    · rintro h ⟨i, hi, hm⟩
      exact h i hi hm
    · intro h i hi hm
      exact h ⟨i, hi, hm⟩
  have e2 : (Finset.range N).filter (fun m => ∀ i, i < k → ¬ n i ∣ m) =
      (Finset.range N).filter (fun m => ¬ ∃ i, i < k ∧ n i ∣ m) := by
    apply Finset.filter_congr
    intro m _
    constructor
    · rintro h ⟨i, hi, hm⟩
      exact h i hi hm
    · intro h i hi hm
      exact h ⟨i, hi, hm⟩
  rw [e1, e2]
  omega

end Rogers

#print axioms Rogers.rogers
#print axioms Rogers.rogers_uncovered
