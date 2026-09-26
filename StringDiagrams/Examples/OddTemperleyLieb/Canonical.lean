import StringDiagrams.Examples.OddTemperleyLieb.Words
import StringDiagrams.Examples.OddTemperleyLieb.Dyck

/-!
# Canonical cup diagrams and the tracking of arcs

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, proof of
Theorem A.2 (spanning part, and the claim that isotopic crossingless matchings give the same
morphism up to sign).

For a Dyck sequence `w` of length `n` (a crossingless matching of `n` points), the canonical
cup diagram `canon n w : 0 ⟶ n` is defined recursively: if the first adjacent pair `+1 -1` of
`w` is at `p`, then `canon n w = canon (n - 2) (w without it) ≫ cup_p`. It realizes the
matching `w` (`trackW_canon`).

* `canon_comp_cup`: `canon n w ≫ cup_i = ± canon (n + 2) (ins i 0 1 w)`;
* `canon_comp_cap`: `canon (n + 2) w ≫ cap_i = ± δ^{[loop]} canon n (capT i w)`, where the
  loop indicator is `loopT i w`;
* `canon_comp_evW` (**tracking**): for every word `u` in cups and caps from `k` strands,
  `canon k w ≫ evW u = ± δ^ℓ canon (trackW w u)`, where `trackW w u` is the crossingless matching
  obtained by following the arcs of `w` through the cups and caps of `u` and `ℓ` is the number
  of closed loops formed. In particular (`w = []`) every diagram `0 → N` equals, up to sign and
  a power of `δ`, the canonical cup diagram of its crossingless matching (`diag_eq_canon`), and
  the canonical cup diagrams span `Hom(0, N)` (`span_canon`).
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory
open TemperleyLieb.Rep (ins del length_ins length_del del_ins del_ins_far del_ins_far')

variable {R : Type*} [CommRing R] {δ : R}

variable (R δ) in
/-- The canonical cup diagram of a crossingless matching given by its Dyck sequence. -/
def canon : (n : ℕ) → List (Fin 2) → (X R δ 0 ⟶ X R δ n)
  | 0, _ => 𝟙 _
  | 1, _ => 0
  | n + 2, w => canon n (del (firstPair w) w) ≫ cup R δ n (firstPair w)

theorem canon_zero (w : List (Fin 2)) : canon R δ 0 w = 𝟙 _ := by rw [canon]

theorem canon_succ_succ (n : ℕ) (w : List (Fin 2)) :
    canon R δ (n + 2) w = canon R δ n (del (firstPair w) w) ≫ cup R δ n (firstPair w) := by
  rw [canon]

/-! ## List lemmas for the first adjacent pair -/

theorem rep_add (i j : ℕ) (c : Fin 2) (r : List (Fin 2)) :
    List.replicate (i + j) c ++ r = List.replicate i c ++ (List.replicate j c ++ r) := by
  rw [List.replicate_add, List.append_assoc]

theorem ins_rep_add (p k : ℕ) (a b c : Fin 2) (r : List (Fin 2)) :
    ins (p + k) a b (List.replicate p c ++ r) = List.replicate p c ++ ins k a b r := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show p + 1 + k = (p + k) + 1 by omega, List.replicate_succ, List.cons_append,
      List.cons_append]
    simp only [TemperleyLieb.Rep.ins, ih]

theorem firstPair_ins_le {p i : ℕ} (r : List (Fin 2)) (hi : i ≤ p + 1) :
    firstPair (ins i 0 1 (List.replicate p 0 ++ 0 :: 1 :: r)) = i ∧
      del i (ins i 0 1 (List.replicate p 0 ++ 0 :: 1 :: r)) =
        List.replicate p 0 ++ 0 :: 1 :: r := by
  have e : List.replicate p (0 : Fin 2) ++ 0 :: 1 :: r =
      List.replicate i 0 ++ (List.replicate (p + 1 - i) 0 ++ 1 :: r) := by
    rw [← rep_add, show i + (p + 1 - i) = p + 1 by omega, List.replicate_succ',
      List.append_assoc, List.singleton_append]
  refine ⟨?_, del_ins _ _ _ (by simp; omega)⟩
  rw [e, ins_rep]
  exact firstPair_rep i _

theorem firstPair_ins_ge {p i : ℕ} (r : List (Fin 2)) (hi : p + 2 ≤ i)
    (hr : i ≤ p + 2 + r.length) :
    firstPair (ins i 0 1 (List.replicate p 0 ++ 0 :: 1 :: r)) = p ∧
      del p (ins i 0 1 (List.replicate p 0 ++ 0 :: 1 :: r)) =
        ins (i - 2) 0 1 (List.replicate p 0 ++ r) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = p + 2 + k := ⟨i - p - 2, by omega⟩
  have e1 : ins (p + 2 + k) 0 1 (List.replicate p 0 ++ 0 :: 1 :: r) =
      List.replicate p 0 ++ 0 :: 1 :: ins k 0 1 r := by
    rw [show p + 2 + k = p + (k + 2) by omega, ins_rep_add]
    rfl
  have e2 : ins (p + 2 + k - 2) 0 1 (List.replicate p 0 ++ r) =
      List.replicate p 0 ++ ins k 0 1 r := by
    rw [show p + 2 + k - 2 = p + k by omega, ins_rep_add]
  rw [e1, e2]
  exact ⟨firstPair_rep p _, del_rep p 0 0 1 _⟩

/-! ## Closure under cups -/

/-- `canon n w ≫ cup_i = ± canon (n + 2) (ins i 0 1 w)`. -/
theorem canon_comp_cup (n : ℕ) : ∀ (w : List (Fin 2)), IsDyck w → w.length = n →
    ∀ i ≤ n, PmEq (canon R δ n w ≫ cup R δ n i) (canon R δ (n + 2) (ins i 0 1 w)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hl i hi
  rcases eq_or_ne w [] with rfl | hne
  · obtain rfl : n = 0 := by simpa using hl.symm
    obtain rfl : i = 0 := by omega
    rw [canon_succ_succ]
    simp [canon_zero, firstPair, TemperleyLieb.Rep.ins, TemperleyLieb.Rep.del]
    exact PmEq.refl _
  obtain ⟨r, hr⟩ := dyck_decomp hw hne
  generalize hp : firstPair w = p at hr
  have hlr : p + 2 + r.length = n := by rw [← hl, hr]; simp; omega
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨p + r.length, by omega⟩
  have hw0 : IsDyck (List.replicate p 0 ++ r) := by
    have := hw.del_pair (p := p) (by omega) (by rw [hr]; simp [getD_rep_add p 0 0 (0 :: 1 :: r)])
      (by rw [hr]; simp [getD_rep_add p 1 0 (0 :: 1 :: r)])
    rwa [hr, del_rep] at this
  have hc : canon R δ (n + 2) w = canon R δ n (List.replicate p 0 ++ r) ≫ cup R δ n p := by
    rw [canon_succ_succ, hp]
    conv_lhs => rw [hr, del_rep]
  by_cases hip : i ≤ p + 1
  · obtain ⟨h1, h2⟩ := firstPair_ins_le (p := p) (i := i) r hip
    rw [← hr] at h1 h2
    rw [canon_succ_succ (n + 2), h1, h2]
    exact PmEq.refl _
  · obtain ⟨h1, h2⟩ := firstPair_ins_ge (p := p) (i := i) r (by omega) (by omega)
    rw [← hr] at h1 h2
    rw [canon_succ_succ (n + 2), h1, h2, hc, Category.assoc,
      show cup R δ n p ≫ cup R δ (n + 2) i = -(cup R δ n (i - 2) ≫ cup R δ (n + 2) p) from
        (by rw [cup_cup (by omega) (by omega), neg_neg]),
      Preadditive.comp_neg, ← Category.assoc]
    exact ((ih n (by omega) (List.replicate p 0 ++ r) hw0 (by simp; omega) (i - 2)
      (by omega)).comp_right _).neg_left

/-! ## Closure under caps -/

/-- The scalar of a cap: `δ` if it closes a loop, `1` otherwise. -/
def loopPow (b : Bool) : ℕ := if b then 1 else 0

/-- `canon (n + 2) w ≫ cap_i = ± δ^{[loop]} canon n (capT i w)`. -/
theorem canon_comp_cap (n : ℕ) : ∀ (w : List (Fin 2)), IsDyck w → w.length = n + 2 →
    ∀ i ≤ n, IsDyck (capT i w) ∧
      PmEq (canon R δ (n + 2) w ≫ cap R δ n i)
        (δ ^ loopPow (loopT i w) • canon R δ n (capT i w)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hl i hi
  have hne : w ≠ [] := by rintro rfl; simp at hl
  obtain ⟨r, hr⟩ := dyck_decomp hw hne
  generalize hp : firstPair w = p at hr
  have hlr : p + r.length = n := by rw [hr] at hl; simp at hl; omega
  have hw0 : IsDyck (List.replicate p 0 ++ r) := by
    have := hw.del_pair (p := p) (by omega) (by rw [hr]; simp [getD_rep_add p 0 0 (0 :: 1 :: r)])
      (by rw [hr]; simp [getD_rep_add p 1 0 (0 :: 1 :: r)])
    rwa [hr, del_rep] at this
  have hl0 : (List.replicate p (0 : Fin 2) ++ r).length = n := by simp; omega
  have hc : canon R δ (n + 2) w = canon R δ n (List.replicate p 0 ++ r) ≫ cup R δ n p := by
    rw [canon_succ_succ, hp]
    conv_lhs => rw [hr, del_rep]
  have hins : w = ins p 0 1 (List.replicate p 0 ++ r) := by
    rw [hr, ins_rep]
  rw [hc]
  simp only [Category.assoc]
  rcases lt_trichotomy i p with hlt | rfl | hgt
  · rcases Nat.lt_or_ge (i + 1) p with hlt' | hge
    · -- the cap is to the left of the first pair
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
      rw [cap_cup (by omega) (by omega), Preadditive.comp_neg, ← Category.assoc]
      obtain ⟨hd, h1⟩ := ih n (by omega) _ hw0 hl0 i (by omega)
      have h2 := canon_comp_cup (R := R) (δ := δ) n _ hd
        (by have := length_capT (i := i) (w := List.replicate p 0 ++ r) (by omega); omega)
        (p - 2) (by omega)
      obtain ⟨e1, e2⟩ := capT_ins_right hw0 (i := i) (p := p) (by omega) (by omega)
      rw [← hins] at e1 e2
      refine ⟨by rw [e1]; exact hd.ins_pair (by
        have := length_capT (i := i) (w := List.replicate p 0 ++ r) (by omega); omega), ?_⟩
      rw [e1, e2]
      refine PmEq.neg_left ?_
      refine (h1.comp_right _).trans ?_
      rw [Linear.smul_comp]
      exact h2.smul _
    · -- the cap is just to the left of the first pair: a zigzag
      obtain rfl : p = i + 1 := by omega
      rw [zigzagA_at (by omega), Category.comp_id]
      have e := capT_rep_pred i r
      rw [← hr] at e
      rw [e.1, e.2]
      refine ⟨hw0, ?_⟩
      simp only [loopPow, Bool.false_eq_true, if_false, pow_zero, one_smul]
      exact PmEq.refl _
  · -- the cap closes the first pair: a loop
    rw [loop_at hi, Linear.comp_smul, Category.comp_id]
    have e := capT_rep_self i r
    rw [← hr] at e
    rw [e.1, e.2]
    refine ⟨hw0, ?_⟩
    simp only [loopPow, if_true, pow_one]
    exact PmEq.refl _
  · rcases Nat.lt_or_ge (p + 1) i with hgt' | hle
    · -- the cap is to the right of the first pair
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
      rw [cup_cap (by omega) (by omega), Preadditive.comp_neg, ← Category.assoc]
      obtain ⟨hd, h1⟩ := ih n (by omega) _ hw0 hl0 (i - 2) (by omega)
      have h2 := canon_comp_cup (R := R) (δ := δ) n _ hd
        (by have := length_capT (i := i - 2) (w := List.replicate p 0 ++ r) (by omega); omega)
        p (by omega)
      obtain ⟨e1, e2⟩ := capT_ins_left hw0 (i := i - 2) (p := p) (by omega) (by omega)
      rw [show i - 2 + 2 = i by omega, ← hins] at e1 e2
      refine ⟨by rw [e1]; exact hd.ins_pair (by
        have := length_capT (i := i - 2) (w := List.replicate p 0 ++ r) (by omega); omega), ?_⟩
      rw [e1, e2]
      refine PmEq.neg_left ?_
      refine (h1.comp_right _).trans ?_
      rw [Linear.smul_comp]
      exact h2.smul _
    · -- the cap is just to the right of the first pair: a zigzag
      obtain rfl : i = p + 1 := by omega
      obtain ⟨c, r, rfl⟩ : ∃ c r', r = c :: r' := by
        rcases r with _ | ⟨c, r'⟩
        · simp at hlr; omega
        · exact ⟨c, r', rfl⟩
      rw [zigzagB_at hi, Preadditive.comp_neg, Category.comp_id]
      have e := capT_rep_succ p c r
      rw [← hr] at e
      rw [e.1, e.2]
      refine ⟨hw0, ?_⟩
      simp only [loopPow, Bool.false_eq_true, if_false, pow_zero, one_smul]
      exact (PmEq.refl _).neg_left

/-! ## Tracking arcs through a word -/

/-- Following the arcs of the crossingless matching `w` through the cups and caps of a word:
the crossingless matching (Dyck sequence) of the top boundary, and the number of closed loops
formed. -/
def trackW : List (Fin 2) → List Step → List (Fin 2) × ℕ
  | w, [] => (w, 0)
  | w, .cup i :: u => trackW (ins i 0 1 w) u
  | w, .cap i :: u => ((trackW (capT i w) u).1, (trackW (capT i w) u).2 + loopPow (loopT i w))

@[simp] theorem trackW_nil (w : List (Fin 2)) : trackW w [] = (w, 0) := rfl

@[simp] theorem trackW_cup (w : List (Fin 2)) (i : ℕ) (u : List Step) :
    trackW w (.cup i :: u) = trackW (ins i 0 1 w) u := rfl

@[simp] theorem trackW_cap (w : List (Fin 2)) (i : ℕ) (u : List Step) :
    trackW w (.cap i :: u) =
      ((trackW (capT i w) u).1, (trackW (capT i w) u).2 + loopPow (loopT i w)) := rfl

theorem trackW_append (w : List (Fin 2)) (u v : List Step) :
    trackW w (u ++ v) = ((trackW (trackW w u).1 v).1, (trackW (trackW w u).1 v).2 + (trackW w u).2) := by
  induction u generalizing w with
  | nil => simp
  | cons s u ih => cases s <;> simp [ih, add_assoc]

/-- **Tracking.** For a crossingless matching `w` of `k` points and a valid word `u` from `k`
strands, `canon k w ≫ evW u = ± δ^ℓ canon (trackW w u)`, where `trackW w u = (w', ℓ)` is obtained
by following the arcs through the cups and caps of `u` and `ℓ` is the number of closed loops. -/
theorem canon_comp_evW (u : List Step) : ∀ (k : ℕ) (w : List (Fin 2)), IsDyck w → w.length = k →
    Valid k u → IsDyck (trackW w u).1 ∧ (trackW w u).1.length = ht k u ∧
      PmEq (canon R δ k w ≫ evW R δ k u (ht k u))
        (δ ^ (trackW w u).2 • canon R δ (ht k u) (trackW w u).1) := by
  induction u with
  | nil =>
    intro k w hw hl _
    refine ⟨hw, hl, ?_⟩
    simp only [ht_nil, evW_nil_self, Category.comp_id, trackW_nil, pow_zero, one_smul]
    exact PmEq.refl _
  | cons s u ih => cases s with
    | cup i =>
      intro k w hw hl hu
      obtain ⟨h1, h2, h3⟩ := ih (k + 2) (ins i 0 1 w) (hw.ins_pair (by rw [hl]; exact hu.1))
        (by simp [hl]) hu.2
      refine ⟨h1, h2, ?_⟩
      simp only [ht_cup, evW_cup, trackW_cup]
      rw [← Category.assoc]
      exact ((canon_comp_cup k w hw hl i hu.1).comp_right _).trans h3
    | cap i =>
      intro k w hw hl hu
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by have := hu.1; omega⟩
      obtain ⟨hd, hc⟩ := canon_comp_cap (R := R) (δ := δ) k w hw hl i (by have := hu.1; omega)
      obtain ⟨h1, h2, h3⟩ := ih k (capT i w) hd
        (by have := length_capT (i := i) (w := w) (by have := hu.1; omega); omega) hu.2
      refine ⟨h1, h2, ?_⟩
      simp only [ht_cap, evW_cap, trackW_cap, Nat.add_sub_cancel]
      rw [← Category.assoc]
      refine (hc.comp_right _).trans ?_
      rw [Linear.smul_comp, pow_add, mul_comm, mul_smul]
      exact h3.smul _

/-- The crossingless matchings of `N` points, given by their Dyck sequences. -/
abbrev DyckSeq (N : ℕ) : Type := {w : List (Fin 2) // IsDyck w ∧ w.length = N}

/-- **Spanning (Theorem A.2 for `m = 0`).** The canonical cup diagrams span `Hom(0, N)`. -/
theorem span_canon (N : ℕ) :
    Submodule.span R (Set.range fun w : DyckSeq N => canon R δ N w.1) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f
  induction f using hom_induction_evW with
  | word u hu hN =>
    obtain ⟨h1, h2, h3⟩ := canon_comp_evW (R := R) (δ := δ) u 0 [] isDyck_nil rfl hu
    rw [canon_zero, Category.id_comp, hN] at h3
    rw [hN] at h2
    have hmem : canon R δ N (trackW [] u).1 ∈
        Submodule.span R (Set.range fun w : DyckSeq N => canon R δ N w.1) :=
      Submodule.subset_span ⟨⟨_, h1, h2⟩, rfl⟩
    rcases h3 with h | h <;> rw [h]
    · exact Submodule.smul_mem _ _ hmem
    · exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hmem)
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | smul r f hf => exact Submodule.smul_mem _ r hf

end StringDiagrams.OddTemperleyLieb

end
