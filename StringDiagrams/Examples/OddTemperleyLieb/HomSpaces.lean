import StringDiagrams.Examples.OddTemperleyLieb.JonesWenzl

/-!
# Morphisms between Jones–Wenzl projectors

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, proof of Theorem A.3
(second paragraph).

Every morphism `m → n` of `STL(δ)` is a linear combination of evaluations of words consisting
of caps followed by cups (`mem_nfSpan`): a cup followed by a cap can be removed (loop, zigzags)
or the two interchanged. Composing with Jones–Wenzl projectors on both sides kills every such
word that contains a cap or a cup, so

* `jw_comp_comp_jw_of_ne`: `f_m ∘ Hom(m, n) ∘ f_n = 0` for `m ≠ n`, i.e.
  `Hom_A(P(m), P(n)) = f_n A f_m = 0`;
* `jw_comp_comp_jw_self`: `f_n ∘ End(n) ∘ f_n = k f_n`, i.e. `End_A(P(n)) = f_n A f_n ≅ k`
  (`f_n ≠ 0` by `jw_ne_zero`), so `f_n` is a primitive idempotent.
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory
open Rep (delta)

variable {R : Type*} [CommRing R] {δ : R}

/-! ## Caps first, then cups -/

/-- A word made of caps only. -/
def IsCapWord : List Step → Prop
  | [] => True
  | .cap _ :: u => IsCapWord u
  | .cup _ :: _ => False

/-- A word made of cups only. -/
def IsCupWord : List Step → Prop
  | [] => True
  | .cup _ :: u => IsCupWord u
  | .cap _ :: _ => False

theorem isCupWord_append {u v : List Step} (hu : IsCupWord u) (hv : IsCupWord v) :
    IsCupWord (u ++ v) := by
  induction u with
  | nil => exact hv
  | cons s u ih => cases s with
    | cup i => exact ih hu
    | cap i => exact absurd hu id

variable (R δ) in
/-- The span of the words "caps, then cups". -/
def nfSpan (a b : ℕ) : Submodule R (X R δ a ⟶ X R δ b) :=
  Submodule.span R {x | ∃ C U, IsCapWord C ∧ IsCupWord U ∧ Valid a (C ++ U) ∧
    ht a (C ++ U) = b ∧ x = evW R δ a (C ++ U) b}

theorem nf_mem {a b : ℕ} {C U : List Step} (hC : IsCapWord C) (hU : IsCupWord U)
    (hv : Valid a (C ++ U)) (hb : ht a (C ++ U) = b) : evW R δ a (C ++ U) b ∈ nfSpan R δ a b :=
  Submodule.subset_span ⟨C, U, hC, hU, hv, hb, rfl⟩

theorem nfSpan_induction {a b : ℕ} {p : (X R δ a ⟶ X R δ b) → Prop}
    (word : ∀ C U, IsCapWord C → IsCupWord U → Valid a (C ++ U) → ht a (C ++ U) = b →
      p (evW R δ a (C ++ U) b))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (smul : ∀ (r : R) x, p x → p (r • x))
    {x : X R δ a ⟶ X R δ b} (hx : x ∈ nfSpan R δ a b) : p x := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨C, U, hC, hU, hv, hb, rfl⟩ := hy; exact word C U hC hU hv hb
  | zero => exact zero
  | add y z _ _ hy hz => exact add y z hy hz
  | smul r y _ hy => exact smul r y hy

/-- A cap below a word "caps, then cups" gives such a word. -/
theorem cap_comp_mem_nfSpan {a b i : ℕ} (hi : i ≤ a) {x : X R δ a ⟶ X R δ b}
    (hx : x ∈ nfSpan R δ a b) : cap R δ a i ≫ x ∈ nfSpan R δ (a + 2) b := by
  refine nfSpan_induction (p := fun x => cap R δ a i ≫ x ∈ nfSpan R δ (a + 2) b)
    (fun C U hC hU hv hb => ?_) (by dsimp only; rw [Limits.comp_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by dsimp only at *; rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy)
    (fun r x hx => by dsimp only at *; rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx) hx
  dsimp only
  rw [← evW_cap, ← List.cons_append]
  exact nf_mem (C := .cap i :: C) hC hU ⟨by omega, hv⟩ hb

/-- A cup below a word "caps, then cups" gives a combination of such words. -/
theorem cup_comp_nf (C : List Step) (hC : IsCapWord C) : ∀ {a j : ℕ} {U : List Step} {b : ℕ},
    IsCupWord U → j ≤ a → Valid (a + 2) (C ++ U) → ht (a + 2) (C ++ U) = b →
      cup R δ a j ≫ evW R δ (a + 2) (C ++ U) b ∈ nfSpan R δ a b := by
  induction C with
  | nil =>
    intro a j U b hU hj hv hb
    rw [← evW_cup]
    exact nf_mem (C := []) (U := .cup j :: U) trivial hU ⟨hj, hv⟩ hb
  | cons s C ih =>
    cases s with
    | cup i => exact absurd hC id
    | cap i =>
      intro a j U b hU hj hv hb
      have hi : i ≤ a := by have := hv.1; omega
      replace hv : Valid a (C ++ U) := hv.2
      replace hb : ht a (C ++ U) = b := hb
      simp only [List.cons_append, evW_cap]
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · rcases Nat.lt_or_ge (i + 1) j with h | h
        · -- the cap is to the left of the cup
          obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
          rw [← Category.assoc, cap_cup (by omega) hj, Preadditive.neg_comp, Category.assoc]
          exact Submodule.neg_mem _ (cap_comp_mem_nfSpan (by omega)
            (ih hC hU (by omega) hv hb))
        · obtain rfl : j = i + 1 := by omega
          rw [← Category.assoc, zigzagA_at hj, Category.id_comp]
          exact nf_mem hC hU hv hb
      · rw [← Category.assoc, loop_at hj, Linear.smul_comp, Category.id_comp]
        exact Submodule.smul_mem _ _ (nf_mem hC hU hv hb)
      · rcases Nat.lt_or_ge (j + 1) i with h | h
        · -- the cap is to the right of the cup
          obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
          rw [← Category.assoc, cup_cap (by omega) (by omega), Preadditive.neg_comp,
            Category.assoc]
          exact Submodule.neg_mem _ (cap_comp_mem_nfSpan (by omega)
            (ih hC hU (by omega) hv hb))
        · obtain rfl : i = j + 1 := by omega
          rw [← Category.assoc, zigzagB_at (by omega), Preadditive.neg_comp, Category.id_comp]
          exact Submodule.neg_mem _ (nf_mem hC hU hv hb)

theorem cup_comp_mem_nfSpan {a b j : ℕ} (hj : j ≤ a) {x : X R δ (a + 2) ⟶ X R δ b}
    (hx : x ∈ nfSpan R δ (a + 2) b) : cup R δ a j ≫ x ∈ nfSpan R δ a b := by
  refine nfSpan_induction (p := fun x => cup R δ a j ≫ x ∈ nfSpan R δ a b)
    (fun C U hC hU hv hb => ?_) (by dsimp only; rw [Limits.comp_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by dsimp only at *; rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy)
    (fun r x hx => by dsimp only at *; rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx) hx
  exact cup_comp_nf C hC hU hj hv hb

/-- **Every morphism is a combination of words "caps, then cups".** -/
theorem mem_nfSpan {a b : ℕ} (x : X R δ a ⟶ X R δ b) : x ∈ nfSpan R δ a b := by
  induction x using hom_induction_evW with
  | word u hu hb =>
    induction u generalizing a with
    | nil => exact nf_mem (C := []) (U := []) trivial trivial trivial hb
    | cons s u ih => cases s with
      | cup j =>
        rw [evW_cup]
        exact cup_comp_mem_nfSpan hu.1 (ih hu.2 hb)
      | cap i =>
        obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by have := hu.1; omega⟩
        rw [evW_cap]
        exact cap_comp_mem_nfSpan (by have := hu.1; omega) (ih (a := a) hu.2 hb)
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | smul r f hf => exact Submodule.smul_mem _ r hf

/-! ## Sandwiching between Jones–Wenzl projectors -/

variable {k : Type*} [Field k] {q : kˣ}

local notation "δq" => delta q

/-- A non-empty word "caps, then cups" between Jones–Wenzl projectors is zero. -/
theorem jw_comp_nf_comp_jw (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) {m n : ℕ} {C U : List Step}
    (hC : IsCapWord C) (hU : IsCupWord U) (hv : Valid m (C ++ U)) (hb : ht m (C ++ U) = n)
    (hne : C ++ U ≠ []) : jw q m ≫ evW k δq m (C ++ U) n ≫ jw q n = 0 := by
  rcases C with _ | ⟨s, C⟩
  · rcases List.eq_nil_or_concat U with rfl | ⟨U', s, rfl⟩
    · exact absurd rfl hne
    · -- the last cup is killed by `f_n`
      simp only [List.concat_eq_append] at hU hv hb hne ⊢
      have hs : IsCupWord (U' ++ [s]) := hU
      obtain ⟨j, rfl⟩ : ∃ j, s = .cup j := by
        clear hb hv hne hU
        induction U' with
        | nil => cases s with
          | cup j => exact ⟨j, rfl⟩
          | cap i => exact absurd hs id
        | cons t U' ih => cases t with
          | cup i => exact ih hs
          | cap i => exact absurd hs id
      simp only [List.nil_append] at hv hb ⊢
      have hv' := (valid_append.mp hv).2
      rw [ht_append] at hb
      simp only [ht_cup, ht_nil] at hb
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨ht m U', by omega⟩
      have hU' : ht m U' = n' := by omega
      rw [evW_append m U' _ hU', evW_cup, evW_nil_self, Category.comp_id]
      simp only [Category.assoc]
      rw [cup_comp_jw hq (by rw [← hU']; exact hv'.1)]
      simp
  · cases s with
    | cup i => exact absurd hC id
    | cap i =>
      have hv' : Valid m (.cap i :: (C ++ U)) := by simpa using hv
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by have := hv'.1; omega⟩
      rw [List.cons_append, evW_cap]
      simp only [Category.assoc]
      rw [← Category.assoc (jw q (m' + 2)), jw_comp_cap hq (by have := hv'.1; omega)]
      simp

/-- **`Hom_A(P(m), P(n)) = 0` for `m ≠ n`.** -/
theorem jw_comp_comp_jw_of_ne (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) {m n : ℕ} (hmn : m ≠ n)
    (x : X k δq m ⟶ X k δq n) : jw q m ≫ x ≫ jw q n = 0 := by
  refine nfSpan_induction (p := fun x => jw q m ≫ x ≫ jw q n = 0) (fun C U hC hU hv hb => ?_)
    (by simp) (fun x y hx hy => by dsimp only at *; simp [hx, hy])
    (fun r x hx => by dsimp only at *; simp [hx]) (mem_nfSpan x)
  refine jw_comp_nf_comp_jw hq hC hU hv hb fun h => ?_
  rw [h] at hb
  exact hmn hb

/-- **`End_A(P(n)) = k f_n`.** -/
theorem jw_comp_comp_jw_self (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) {n : ℕ}
    (x : X k δq n ⟶ X k δq n) : ∃ c : k, jw q n ≫ x ≫ jw q n = c • jw q n := by
  refine nfSpan_induction (p := fun x => ∃ c : k, jw q n ≫ x ≫ jw q n = c • jw q n)
    (fun C U hC hU hv hb => ?_) ⟨0, by simp⟩
    (fun x y hx hy => by
      obtain ⟨c, hc⟩ := hx; obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, by simp [Preadditive.add_comp, Preadditive.comp_add, hc, hd, add_smul]⟩)
    (fun r x hx => by
      obtain ⟨c, hc⟩ := hx
      exact ⟨r * c, by simp [hc, smul_smul]⟩) (mem_nfSpan x)
  by_cases hne : C ++ U = []
  · refine ⟨1, ?_⟩
    rw [hne, evW_nil_self, Category.id_comp, jw_idem hq, one_smul]
  · exact ⟨0, by rw [jw_comp_nf_comp_jw hq hC hU hv hb hne, zero_smul]⟩

end StringDiagrams.OddTemperleyLieb

end
