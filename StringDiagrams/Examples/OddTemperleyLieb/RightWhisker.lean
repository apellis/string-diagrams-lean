import StringDiagrams.Examples.OddTemperleyLieb.Words

/-!
# Right whiskering and even morphisms of `STL(δ)`

* `wR1 x = x ⊗ 1`: right whiskering by one strand (`wR1_cup`, `wR1_cap`, `wR1_evW`: it does not
  change the positions of the generators).
* `evenSpan a b`: the span of the evaluations of words with an even number of generators, i.e.
  the even morphisms `a → b` (`evenSpan_eq_parity`, the parity-`0` part of the supercategory
  structure). It is closed under composition and right whiskering.
* The super interchange law for an even morphism and a cup or cap on its right, without sign:
  `x ≫ cup_b = cup_a ≫ (x ⊗ 1 ⊗ 1)` and `(x ⊗ 1 ⊗ 1) ≫ cap_b = cap_a ≫ x` for `x` even
  (`comp_cup_right`, `wR2_comp_cap_right`), from the exact-sign slides of a cup or cap at the far
  right of a word (`evW_slideCup`, `evW_slideCap`).
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory

variable {R : Type*} [CommRing R] {δ : R}

/-! ## Right whiskering by one strand -/

theorem strands_tensor_one (a : ℕ) : (strands a).tensor (strands 1) = strands (a + 1) :=
  obj_ext (by simp [strands, Obj.tensor])

variable (R δ) in
/-- Right whiskering `- ⊗ 1` by one strand. -/
def wR1 {a b : ℕ} (x : X R δ a ⟶ X R δ b) : X R δ (a + 1) ⟶ X R δ (b + 1) :=
  eqToHom (congrArg (pres R δ).obj (strands_tensor_one a).symm) ≫ (pres R δ).wR x (strands 1) ≫
    eqToHom (congrArg (pres R δ).obj (strands_tensor_one b))

theorem wR1_comp {a b c : ℕ} (x : X R δ a ⟶ X R δ b) (y : X R δ b ⟶ X R δ c) :
    wR1 R δ (x ≫ y) = wR1 R δ x ≫ wR1 R δ y := by
  simp [wR1, Presentation.wR_comp]

theorem wR1_add {a b : ℕ} (x y : X R δ a ⟶ X R δ b) :
    wR1 R δ (x + y) = wR1 R δ x + wR1 R δ y := by
  simp [wR1, Presentation.wR_add]

theorem wR1_smul {a b : ℕ} (r : R) (x : X R δ a ⟶ X R δ b) :
    wR1 R δ (r • x) = r • wR1 R δ x := by
  simp [wR1, Presentation.wR_smul]

theorem wR1_zero {a b : ℕ} : wR1 R δ (0 : X R δ a ⟶ X R δ b) = 0 := by
  simp [wR1, Presentation.wR_zero]

theorem wR1_neg {a b : ℕ} (x : X R δ a ⟶ X R δ b) : wR1 R δ (-x) = -wR1 R δ x := by
  rw [← neg_one_smul R x, wR1_smul, neg_one_smul]

theorem wR1_sub {a b : ℕ} (x y : X R δ a ⟶ X R δ b) :
    wR1 R δ (x - y) = wR1 R δ x - wR1 R δ y := by
  rw [sub_eq_add_neg, wR1_add, wR1_neg, ← sub_eq_add_neg]

theorem wR1_id (a : ℕ) : wR1 R δ (𝟙 (X R δ a)) = 𝟙 _ := by
  simp [wR1, Presentation.wR_id]

theorem wR1_cup {a i : ℕ} (h : i ≤ a) : wR1 R δ (cup R δ a i) = cup R δ (a + 1) i := by
  rw [cup_def h, cup_def (by omega), wR1, Presentation.wR_diag,
    (pres R δ).diag_eq_of_layers_eq' (Diagram.whiskerR (dcup h) (strands 1))
      (dcup (m := a + 1) (i := i) (by omega)) (strands_tensor_one a) (strands_tensor_one (a + 2)) ?_]
  · simp
  · simp only [Diagram.layers_whiskerR, dcup, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons.injEq, and_true]
    exact Layer.ext rfl rfl rfl (list_unit_ext (by simp [Layer.wr, strands]; omega))

theorem wR1_cap {a i : ℕ} (h : i ≤ a) : wR1 R δ (cap R δ a i) = cap R δ (a + 1) i := by
  rw [cap_def h, cap_def (by omega), wR1, Presentation.wR_diag,
    (pres R δ).diag_eq_of_layers_eq' (Diagram.whiskerR (dcap h) (strands 1))
      (dcap (m := a + 1) (i := i) (by omega)) (strands_tensor_one (a + 2)) (strands_tensor_one a) ?_]
  · simp
  · simp only [Diagram.layers_whiskerR, dcap, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons.injEq, and_true]
    exact Layer.ext rfl rfl rfl (list_unit_ext (by simp [Layer.wr, strands]; omega))

theorem wR1_eqToHom {a b : ℕ} (h : X R δ a = X R δ b) :
    wR1 R δ (eqToHom h) = eqToHom (by
      have := (pres R δ).obj_injective h
      rw [show a = b by simpa using congrArg (fun o : Obj sig => o.word.length) this]) := by
  have := (pres R δ).obj_injective h
  obtain rfl : a = b := by simpa using congrArg (fun o : Obj sig => o.word.length) this
  simp [wR1_id]

/-- Right whiskering does not change the positions of the generators of a word. -/
theorem wR1_evW {a : ℕ} {u : List Step} (hu : Valid a u) (b : ℕ) :
    wR1 R δ (evW R δ a u b) = evW R δ (a + 1) u (b + 1) := by
  induction u generalizing a with
  | nil =>
    by_cases hab : a = b
    · subst hab; simp only [evW_nil_self, wR1_id]
    · rw [evW_nil_of_ne hab, wR1_zero, evW_nil_of_ne (by omega)]
  | cons s u ih => cases s with
    | cup i =>
      rw [evW_cup, wR1_comp, wR1_cup hu.1, ih hu.2, evW_cup]
    | cap i =>
      obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by have := hu.1; omega⟩
      rw [evW_cap, wR1_comp, wR1_cap (by have := hu.1; omega), ih (a := a) hu.2]
      exact (evW_cap (a + 1) i u (b + 1)).symm

theorem valid_add {a : ℕ} {u : List Step} (hu : Valid a u) (k : ℕ) : Valid (a + k) u := by
  induction u generalizing a with
  | nil => trivial
  | cons s u ih => cases s with
    | cup i => exact ⟨by have := hu.1; omega, by
        have := ih hu.2; rwa [show a + 2 + k = a + k + 2 by omega] at this⟩
    | cap i => exact ⟨by have := hu.1; omega, by
        have := ih hu.2; rwa [show a - 2 + k = a + k - 2 by have := hu.1; omega] at this⟩

theorem ht_add {a : ℕ} {u : List Step} (hu : Valid a u) (k : ℕ) : ht (a + k) u = ht a u + k := by
  induction u generalizing a with
  | nil => rfl
  | cons s u ih => cases s with
    | cup i => simp only [ht_cup]; rw [show a + k + 2 = a + 2 + k by omega]; exact ih hu.2
    | cap i =>
      simp only [ht_cap]; rw [show a + k - 2 = a - 2 + k by have := hu.1; omega]; exact ih hu.2

/-! ## Sliding a cup or a cap at the far right -/

/-- A cup at the far right slides under a word, with the sign `(-1)^{length}`. -/
theorem evW_slideCup (u : List Step) {A : ℕ} (hu : Valid A u) (v : List Step) (c : ℕ) :
    evW R δ A (u ++ .cup (ht A u) :: v) c =
      ((-1 : R) ^ u.length) • evW R δ A (.cup A :: (u ++ v)) c := by
  induction u generalizing A with
  | nil => simp
  | cons s u ih => cases s with
    | cup i =>
      simp only [List.cons_append, ht_cup, evW_cup, List.length_cons]
      rw [ih hu.2, Linear.comp_smul, ← evW_cup, ← evW_cup,
        evW_cup_cup (by have := hu.1; omega) le_rfl, show A + 2 - 2 = A by omega, pow_succ,
        mul_neg_one, neg_smul, smul_neg, evW_cup]
    | cap i =>
      obtain ⟨A, rfl⟩ : ∃ A', A = A' + 2 := ⟨A - 2, by have := hu.1; omega⟩
      simp only [List.cons_append, ht_cap, evW_cap, List.length_cons, Nat.add_sub_cancel]
      rw [ih (A := A) hu.2, Linear.comp_smul, ← evW_cap]
      have := evW_cap_cup (R := R) (δ := δ) (W := A + 2) (i := i) (j := A + 2)
        (by have := hu.1; omega) le_rfl (u ++ v) c
      rw [show A + 2 - 2 = A by omega] at this
      rw [this, pow_succ, mul_neg_one, neg_smul, smul_neg, neg_neg]

/-- A cap at the far right slides under a word, with the sign `(-1)^{length}`. -/
theorem evW_slideCap (u : List Step) {A : ℕ} (hu : Valid A u) (v : List Step) (c : ℕ) :
    evW R δ (A + 2) (u ++ .cap (ht A u) :: v) c =
      ((-1 : R) ^ u.length) • evW R δ (A + 2) (.cap A :: (u ++ v)) c := by
  induction u generalizing A with
  | nil => simp
  | cons s u ih => cases s with
    | cup i =>
      simp only [List.cons_append, ht_cup, evW_cup, List.length_cons]
      rw [ih hu.2, Linear.comp_smul, ← evW_cup]
      have := evW_cup_cap (R := R) (δ := δ) (W := A + 2) (i := i) (j := A + 2)
        (by have := hu.1; omega) le_rfl (by have := hu.1; omega) (u ++ v) c
      rw [show A + 2 - 2 = A by omega] at this
      rw [this, pow_succ, mul_neg_one, neg_smul, smul_neg, evW_cap]
    | cap i =>
      obtain ⟨A, rfl⟩ : ∃ A', A = A' + 2 := ⟨A - 2, by have := hu.1; omega⟩
      simp only [List.cons_append, ht_cap, List.length_cons, Nat.add_sub_cancel]
      rw [evW_cap, ih (A := A) hu.2, Linear.comp_smul, ← evW_cap]
      have := evW_cap_cap (R := R) (δ := δ) (W := A + 2 + 2) (i := i) (j := A + 2)
        (by have := hu.1; omega) le_rfl (u ++ v) c
      rw [show A + 2 - 2 = A by omega] at this
      rw [this, pow_succ, mul_neg_one, neg_smul, smul_neg, neg_neg]

/-! ## Even morphisms -/

variable (R δ) in
/-- The even morphisms `a → b`: the span of evaluations of words with an even number of
generators. -/
def evenSpan (a b : ℕ) : Submodule R (X R δ a ⟶ X R δ b) :=
  Submodule.span R {x | ∃ u, Valid a u ∧ ht a u = b ∧ Even u.length ∧ x = evW R δ a u b}

theorem evW_mem_evenSpan {a b : ℕ} {u : List Step} (hu : Valid a u) (hb : ht a u = b)
    (he : Even u.length) : evW R δ a u b ∈ evenSpan R δ a b :=
  Submodule.subset_span ⟨u, hu, hb, he, rfl⟩

theorem id_mem_evenSpan (a : ℕ) : 𝟙 (X R δ a) ∈ evenSpan R δ a a := by
  rw [← evW_nil_self]; exact evW_mem_evenSpan trivial rfl (by simp)

/-- Induction on even morphisms. -/
theorem evenSpan_induction {a b : ℕ} {p : (X R δ a ⟶ X R δ b) → Prop}
    (word : ∀ u, Valid a u → ht a u = b → Even u.length → p (evW R δ a u b)) (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y)) (smul : ∀ (r : R) x, p x → p (r • x))
    {x : X R δ a ⟶ X R δ b} (hx : x ∈ evenSpan R δ a b) : p x := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨u, hu, hb, he, rfl⟩ := hy; exact word u hu hb he
  | zero => exact zero
  | add y z _ _ hy hz => exact add y z hy hz
  | smul r y _ hy => exact smul r y hy

theorem comp_mem_evenSpan {a b c : ℕ} {x : X R δ a ⟶ X R δ b} {y : X R δ b ⟶ X R δ c}
    (hx : x ∈ evenSpan R δ a b) (hy : y ∈ evenSpan R δ b c) : x ≫ y ∈ evenSpan R δ a c := by
  refine evenSpan_induction (p := fun x => x ≫ y ∈ evenSpan R δ a c) (fun u hu hb he => ?_)
    (by dsimp only; rw [Limits.zero_comp]; exact Submodule.zero_mem _)
    (fun x z hx hz => by dsimp only at *; rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hz)
    (fun r x hx => by dsimp only at *; rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx) hx
  refine evenSpan_induction (p := fun y => evW R δ a u b ≫ y ∈ evenSpan R δ a c)
    (fun v hv hc hve => ?_) (by dsimp only; rw [Limits.comp_zero]; exact Submodule.zero_mem _)
    (fun y z hy hz => by dsimp only at *; rw [Preadditive.comp_add]; exact Submodule.add_mem _ hy hz)
    (fun r y hy => by dsimp only at *; rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hy) hy
  dsimp only
  rw [← evW_append a u v hb]
  refine evW_mem_evenSpan (valid_append.mpr ⟨hu, hb ▸ hv⟩) (by rw [ht_append, hb, hc]) ?_
  rw [List.length_append]; exact he.add hve

theorem wR1_mem_evenSpan {a b : ℕ} {x : X R δ a ⟶ X R δ b} (hx : x ∈ evenSpan R δ a b) :
    wR1 R δ x ∈ evenSpan R δ (a + 1) (b + 1) := by
  refine evenSpan_induction (p := fun x => wR1 R δ x ∈ evenSpan R δ (a + 1) (b + 1))
    (fun u hu hb he => ?_) (by dsimp only; rw [wR1_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by dsimp only at *; rw [wR1_add]; exact Submodule.add_mem _ hx hy)
    (fun r x hx => by dsimp only at *; rw [wR1_smul]; exact Submodule.smul_mem _ r hx) hx
  dsimp only
  rw [wR1_evW hu]
  exact evW_mem_evenSpan (valid_add hu 1) (by rw [ht_add hu, hb]) he

/-- An even morphism commutes with a cup on its right. -/
theorem comp_cup_right {a b : ℕ} {x : X R δ a ⟶ X R δ b} (hx : x ∈ evenSpan R δ a b) :
    x ≫ cup R δ b b = cup R δ a a ≫ wR1 R δ (wR1 R δ x) := by
  refine evenSpan_induction (p := fun x => x ≫ cup R δ b b = cup R δ a a ≫ wR1 R δ (wR1 R δ x))
    (fun u hu hb he => ?_) (by simp [wR1_zero])
    (fun x y hx hy => by
      dsimp only at *; simp only [Preadditive.add_comp, hx, hy, wR1_add, Preadditive.comp_add])
    (fun r x hx => by
      dsimp only at *; simp only [Linear.smul_comp, hx, wR1_smul, Linear.comp_smul]) hx
  · dsimp only
    rw [wR1_evW hu, wR1_evW (valid_add hu 1)]
    have h1 := evW_slideCup (R := R) (δ := δ) u hu [] (b + 2)
    rw [hb, evW_append a u _ hb, evW_cup, evW_nil_self, Category.comp_id, he.neg_one_pow,
      one_smul, List.append_nil, evW_cup] at h1
    exact h1

/-- An even morphism commutes with a cap on its right. -/
theorem wR2_comp_cap_right {a b : ℕ} {x : X R δ a ⟶ X R δ b} (hx : x ∈ evenSpan R δ a b) :
    wR1 R δ (wR1 R δ x) ≫ cap R δ b b = cap R δ a a ≫ x := by
  refine evenSpan_induction (p := fun x => wR1 R δ (wR1 R δ x) ≫ cap R δ b b = cap R δ a a ≫ x)
    (fun u hu hb he => ?_) (by simp [wR1_zero])
    (fun x y hx hy => by
      dsimp only at *; simp only [Preadditive.comp_add, hx, hy, wR1_add, Preadditive.add_comp])
    (fun r x hx => by
      dsimp only at *; simp only [Linear.comp_smul, hx, wR1_smul, Linear.smul_comp]) hx
  · dsimp only
    rw [wR1_evW hu, wR1_evW (valid_add hu 1)]
    have h1 := evW_slideCap (R := R) (δ := δ) u hu [] b
    rw [hb, evW_append (a + 2) u _ (b := b + 2) (by rw [ht_add hu, hb]), evW_cap, evW_nil_self,
      Category.comp_id, he.neg_one_pow, one_smul, List.append_nil, evW_cap] at h1
    exact h1

end StringDiagrams.OddTemperleyLieb

end
