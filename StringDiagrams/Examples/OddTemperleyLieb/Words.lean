import StringDiagrams.Examples.OddTemperleyLieb.Basic
import StringDiagrams.Monoidal

/-!
# Words in cups and caps

A diagram of `STL(δ)` is a composite of layers, each a cup or a cap at some position. This
file records diagrams as *words* `List Step` and evaluates a word, starting from a given number
of strands, in the presented category (`evW`); the evaluation is defined for every source and
target, and is zero when the target is not the number of strands reached (`ht`) or a step is
out of range (`Valid`). The class of a diagram is the evaluation of its word (`diag_eq_evW`).

Equalities of evaluations up to sign (`PmEq`) are derived from the local relations: the
zigzag and loop relations (`evW_zigzagA`, `evW_zigzagB`, `evW_loop`) and the anticommutation
of generators at disjoint positions (`evW_cup_cup`, `evW_cap_cap`, `evW_cup_cap`,
`evW_cap_cup`). From them:

* `evW_farCap`: a cap slides under a word acting to its right, with a sign;
* `evW_farCaps`: `m` nested caps slide under a word acting to their right;
* `evW_snake`: the `m`-strand zigzag (nested cups on the right, then nested caps) is `± 1`;
* `evW_farCup`, `evW_snake'`: the mirror statements (a cup slides over a word to its right,
  and the `m`-strand zigzag with nested cups on the left is `± 1`).

Left whiskering by `m` strands (`wLs`) shifts words (`wLs_evW`).
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory

/-! ## Signs -/

/-- Equality up to sign. -/
def PmEq {M : Type*} [AddCommGroup M] (x y : M) : Prop := x = y ∨ x = -y

namespace PmEq

variable {M : Type*} [AddCommGroup M] {x y z : M}

theorem refl (x : M) : PmEq x x := Or.inl rfl

theorem of_eq (h : x = y) : PmEq x y := Or.inl h

theorem of_eq_neg (h : x = -y) : PmEq x y := Or.inr h

theorem symm (h : PmEq x y) : PmEq y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

theorem trans (h₁ : PmEq x y) (h₂ : PmEq y z) : PmEq x z := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> subst h₁ h₂
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

theorem neg_left (h : PmEq x y) : PmEq (-x) y := by
  rcases h with h | h <;> subst h
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

theorem neg_right (h : PmEq x y) : PmEq x (-y) := (neg_left h.symm).symm

theorem map {N : Type*} [AddCommGroup N] (f : M →+ N) (h : PmEq x y) : PmEq (f x) (f y) := by
  rcases h with h | h <;> subst h
  · exact Or.inl rfl
  · exact Or.inr (map_neg f _)

theorem smul {R : Type*} [Ring R] [Module R M] (r : R) (h : PmEq x y) : PmEq (r • x) (r • y) := by
  rcases h with h | h <;> subst h
  · exact Or.inl rfl
  · exact Or.inr (smul_neg r _)

theorem zero_iff (h : PmEq x y) : x = 0 ↔ y = 0 := by
  rcases h with h | h <;> subst h <;> simp

end PmEq

section Comp

variable {C : Type*} [Category C] [Preadditive C] {A B D : C}

theorem PmEq.comp_right {x y : A ⟶ B} (h : PmEq x y) (f : B ⟶ D) : PmEq (x ≫ f) (y ≫ f) :=
  h.map (Preadditive.rightComp A f)

theorem PmEq.comp_left {x y : B ⟶ D} (h : PmEq x y) (f : A ⟶ B) : PmEq (f ≫ x) (f ≫ y) :=
  h.map (Preadditive.leftComp D f)

end Comp

/-! ## Words -/

/-- A cup or a cap at a position. -/
inductive Step
  | cup (i : ℕ)
  | cap (i : ℕ)
  deriving DecidableEq

/-- Shift a step by `m` positions to the right. -/
def Step.shift (m : ℕ) : Step → Step
  | .cup i => .cup (m + i)
  | .cap i => .cap (m + i)

/-- Shift a word by `m` positions to the right (left whiskering by `m` strands). -/
def shiftW (m : ℕ) (u : List Step) : List Step := u.map (Step.shift m)

@[simp] theorem shiftW_nil (m : ℕ) : shiftW m [] = [] := rfl

@[simp] theorem shiftW_cons (m : ℕ) (s : Step) (u : List Step) :
    shiftW m (s :: u) = s.shift m :: shiftW m u := rfl

@[simp] theorem shiftW_append (m : ℕ) (u v : List Step) :
    shiftW m (u ++ v) = shiftW m u ++ shiftW m v := List.map_append

@[simp] theorem Step.shift_cup (m i : ℕ) : (Step.cup i).shift m = .cup (m + i) := rfl
@[simp] theorem Step.shift_cap (m i : ℕ) : (Step.cap i).shift m = .cap (m + i) := rfl

theorem shiftW_zero (u : List Step) : shiftW 0 u = u := by
  induction u with
  | nil => rfl
  | cons s u ih => cases s <;> simp [ih]

theorem shiftW_shiftW (m n : ℕ) (u : List Step) : shiftW m (shiftW n u) = shiftW (m + n) u := by
  induction u with
  | nil => rfl
  | cons s u ih => cases s <;> simp [ih, add_assoc]

/-- The number of strands reached by a word from `a` strands. -/
def ht : ℕ → List Step → ℕ
  | a, [] => a
  | a, .cup _ :: u => ht (a + 2) u
  | a, .cap _ :: u => ht (a - 2) u

/-- All steps of a word from `a` strands are in range. -/
def Valid : ℕ → List Step → Prop
  | _, [] => True
  | a, .cup i :: u => i ≤ a ∧ Valid (a + 2) u
  | a, .cap i :: u => i + 2 ≤ a ∧ Valid (a - 2) u

@[simp] theorem ht_nil (a : ℕ) : ht a [] = a := rfl
@[simp] theorem ht_cup (a i : ℕ) (u : List Step) : ht a (.cup i :: u) = ht (a + 2) u := rfl
@[simp] theorem ht_cap (a i : ℕ) (u : List Step) : ht a (.cap i :: u) = ht (a - 2) u := rfl
@[simp] theorem valid_nil (a : ℕ) : Valid a [] := trivial
@[simp] theorem valid_cup (a i : ℕ) (u : List Step) :
    Valid a (.cup i :: u) ↔ i ≤ a ∧ Valid (a + 2) u := Iff.rfl
@[simp] theorem valid_cap (a i : ℕ) (u : List Step) :
    Valid a (.cap i :: u) ↔ i + 2 ≤ a ∧ Valid (a - 2) u := Iff.rfl

theorem ht_append (a : ℕ) (u v : List Step) : ht a (u ++ v) = ht (ht a u) v := by
  induction u generalizing a with
  | nil => rfl
  | cons s u ih => cases s <;> simp [ih]

theorem valid_append {a : ℕ} {u v : List Step} :
    Valid a (u ++ v) ↔ Valid a u ∧ Valid (ht a u) v := by
  induction u generalizing a with
  | nil => simp
  | cons s u ih => cases s <;> simp [ih, and_assoc]

theorem ht_shiftW (m a : ℕ) {u : List Step} (hu : Valid a u) : ht (m + a) (shiftW m u) = m + ht a u := by
  induction u generalizing a with
  | nil => rfl
  | cons s u ih => cases s with
    | cup i => simp only [shiftW_cons, Step.shift_cup, ht_cup]; exact ih (a + 2) hu.2
    | cap i =>
      simp only [shiftW_cons, Step.shift_cap, ht_cap]
      rw [show m + a - 2 = m + (a - 2) by have := hu.1; omega]; exact ih (a - 2) hu.2

theorem valid_shiftW (m a : ℕ) {u : List Step} (hu : Valid a u) : Valid (m + a) (shiftW m u) := by
  induction u generalizing a with
  | nil => trivial
  | cons s u ih => cases s with
    | cup i => exact ⟨by have := hu.1; omega, ih (a + 2) hu.2⟩
    | cap i =>
      refine ⟨by have := hu.1; omega, ?_⟩
      rw [show m + a - 2 = m + (a - 2) by have := hu.1; omega]; exact ih (a - 2) hu.2

variable (R : Type*) [CommRing R] (δ : R)

/-- The evaluation of a word from `a` strands, as a morphism to `b` strands (zero if `b` is
not the number of strands reached, or if a step is out of range). -/
def evW : (a : ℕ) → List Step → (b : ℕ) → (X R δ a ⟶ X R δ b)
  | a, [], b => if h : a = b then eqToHom (by rw [h]) else 0
  | a, .cup i :: u, b => cup R δ a i ≫ evW (a + 2) u b
  | a + 2, .cap i :: u, b => cap R δ a i ≫ evW a u b
  | _, .cap _ :: _, _ => 0

variable {R δ}

@[simp] theorem evW_nil_self (a : ℕ) : evW R δ a [] a = 𝟙 _ := by simp [evW]

theorem evW_nil_of_ne {a b : ℕ} (h : a ≠ b) : evW R δ a [] b = 0 := by simp [evW, h]

@[simp] theorem evW_cup (a i : ℕ) (u : List Step) (b : ℕ) :
    evW R δ a (.cup i :: u) b = cup R δ a i ≫ evW R δ (a + 2) u b := by rw [evW]

@[simp] theorem evW_cap (a i : ℕ) (u : List Step) (b : ℕ) :
    evW R δ (a + 2) (.cap i :: u) b = cap R δ a i ≫ evW R δ a u b := by rw [evW]

theorem evW_cap_of_lt {a : ℕ} (ha : a < 2) (i : ℕ) (u : List Step) (b : ℕ) :
    evW R δ a (.cap i :: u) b = 0 := by
  rcases a with _ | _ | a
  · rw [evW]; intros; omega
  · rw [evW]; intros; omega
  · omega

/-- Evaluation of a concatenation. -/
theorem evW_append (a : ℕ) (u v : List Step) {b : ℕ} (hb : ht a u = b) (c : ℕ) :
    evW R δ a (u ++ v) c = evW R δ a u b ≫ evW R δ b v c := by
  subst hb
  induction u generalizing a with
  | nil => simp
  | cons s u ih => cases s with
    | cup i => simp [ih]
    | cap i =>
      match a with
      | 0 => simp [evW_cap_of_lt]
      | 1 => simp [evW_cap_of_lt]
      | a + 2 => simp [ih]; rfl

/-- Right congruence: equal evaluations up to sign stay so after appending a word. -/
theorem PmEq.append_right {a : ℕ} {u u' : List Step} {b : ℕ} (hu : ht a u = b) (hu' : ht a u' = b)
    (h : PmEq (evW R δ a u b) (evW R δ a u' b)) (v : List Step) (c : ℕ) :
    PmEq (evW R δ a (u ++ v) c) (evW R δ a (u' ++ v) c) := by
  rw [evW_append a u v hu, evW_append a u' v hu']
  exact h.comp_right _

/-- Left congruence for a prefix. -/
theorem PmEq.evW_prefix {a : ℕ} (w : List Step) {b : ℕ} (hb : ht a w = b) {v v' : List Step}
    {c : ℕ} (h : PmEq (evW R δ b v c) (evW R δ b v' c)) :
    PmEq (evW R δ a (w ++ v) c) (evW R δ a (w ++ v') c) := by
  rw [evW_append a w v hb, evW_append a w v' hb]
  exact h.comp_left _

/-- Left congruence for a cup. -/
theorem PmEq.evW_cons_cup {a i : ℕ} {v v' : List Step} {c : ℕ}
    (h : PmEq (evW R δ (a + 2) v c) (evW R δ (a + 2) v' c)) :
    PmEq (evW R δ a (.cup i :: v) c) (evW R δ a (.cup i :: v') c) := by
  rw [evW_cup, evW_cup]; exact h.comp_left _

/-- Left congruence for a cap. -/
theorem PmEq.evW_cons_cap {a i : ℕ} {v v' : List Step} {c : ℕ}
    (h : PmEq (evW R δ a v c) (evW R δ a v' c)) :
    PmEq (evW R δ (a + 2) (.cap i :: v) c) (evW R δ (a + 2) (.cap i :: v') c) := by
  rw [evW_cap, evW_cap]; exact h.comp_left _

/-! ## The local relations on words -/

theorem evW_zigzagA {W i : ℕ} (h : i + 1 ≤ W) (v : List Step) (c : ℕ) :
    evW R δ W (.cup (i + 1) :: .cap i :: v) c = evW R δ W v c := by
  rw [evW_cup, evW_cap, ← Category.assoc, zigzagA_at h, Category.id_comp]

theorem evW_zigzagB {W i : ℕ} (h : i + 1 ≤ W) (v : List Step) (c : ℕ) :
    evW R δ W (.cup i :: .cap (i + 1) :: v) c = -evW R δ W v c := by
  rw [evW_cup, evW_cap, ← Category.assoc, zigzagB_at h, Preadditive.neg_comp, Category.id_comp]

theorem evW_loop {W i : ℕ} (h : i ≤ W) (v : List Step) (c : ℕ) :
    evW R δ W (.cup i :: .cap i :: v) c = δ • evW R δ W v c := by
  rw [evW_cup, evW_cap, ← Category.assoc, loop_at h, Linear.smul_comp, Category.id_comp]

theorem evW_cup_cup {W i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ W + 2) (v : List Step) (c : ℕ) :
    evW R δ W (.cup i :: .cup j :: v) c = -evW R δ W (.cup (j - 2) :: .cup i :: v) c := by
  simp only [evW_cup, ← Category.assoc]
  rw [cup_cup hij hj, Preadditive.neg_comp, neg_neg]

theorem evW_cap_cap {W i j : ℕ} (hij : i + 2 ≤ j) (hj : j + 2 ≤ W) (v : List Step) (c : ℕ) :
    evW R δ W (.cap j :: .cap i :: v) c = -evW R δ W (.cap i :: .cap (j - 2) :: v) c := by
  obtain ⟨n, rfl⟩ : ∃ n, W = n + 2 + 2 := ⟨W - 4, by omega⟩
  simp only [evW_cap, ← Category.assoc]
  rw [cap_cap hij (by omega), Preadditive.neg_comp]

theorem evW_cup_cap {W i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ W) (hi : i ≤ W) (v : List Step) (c : ℕ) :
    evW R δ W (.cup i :: .cap j :: v) c = -evW R δ W (.cap (j - 2) :: .cup i :: v) c := by
  obtain ⟨n, rfl⟩ : ∃ n, W = n + 2 := ⟨W - 2, by omega⟩
  simp only [evW_cup, evW_cap, ← Category.assoc]
  rw [cup_cap hij hj, Preadditive.neg_comp]

theorem evW_cap_cup {W i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ W) (v : List Step) (c : ℕ) :
    evW R δ W (.cup j :: .cap i :: v) c = -evW R δ W (.cap i :: .cup (j - 2) :: v) c := by
  obtain ⟨n, rfl⟩ : ∃ n, W = n + 2 := ⟨W - 2, by omega⟩
  simp only [evW_cup, evW_cap, ← Category.assoc]
  rw [cap_cup hij hj, Preadditive.neg_comp]

/-! ## Sliding caps and cups past words -/

/-- A cap slides under a word acting at positions `≥ i + 2`, with a sign. -/
theorem evW_farCap (u : List Step) {A : ℕ} (hu : Valid A u) {i j W : ℕ} (hij : i + 2 ≤ j)
    (hW : W = j + A) (v : List Step) (c : ℕ) :
    PmEq (evW R δ W (shiftW j u ++ .cap i :: v) c)
      (evW R δ W (.cap i :: (shiftW (j - 2) u ++ v)) c) := by
  induction u generalizing A W with
  | nil => exact PmEq.refl _
  | cons s u ih => cases s with
    | cup k =>
      obtain ⟨hk, hu⟩ := hu
      simp only [shiftW_cons, Step.shift_cup, List.cons_append]
      refine (PmEq.evW_cons_cup (ih hu (W := W + 2) (by omega))).trans ?_
      rw [evW_cap_cup (by omega) (by omega), show j + k - 2 = j - 2 + k by omega]
      exact (PmEq.refl _).neg_left
    | cap k =>
      obtain ⟨hk, hu⟩ := hu
      obtain ⟨W, rfl⟩ : ∃ W', W = W' + 2 := ⟨W - 2, by omega⟩
      simp only [shiftW_cons, Step.shift_cap, List.cons_append]
      refine (PmEq.evW_cons_cap (ih hu (W := W) (by omega))).trans ?_
      rw [evW_cap_cap (by omega) (by omega), show j + k - 2 = j - 2 + k by omega]
      exact (PmEq.refl _).neg_left

/-- The nested caps `capsW m = [cap (m-1), …, cap 0]`, joining the strands `m - 1 - k` and
`m + k`. -/
def capsW : ℕ → List Step
  | 0 => []
  | m + 1 => .cap m :: capsW m

/-- The nested cups `nestW m = [cup 0, cup 1, …, cup (m-1)]` from `0` strands, joining the
strands `k` and `2m - 1 - k`. -/
def nestW : ℕ → List Step
  | 0 => []
  | m + 1 => .cup 0 :: shiftW 1 (nestW m)

theorem valid_nestW (m A : ℕ) : Valid A (nestW m) := by
  induction m generalizing A with
  | zero => trivial
  | succ m ih =>
    refine ⟨Nat.zero_le _, ?_⟩
    have := valid_shiftW 1 (A + 1) (ih (A + 1))
    rwa [show 1 + (A + 1) = A + 2 by omega] at this

theorem ht_nestW (m A : ℕ) : ht A (nestW m) = A + (m + m) := by
  induction m generalizing A with
  | zero => rfl
  | succ m ih =>
    simp only [nestW, ht_cup]
    rw [show A + 2 = 1 + (A + 1) by omega, ht_shiftW 1 (A + 1) (valid_nestW m _), ih]
    omega

theorem valid_capsW (m A : ℕ) (h : m + m ≤ A) : Valid A (capsW m) := by
  induction m generalizing A with
  | zero => trivial
  | succ m ih => exact ⟨by omega, ih _ (by omega)⟩

theorem ht_capsW (m A : ℕ) : ht A (capsW m) = A - (m + m) := by
  induction m generalizing A with
  | zero => rfl
  | succ m ih => simp only [capsW, ht_cap, ih]; omega

/-- `m` nested caps slide under a word acting to their right. -/
theorem evW_farCaps (m : ℕ) (u : List Step) {A : ℕ} (hu : Valid A u) {W : ℕ}
    (hW : W = m + m + A) (v : List Step) (c : ℕ) :
    PmEq (evW R δ W (shiftW (m + m) u ++ capsW m ++ v) c)
      (evW R δ W (capsW m ++ u ++ v) c) := by
  induction m generalizing W with
  | zero =>
    simp only [add_zero, shiftW_zero, capsW, List.append_nil, List.nil_append]
    exact PmEq.refl _
  | succ m ih =>
    obtain ⟨W, rfl⟩ : ∃ W', W = W' + 2 := ⟨m + m + A, by omega⟩
    simp only [capsW, List.append_assoc, List.cons_append]
    refine (evW_farCap u hu (i := m) (j := m + 1 + (m + 1)) (by omega) (by omega) _ c).trans ?_
    refine PmEq.evW_cons_cap ?_
    rw [show m + 1 + (m + 1) - 2 = m + m by omega, ← List.append_assoc]
    have := ih (W := W) (by omega)
    simpa only [List.append_assoc] using this

/-- **The snake identity.** The nested cups on the right of `m` strands followed by the nested
caps joining them to the `m` strands is `± 1`. -/
theorem evW_snake (m : ℕ) {r W : ℕ} (hW : W = m + r) (v : List Step) (c : ℕ) :
    PmEq (evW R δ W (shiftW m (nestW m) ++ capsW m ++ v) c) (evW R δ W v c) := by
  induction m generalizing r W with
  | zero => simp only [nestW, shiftW_nil, capsW, List.nil_append]; exact PmEq.refl _
  | succ m ih =>
    simp only [nestW, shiftW_cons, Step.shift_cup, add_zero, shiftW_shiftW, capsW,
      List.cons_append, List.append_assoc]
    refine (PmEq.evW_cons_cup (evW_farCap (nestW m) (valid_nestW m (1 + r)) (i := m)
      (j := m + 1 + 1) (by omega) (by omega) _ c)).trans ?_
    rw [evW_zigzagA (by omega), show m + 1 + 1 - 2 = m by omega, ← List.append_assoc]
    exact ih (r := r + 1) (by omega)

/-- A cup slides over a word acting at positions `≥ i + 2` (after the cup), with a sign. -/
theorem evW_farCup (u : List Step) {A : ℕ} (hu : Valid A u) {i j W : ℕ} (hij : i + 2 ≤ j)
    (hW : W + 2 = j + A) (v : List Step) (c : ℕ) :
    PmEq (evW R δ W (.cup i :: (shiftW j u ++ v)) c)
      (evW R δ W (shiftW (j - 2) u ++ .cup i :: v) c) := by
  induction u generalizing A W with
  | nil => exact PmEq.refl _
  | cons s u ih => cases s with
    | cup k =>
      obtain ⟨hk, hu⟩ := hu
      simp only [shiftW_cons, Step.shift_cup, List.cons_append]
      rw [evW_cup_cup (by omega) (by omega), show j + k - 2 = j - 2 + k by omega]
      exact (PmEq.evW_cons_cup (ih hu (W := W + 2) (by omega))).neg_left
    | cap k =>
      obtain ⟨hk, hu⟩ := hu
      obtain ⟨W, rfl⟩ : ∃ W', W = W' + 2 := ⟨W - 2, by omega⟩
      simp only [shiftW_cons, Step.shift_cap, List.cons_append]
      rw [evW_cup_cap (by omega) (by omega) (by omega), show j + k - 2 = j - 2 + k by omega]
      exact (PmEq.evW_cons_cap (ih hu (W := W) (by omega))).neg_left

theorem nestW_succ' (m : ℕ) : nestW (m + 1) = nestW m ++ [.cup m] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    conv_lhs => rw [nestW, ih]
    conv_rhs => rw [nestW]
    simp [add_comm]

theorem capsW_succ' (m : ℕ) : capsW (m + 1) = shiftW 1 (capsW m) ++ [.cap 0] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    conv_lhs => rw [capsW, ih]
    conv_rhs => rw [capsW]
    simp [add_comm]

/-- The nested cups on the left slide over a word acting on the strands to their right. -/
theorem evW_farCups (m : ℕ) (u : List Step) {W : ℕ} (hu : Valid W u) (v : List Step) (c : ℕ) :
    PmEq (evW R δ W (nestW m ++ shiftW (m + m) u ++ v) c) (evW R δ W (u ++ nestW m ++ v) c) := by
  induction m generalizing v with
  | zero =>
    simp only [nestW, add_zero, shiftW_zero, List.nil_append, List.append_nil]
    exact PmEq.refl _
  | succ m ih =>
    rw [nestW_succ']
    simp only [List.append_assoc, List.singleton_append]
    have h1 := evW_farCup (R := R) (δ := δ) u hu (i := m) (j := m + 1 + (m + 1))
      (W := W + (m + m)) (by omega) (by omega) v c
    rw [show m + 1 + (m + 1) - 2 = m + m by omega] at h1
    refine (PmEq.evW_prefix (nestW m) (ht_nestW m W) h1).trans ?_
    · have := ih (.cup m :: v)
      simpa only [List.append_assoc] using this

theorem ht_mirrorSnake (m : ℕ) {W : ℕ} (hW : m ≤ W) :
    ht W (nestW m ++ shiftW m (capsW m)) = W := by
  rw [ht_append, ht_nestW, show W + (m + m) = m + (W + m) by omega,
    ht_shiftW m _ (valid_capsW m _ (by omega)), ht_capsW]
  omega

/-- **The mirror snake identity.** The nested cups on the left followed by the nested caps
joining them to the first `m` of the original strands is `± 1`. -/
theorem evW_snake' (m : ℕ) {W : ℕ} (hW : m ≤ W) (v : List Step) (c : ℕ) :
    PmEq (evW R δ W (nestW m ++ shiftW m (capsW m) ++ v) c) (evW R δ W v c) := by
  induction m with
  | zero => simp only [nestW, capsW, shiftW_nil, List.nil_append]; exact PmEq.refl _
  | succ m ih =>
    rw [nestW_succ', capsW_succ', shiftW_append, shiftW_shiftW]
    simp only [shiftW_cons, Step.shift_cap, shiftW_nil, add_zero, List.append_assoc,
      List.singleton_append, List.cons_append]
    have h1 := evW_farCup (R := R) (δ := δ) (capsW m) (valid_capsW m (W + m) (by omega))
      (i := m) (j := m + 2) (W := W + (m + m)) (by omega) (by omega)
      (.cap (m + 1) :: v) c
    rw [show m + 2 - 2 = m by omega, show m + 2 = m + 1 + 1 from rfl] at h1
    refine (PmEq.evW_prefix (nestW m) (ht_nestW m W) h1).trans ?_
    rw [← List.append_assoc]
    refine (PmEq.evW_prefix _ (ht_mirrorSnake m (by omega))
      (PmEq.of_eq_neg (evW_zigzagB (by omega) v c))).trans ?_
    exact ih (by omega)

/-! ## Diagrams as words -/

/-- The step of a layer. -/
def toStep (L : Layer sig) : Step :=
  match L.gen with
  | .cup => .cup L.left.length
  | .cap => .cap L.left.length

/-- The word of a diagram. -/
def steps {a b : Obj sig} (d : a ⟶ b) : List Step := (Diagram.layers d).map toStep

theorem diag_mk_eq_evW (ls : List (Layer sig)) :
    ∀ (a b : ℕ) (h : Chain (strands a) ls (strands b)),
      (pres R δ).diag (Diagram.mk ls h) = evW R δ a (ls.map toStep) b ∧
        Valid a (ls.map toStep) ∧ ht a (ls.map toStep) = b := by
  induction ls with
  | nil =>
    intro a b h
    have hab : a = b := by simpa using congrArg (fun o : Obj sig => o.word.length) h
    subst hab
    refine ⟨?_, trivial, rfl⟩
    rw [Diagram.mk_nil, Presentation.diag_eqToHom, List.map_nil, evW_nil_self]
    simp
  | cons L ls ih =>
    intro a b h
    obtain ⟨hv, hdom, hc⟩ := h
    obtain ⟨s, l, g, r⟩ := L
    cases g with
    | cup =>
      have hl : l.length + r.length = a := by
        have := congrArg (fun o : Obj sig => o.word.length) hdom
        simpa [Layer.dom] using this
      have hcod : Layer.cod ⟨s, l, .cup, r⟩ = strands (a + 2) :=
        obj_ext (by simp [Layer.cod]; omega)
      have hc' : Chain (strands (a + 2)) ls (strands b) := hcod ▸ hc
      have e : Diagram.mk (⟨s, l, .cup, r⟩ :: ls) ⟨hv, hdom, hc⟩ =
          dcup (m := a) (i := l.length) (by omega) ≫ Diagram.mk ls hc' := by
        apply Diagram.ext
        simp only [Diagram.layers_mk, Diagram.layers_comp, dcup, Diagram.layers_layer,
          List.singleton_append, List.cons.injEq, and_true]
        exact Layer.ext (Subsingleton.elim _ _) (list_unit_ext (by simp))
          rfl (list_unit_ext (by simp; omega))
      obtain ⟨h1, h2, h3⟩ := ih (a + 2) b hc'
      refine ⟨?_, ⟨by simp only [List.map_cons, toStep]; omega, h2⟩, h3⟩
      rw [e, Presentation.diag_comp, h1, ← cup_def]
      simp only [List.map_cons, toStep, evW_cup]
    | cap =>
      have hl : l.length + 2 + r.length = a := by
        have := congrArg (fun o : Obj sig => o.word.length) hdom
        simp [Layer.dom] at this; omega
      obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨l.length + r.length, by omega⟩
      have hcod : Layer.cod ⟨s, l, .cap, r⟩ = strands a :=
        obj_ext (by simp [Layer.cod]; omega)
      have hc' : Chain (strands a) ls (strands b) := hcod ▸ hc
      have e : Diagram.mk (⟨s, l, .cap, r⟩ :: ls) ⟨hv, hdom, hc⟩ =
          dcap (m := a) (i := l.length) (by omega) ≫ Diagram.mk ls hc' := by
        apply Diagram.ext
        simp only [Diagram.layers_mk, Diagram.layers_comp, dcap, Diagram.layers_layer,
          List.singleton_append, List.cons.injEq, and_true]
        exact Layer.ext (Subsingleton.elim _ _) (list_unit_ext (by simp))
          rfl (list_unit_ext (by simp; omega))
      obtain ⟨h1, h2, h3⟩ := ih a b hc'
      refine ⟨?_, ⟨by simp only [List.map_cons, toStep]; omega, h2⟩, h3⟩
      rw [e, Presentation.diag_comp, h1, ← cap_def]
      simp only [List.map_cons, toStep, evW_cap]

/-- The class of a diagram is the evaluation of its word. -/
theorem diag_eq_evW {a b : ℕ} (d : strands a ⟶ strands b) :
    (pres R δ).diag d = evW R δ a (steps d) b :=
  (diag_mk_eq_evW _ a b (Diagram.chain d)).1

theorem valid_steps {a b : ℕ} (d : strands a ⟶ strands b) : Valid a (steps d) :=
  (diag_mk_eq_evW (R := ℤ) (δ := 0) _ a b (Diagram.chain d)).2.1

theorem ht_steps {a b : ℕ} (d : strands a ⟶ strands b) : ht a (steps d) = b :=
  (diag_mk_eq_evW (R := ℤ) (δ := 0) _ a b (Diagram.chain d)).2.2

/-- Every morphism between numbers of strands is a linear combination of evaluations of valid
words. -/
theorem hom_induction_evW {a b : ℕ} {p : (X R δ a ⟶ X R δ b) → Prop}
    (word : ∀ u : List Step, Valid a u → ht a u = b → p (evW R δ a u b)) (zero : p 0)
    (add : ∀ f g, p f → p g → p (f + g)) (smul : ∀ (r : R) f, p f → p (r • f))
    (f : X R δ a ⟶ X R δ b) : p f :=
  (pres R δ).hom_induction (fun d => by
    rw [diag_eq_evW]; exact word _ (valid_steps d) (ht_steps d)) zero add smul f

/-! ## Left whiskering by `m` strands -/

theorem strands_tensor (m a : ℕ) : (strands m).tensor (strands a) = strands (m + a) :=
  obj_ext (by simp [strands, Obj.tensor])

variable (R δ) in
/-- Left whiskering `1_m ⊗ -` by `m` strands. -/
def wLs (m : ℕ) {a b : ℕ} (x : X R δ a ⟶ X R δ b) : X R δ (m + a) ⟶ X R δ (m + b) :=
  eqToHom (congrArg (pres R δ).obj (strands_tensor m a).symm) ≫ (pres R δ).wL (strands m) x ≫
    eqToHom (congrArg (pres R δ).obj (strands_tensor m b))

theorem wLs_comp (m : ℕ) {a b c : ℕ} (x : X R δ a ⟶ X R δ b) (y : X R δ b ⟶ X R δ c) :
    wLs R δ m (x ≫ y) = wLs R δ m x ≫ wLs R δ m y := by
  simp [wLs, Presentation.wL_comp]

theorem wLs_add (m : ℕ) {a b : ℕ} (x y : X R δ a ⟶ X R δ b) :
    wLs R δ m (x + y) = wLs R δ m x + wLs R δ m y := by
  simp [wLs, Presentation.wL_add]

theorem wLs_smul (m : ℕ) {a b : ℕ} (r : R) (x : X R δ a ⟶ X R δ b) :
    wLs R δ m (r • x) = r • wLs R δ m x := by
  simp [wLs, Presentation.wL_smul]

theorem wLs_zero (m : ℕ) {a b : ℕ} : wLs R δ m (0 : X R δ a ⟶ X R δ b) = 0 := by
  simp [wLs, Presentation.wL_zero]

theorem wLs_neg (m : ℕ) {a b : ℕ} (x : X R δ a ⟶ X R δ b) :
    wLs R δ m (-x) = -wLs R δ m x := by
  rw [← neg_one_smul R x, wLs_smul, neg_one_smul]

theorem wLs_eqToHom (m : ℕ) {a b : ℕ} (h : X R δ a = X R δ b) :
    wLs R δ m (eqToHom h) = eqToHom (by
      have := (pres R δ).obj_injective h
      rw [show a = b by simpa using congrArg (fun o : Obj sig => o.word.length) this]) := by
  have := (pres R δ).obj_injective h
  obtain rfl : a = b := by simpa using congrArg (fun o : Obj sig => o.word.length) this
  simp [wLs, Presentation.wL_id]

theorem wLs_cup (m : ℕ) {a i : ℕ} (h : i ≤ a) :
    wLs R δ m (cup R δ a i) = cup R δ (m + a) (m + i) := by
  rw [cup_def h, cup_def (by omega), wLs, Presentation.wL_diag,
    (pres R δ).diag_eq_of_layers_eq' (Diagram.whiskerL (strands m) (dcup h))
      (dcup (m := m + a) (i := m + i) (by omega))
      (strands_tensor m a) (strands_tensor m (a + 2)) ?_]
  · simp
  · simp only [Diagram.layers_whiskerL, dcup, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons.injEq, and_true]
    exact Layer.ext rfl (list_unit_ext (by simp [Layer.wl, strands])) rfl
      (list_unit_ext (by simp [Layer.wl]; omega))

theorem wLs_cap (m : ℕ) {a i : ℕ} (h : i ≤ a) :
    wLs R δ m (cap R δ a i) = cap R δ (m + a) (m + i) := by
  rw [cap_def h, cap_def (by omega), wLs, Presentation.wL_diag,
    (pres R δ).diag_eq_of_layers_eq' (Diagram.whiskerL (strands m) (dcap h))
      (dcap (m := m + a) (i := m + i) (by omega))
      (strands_tensor m (a + 2)) (strands_tensor m a) ?_]
  · simp
  · simp only [Diagram.layers_whiskerL, dcap, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons.injEq, and_true]
    exact Layer.ext rfl (list_unit_ext (by simp [Layer.wl, strands])) rfl
      (list_unit_ext (by simp [Layer.wl]; omega))

/-- Left whiskering shifts words. -/
theorem wLs_evW (m : ℕ) {a : ℕ} {u : List Step} (hu : Valid a u) (b : ℕ) :
    wLs R δ m (evW R δ a u b) = evW R δ (m + a) (shiftW m u) (m + b) := by
  induction u generalizing a with
  | nil =>
    by_cases hab : a = b
    · subst hab; simp only [evW_nil_self, shiftW_nil]
      rw [show (𝟙 (X R δ a)) = eqToHom rfl from rfl, wLs_eqToHom]; simp
    · rw [evW_nil_of_ne hab, wLs_zero, shiftW_nil, evW_nil_of_ne (by omega)]
  | cons s u ih => cases s with
    | cup i =>
      rw [evW_cup, wLs_comp, wLs_cup m hu.1, ih hu.2, shiftW_cons, Step.shift_cup, evW_cup]
      rfl
    | cap i =>
      obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by have := hu.1; omega⟩
      rw [evW_cap, wLs_comp, wLs_cap m (by have := hu.1; omega), ih (a := a) hu.2, shiftW_cons,
        Step.shift_cap]
      exact (evW_cap (m + a) (m + i) (shiftW m u) (m + b)).symm

end StringDiagrams.OddTemperleyLieb

end
