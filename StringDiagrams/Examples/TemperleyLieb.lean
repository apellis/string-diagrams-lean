import StringDiagrams.Interpretation

/-!
# The Temperley–Lieb category

A test of width-changing generators. The signature has one self-dual strand colour, a cup
`[] → [c, c]` and a cap `[c, c] → []`; the relations are the two zigzag (snake) identities
and the loop relation `cap ∘ cup = δ` for a parameter `δ ∈ R`.

For every width, the elements `e m i = cup_i ∘ cap_i` of the endomorphism algebra of `m + 2`
strands satisfy the Temperley–Lieb relations `e_i² = δ e_i` (`e_mul_self`) and
`e_i e_{i+1} e_i = e_i`, `e_{i+1} e_i e_{i+1} = e_{i+1}` (`e_mul_e_succ_mul_e`,
`e_succ_mul_e_mul_e_succ`), derived from the zigzag and loop relations transported to
symbolic positions.

Far commutativity is proved in `StringDiagrams.Examples.TemperleyLieb.FarCommutativity`, and a
representation on `(R²)^{⊗n}` showing that the generators are non-zero in
`StringDiagrams.Examples.TemperleyLieb.Representation`.
-/

noncomputable section

namespace StringDiagrams.TemperleyLieb

open CategoryTheory

/-- The generators: a cup and a cap. -/
inductive Gen
  | cup
  | cap
  deriving DecidableEq

/-- One region, one self-dual colour, a cup and a cap. -/
def sig : Signature where
  Region := Unit
  Colour := Unit
  colourSrc _ := ()
  colourTgt _ := ()
  Gen := Gen
  dom
    | .cup => []
    | .cap => [(), ()]
  cod
    | .cup => [(), ()]
    | .cap => []
  left _ := ()
  right _ := ()

instance : Subsingleton sig.Region := inferInstanceAs (Subsingleton Unit)

/-- `n` strands. -/
def strands (n : ℕ) : Obj sig := ⟨(), List.replicate n ()⟩

theorem list_unit_ext {l₁ l₂ : List Unit} (h : l₁.length = l₂.length) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a l ih => cases l₂ with
    | nil => simp at h
    | cons b l₂ => rw [ih (by simpa using h)]

@[simp] theorem list_unit_eq_iff {l₁ l₂ : List Unit} : l₁ = l₂ ↔ l₁.length = l₂.length :=
  ⟨congrArg List.length, list_unit_ext⟩

theorem obj_ext {a b : Obj sig} (h : a.word.length = b.word.length) : a = b :=
  Obj.ext (Subsingleton.elim (α := Unit) _ _) (list_unit_ext h)

/-- The generator `g` with `i` strands to its left and `m - i` to its right. -/
def lay (m i : ℕ) (g : Gen) : Layer sig := ⟨(), List.replicate i (), g, List.replicate (m - i) ()⟩

/-- A cup with `i` strands to its left, from `m` to `m + 2` strands. -/
def dcup {m i : ℕ} (h : i ≤ m) : strands m ⟶ strands (m + 2) :=
  Diagram.layer (lay m i .cup) (Layer.valid_of_subsingleton _)
    (obj_ext (by simp [lay, Layer.dom, strands, sig]; omega))
    (obj_ext (by simp [lay, Layer.cod, strands, sig]; omega))

/-- A cap with `i` strands to its left, from `m + 2` to `m` strands. -/
def dcap {m i : ℕ} (h : i ≤ m) : strands (m + 2) ⟶ strands m :=
  Diagram.layer (lay m i .cap) (Layer.valid_of_subsingleton _)
    (obj_ext (by simp [lay, Layer.dom, strands, sig]; omega))
    (obj_ext (by simp [lay, Layer.cod, strands, sig]; omega))

/-- The relations. -/
inductive Rel
  | loop
  | zigzagA
  | zigzagB

/-- Width of the relations. -/
def Rel.width : Rel → ℕ
  | .loop => 0
  | _ => 1

variable (R : Type*) [CommRing R] (δ : R)

open LinDiagram in
/-- The relations (`f ≫ g` means `f` below `g`):
* `loop`: `cup ≫ cap - δ`;
* `zigzagA`: `cup₁ ≫ cap₀ - 1` on one strand;
* `zigzagB`: `cup₀ ≫ cap₁ - 1` on one strand. -/
def relation : (r : Rel) → LinDiagram R (strands r.width) (strands r.width)
  | .loop => of (dcup (m := 0) (i := 0) le_rfl ≫ dcap (m := 0) (i := 0) le_rfl) - δ • of (𝟙 _)
  | .zigzagA => of (dcup (m := 1) (i := 1) le_rfl ≫ dcap (m := 1) (i := 0) zero_le_one) - of (𝟙 _)
  | .zigzagB => of (dcup (m := 1) (i := 0) zero_le_one ≫ dcap (m := 1) (i := 1) le_rfl) - of (𝟙 _)

/-- The Temperley–Lieb presentation with loop value `δ`. -/
def pres : Presentation sig R where
  Rel := Rel
  dom r := strands r.width
  cod r := strands r.width
  rel := relation R δ

variable {R}

/-- `i` strands, used to whisker on the left. -/
def shift (i : ℕ) : Obj sig := ⟨(), List.replicate i ()⟩

theorem whisker_strands {w i n : ℕ} (h : i + w ≤ n) :
    (strands w).whisker (shift i) (List.replicate (n - i - w) ()) = strands n :=
  obj_ext (by simp [strands, shift, Obj.whisker]; omega)

theorem relation_at (r : Rel) {n i : ℕ} (h : i + r.width ≤ n) :
    (pres R δ).lin (LinDiagram.cast (LinDiagram.whisker (relation R δ r) (shift i)
      (List.replicate (n - i - r.width) ()) (Obj.whiskerOK_of_subsingleton _ _ _))
      (whisker_strands h) (whisker_strands h)) = 0 :=
  (pres R δ).lin_rel_cast r (shift i) _ _ _ _

/-- The loop relation at position `i` in width `m`. -/
theorem loop_at {m i : ℕ} (h : i ≤ m) :
    (pres R δ).diag (dcup h) ≫ (pres R δ).diag (dcap h) = δ • 𝟙 _ := by
  have key := relation_at δ .loop (n := m) (i := i) (by simp [Rel.width]; omega)
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_smul, LinDiagram.whisker_of,
    LinDiagram.cast_sub, LinDiagram.cast_smul, LinDiagram.cast_of, Presentation.lin_sub,
    Presentation.lin_smul, Presentation.lin_of, sub_eq_zero] at key
  rw [← Presentation.diag_comp, ← (pres R δ).diag_id]
  refine Eq.trans ?_ (key.trans ?_)
  · apply Presentation.diag_eq_of_layers_eq
    simp [dcup, dcap, lay, shift, Layer.whisker, Rel.width, sig]
  · congr 1

/-- The zigzag relation `cup_{i+1} ≫ cap_i = 1` in width `m`. -/
theorem zigzagA_at {m i : ℕ} (h : i + 1 ≤ m) :
    (pres R δ).diag (dcup (i := i + 1) h) ≫ (pres R δ).diag (dcap (i := i) (by omega)) = 𝟙 _ := by
  have key := relation_at δ .zigzagA (n := m) (i := i) (by simp [Rel.width]; omega)
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.cast_sub,
    LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_of, sub_eq_zero] at key
  rw [← Presentation.diag_comp, ← (pres R δ).diag_id]
  refine Eq.trans ?_ (key.trans ?_) <;> apply Presentation.diag_eq_of_layers_eq
  · simp [dcup, dcap, lay, shift, Layer.whisker, Rel.width, sig]; omega
  · rfl

/-- The zigzag relation `cup_i ≫ cap_{i+1} = 1` in width `m`. -/
theorem zigzagB_at {m i : ℕ} (h : i + 1 ≤ m) :
    (pres R δ).diag (dcup (i := i) (by omega)) ≫ (pres R δ).diag (dcap (i := i + 1) h) = 𝟙 _ := by
  have key := relation_at δ .zigzagB (n := m) (i := i) (by simp [Rel.width]; omega)
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.cast_sub,
    LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_of, sub_eq_zero] at key
  rw [← Presentation.diag_comp, ← (pres R δ).diag_id]
  refine Eq.trans ?_ (key.trans ?_) <;> apply Presentation.diag_eq_of_layers_eq
  · simp [dcup, dcap, lay, shift, Layer.whisker, Rel.width, sig]; omega
  · rfl

/-! ## The Temperley–Lieb algebras -/

/-- The Temperley–Lieb generator `e_i = cup_i ∘ cap_i` on `m + 2` strands (zero if `i > m`). -/
def e (m i : ℕ) : End ((pres R δ).obj (strands (m + 2))) :=
  if h : i ≤ m then (pres R δ).diag (dcap h) ≫ (pres R δ).diag (dcup h) else 0

theorem e_def {m i : ℕ} (h : i ≤ m) :
    e δ m i = (pres R δ).diag (dcap h) ≫ (pres R δ).diag (dcup h) := dif_pos h

theorem e_mul_self (m i : ℕ) : e δ m i * e δ m i = δ • e δ m i := by
  by_cases h : i ≤ m
  · rw [e_def δ h, End.mul_def]
    simp only [Category.assoc]
    rw [← Category.assoc ((pres R δ).diag (dcup h)), loop_at δ h, Linear.smul_comp,
      Category.id_comp, Linear.comp_smul]
  · simp [e, h]

theorem e_mul_e_succ_mul_e {m i : ℕ} (h : i + 1 ≤ m) :
    e δ m i * e δ m (i + 1) * e δ m i = e δ m i := by
  rw [e_def δ (show i ≤ m by omega), e_def δ h, End.mul_def, End.mul_def]
  simp only [Category.assoc]
  rw [← Category.assoc ((pres R δ).diag (dcup _)) ((pres R δ).diag (dcap _)), zigzagB_at δ h,
    Category.id_comp, ← Category.assoc ((pres R δ).diag (dcup _)) ((pres R δ).diag (dcap _)),
    zigzagA_at δ h, Category.id_comp]

theorem e_succ_mul_e_mul_e_succ {m i : ℕ} (h : i + 1 ≤ m) :
    e δ m (i + 1) * e δ m i * e δ m (i + 1) = e δ m (i + 1) := by
  rw [e_def δ (show i ≤ m by omega), e_def δ h, End.mul_def, End.mul_def]
  simp only [Category.assoc]
  rw [← Category.assoc ((pres R δ).diag (dcup _)) ((pres R δ).diag (dcap _)), zigzagA_at δ h,
    Category.id_comp, ← Category.assoc ((pres R δ).diag (dcup _)) ((pres R δ).diag (dcap _)),
    zigzagB_at δ h, Category.id_comp]

end StringDiagrams.TemperleyLieb

end
