import StringDiagrams.Interpretation
import StringDiagrams.Monoidal

/-!
# Free commuting dots

The simplest monoidal presentation with a nontrivial generator: one region, one strand colour
and a single *even* dot, subject to no relations at all. The only identifications in the
presented category come from the interchange law, so dots on distinct strands commute
(`x_mul_x_comm`), while no relation is imposed on dots on the same strand. The polynomial
representation in `StringDiagrams.Examples.FreeDots.Representation` shows that dots are nonzero
and pairwise distinct; the identification of the endomorphism algebra of `n` strands with a
polynomial algebra is not addressed here.

This is the even counterpart of `StringDiagrams.Examples.Exterior`, where the dot is odd and
distinct dots anticommute.

## Main declarations

* `FreeDots.sig`, `FreeDots.pres R` (no relations), `FreeDots.FD R` the presented category and
  `FD.obj R n` its object of `n` strands.
* `FreeDots.x R n i : End (FD.obj R n)`: a dot on strand `i` (zero when out of range).
* `x_mul_x_comm`: dots on distinct strands commute, for symbolic `n`, `i`, `j`.
* Monoidal structure: `FD.obj_tensor`, `x_whiskerRight`, `whiskerLeft_x`,
  `x_whiskerRight_strands`, and `x_mul_x_comm_two` (commutativity from `whisker_exchange`).
-/

noncomputable section

namespace StringDiagrams.FreeDots

open CategoryTheory MonoidalCategory

/-- The single generator. -/
inductive Gen
  | dot
  deriving DecidableEq

/-- One region, one colour, one even dot. -/
def sig : Signature where
  Region := Unit
  Colour := Unit
  colourSrc _ := ()
  colourTgt _ := ()
  Gen := Gen
  dom _ := [()]
  cod _ := [()]
  left _ := ()
  right _ := ()

instance : Subsingleton sig.Region := inferInstanceAs (Subsingleton Unit)

instance : Inhabited sig.Region := ⟨()⟩

instance : sig.IsEven := ⟨fun _ => rfl⟩

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

@[simp] theorem word_eq_iff {l₁ l₂ : List sig.Colour} : l₁ = l₂ ↔ l₁.length = l₂.length :=
  ⟨congrArg List.length, list_unit_ext⟩

@[simp] theorem list_unit_eq_iff {l₁ l₂ : List Unit} : l₁ = l₂ ↔ l₁.length = l₂.length :=
  ⟨congrArg List.length, list_unit_ext⟩

theorem obj_ext {a b : Obj sig} (h : a.word.length = b.word.length) : a = b :=
  Obj.ext (Subsingleton.elim (α := Unit) _ _) (list_unit_ext h)

theorem layer_ext {L₁ L₂ : Layer sig} (hl : L₁.left.length = L₂.left.length)
    (hr : L₁.right.length = L₂.right.length) : L₁ = L₂ :=
  Layer.ext (Subsingleton.elim (α := Unit) _ _) (list_unit_ext hl) rfl (list_unit_ext hr)

/-- The dot with `i` strands to its left, on `n` strands. -/
def lay (n i : ℕ) : Layer sig := ⟨(), List.replicate i (), .dot, List.replicate (n - i - 1) ()⟩

theorem lay_dom {n i : ℕ} (h : i < n) : (lay n i).dom = strands n :=
  obj_ext (by simp [lay, Layer.dom, strands, sig]; omega)

theorem lay_cod {n i : ℕ} (h : i < n) : (lay n i).cod = strands n :=
  obj_ext (by simp [lay, Layer.cod, strands, sig]; omega)

/-- The dot as an endomorphism of `n` strands in the free 2-category. -/
def dlay {n i : ℕ} (h : i < n) : strands n ⟶ strands n :=
  Diagram.layer (lay n i) (Layer.valid_of_subsingleton _) (lay_dom h) (lay_cod h)

@[simp] theorem layers_dlay {n i : ℕ} (h : i < n) : Diagram.layers (dlay h) = [lay n i] := rfl

variable (R : Type*) [CommRing R]

/-- The presentation with no relations. -/
def pres : Presentation sig R where
  Rel := Empty
  dom _ := strands 0
  cod _ := strands 0
  rel r := r.elim

/-- The presented category of free commuting dots. -/
abbrev FD : Type _ := (pres R).Presented

/-- The object of `n` strands in `FD R`. -/
abbrev FD.obj (n : ℕ) : FD R := (pres R).obj (strands n)

/-- A dot on strand `i` of `n` (zero if `i ≥ n`). -/
def x (n i : ℕ) : End (FD.obj R n) :=
  if h : i < n then (pres R).diag (dlay h) else 0

theorem x_def {n i : ℕ} (h : i < n) : x R n i = (pres R).diag (dlay h) := dif_pos h

/-- `i` strands, used to whisker on the left. -/
def shift (i : ℕ) : Obj sig := ⟨(), List.replicate i ()⟩

/-- Dots on strands `i < j` commute: the interchange law with two even generators. -/
theorem x_mul_x_comm_of_lt {n i j : ℕ} (hij : i < j) : x R n i * x R n j = x R n j * x R n i := by
  by_cases hj : j < n
  · let d : InterchangeData sig := ⟨(), .dot, List.replicate (j - i - 1) (), .dot⟩
    have hx : d.Valid := InterchangeData.valid_of_subsingleton d
    have hd : d.dom.whisker (shift i) (List.replicate (n - j - 1) ()) = strands n :=
      obj_ext (by simp [d, InterchangeData.dom, shift, strands, sig]; omega)
    have hc : d.cod.whisker (shift i) (List.replicate (n - j - 1) ()) = strands n :=
      obj_ext (by simp [d, InterchangeData.cod, shift, strands, sig]; omega)
    have key := (pres R).diag_interchange d hx (shift i) _
      (Obj.whiskerOK_of_subsingleton _ _ _) hd hc
    have hs : ((d.sign : ℤ) : R) = 1 := by simp [d, InterchangeData.sign, sig]
    rw [hs, one_smul] at key
    rw [x_def R (show i < n by omega), x_def R hj, End.mul_def, End.mul_def,
      ← Presentation.diag_comp, ← Presentation.diag_comp]
    have e₁ : (pres R).diag (dlay (show i < n by omega) ≫ dlay hj) =
        (pres R).diag (Diagram.cast (Diagram.whisker (InterchangeData.ghDiagram hx) (shift i)
          (List.replicate (n - j - 1) ()) (Obj.whiskerOK_of_subsingleton _ _ _)) hd hc) := by
      apply Presentation.diag_eq_of_layers_eq
      simp [d, dlay, lay, shift, Layer.whisker, InterchangeData.ghDiagram, InterchangeData.gh₁,
        InterchangeData.gh₂, sig]
      omega
    have e₂ : (pres R).diag (dlay hj ≫ dlay (show i < n by omega)) =
        (pres R).diag (Diagram.cast (Diagram.whisker (InterchangeData.hgDiagram hx) (shift i)
          (List.replicate (n - j - 1) ()) (Obj.whiskerOK_of_subsingleton _ _ _)) hd hc) := by
      apply Presentation.diag_eq_of_layers_eq
      simp [d, dlay, lay, shift, Layer.whisker, InterchangeData.hgDiagram, InterchangeData.hg₁,
        InterchangeData.hg₂, sig]
      omega
    rw [e₂, e₁, key]
  · simp only [x, dif_neg hj]; simp

/-- Dots on distinct strands commute. -/
theorem x_mul_x_comm {n i j : ℕ} (hij : i ≠ j) : x R n i * x R n j = x R n j * x R n i := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact x_mul_x_comm_of_lt R h
  · exact (x_mul_x_comm_of_lt R h).symm

/-! ## Monoidal structure -/

example : MonoidalCategory (FD R) := inferInstance
example : MonoidalLinear R (FD R) := inferInstance

/-- Tensor product of objects adds numbers of strands. -/
theorem FD.obj_tensor (m n : ℕ) : FD.obj R m ⊗ FD.obj R n = FD.obj R (m + n) := by
  rw [FD.obj, FD.obj, Presentation.obj_tensor]
  congr 1
  exact obj_ext (by simp [strands, Obj.tensor])

/-- The unit object is the empty object. -/
theorem FD.obj_zero : 𝟙_ (FD R) = FD.obj R 0 := rfl

/-- A dot on one strand, followed by a strand on the right, is a dot on strand `0` of `2`. -/
theorem x_whiskerRight : x R 1 0 ▷ FD.obj R 1 = x R 2 0 := by
  rw [x_def R (show 0 < 1 by omega), x_def R (show 0 < 2 by omega),
    Presentation.diag_whiskerRight]
  apply Presentation.diag_eq_of_layers_eq
  rfl

/-- A strand, followed by a dot on one strand, is a dot on strand `1` of `2`. -/
theorem whiskerLeft_x : FD.obj R 1 ◁ x R 1 0 = x R 2 1 := by
  rw [x_def R (show 0 < 1 by omega), x_def R (show 1 < 2 by omega),
    Presentation.diag_whiskerLeft]
  apply Presentation.diag_eq_of_layers_eq
  rfl

/-- Right whiskering of a dot at symbolic width. -/
theorem x_whiskerRight_strands {n i : ℕ} (h : i < n) (m : ℕ) :
    x R n i ▷ FD.obj R m = eqToHom (FD.obj_tensor R n m) ≫ x R (n + m) i ≫
      eqToHom (FD.obj_tensor R n m).symm := by
  rw [x_def R h, x_def R (show i < n + m by omega), Presentation.diag_whiskerRight]
  simp only [FD.obj, (pres R).eqToHom_obj, ← Presentation.diag_comp]
  apply Presentation.diag_eq_of_layers_eq
  simp only [Diagram.layers_whiskerR, Diagram.layers_comp, Diagram.layers_eqToHom, dlay,
    Diagram.layers_layer, List.map_cons, List.map_nil, List.nil_append, List.append_nil,
    List.cons.injEq, and_true]
  exact layer_ext (by simp [lay, Layer.wr]) (by simp [lay, Layer.wr, strands]; omega)

/-- Dots on neighbouring strands commute, from the interchange law of the monoidal
structure. -/
theorem x_mul_x_comm_two : x R 2 0 * x R 2 1 = x R 2 1 * x R 2 0 := by
  rw [← x_whiskerRight, ← whiskerLeft_x, End.mul_def, End.mul_def]
  exact (whisker_exchange _ _).trans rfl

end StringDiagrams.FreeDots

end
