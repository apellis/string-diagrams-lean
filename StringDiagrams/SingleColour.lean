import StringDiagrams.Positional

/-!
# Signatures with one region and one colour

For a signature with a single region and a single strand colour (for instance a nilHecke or
Temperley–Lieb type calculus), an object is determined by its number of strands and a layer
by the numbers of strands to the left and to the right of its generator. This file provides
the corresponding normal forms and reduces equalities of objects and layers to equalities of
natural numbers, so that positions and widths may be symbolic and side conditions are
discharged by `omega`.

Throughout, `S` has a unique region and a unique colour, given by instances
`[Subsingleton S.Region] [Inhabited S.Region] [Subsingleton S.Colour] [Inhabited S.Colour]`.
The number of strands of the source and target of a generator `g` are `(S.dom g).length` and
`(S.cod g).length`; they need not agree.

## Main definitions and results

* `SingleColour.strands n`: the object of `n` strands; `SingleColour.obj_eq_iff`,
  `SingleColour.eq_strands`, `SingleColour.whisker_strands`.
* `SingleColour.lay i g j`: the generator `g` with `i` strands on its left and `j` on its
  right; `SingleColour.dlay i g j hn hm : strands n ⟶ strands m`, its diagram;
  `SingleColour.layer_eq_iff`, `SingleColour.eq_lay`, `SingleColour.lay_whisker`.
* `SingleColour.relation_at`: a defining relation of a presentation at any position and width.
* `SingleColour.interchange_at`: the interchange law for two generators at any positions, with
  the Koszul sign (`interchange_at_of_even`, `interchange_at_of_odd`).
* For width-preserving generators: morphisms between different numbers of strands vanish
  (`SingleColour.eq_zero_of_length_ne`) and `End (strands n)` is generated as an algebra by
  the single layers `dlay i g j` (`SingleColour.mem_subalgebra_of_dlay`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

namespace SingleColour

/-! ## Lists over a type with one element -/

theorem list_eq_of_length_eq {α : Type*} [Subsingleton α] {l₁ l₂ : List α}
    (h : l₁.length = l₂.length) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a l ih => cases l₂ with
    | nil => simp at h
    | cons b l₂ =>
      rw [Subsingleton.elim a b, ih (by simpa using h)]

theorem list_eq_iff {α : Type*} [Subsingleton α] {l₁ l₂ : List α} :
    l₁ = l₂ ↔ l₁.length = l₂.length :=
  ⟨congrArg List.length, list_eq_of_length_eq⟩

theorem list_eq_replicate {α : Type*} [Subsingleton α] [Inhabited α] (l : List α) :
    l = List.replicate l.length default :=
  list_eq_of_length_eq (by simp)

variable {S : Signature.{u₀, u₁, u₂}}

/-- Words in the single colour are determined by their length. -/
@[simp] theorem word_eq_iff [Subsingleton S.Colour] {l₁ l₂ : List S.Colour} :
    l₁ = l₂ ↔ l₁.length = l₂.length :=
  list_eq_iff

/-! ## Objects and layers in normal form -/

section Normal

variable [Inhabited S.Region] [Inhabited S.Colour]

/-- The object of `n` strands. -/
def strands (n : ℕ) : Obj S := ⟨default, List.replicate n default⟩

@[simp] theorem strands_start (n : ℕ) : (strands n : Obj S).start = default := rfl

@[simp] theorem strands_word (n : ℕ) :
    (strands n : Obj S).word = List.replicate n default := rfl

theorem strands_word_length (n : ℕ) : (strands n : Obj S).word.length = n := by
  simp

theorem strands_zero : (strands 0 : Obj S) = Obj.unit := rfl

/-- The generator `g` with `i` strands on its left and `j` strands on its right. -/
def lay (i : ℕ) (g : S.Gen) (j : ℕ) : Layer S :=
  ⟨default, List.replicate i default, g, List.replicate j default⟩

@[simp] theorem lay_start (i : ℕ) (g : S.Gen) (j : ℕ) : (lay i g j).start = default := rfl
@[simp] theorem lay_left (i : ℕ) (g : S.Gen) (j : ℕ) :
    (lay i g j).left = List.replicate i default := rfl
@[simp] theorem lay_gen (i : ℕ) (g : S.Gen) (j : ℕ) : (lay i g j).gen = g := rfl
@[simp] theorem lay_right (i : ℕ) (g : S.Gen) (j : ℕ) :
    (lay i g j).right = List.replicate j default := rfl

end Normal

variable [Subsingleton S.Region] [Inhabited S.Region] [Subsingleton S.Colour]
  [Inhabited S.Colour]

/-! ## Objects -/

omit [Inhabited S.Region] [Subsingleton S.Colour] [Inhabited S.Colour] in
theorem obj_ext_iff' {a b : Obj S} : a = b ↔ a.word = b.word :=
  ⟨congrArg Obj.word, fun h => Obj.ext (Subsingleton.elim _ _) h⟩

omit [Inhabited S.Region] [Inhabited S.Colour] in
/-- Objects are determined by their number of strands. -/
theorem obj_ext {a b : Obj S} (h : a.word.length = b.word.length) : a = b :=
  obj_ext_iff'.mpr (list_eq_of_length_eq h)

omit [Inhabited S.Region] [Inhabited S.Colour] in
@[simp] theorem obj_eq_iff {a b : Obj S} : a = b ↔ a.word.length = b.word.length :=
  ⟨fun h => h ▸ rfl, obj_ext⟩

/-- Every object is `strands` of its width. -/
theorem eq_strands (a : Obj S) : a = strands a.word.length :=
  obj_ext (by simp)

theorem strands_inj {m n : ℕ} : (strands m : Obj S) = strands n ↔ m = n := by
  simp

theorem strands_tensor (m n : ℕ) : (strands m : Obj S).tensor (strands n) = strands (m + n) := by
  simp

/-- Whiskering an object by `i` strands on the left and `j` on the right. -/
theorem whisker_strands {a : Obj S} {i j n : ℕ} (h : i + a.word.length + j = n) :
    a.whisker (strands i) (List.replicate j default) = strands n := by
  simp; omega

/-! ## Layers -/

omit [Inhabited S.Region] [Subsingleton S.Colour] [Inhabited S.Colour] in
theorem layer_ext_iff' {L₁ L₂ : Layer S} :
    L₁ = L₂ ↔ L₁.left = L₂.left ∧ L₁.gen = L₂.gen ∧ L₁.right = L₂.right := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h₁, h₂, h₃⟩; exact Layer.ext (Subsingleton.elim _ _) h₁ h₂ h₃

omit [Inhabited S.Region] [Inhabited S.Colour] in
/-- Layers are determined by their generator and the numbers of strands on either side. -/
@[simp] theorem layer_eq_iff {L₁ L₂ : Layer S} :
    L₁ = L₂ ↔ L₁.left.length = L₂.left.length ∧ L₁.gen = L₂.gen ∧
      L₁.right.length = L₂.right.length := by
  rw [layer_ext_iff', word_eq_iff, word_eq_iff]

omit [Inhabited S.Region] [Inhabited S.Colour] in
theorem layer_ext {L₁ L₂ : Layer S} (hl : L₁.left.length = L₂.left.length)
    (hg : L₁.gen = L₂.gen) (hr : L₁.right.length = L₂.right.length) : L₁ = L₂ :=
  layer_eq_iff.mpr ⟨hl, hg, hr⟩

omit [Subsingleton S.Colour] in
theorem lay_valid (i : ℕ) (g : S.Gen) (j : ℕ) : (lay i g j).Valid :=
  Layer.valid_of_subsingleton _

theorem lay_dom (i : ℕ) (g : S.Gen) (j : ℕ) :
    (lay i g j).dom = strands (i + (S.dom g).length + j) := by
  simp [Layer.dom]; omega

theorem lay_cod (i : ℕ) (g : S.Gen) (j : ℕ) :
    (lay i g j).cod = strands (i + (S.cod g).length + j) := by
  simp [Layer.cod]; omega

/-- Every layer is of the form `lay i g j`. -/
theorem eq_lay (L : Layer S) : L = lay L.left.length L.gen L.right.length := by
  simp

theorem lay_eq_iff {i i' j j' : ℕ} {g g' : S.Gen} :
    lay i g j = lay i' g' j' ↔ i = i' ∧ g = g' ∧ j = j' := by
  simp

@[simp] theorem lay_whisker (i : ℕ) (g : S.Gen) (j k l : ℕ) :
    (lay i g j).whisker (strands k) (List.replicate l default) = lay (k + i) g (j + l) := by
  simp [Layer.whisker]

/-- The layer `lay i g j` as a diagram from `n` strands to `m` strands. -/
def dlay (i : ℕ) (g : S.Gen) (j : ℕ) {n m : ℕ} (hn : i + (S.dom g).length + j = n)
    (hm : i + (S.cod g).length + j = m) : (strands n : Obj S) ⟶ strands m :=
  Diagram.layer (lay i g j) (lay_valid i g j) (by rw [lay_dom, hn]) (by rw [lay_cod, hm])

@[simp] theorem layers_dlay (i : ℕ) (g : S.Gen) (j : ℕ) {n m : ℕ}
    (hn : i + (S.dom g).length + j = n) (hm : i + (S.cod g).length + j = m) :
    Diagram.layers (dlay i g j hn hm) = [lay i g j] := rfl

/-! ## Relations and the interchange law at symbolic positions -/

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

/-- A defining relation of `P`, whiskered by `i` strands on the left and `j` on the right and
retyped to objects of `n` and `m` strands, holds in the presented category. -/
theorem relation_at (r : P.Rel) (i j : ℕ) {n m : ℕ} (hn : i + (P.dom r).word.length + j = n)
    (hm : i + (P.cod r).word.length + j = m) :
    P.lin (LinDiagram.cast (LinDiagram.whisker (P.rel r) (strands i) (List.replicate j default)
      (Obj.whiskerOK_of_subsingleton _ _ _)) (whisker_strands hn) (whisker_strands hm)) = 0 :=
  P.lin_rel_cast r _ _ _ _ _

/-- The layers of a diagram whiskered by `k` strands on the left and `l` on the right. -/
theorem layers_whisker_strands {a b : Obj S} (f : a ⟶ b) (k l : ℕ) (hw : a.WhiskerOK (strands k)
    (List.replicate l default)) :
    Diagram.layers (Diagram.whisker f (strands k) (List.replicate l default) hw) =
      (Diagram.layers f).map fun L => lay (k + L.left.length) L.gen (L.right.length + l) := by
  rw [Diagram.layers_whisker]
  refine List.map_congr_left fun L _ => ?_
  simp [Layer.whisker]

/-- **The interchange law at symbolic positions.** The generator `g` with `i` strands on its
left and the generator `h` with `j` strands on its right, separated by `m` strands, can be
applied in either order, up to the Koszul sign `(-1)^{|g||h|}`. -/
theorem interchange_at (g h : S.Gen) (i m j : ℕ) {n₀ n₁ n₂ n₃ : ℕ}
    (h₀ : i + (S.dom g).length + m + (S.dom h).length + j = n₀)
    (h₁ : i + (S.cod g).length + m + (S.dom h).length + j = n₁)
    (h₂ : i + (S.dom g).length + m + (S.cod h).length + j = n₂)
    (h₃ : i + (S.cod g).length + m + (S.cod h).length + j = n₃) :
    P.diag (dlay i g (m + (S.dom h).length + j) (by omega) (by omega) :
        (strands n₀ : Obj S) ⟶ strands n₁) ≫
      P.diag (dlay (i + (S.cod g).length + m) h j (by omega) (by omega) :
        (strands n₁ : Obj S) ⟶ strands n₃) =
    ((if S.odd g && S.odd h then -1 else 1 : ℤ) : R) •
      (P.diag (dlay (i + (S.dom g).length + m) h j (by omega) (by omega) :
          (strands n₀ : Obj S) ⟶ strands n₂) ≫
        P.diag (dlay i g (m + (S.cod h).length + j) (by omega) (by omega) :
          (strands n₂ : Obj S) ⟶ strands n₃)) := by
  rw [← P.diag_comp, ← P.diag_comp]
  refine P.diag_interchange_of_layers default (List.replicate i default)
    (List.replicate m default) (List.replicate j default) g h _ _ ?_ ?_
  · simp [lay]; omega
  · simp [lay]; omega

/-- The interchange law at symbolic positions, when one of the generators is even. -/
theorem interchange_at_of_even (g h : S.Gen) (hgh : S.odd g = false ∨ S.odd h = false)
    (i m j : ℕ) {n₀ n₁ n₂ n₃ : ℕ}
    (h₀ : i + (S.dom g).length + m + (S.dom h).length + j = n₀)
    (h₁ : i + (S.cod g).length + m + (S.dom h).length + j = n₁)
    (h₂ : i + (S.dom g).length + m + (S.cod h).length + j = n₂)
    (h₃ : i + (S.cod g).length + m + (S.cod h).length + j = n₃) :
    P.diag (dlay i g (m + (S.dom h).length + j) (by omega) (by omega) :
        (strands n₀ : Obj S) ⟶ strands n₁) ≫
      P.diag (dlay (i + (S.cod g).length + m) h j (by omega) (by omega) :
        (strands n₁ : Obj S) ⟶ strands n₃) =
    P.diag (dlay (i + (S.dom g).length + m) h j (by omega) (by omega) :
        (strands n₀ : Obj S) ⟶ strands n₂) ≫
      P.diag (dlay i g (m + (S.cod h).length + j) (by omega) (by omega) :
        (strands n₂ : Obj S) ⟶ strands n₃) := by
  rw [interchange_at P g h i m j h₀ h₁ h₂ h₃]
  rcases hgh with hg | hh <;> simp [*]

/-- The interchange law at symbolic positions, for two odd generators. -/
theorem interchange_at_of_odd (g h : S.Gen) (hg : S.odd g = true) (hh : S.odd h = true)
    (i m j : ℕ) {n₀ n₁ n₂ n₃ : ℕ}
    (h₀ : i + (S.dom g).length + m + (S.dom h).length + j = n₀)
    (h₁ : i + (S.cod g).length + m + (S.dom h).length + j = n₁)
    (h₂ : i + (S.dom g).length + m + (S.cod h).length + j = n₂)
    (h₃ : i + (S.cod g).length + m + (S.cod h).length + j = n₃) :
    P.diag (dlay i g (m + (S.dom h).length + j) (by omega) (by omega) :
        (strands n₀ : Obj S) ⟶ strands n₁) ≫
      P.diag (dlay (i + (S.cod g).length + m) h j (by omega) (by omega) :
        (strands n₁ : Obj S) ⟶ strands n₃) =
    -(P.diag (dlay (i + (S.dom g).length + m) h j (by omega) (by omega) :
        (strands n₀ : Obj S) ⟶ strands n₂) ≫
      P.diag (dlay i g (m + (S.cod h).length + j) (by omega) (by omega) :
        (strands n₂ : Obj S) ⟶ strands n₃)) := by
  rw [interchange_at P g h i m j h₀ h₁ h₂ h₃]
  simp [hg, hh]

/-! ## Width-preserving generators -/

section WidthPreserving

variable (hS : ∀ g : S.Gen, (S.cod g).length = (S.dom g).length)
include hS

omit [Subsingleton S.Region] [Inhabited S.Region] [Subsingleton S.Colour]
  [Inhabited S.Colour] in
/-- If every generator preserves the number of strands, so does every layer. -/
theorem layer_cod_length (L : Layer S) : L.cod.word.length = L.dom.word.length := by
  simp [Layer.cod, Layer.dom, hS]

omit [Subsingleton S.Region] [Inhabited S.Region] [Subsingleton S.Colour]
  [Inhabited S.Colour] in
/-- If every generator preserves the number of strands, so does every diagram. -/
theorem chain_length_eq {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    b.word.length = a.word.length := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih => rw [ih h.2.2, layer_cod_length hS, h.2.1]

omit [Subsingleton S.Region] [Inhabited S.Region] [Subsingleton S.Colour]
  [Inhabited S.Colour] in
/-- If every generator preserves the number of strands, morphisms between objects with
different numbers of strands vanish. -/
theorem eq_zero_of_length_ne {a b : Obj S} (h : a.word.length ≠ b.word.length)
    (f : P.obj a ⟶ P.obj b) : f = 0 :=
  P.eq_zero_of_invariant (fun a => a.word.length) (fun L _ => layer_cod_length hS L) h f

/-- **Generation by layers.** If every generator preserves the number of strands, then
`End (strands n)` is generated as an `R`-algebra by the single layers `dlay i g j`. -/
theorem mem_subalgebra_of_dlay (n : ℕ) (A : Subalgebra R (End (P.obj (strands n : Obj S))))
    (hA : ∀ (i : ℕ) (g : S.Gen) (j : ℕ) (h : i + (S.dom g).length + j = n),
      P.diag (dlay i g j h (by rw [hS]; exact h)) ∈ A)
    (f : End (P.obj (strands n : Obj S))) : f ∈ A := by
  refine P.mem_subalgebra_of_layers (fun L _ hL => obj_ext ?_) A (fun L hv hd => ?_) f
  · rw [layer_cod_length hS, hL]
  · have hn : L.left.length + (S.dom L.gen).length + L.right.length = n := by
      have := congrArg (fun a : Obj S => a.word.length) hd
      simp [Layer.dom] at this; omega
    convert hA L.left.length L.gen L.right.length hn using 1
    exact P.diag_eq_of_layers_eq (by simp)

end WidthPreserving

end SingleColour

end StringDiagrams

end
