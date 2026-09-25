import Mathlib.Logic.Basic
import Mathlib.Data.List.Basic

/-!
# Signatures for string diagrams

A `Signature` describes the generating data of a (strict) 2-category presented by
generators, in the form used by string diagrams:

* `Region` — generating 0-cells, drawn as labels of the planar regions;
* `Colour` — generating 1-cells, drawn as labelled strands, each with a region on its
  left (`colourSrc`) and a region on its right (`colourTgt`);
* `Gen` — generating 2-cells, drawn as vertices (dots, crossings, cups, …), each with a
  bottom boundary word `dom`, a top boundary word `cod`, and the regions `left` / `right`
  immediately to its left and right.

A strict monoidal signature is the special case `Region = PUnit`; then every
compatibility condition below is automatic (see `Signature.ok_of_subsingleton`).

Each generator also carries a parity `odd`. Parities only enter through the sign of
the interchange law (the Koszul rule of a super 2-category); for purely even
signatures one takes `odd := fun _ => false`.

Conventions: diagrams are read from bottom to top and boundary words from left to right.
A word `w` of colours read from a starting region `r` is *well formed* (`S.ok r w`) if the
left region of each strand is the right region of the previous one (or `r`); its final
region is `S.endR r w`.
-/

namespace StringDiagrams

universe u₀ u₁ u₂

/-- Generating data for string diagrams: regions (0-cells), strand colours (1-cells) and
generators (2-cells) with typed boundaries. -/
structure Signature where
  /-- Region labels (generating 0-cells). `PUnit` for monoidal signatures. -/
  Region : Type u₀
  /-- Strand labels (generating 1-cells). -/
  Colour : Type u₁
  /-- The region to the left of a strand. -/
  colourSrc : Colour → Region
  /-- The region to the right of a strand. -/
  colourTgt : Colour → Region
  /-- Generating 2-cells. -/
  Gen : Type u₂
  /-- Bottom boundary word of a generator. -/
  dom : Gen → List Colour
  /-- Top boundary word of a generator. -/
  cod : Gen → List Colour
  /-- The region immediately to the left of a generator. -/
  left : Gen → Region
  /-- The region immediately to the right of a generator. -/
  right : Gen → Region
  /-- Parity of a generator (used only for the sign of the interchange law). -/
  odd : Gen → Bool := fun _ => false

namespace Signature

variable (S : Signature.{u₀, u₁, u₂})

/-- A word of colours is well formed when read from region `r`. -/
def ok : S.Region → List S.Colour → Prop
  | _, [] => True
  | r, c :: w => S.colourSrc c = r ∧ ok (S.colourTgt c) w

/-- The region reached after reading a word of colours from region `r`. -/
def endR : S.Region → List S.Colour → S.Region
  | r, [] => r
  | _, c :: w => endR (S.colourTgt c) w

variable {S}

@[simp] theorem ok_nil (r : S.Region) : S.ok r [] := trivial

@[simp] theorem ok_cons (r : S.Region) (c : S.Colour) (w : List S.Colour) :
    S.ok r (c :: w) ↔ S.colourSrc c = r ∧ S.ok (S.colourTgt c) w := Iff.rfl

@[simp] theorem endR_nil (r : S.Region) : S.endR r [] = r := rfl

@[simp] theorem endR_cons (r : S.Region) (c : S.Colour) (w : List S.Colour) :
    S.endR r (c :: w) = S.endR (S.colourTgt c) w := rfl

@[simp] theorem ok_append (r : S.Region) (w w' : List S.Colour) :
    S.ok r (w ++ w') ↔ S.ok r w ∧ S.ok (S.endR r w) w' := by
  induction w generalizing r with
  | nil => simp
  | cons c w ih => simp [ih, and_assoc]

@[simp] theorem endR_append (r : S.Region) (w w' : List S.Colour) :
    S.endR r (w ++ w') = S.endR (S.endR r w) w' := by
  induction w generalizing r with
  | nil => rfl
  | cons c w ih => simp [ih]

theorem ok_of_subsingleton [Subsingleton S.Region] (r : S.Region) (w : List S.Colour) :
    S.ok r w := by
  induction w generalizing r with
  | nil => trivial
  | cons c w ih => exact ⟨Subsingleton.elim _ _, ih _⟩

end Signature

/-! ## Objects and layers -/

variable {S : Signature.{u₀, u₁, u₂}}

/-- An object (a 1-cell) of the free 2-category on `S`: a starting region together with a
word of colours. Objects need not be well formed; only well-formed layers occur in
diagrams. -/
@[ext]
structure Obj (S : Signature.{u₀, u₁, u₂}) where
  /-- The leftmost region. -/
  start : S.Region
  /-- The word of strand colours, from left to right. -/
  word : List S.Colour

namespace Obj

/-- The rightmost region of an object. -/
def endR (a : Obj S) : S.Region := S.endR a.start a.word

/-- Whiskering of an object: `u ⊗ a ⊗ v` (the start of `u` is kept; `v` is a word). -/
def whisker (a : Obj S) (u : Obj S) (v : List S.Colour) : Obj S :=
  ⟨u.start, u.word ++ a.word ++ v⟩

@[simp] theorem whisker_start (a u : Obj S) (v : List S.Colour) :
    (a.whisker u v).start = u.start := rfl

@[simp] theorem whisker_word (a u : Obj S) (v : List S.Colour) :
    (a.whisker u v).word = u.word ++ a.word ++ v := rfl

/-- The condition under which whiskering an object `a` by `u` on the left and `v` on the
right preserves well-formedness of layers with domain `a`. -/
def WhiskerOK (a u : Obj S) (v : List S.Colour) : Prop :=
  S.ok u.start u.word ∧ u.endR = a.start ∧ S.ok a.endR v

theorem whiskerOK_of_subsingleton [Subsingleton S.Region] (a u : Obj S) (v : List S.Colour) :
    a.WhiskerOK u v :=
  ⟨Signature.ok_of_subsingleton _ _, Subsingleton.elim _ _, Signature.ok_of_subsingleton _ _⟩

end Obj

/-- A layer `id_left ⊗ g ⊗ id_right`: one generator with identity strands on either side,
starting from region `start`. -/
@[ext]
structure Layer (S : Signature.{u₀, u₁, u₂}) where
  /-- The leftmost region. -/
  start : S.Region
  /-- The strands to the left of the generator. -/
  left : List S.Colour
  /-- The generator. -/
  gen : S.Gen
  /-- The strands to the right of the generator. -/
  right : List S.Colour

namespace Layer

/-- The bottom boundary of a layer. -/
def dom (L : Layer S) : Obj S := ⟨L.start, L.left ++ S.dom L.gen ++ L.right⟩

/-- The top boundary of a layer. -/
def cod (L : Layer S) : Obj S := ⟨L.start, L.left ++ S.cod L.gen ++ L.right⟩

@[simp] theorem dom_start (L : Layer S) : L.dom.start = L.start := rfl
@[simp] theorem cod_start (L : Layer S) : L.cod.start = L.start := rfl
@[simp] theorem dom_word (L : Layer S) : L.dom.word = L.left ++ S.dom L.gen ++ L.right := rfl
@[simp] theorem cod_word (L : Layer S) : L.cod.word = L.left ++ S.cod L.gen ++ L.right := rfl

/-- A layer is well formed when all its regions match up. -/
structure Valid (L : Layer S) : Prop where
  left_ok : S.ok L.start L.left
  left_end : S.endR L.start L.left = S.left L.gen
  dom_ok : S.ok (S.left L.gen) (S.dom L.gen)
  dom_end : S.endR (S.left L.gen) (S.dom L.gen) = S.right L.gen
  cod_ok : S.ok (S.left L.gen) (S.cod L.gen)
  cod_end : S.endR (S.left L.gen) (S.cod L.gen) = S.right L.gen
  right_ok : S.ok (S.right L.gen) L.right

theorem valid_of_subsingleton [Subsingleton S.Region] (L : Layer S) : L.Valid where
  left_ok := Signature.ok_of_subsingleton _ _
  left_end := Subsingleton.elim _ _
  dom_ok := Signature.ok_of_subsingleton _ _
  dom_end := Subsingleton.elim _ _
  cod_ok := Signature.ok_of_subsingleton _ _
  cod_end := Subsingleton.elim _ _
  right_ok := Signature.ok_of_subsingleton _ _

theorem Valid.endR_dom {L : Layer S} (h : L.Valid) :
    L.dom.endR = S.endR (S.right L.gen) L.right := by
  simp [Obj.endR, h.left_end, h.dom_end]

theorem Valid.endR_cod {L : Layer S} (h : L.Valid) :
    L.cod.endR = S.endR (S.right L.gen) L.right := by
  simp [Obj.endR, h.left_end, h.cod_end]

theorem Valid.endR_eq {L : Layer S} (h : L.Valid) : L.cod.endR = L.dom.endR := by
  rw [h.endR_dom, h.endR_cod]

/-- Whiskering of a layer: `u ⊗ L ⊗ v`. -/
def whisker (L : Layer S) (u : Obj S) (v : List S.Colour) : Layer S :=
  ⟨u.start, u.word ++ L.left, L.gen, L.right ++ v⟩

@[simp] theorem whisker_dom (L : Layer S) (u : Obj S) (v : List S.Colour) :
    (L.whisker u v).dom = L.dom.whisker u v := by
  simp [whisker, dom, Obj.whisker, List.append_assoc]

@[simp] theorem whisker_cod (L : Layer S) (u : Obj S) (v : List S.Colour) :
    (L.whisker u v).cod = L.cod.whisker u v := by
  simp [whisker, cod, Obj.whisker, List.append_assoc]

theorem Valid.whisker {L : Layer S} (h : L.Valid) {u : Obj S} {v : List S.Colour}
    (hw : L.dom.WhiskerOK u v) : (L.whisker u v).Valid := by
  obtain ⟨hu, hue, hv⟩ := hw
  have hue' : S.endR u.start u.word = L.start := hue
  refine ⟨?_, ?_, h.dom_ok, h.dom_end, h.cod_ok, h.cod_end, ?_⟩
  · show S.ok u.start (u.word ++ L.left)
    rw [Signature.ok_append, hue']; exact ⟨hu, h.left_ok⟩
  · show S.endR u.start (u.word ++ L.left) = S.left L.gen
    rw [Signature.endR_append, hue']; exact h.left_end
  · show S.ok (S.right L.gen) (L.right ++ v)
    rw [Signature.ok_append]; exact ⟨h.right_ok, by rw [← h.endR_dom]; exact hv⟩

end Layer

/-! ## Decidability of well-formedness -/

section Decidable

variable {S : Signature.{u₀, u₁, u₂}}

instance Signature.decOk [DecidableEq S.Region] :
    (r : S.Region) → (w : List S.Colour) → Decidable (S.ok r w)
  | _, [] => isTrue trivial
  | r, c :: w =>
    have := Signature.decOk (S.colourTgt c) w
    decidable_of_iff _ (Signature.ok_cons r c w).symm

instance Obj.decEq [DecidableEq S.Region] [DecidableEq S.Colour] : DecidableEq (Obj S) :=
  fun a b => decidable_of_iff (a.start = b.start ∧ a.word = b.word) Obj.ext_iff.symm

instance Layer.decValid [DecidableEq S.Region] (L : Layer S) : Decidable L.Valid :=
  decidable_of_iff
    (S.ok L.start L.left ∧ S.endR L.start L.left = S.left L.gen ∧
      S.ok (S.left L.gen) (S.dom L.gen) ∧ S.endR (S.left L.gen) (S.dom L.gen) = S.right L.gen ∧
      S.ok (S.left L.gen) (S.cod L.gen) ∧ S.endR (S.left L.gen) (S.cod L.gen) = S.right L.gen ∧
      S.ok (S.right L.gen) L.right)
    ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩,
      fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩⟩

instance Layer.decEq [DecidableEq S.Region] [DecidableEq S.Colour] [DecidableEq S.Gen] :
    DecidableEq (Layer S) :=
  fun L L' => decidable_of_iff
    (L.start = L'.start ∧ L.left = L'.left ∧ L.gen = L'.gen ∧ L.right = L'.right)
    Layer.ext_iff.symm

end Decidable

end StringDiagrams
