import StringDiagrams.Signature
import Mathlib.CategoryTheory.EqToHom

/-!
# The free 2-category on a signature

Morphisms of the free (strict) 2-category on a signature `S` are *layered diagrams*: finite
lists of well-formed layers `id_left ⊗ g ⊗ id_right`, composed by concatenation. The
morphism type `a ⟶ b` is the subtype of layer lists that form a chain from `a` to `b`
(`Chain a ls b`). Typing information is carried by proofs only, so a morphism is
determined by its list of layers (`Diagram.ext`) and changing the type along an equality
of objects never changes the underlying data (`Diagram.layers_eqToHom`). This is what makes
diagrams of symbolic width (for example `n` strands with `n` a variable) convenient.

No relations are imposed here, not even the interchange law; interchange is imposed
together with the defining relations of a presentation (see
`StringDiagrams.Presentation`), where the Koszul sign of a super interchange law can be
included.

## Main definitions

* `StringDiagrams.Chain a ls b`: the layers `ls` form a well-typed diagram from `a` to `b`.
* `CategoryTheory.Category (Obj S)`: the free 2-category, with `a ⟶ b` the well-typed
  layer lists.
* `StringDiagrams.Diagram.ofLayer`: a single layer as a morphism.
* `StringDiagrams.Diagram.whisker`: whiskering `u ⊗ f ⊗ v` of a diagram.
-/

namespace StringDiagrams

open CategoryTheory

universe u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

/-- The layers `ls` form a well-typed diagram from `a` (bottom) to `b` (top). -/
def Chain : Obj S → List (Layer S) → Obj S → Prop
  | a, [], b => a = b
  | a, L :: ls, b => L.Valid ∧ L.dom = a ∧ Chain L.cod ls b

@[simp] theorem chain_nil (a b : Obj S) : Chain a [] b ↔ a = b := Iff.rfl

@[simp] theorem chain_cons (a b : Obj S) (L : Layer S) (ls : List (Layer S)) :
    Chain a (L :: ls) b ↔ L.Valid ∧ L.dom = a ∧ Chain L.cod ls b := Iff.rfl

theorem Chain.append {a b c : Obj S} {ls ms : List (Layer S)} (h₁ : Chain a ls b)
    (h₂ : Chain b ms c) : Chain a (ls ++ ms) c := by
  induction ls generalizing a with
  | nil => cases h₁; exact h₂
  | cons L ls ih => exact ⟨h₁.1, h₁.2.1, ih h₁.2.2⟩

theorem Chain.start_eq {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    b.start = a.start := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih => rw [ih h.2.2, ← h.2.1]; rfl

theorem Chain.endR_eq {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    b.endR = a.endR := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih => rw [ih h.2.2, h.1.endR_eq, h.2.1]

theorem Chain.whiskerOK {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b)
    {u : Obj S} {v : List S.Colour} (hw : a.WhiskerOK u v) : b.WhiskerOK u v :=
  ⟨hw.1, by rw [h.start_eq]; exact hw.2.1, by rw [h.endR_eq]; exact hw.2.2⟩

theorem Chain.whisker {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b)
    {u : Obj S} {v : List S.Colour} (hw : a.WhiskerOK u v) :
    Chain (a.whisker u v) (ls.map (·.whisker u v)) (b.whisker u v) := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    rw [List.map_cons, chain_cons, Layer.whisker_dom, Layer.whisker_cod]
    have hw' : L.cod.WhiskerOK u v := Chain.whiskerOK (ls := [L]) ⟨hv, rfl, rfl⟩ hw
    exact ⟨hv.whisker hw, rfl, ih hc hw'⟩

/-- A diagram from `a` to `b` in the free 2-category: a well-typed list of layers. -/
def Diagram (a b : Obj S) : Type (max u₀ u₁ u₂) := {ls : List (Layer S) // Chain a ls b}

instance : Category (Obj S) where
  Hom := Diagram
  id _ := ⟨[], rfl⟩
  comp f g := ⟨f.1 ++ g.1, f.2.append g.2⟩
  id_comp _ := Subtype.ext (List.nil_append _)
  comp_id _ := Subtype.ext (List.append_nil _)
  assoc _ _ _ := Subtype.ext (List.append_assoc _ _ _)

namespace Diagram

variable {a b c : Obj S}

/-- The list of layers of a diagram, from bottom to top. -/
def layers (f : a ⟶ b) : List (Layer S) := f.1

theorem chain (f : a ⟶ b) : Chain a (layers f) b := f.2

/-- Build a diagram from a list of layers and a typing proof. -/
def mk (ls : List (Layer S)) (h : Chain a ls b) : a ⟶ b := ⟨ls, h⟩

@[simp] theorem layers_mk (ls : List (Layer S)) (h : Chain a ls b) :
    layers (mk ls h) = ls := rfl

@[ext] theorem ext {f g : a ⟶ b} (h : layers f = layers g) : f = g := Subtype.ext h

@[simp] theorem layers_id (a : Obj S) : layers (𝟙 a) = [] := rfl

@[simp] theorem layers_comp (f : a ⟶ b) (g : b ⟶ c) : layers (f ≫ g) = layers f ++ layers g :=
  rfl

@[simp] theorem layers_eqToHom (h : a = b) : layers (eqToHom h) = [] := by
  subst h; rfl

/-- A single well-formed layer as a diagram. -/
def ofLayer (L : Layer S) (hv : L.Valid) : L.dom ⟶ L.cod := ⟨[L], hv, rfl, rfl⟩

@[simp] theorem layers_ofLayer (L : Layer S) (hv : L.Valid) : layers (ofLayer L hv) = [L] :=
  rfl

/-- A single well-formed layer as a diagram between objects equal to its boundaries. -/
def layer (L : Layer S) (hv : L.Valid) (ha : L.dom = a) (hb : L.cod = b) : a ⟶ b :=
  ⟨[L], hv, ha, hb⟩

@[simp] theorem layers_layer (L : Layer S) (hv : L.Valid) (ha : L.dom = a) (hb : L.cod = b) :
    layers (layer L hv ha hb) = [L] := rfl

/-- Whiskering `u ⊗ f ⊗ v` of a diagram. -/
def whisker (f : a ⟶ b) (u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v) :
    a.whisker u v ⟶ b.whisker u v :=
  ⟨(layers f).map (·.whisker u v), (chain f).whisker hw⟩

@[simp] theorem layers_whisker (f : a ⟶ b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) : layers (whisker f u v hw) = (layers f).map (·.whisker u v) := rfl

theorem whisker_id (u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v) :
    whisker (𝟙 a) u v hw = 𝟙 _ := rfl

theorem whisker_comp (f : a ⟶ b) (g : b ⟶ c) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) :
    whisker (f ≫ g) u v hw = whisker f u v hw ≫ whisker g u v ((chain f).whiskerOK hw) := by
  ext; simp

end Diagram

end StringDiagrams
