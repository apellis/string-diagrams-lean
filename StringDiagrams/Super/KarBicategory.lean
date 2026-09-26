import StringDiagrams.Super.MatBicategory
import StringDiagrams.Super.KaroubiBicategory
import StringDiagrams.Super.TwoEnvelopePi
import StringDiagrams.Super.GradedTwoEnvelope
import StringDiagrams.Super.GSKar

/-!
# The additive Karoubi envelope of a 2-category, and the super Karoubi envelopes of
2-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §1.5 and the
end of §6.

* `Kar B := KarBicat (MatBicat B)`: the *additive Karoubi envelope* of a bicategory `B` with
  preadditive hom categories and additive whiskerings: the same objects, and the hom categories
  `Karoubi (Mat_ (a ⟶ b))`, the additive Karoubi envelopes of the hom categories of `B`, with
  horizontal composition extended bilinearly and to idempotents. It is a bicategory whose hom
  categories are additive and idempotent complete; it is `R`-linear when `B` is; a Π-2-category
  structure (Definition 5.2) or a `(Q, Π)`-2-category structure (Definition 6.14) on `B`
  extends to `Kar B` (`Kar.instPiTwoCategory`, `Kar.instQPiTwoCategory`).
* `SKAR R 𝔄 := Kar (Underlying2 R (TwoEnvelope R 𝔄))`: for a 2-supercategory `𝔄`, the
  additive Karoubi envelope of the underlying 2-category of the Π-envelope `𝔄_π` (the
  2-categorical analogue of the super Karoubi envelope `SKar` of §1.5). It is an additive,
  idempotent complete Π-2-category (`SKAR.instPiTwoCategory`), and its hom categories are the
  super Karoubi envelopes `SKar R (Hom_𝔄(λ, μ))` of the hom supercategories (`SKAR.hom_eq`,
  definitionally).
* `GSKAR R 𝔄 := Kar (GUnderlying2 R (QPiTwoEnvelope R 𝔄))`: for a graded 2-supercategory `𝔄`,
  the additive Karoubi envelope of the `(Q, Π)`-2-category underlying the `(Q, Π)`-envelope
  `𝔄_{q,π}` (**Brundan–Ellis, end of §6**). It is an additive, idempotent complete
  `(Q, Π)`-2-category (`GSKAR.instQPiTwoCategory`), and its hom categories are the graded super
  Karoubi envelopes `GSKar R (Hom_𝔄(λ, μ))` (`GSKAR.hom_eq`, definitionally). Its Grothendieck
  ring is constructed in `StringDiagrams.Super.K0Ring`.

Compositions of 1-morphisms are written in diagrammatic order.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Idempotents

universe w v u w₁

/-! ## The additive Karoubi envelope of a bicategory -/

/-- **Brundan–Ellis, §1.5 and §6.** The additive Karoubi envelope of a bicategory: the same
objects, and the hom categories `Karoubi (Mat_ (a ⟶ b))`. -/
abbrev Kar (B : Type u) [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
    [PreadditiveBicategory B] :=
  KarBicat (MatBicat B)

namespace Kar

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B]

example : Bicategory (Kar B) := inferInstance
example : PreadditiveBicategory (Kar B) := inferInstance
example (a b : Kar B) : Limits.HasFiniteBiproducts (a ⟶ b) := inferInstance
example (a b : Kar B) : Limits.HasBinaryBiproducts (a ⟶ b) := inferInstance
example (a b : Kar B) : IsIdempotentComplete (a ⟶ b) := inferInstance

/-- An object of `B` as an object of `Kar B`. -/
abbrev mkObj (a : B) : Kar B := ⟨⟨a⟩⟩

/-- The hom categories of `Kar B` are the additive Karoubi envelopes of those of `B`. -/
theorem hom_eq (a b : B) : (mkObj a ⟶ mkObj b) = Karoubi (Mat_ (a ⟶ b)) := rfl

/-- A 1-morphism of `B` as a 1-morphism of `Kar B` (a one-by-one matrix with the identity
idempotent). -/
abbrev of {a b : B} (f : a ⟶ b) : mkObj a ⟶ mkObj b := KarBicat.of (MatBicat.single f)

theorem id_eq (a : B) : 𝟙 (mkObj a) = of (𝟙 a) := rfl

section Linear

variable {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)] [LinearBicategory R B]

example : LinearBicategory R (Kar B) := inferInstance

/-- **Brundan–Ellis, §6.** The additive Karoubi envelope of a Π-2-category is a Π-2-category. -/
instance instPiTwoCategory [PiTwoCategory R B] : PiTwoCategory R (Kar B) := inferInstance

theorem pi_eq [PiTwoCategory R B] (a : B) :
    PiTwoCategory.pi (R := R) (mkObj a) = of (PiTwoCategory.pi (R := R) a) := rfl

/-- **Brundan–Ellis, §6.** The additive Karoubi envelope of a `(Q, Π)`-2-category is a
`(Q, Π)`-2-category. -/
instance instQPiTwoCategory [QPiTwoCategory R B] : QPiTwoCategory R (Kar B) := inferInstance

theorem q_eq [QPiTwoCategory R B] (a : B) :
    QPiTwoCategory.q (R := R) (mkObj a) = of (QPiTwoCategory.q (R := R) a) := rfl

theorem qinv_eq [QPiTwoCategory R B] (a : B) :
    QPiTwoCategory.qinv (R := R) (mkObj a) = of (QPiTwoCategory.qinv (R := R) a) := rfl

end Linear

end Kar

/-! ## The super Karoubi envelope of a 2-supercategory -/

section SKAR

variable (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- **Brundan–Ellis, §1.5 (2-categorical version).** The super Karoubi envelope
`SKAR(𝔄) := Kar(𝔄̲_π)` of a 2-supercategory: the additive Karoubi envelope of the underlying
2-category of the Π-envelope. -/
abbrev SKAR := Kar (Underlying2 R (TwoEnvelope R B))

namespace SKAR

example : Bicategory (SKAR R B) := inferInstance
example : PreadditiveBicategory (SKAR R B) := inferInstance
example : LinearBicategory R (SKAR R B) := inferInstance
example (a b : SKAR R B) : Limits.HasFiniteBiproducts (a ⟶ b) := inferInstance
example (a b : SKAR R B) : IsIdempotentComplete (a ⟶ b) := inferInstance

/-- An object of `𝔄` as an object of `SKAR(𝔄)`. -/
abbrev mkObj (a : B) : SKAR R B := Kar.mkObj ⟨⟨a⟩⟩

/-- The hom categories of `SKAR(𝔄)` are the super Karoubi envelopes of the hom supercategories
of `𝔄`: `Hom_{SKAR(𝔄)}(λ, μ) = SKar(Hom_𝔄(λ, μ))`. -/
theorem hom_eq (a b : B) : (mkObj R B a ⟶ mkObj R B b) = SKar R (a ⟶ b) := rfl

/-- **Brundan–Ellis, §6.** `SKAR(𝔄)` is a Π-2-category. -/
instance instPiTwoCategory : PiTwoCategory R (SKAR R B) := inferInstance

end SKAR

end SKAR

/-! ## The graded super Karoubi envelope of a graded 2-supercategory -/

section GSKAR

variable (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B]

/-- **Brundan–Ellis, end of §6.** The graded super Karoubi envelope `GSKAR(𝔄) := Kar(𝔄̲_{q,π})`
of a graded 2-supercategory: the additive Karoubi envelope of the `(Q, Π)`-2-category underlying
the `(Q, Π)`-envelope. -/
abbrev GSKAR := Kar (GUnderlying2 R (QPiTwoEnvelope R B))

namespace GSKAR

example : Bicategory (GSKAR R B) := inferInstance
example : PreadditiveBicategory (GSKAR R B) := inferInstance
example : LinearBicategory R (GSKAR R B) := inferInstance
example (a b : GSKAR R B) : Limits.HasFiniteBiproducts (a ⟶ b) := inferInstance
example (a b : GSKAR R B) : IsIdempotentComplete (a ⟶ b) := inferInstance

/-- An object of `𝔄` as an object of `GSKAR(𝔄)`. -/
abbrev mkObj (a : B) : GSKAR R B := Kar.mkObj ⟨⟨⟨⟨a⟩⟩⟩⟩

/-- The hom categories of `GSKAR(𝔄)` are the graded super Karoubi envelopes of the hom
supercategories of `𝔄`: `Hom_{GSKAR(𝔄)}(λ, μ) = GSKar(Hom_𝔄(λ, μ))`. -/
theorem hom_eq (a b : B) : (mkObj R B a ⟶ mkObj R B b) = GSKar R (a ⟶ b) := rfl

/-- **Brundan–Ellis, end of §6.** `GSKAR(𝔄)` is an additive, idempotent complete
`(Q, Π)`-2-category. -/
instance instQPiTwoCategory : QPiTwoCategory R (GSKAR R B) := inferInstance

end GSKAR

end GSKAR

end StringDiagrams

end
