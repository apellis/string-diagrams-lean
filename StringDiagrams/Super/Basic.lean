import StringDiagrams.Grading
import Mathlib.Data.ZMod.Defs

/-!
# Supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.1: a supercategory is a category enriched in superspaces, i.e. every morphism
space is `ℤ/2`-graded and composition is an even bilinear map.

We use the unpacked form of this definition for an `R`-linear category: each `Hom` module is
the internal direct sum of an even and an odd submodule (`Supercategory.parity`), identities
are even, and composition of homogeneous morphisms is homogeneous with parities adding.
Mathlib has no category of superspaces at the pinned version, so the enriched formulation is
replaced by this equivalent structure on a linear category.

## Main definitions

* `StringDiagrams.Supercategory R C`: parities of morphisms in an `R`-linear category.
* `Supercategory.IsHomogeneous`, `Supercategory.parity_comp`, `Supercategory.parity_id`.
* `Presentation.parityDeg`: the parity of a generator, as a degree in `ZMod 2`;
  `Presentation.IsParityHomogeneous`: the relations are homogeneous for it.
* `Presentation.supercategory`: the presented category of a presentation with
  parity-homogeneous relations is a supercategory (the parity of a diagram is the number of
  odd generators modulo `2`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂ w₁ w₂

/-- A supercategory structure on an `R`-linear category (Brundan–Ellis, Definition 1.1(i)):
each morphism module is the internal direct sum of its even and odd parts, identities are
even, and composition adds parities. -/
class Supercategory (R : Type w) [CommRing R] (C : Type w₁) [Category.{w₂} C] [Preadditive C]
    [Linear R C] where
  /-- The morphisms of parity `p`. -/
  parity : ∀ X Y : C, ZMod 2 → Submodule R (X ⟶ Y)
  /-- Every morphism is uniquely a sum of an even and an odd morphism. -/
  isInternal : ∀ X Y : C, DirectSum.IsInternal (parity X Y)
  /-- Identities are even. -/
  id_mem : ∀ X : C, 𝟙 X ∈ parity X X 0
  /-- Composition adds parities. -/
  comp_mem : ∀ {X Y Z : C} {p q : ZMod 2} {f : X ⟶ Y} {g : Y ⟶ Z},
    f ∈ parity X Y p → g ∈ parity Y Z q → f ≫ g ∈ parity X Z (p + q)

namespace Supercategory

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C]

/-- A morphism is homogeneous of parity `p`. -/
def IsHomogeneous {X Y : C} (f : X ⟶ Y) (p : ZMod 2) : Prop := f ∈ parity (R := R) X Y p

theorem parity_id (X : C) : IsHomogeneous (R := R) (𝟙 X) 0 := id_mem X

theorem parity_comp {X Y Z : C} {p q : ZMod 2} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsHomogeneous (R := R) f p) (hg : IsHomogeneous (R := R) g q) :
    IsHomogeneous (R := R) (f ≫ g) (p + q) := comp_mem hf hg

theorem zero_isHomogeneous {X Y : C} (p : ZMod 2) : IsHomogeneous (R := R) (0 : X ⟶ Y) p :=
  Submodule.zero_mem _

theorem IsHomogeneous.add {X Y : C} {p : ZMod 2} {f g : X ⟶ Y} (hf : IsHomogeneous (R := R) f p)
    (hg : IsHomogeneous (R := R) g p) : IsHomogeneous (R := R) (f + g) p :=
  Submodule.add_mem _ hf hg

theorem IsHomogeneous.smul {X Y : C} {p : ZMod 2} {f : X ⟶ Y} (r : R)
    (hf : IsHomogeneous (R := R) f p) : IsHomogeneous (R := R) (r • f) p :=
  Submodule.smul_mem _ r hf

theorem IsHomogeneous.neg {X Y : C} {p : ZMod 2} {f : X ⟶ Y} (hf : IsHomogeneous (R := R) f p) :
    IsHomogeneous (R := R) (-f) p :=
  Submodule.neg_mem _ hf

end Supercategory

/-! ## Presented categories are supercategories -/

namespace Presentation

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

/-- The parity of a generator, as a degree in `ZMod 2`. -/
def parityDeg (S : Signature.{u₀, u₁, u₂}) (g : S.Gen) : ZMod 2 := if S.odd g then 1 else 0

/-- The relations of `P` are homogeneous for the parity grading. -/
def IsParityHomogeneous : Prop := P.IsHomogeneous (parityDeg S)

variable {P}

/-- The presented category of a presentation with parity-homogeneous relations is a
supercategory: the parity of the class of a diagram is its number of odd generators modulo
`2`. -/
def supercategory (hP : P.IsParityHomogeneous) : Supercategory R P.Presented where
  parity X Y := P.homDeg (parityDeg S) X.as Y.as
  isInternal X Y := isInternal_homDeg hP X.as Y.as
  id_mem X := P.id_mem_homDeg (parityDeg S) X.as
  comp_mem hf hg := comp_mem_homDeg hf hg

theorem supercategory_parity (hP : P.IsParityHomogeneous) (a b : Obj S) (p : ZMod 2) :
    letI := P.supercategory hP
    Supercategory.parity (R := R) (P.obj a) (P.obj b) p = P.homDeg (parityDeg S) a b p := rfl

/-- The class of a diagram is homogeneous of parity its number of odd generators. -/
theorem diag_isHomogeneous (hP : P.IsParityHomogeneous) {a b : Obj S} (f : a ⟶ b) :
    letI := P.supercategory hP
    Supercategory.IsHomogeneous (R := R) (P.diag f) (Diagram.degree (parityDeg S) f) :=
  P.diag_mem_homDeg (deg := parityDeg S) f

end Presentation

end StringDiagrams

end
