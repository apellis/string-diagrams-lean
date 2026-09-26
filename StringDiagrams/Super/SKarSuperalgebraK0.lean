import StringDiagrams.Super.SKarSuperalgebra
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# `K₀(SKar(A))` is the split Grothendieck group of `A` (Example 1.17(i))

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 1.17(i), last sentence: `K₀(SKar(A))` is the usual split Grothendieck group of the
superalgebra `A`, i.e. of the category of finitely generated projective right `A`-supermodules
and even homomorphisms.

* `SKarAlg.FGProj 𝒜`: the full subcategory of `(k-SMod-A)̲` on the finitely generated
  projective supermodules (`SKarAlg.IsFGProjective`); it is preadditive, and has binary
  biproducts because it is equivalent to `SKar(A)`.
* `SKarAlg.toFGProj : SKar(A) ⥤ FGProj 𝒜`: the functor `(M, p) ↦ p(⊕ᵢ Π^{aᵢ} A)` of
  `SKarAlg.toMod`, corestricted to its essential image; it is an additive equivalence
  (`SKarAlg.toFGProj_isEquivalence`).
* `SKarAlg.K₀Equiv : K₀(SKar(A)) ≃+ K₀(FGProj 𝒜)`, `[(M, p)] ↦ [p(⊕ᵢ Π^{aᵢ} A)]`.

The biproduct of two finitely generated projective supermodules in `FGProj 𝒜` is characterised
by its universal property in that category; direct sums of supermodules are not constructed
here.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Limits Idempotents

universe u

namespace SKarAlg

variable {k : Type u} [CommRing k] {A : Type u} [Ring A] [Algebra k A]
  {𝒜 : ZMod 2 → Submodule k A} [GradedAlgebra 𝒜]

variable (𝒜) in
/-- The property of a right `A`-supermodule of being finitely generated projective. -/
def fgProjective : ObjectProperty (Underlying k (SuperBimodule (trivialGrading k) 𝒜)) :=
  fun V => IsFGProjective V.obj

variable (𝒜) in
/-- **Brundan–Ellis, Example 1.17(i).** The category of finitely generated projective right
`A`-supermodules and even homomorphisms. -/
abbrev FGProj := (fgProjective 𝒜).FullSubcategory

variable (𝒜) in
/-- **Example 1.17(i).** The functor `SKar(A) ⥤ FGProj`, `(M, p) ↦ p(⊕ᵢ Π^{aᵢ} A)`. -/
def toFGProj : SKar k (SuperalgebraCat 𝒜) ⥤ FGProj 𝒜 :=
  (fgProjective 𝒜).lift (toMod 𝒜) isFGProjective_toMod_obj

theorem toFGProj_obj (P : SKar k (SuperalgebraCat 𝒜)) :
    ((toFGProj 𝒜).obj P).obj = (toMod 𝒜).obj P := rfl

instance toFGProj_faithful : (toFGProj 𝒜).Faithful := by
  unfold toFGProj; infer_instance

instance toFGProj_full : (toFGProj 𝒜).Full := by
  unfold toFGProj; infer_instance

instance toFGProj_essSurj : (toFGProj 𝒜).EssSurj where
  mem_essImage V := by
    obtain ⟨P, ⟨e⟩⟩ := exists_iso_toMod_obj V.2
    exact ⟨P, ⟨(fgProjective 𝒜).ι.preimageIso e⟩⟩

/-- **Example 1.17(i).** `SKar(A)` is equivalent to the category of finitely generated
projective `A`-supermodules and even homomorphisms. -/
instance toFGProj_isEquivalence : (toFGProj 𝒜).IsEquivalence := {}

instance toFGProj_additive : (toFGProj 𝒜).Additive where
  map_add := (toMod 𝒜).map_add

instance : HasBinaryBiproducts (FGProj 𝒜) :=
  haveI : HasBinaryProducts (FGProj 𝒜) :=
    Adjunction.hasLimitsOfShape_of_equivalence (toFGProj 𝒜).inv
  HasBinaryBiproducts.of_hasBinaryProducts

variable (𝒜) in
/-- **Brundan–Ellis, Example 1.17(i).** `K₀(SKar(A))` is the split Grothendieck group of the
category of finitely generated projective `A`-supermodules. -/
def K₀Equiv : K₀ (SKar k (SuperalgebraCat 𝒜)) ≃+ K₀ (FGProj 𝒜) :=
  haveI : (toFGProj 𝒜).asEquivalence.functor.Additive := toFGProj_additive
  K₀.mapEquiv (toFGProj 𝒜).asEquivalence

theorem K₀Equiv_mk (P : SKar k (SuperalgebraCat 𝒜)) :
    K₀Equiv 𝒜 (K₀.mk P) = K₀.mk ((toFGProj 𝒜).obj P) := by
  haveI : (toFGProj 𝒜).asEquivalence.functor.Additive := toFGProj_additive
  exact K₀.mapEquiv_mk _ _

end SKarAlg

end StringDiagrams

end
