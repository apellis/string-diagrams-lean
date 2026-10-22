/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.K0Ring
import StringDiagrams.Super.MonoidalTwo

/-!
# Horizontal composites of one-by-one 1-morphisms in `Kar B`

For a bicategory `B` with preadditive hom categories, a 1-morphism `f` of `B` gives the
one-by-one matrix `MatBicat.single f` and the 1-morphism `Kar.of f` of the additive Karoubi
envelope `Kar B` (J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
§1.5 and the end of §6). An isomorphism `f ≫ g ≅ h` in `B` gives
`Kar.of f ≫ Kar.of g ≅ Kar.of h` (`Kar.ofCompIso`), so in the Grothendieck ring
`[Kar.of g] · [Kar.of f] = [Kar.of h]` (`K₀Ring.mk_of_mul_mk_of`). This is how products of
classes of 1-morphisms of `B` are computed in `K₀Ring (Kar B)`, for instance the product of
words in the Grothendieck ring of a monoidal supercategory (`MonoidalTwo`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Idempotents MonoidalCategory

universe w v u w₁

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B]

namespace MatBicat

open StringDiagrams.Mat_

variable {a b c : B}

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `single f ≫ single g ≅ single h` determined by `f ≫ g ≅ h`. -/
@[simps]
def singleCompIso {f : a ⟶ b} {g : b ⟶ c} {h : a ⟶ c} (e : f ≫ g ≅ h) :
    (single f ≫ single g : (⟨a⟩ : MatBicat B) ⟶ ⟨c⟩) ≅ single h where
  hom := permMat (Equiv.punitProd PUnit) fun _ => e.hom
  inv := permMat (Equiv.punitProd PUnit).symm fun _ => e.inv
  hom_inv_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.hom_inv_id _
  inv_hom_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.inv_hom_id _

end MatBicat

namespace KarBicat

open StringDiagrams.Karoubi

variable {C : Type u} [Bicategory.{w, v} C] {a b c : C}

theorem of_comp_comm (f : a ⟶ b) (g : b ⟶ c) :
    (of f ≫ of g).p ≫ 𝟙 (f ≫ g) = 𝟙 (f ≫ g) ≫ (of (f ≫ g)).p := by
  change hcomp₂ (𝟙 f) (𝟙 g) ≫ _ = _
  rw [hcomp₂_id_id]

/-- `of f ≫ of g ≅ of (f ≫ g)`. -/
def ofComp (f : a ⟶ b) (g : b ⟶ c) : of f ≫ of g ≅ of (f ≫ g) :=
  mkIso (Iso.refl _) (of_comp_comm f g)

end KarBicat

namespace Kar

variable {a b c : B}

/-- `Kar.of f ≅ Kar.of f'` for `f ≅ f'`. -/
def ofIso {f f' : a ⟶ b} (e : f ≅ f') : of f ≅ of f' :=
  (toKaroubi _).mapIso ((Mat_.embedding _).mapIso e)

/-- **Horizontal composition of one-by-one 1-morphisms**: `of f ≫ of g ≅ of h` for
`f ≫ g ≅ h`. -/
def ofCompIso {f : a ⟶ b} {g : b ⟶ c} {h : a ⟶ c} (e : f ≫ g ≅ h) : of f ≫ of g ≅ of h :=
  KarBicat.ofComp _ _ ≪≫ (toKaroubi _).mapIso (MatBicat.singleCompIso e)

end Kar

namespace K₀Ring

variable {a b c : B}

/-- **Products of one-by-one classes**: `[of g] · [of f] = [of h]` for `f ≫ g ≅ h`. -/
theorem mk_of_mul_mk_of {f : a ⟶ b} {g : b ⟶ c} {h : a ⟶ c} (e : f ≫ g ≅ h) :
    mk (Kar.of g) * mk (Kar.of f) = mk (Kar.of h) := by
  rw [mk_mul_mk]
  exact mk_eq_mk_of_iso (Kar.ofCompIso e)

end K₀Ring

namespace GSKAR

variable (R : Type w₁) [CommRing R] {𝔄 : Type u} [BicategoryStruct.{w, v} 𝔄]
  [∀ a b : 𝔄, Preadditive (a ⟶ b)] [∀ a b : 𝔄, Linear R (a ⟶ b)]
  [∀ a b : 𝔄, Supercategory R (a ⟶ b)] [∀ a b : 𝔄, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R 𝔄] [GradedTwoSupercategory R 𝔄] {a b c : 𝔄}

/-- A 1-morphism of `𝔄`, unshifted and even, as a 1-morphism of `GSKAR(𝔄)`. -/
abbrev of (f : a ⟶ b) : mkObj R 𝔄 a ⟶ mkObj R 𝔄 b :=
  Kar.of (show (⟨⟨⟨⟨a⟩⟩⟩⟩ : GUnderlying2 R (QPiTwoEnvelope R 𝔄)) ⟶ ⟨⟨⟨⟨b⟩⟩⟩⟩ from ⟨⟨⟨0, ⟨0, f⟩⟩⟩⟩)

/-- **Products of 1-morphisms of `𝔄`** in the Grothendieck ring of `GSKAR(𝔄)`:
`[g] · [f] = [f ≫ g]`. -/
theorem mk_of_mul_mk_of (f : a ⟶ b) (g : b ⟶ c) :
    K₀Ring.mk (of R g) * K₀Ring.mk (of R f) = K₀Ring.mk (of R (f ≫ g)) :=
  K₀Ring.mk_of_mul_mk_of (Iso.refl _)

/-- For a graded monoidal supercategory (`MonoidalTwo`), the product of classes of objects is the
class of their tensor product: `[Y] · [X] = [X ⊗ Y]`. -/
example {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C]
    [GradedSupercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]
    [GradedMonoidalSupercategory R C] (X Y : C) :
    K₀Ring.mk (of R (𝔄 := MonoidalTwo C) (a := MonoidalTwo.star C) (b := MonoidalTwo.star C)
        Y) * K₀Ring.mk (of R (𝔄 := MonoidalTwo C) (a := MonoidalTwo.star C)
          (b := MonoidalTwo.star C) X) =
      K₀Ring.mk (of R (𝔄 := MonoidalTwo C) (a := MonoidalTwo.star C) (b := MonoidalTwo.star C)
        (X ⊗ Y : C)) :=
  mk_of_mul_mk_of R (a := MonoidalTwo.star C) (b := MonoidalTwo.star C)
    (c := MonoidalTwo.star C) X Y

end GSKAR

end StringDiagrams
