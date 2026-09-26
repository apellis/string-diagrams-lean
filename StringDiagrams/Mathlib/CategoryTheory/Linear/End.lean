import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Conj
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Endomorphism algebras under linear functors

For an `R`-linear functor `F : C ⥤ D` between `R`-linear categories, `F.map` is an `R`-algebra
homomorphism `End X →ₐ[R] End (F.obj X)` (`CategoryTheory.Functor.mapEndAlgHom`), and
conjugation by an isomorphism `e : X ≅ Y` is an `R`-algebra isomorphism
`End X ≃ₐ[R] End Y` (`CategoryTheory.Iso.conjAlgEquiv`).

For a module category, `ModuleCat.Hom.hom` is an `R`-algebra isomorphism
`End M ≃ₐ[R] Module.End R M` (`ModuleCat.endAlgEquiv`). Hence an `R`-linear functor
`F : C ⥤ ModuleCat R` gives representations of the endomorphism algebras of `C`
(`CategoryTheory.Functor.mapModuleEnd`) and linear maps of hom modules
(`CategoryTheory.Functor.mapModuleHom`), computed by `(F.map f).hom`.

Recall that in `End X` the product is `f * g = g ≫ f`.
-/

universe w v v₁ v₂ u₁ u₂

namespace CategoryTheory

variable (R : Type w) [CommSemiring R]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [CategoryTheory.Linear R D]

/-- `F.map` as an `R`-algebra homomorphism of endomorphism algebras. -/
def Functor.mapEndAlgHom (F : C ⥤ D) [F.Additive] [F.Linear R] (X : C) :
    End X →ₐ[R] End (F.obj X) :=
  AlgHom.ofLinearMap (F.mapLinearMap R) (F.map_id X) fun f g => F.map_comp g f

@[simp] theorem Functor.mapEndAlgHom_apply (F : C ⥤ D) [F.Additive] [F.Linear R] {X : C}
    (f : End X) : F.mapEndAlgHom R X f = F.map f := rfl

/-- Conjugation `f ↦ e.inv ≫ f ≫ e.hom` by an isomorphism, as an `R`-algebra isomorphism of
endomorphism algebras. -/
def Iso.conjAlgEquiv {X Y : C} (e : X ≅ Y) : End X ≃ₐ[R] End Y :=
  AlgEquiv.ofLinearEquiv
    { e.conj with
      map_add' := fun f g => by
        change e.inv ≫ ((f : X ⟶ X) + g) ≫ e.hom =
          ((e.inv ≫ f ≫ e.hom : Y ⟶ Y) + e.inv ≫ g ≫ e.hom)
        rw [Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := fun r f => by
        change e.inv ≫ (r • (f : X ⟶ X)) ≫ e.hom = (r • (e.inv ≫ f ≫ e.hom : Y ⟶ Y))
        rw [Linear.smul_comp, Linear.comp_smul] }
    (e.conj.map_one) (fun f g => e.conj.map_mul f g)

@[simp] theorem Iso.conjAlgEquiv_apply {X Y : C} (e : X ≅ Y) (f : End X) :
    Iso.conjAlgEquiv R e f = e.inv ≫ f ≫ e.hom := rfl

@[simp] theorem Iso.conjAlgEquiv_symm_apply {X Y : C} (e : X ≅ Y) (f : End Y) :
    (Iso.conjAlgEquiv R e).symm f = e.hom ≫ f ≫ e.inv := rfl

end CategoryTheory

namespace ModuleCat

variable {R : Type w} [CommRing R]

/-- `ModuleCat.Hom.hom` as an `R`-algebra isomorphism `End M ≃ₐ[R] Module.End R M`. -/
def endAlgEquiv (M : ModuleCat.{v} R) : CategoryTheory.End M ≃ₐ[R] Module.End R M :=
  AlgEquiv.ofRingEquiv (f := endRingEquiv M) fun _ => rfl

@[simp] theorem endAlgEquiv_apply (M : ModuleCat.{v} R) (f : CategoryTheory.End M) :
    endAlgEquiv M f = f.hom := rfl

@[simp] theorem endAlgEquiv_symm_apply (M : ModuleCat.{v} R) (f : Module.End R M) :
    (endAlgEquiv M).symm f = ofHom f := rfl

end ModuleCat

namespace CategoryTheory

variable (R : Type w) [CommRing R]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear R C]

/-- An `R`-linear functor to modules, on morphisms: an `R`-linear map
`(X ⟶ Y) →ₗ[R] (F.obj X →ₗ[R] F.obj Y)`, `f ↦ (F.map f).hom`. -/
def Functor.mapModuleHom (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R] (X Y : C) :
    (X ⟶ Y) →ₗ[R] (F.obj X →ₗ[R] F.obj Y) :=
  ModuleCat.homLinearEquiv.toLinearMap ∘ₗ F.mapLinearMap R

@[simp] theorem Functor.mapModuleHom_apply (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R]
    {X Y : C} (f : X ⟶ Y) : F.mapModuleHom R X Y f = (F.map f).hom := rfl

/-- An `R`-linear functor to modules, on endomorphisms: the representation
`End X →ₐ[R] Module.End R (F.obj X)`, `f ↦ (F.map f).hom`. -/
def Functor.mapModuleEnd (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R] (X : C) :
    End X →ₐ[R] Module.End R (F.obj X) :=
  (ModuleCat.endAlgEquiv (F.obj X)).toAlgHom.comp (F.mapEndAlgHom R X)

@[simp] theorem Functor.mapModuleEnd_apply (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R]
    {X : C} (f : End X) : F.mapModuleEnd R X f = (F.map f).hom := rfl

theorem Functor.mapModuleEnd_apply_apply (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R]
    {X : C} (f : End X) (x : F.obj X) : F.mapModuleEnd R X f x = (F.map f).hom x := rfl

/-- The representation `End X →ₐ[R] Module.End R M` of an `R`-linear functor to modules,
transported along an isomorphism `e : F.obj X ≅ M`: `f ↦ e.inv ≫ F.map f ≫ e.hom`. Typical
use: `e = eqToIso h` when the image of `X` is only propositionally equal to a fixed module. -/
def Functor.mapModuleEndOfIso (F : C ⥤ ModuleCat.{v} R) [F.Additive] [F.Linear R] {X : C}
    {M : ModuleCat.{v} R} (e : F.obj X ≅ M) : End X →ₐ[R] Module.End R M :=
  ((ModuleCat.endAlgEquiv M).toAlgHom.comp (Iso.conjAlgEquiv R e).toAlgHom).comp
    (F.mapEndAlgHom R X)

@[simp] theorem Functor.mapModuleEndOfIso_apply (F : C ⥤ ModuleCat.{v} R) [F.Additive]
    [F.Linear R] {X : C} {M : ModuleCat.{v} R} (e : F.obj X ≅ M) (f : End X) :
    F.mapModuleEndOfIso R e f = (e.inv ≫ F.map f ≫ e.hom).hom := rfl

end CategoryTheory
