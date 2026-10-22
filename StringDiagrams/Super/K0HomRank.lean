/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.K0
import StringDiagrams.Super.GSKar
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Dimensions of Hom spaces on the split Grothendieck group

For an additive `K`-linear category `C` over a field `K` and an object `Z` with finite
dimensional Hom spaces `Z ⟶ X` for all `X`, the function `X ↦ dim_K (Z ⟶ X)` is invariant
under isomorphism and additive on biproducts, so it induces a homomorphism
`K₀.homRank Z : K₀ C →+ ℤ` (`K₀.homRank_mk`).

The Hom spaces of `Karoubi (Mat_ D)` are finite dimensional when those of `D` are
(`Karoubi.finiteDimensional_hom_mat`). In particular, for a graded supercategory `C` whose degree
pieces of Hom spaces are finite dimensional, every Hom space of the graded super Karoubi
envelope `GSKar K C` is finite dimensional (`GSKar.finiteDimensional_hom`), and `K₀.homRank`
applies to every object.

This is the basic ingredient of categorical pairings `([P], [Q]) ↦ gdim HOM(P, Q)` on split
Grothendieck groups, as in Khovanov–Lauda, arXiv:0803.4121v2, §2.5, and in Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §11, where the coefficients of the graded
dimension are the ranks of Hom spaces out of shifts of a fixed object.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Limits Module

universe w v u

variable {K : Type w} [Field K] {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [HasBinaryBiproducts C]

variable (K) in
/-- `Z ⟶ X ⊞ Y ≃ (Z ⟶ X) × (Z ⟶ Y)`, `K`-linearly. -/
@[simps]
def homBiprodEquiv (Z X Y : C) : (Z ⟶ X ⊞ Y) ≃ₗ[K] (Z ⟶ X) × (Z ⟶ Y) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  invFun g := biprod.lift g.1 g.2
  map_add' f g := by simp
  map_smul' c f := by simp
  left_inv f := by ext <;> simp
  right_inv g := by simp

namespace K₀

variable (K) in
/-- **The rank of `Hom(Z, -)` on `K₀`**: `[X] ↦ dim_K (Z ⟶ X)`, for an object `Z` all of whose
Hom spaces are finite dimensional. -/
def homRank (Z : C) (hfin : ∀ X : C, FiniteDimensional K (Z ⟶ X)) : K₀ C →+ ℤ :=
  lift (fun X => (finrank K (Z ⟶ X) : ℤ))
    (fun X Y e => by
      rw [(Linear.homCongr K (Iso.refl Z) e).finrank_eq])
    (fun X Y => by
      have := hfin X
      have := hfin Y
      rw [(homBiprodEquiv K Z X Y).finrank_eq, Module.finrank_prod, Nat.cast_add])

@[simp] theorem homRank_mk (Z : C) (hfin : ∀ X : C, FiniteDimensional K (Z ⟶ X)) (X : C) :
    homRank K Z hfin (mk X) = finrank K (Z ⟶ X) := by
  simp [homRank]

/-- `homRank` only depends on `Z` up to isomorphism. -/
theorem homRank_congr {Z Z' : C} (e : Z ≅ Z') (hfin : ∀ X : C, FiniteDimensional K (Z ⟶ X))
    (hfin' : ∀ X : C, FiniteDimensional K (Z' ⟶ X)) :
    homRank K Z hfin = homRank K Z' hfin' :=
  hom_ext fun X => by
    rw [homRank_mk, homRank_mk, (Linear.homCongr K e (Iso.refl X)).finrank_eq]

end K₀

end StringDiagrams

/-! ## Finite dimensional Hom spaces in graded super Karoubi envelopes -/

namespace StringDiagrams

open CategoryTheory Idempotents Module GradedSupercategory

universe w₁ v₁ u₁

variable {K : Type w} [Field K]

section Karoubi

variable {D : Type u₁} [Category.{v₁} D] [Preadditive D] [Linear K D]

/-- Hom spaces of `Mat_ D` are finite dimensional when those of `D` are. -/
theorem Mat_.finiteDimensional_hom (h : ∀ X Y : D, FiniteDimensional K (X ⟶ Y))
    (M N : Mat_ D) : FiniteDimensional K (M ⟶ N) := by
  change FiniteDimensional K (∀ i j, M.X i ⟶ N.X j)
  infer_instance

/-- Hom spaces of `Karoubi (Mat_ D)` are finite dimensional when those of `D` are. -/
theorem Karoubi.finiteDimensional_hom_mat (h : ∀ X Y : D, FiniteDimensional K (X ⟶ Y))
    (P Q : Karoubi (Mat_ D)) : FiniteDimensional K (P ⟶ Q) := by
  have := Mat_.finiteDimensional_hom h P.X Q.X
  let φ : (P ⟶ Q) →ₗ[K] (P.X ⟶ Q.X) :=
    { toFun := fun f => f.f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective φ fun f g e => Karoubi.hom_ext f g e

end Karoubi

section GSKar

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear K C] [Supercategory K C]
  [GradedSupercategory K C]

/-- **Hom spaces of `GSKar K C`** are finite dimensional when every degree piece of every Hom
space of `C` is. -/
theorem GSKar.finiteDimensional_hom
    (hfd : ∀ (X Y : C) (n : ℤ), FiniteDimensional K (degree (R := K) X Y n))
    (P Q : GSKar K C) : FiniteDimensional K (P ⟶ Q) := by
  refine Karoubi.finiteDimensional_hom_mat (fun X Y => ?_) P Q
  have := hfd X.obj.obj.obj.obj Y.obj.obj.obj.obj
    (0 + (X.obj.obj.obj.shift - Y.obj.obj.obj.shift))
  exact FiniteDimensional.finiteDimensional_submodule _

end GSKar

end StringDiagrams
