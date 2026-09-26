import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# The opposite of a linear category

If `C` is an `R`-linear category, then so is `Cᵒᵖ`, with `r • f.op = (r • f).op`. The scalar
multiplication is transported along `Quiver.Hom.unop`, exactly as the additive structure of
`Cᵒᵖ` in `Mathlib.CategoryTheory.Preadditive.Opposite`, so that `op` and `unop` commute with
scalars definitionally (`CategoryTheory.op_smul`, `CategoryTheory.unop_smul`).

The opposite, left-opposite, right-opposite and unopposite of an `R`-linear functor are
`R`-linear.
-/

namespace CategoryTheory

open Opposite

universe w v₁ v₂ u₁ u₂

-- `CategoryTheory.Linear` is written in full: in the declarations named `Functor.*` below,
-- `Linear` would resolve to `CategoryTheory.Functor.Linear`.
variable (R : Type w) [Semiring R] (C : Type u₁) [Category.{v₁} C] [Preadditive C]
  [CategoryTheory.Linear R C]

/-- The opposite of an `R`-linear category is `R`-linear: `r • f = (r • f.unop).op`. -/
instance Linear.opposite : Linear R Cᵒᵖ where
  homModule _ _ :=
    { smul := fun r f => (r • f.unop).op
      one_smul := fun f => Quiver.Hom.unop_inj (one_smul R f.unop)
      mul_smul := fun r s f => Quiver.Hom.unop_inj (mul_smul r s f.unop)
      smul_zero := fun r => Quiver.Hom.unop_inj (smul_zero r)
      smul_add := fun r f g => Quiver.Hom.unop_inj (smul_add r f.unop g.unop)
      add_smul := fun r s f => Quiver.Hom.unop_inj (add_smul r s f.unop)
      zero_smul := fun f => Quiver.Hom.unop_inj (zero_smul R f.unop) }
  smul_comp _ _ _ r f g := Quiver.Hom.unop_inj (Linear.comp_smul _ _ _ g.unop r f.unop)
  comp_smul _ _ _ f r g := Quiver.Hom.unop_inj (Linear.smul_comp _ _ _ r g.unop f.unop)

variable {R C}

@[simp] theorem unop_smul {X Y : Cᵒᵖ} (r : R) (f : X ⟶ Y) : (r • f).unop = r • f.unop := rfl

@[simp] theorem op_smul {X Y : C} (r : R) (f : X ⟶ Y) : (r • f).op = r • f.op := rfl

/-- `unop` as an `R`-linear equivalence of hom modules. -/
@[simps]
def unopLinearEquiv (X Y : Cᵒᵖ) : (X ⟶ Y) ≃ₗ[R] (unop Y ⟶ unop X) where
  toFun f := f.unop
  invFun g := g.op
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [CategoryTheory.Linear R D]

instance Functor.op_linear (F : C ⥤ D) [F.Linear R] : F.op.Linear R where
  map_smul f r := Quiver.Hom.unop_inj (Functor.Linear.map_smul (F := F) f.unop r)

instance Functor.leftOp_linear (F : C ⥤ Dᵒᵖ) [F.Linear R] : F.leftOp.Linear R where
  map_smul f r := Quiver.Hom.op_inj (Functor.Linear.map_smul (F := F) f.unop r)

instance Functor.rightOp_linear (F : Cᵒᵖ ⥤ D) [F.Linear R] : F.rightOp.Linear R where
  map_smul f r := Quiver.Hom.unop_inj (Functor.Linear.map_smul (F := F) f.op r)

instance Functor.unop_linear (F : Cᵒᵖ ⥤ Dᵒᵖ) [F.Linear R] : F.unop.Linear R where
  map_smul f r := Quiver.Hom.op_inj (Functor.Linear.map_smul (F := F) f.op r)

end CategoryTheory
