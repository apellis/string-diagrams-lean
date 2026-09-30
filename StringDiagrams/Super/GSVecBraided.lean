import StringDiagrams.Super.GSVecMonoidal
import StringDiagrams.Super.SVecBraided

/-!
# The symmetric braiding of graded superspaces

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6 (before
Definition 6.1): the category `GSVec̲` of graded superspaces and degree-preserving even linear
maps "is a symmetric monoidal category with `(V ⊗ W)ₙ = ⨁_{r+s=n} Vᵣ ⊗ Wₛ`, and the same
braiding as in `SVec`". Thus the sign of the braiding depends only on the parities, not on the
`ℤ`-degrees: `c_{V,W}(v ⊗ w) = (-1)^{|v||w|} w ⊗ v` for `v`, `w` of parities `|v|`, `|w|` and
arbitrary degrees (`GSVec.braiding_hom_tmul`).

* The braiding `SVec.braidingMap` of `StringDiagrams.Super.SVecBraided` has degree zero
  (`GradedSuperspace.braidingMap_mem_degHom`): it maps `Vᵣ ⊗ Wₛ` to `Wₛ ⊗ Vᵣ`.
* Hence `GSVec k` is a braided monoidal supercategory
  (`GSVec.instBraidedMonoidalSupercategory`), with braiding of degree zero
  (`GSVec.braiding_hom_mem_degree`) and symmetric (`GSVec.braiding_hom_comp_braiding_hom`).
* For a graded monoidal supercategory `C`, the morphisms of degree zero form a monoidal
  supercategory (`GradedSupercategory.DegreeZero.instMonoidalSupercategory`), so that the
  underlying category `GUnderlying R C` of even morphisms of degree zero is a monoidal category.
  For `GSVec k` the braiding restricts to the degree-zero morphisms
  (`GSVec.instBraidedMonoidalSupercategoryDegreeZero`), and the paper's `GSVec̲ =
  GradedSupercategory.GUnderlying k (GSVec k)` is a symmetric monoidal category
  (`GSVec.instSymmetricCategoryGUnderlying`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory GradedSupercategory TensorProduct

/-! ## The monoidal supercategory of morphisms of degree zero -/

namespace GradedSupercategory.DegreeZero

universe w w₁ w₂

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [GradedSupercategory R C] [MonoidalCategoryStruct C]
  [MonoidalSupercategory R C] [GradedMonoidalSupercategory R C]

/-- The monoidal structure of the morphisms of degree zero of a graded monoidal
supercategory. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (DegreeZero R C) where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  whiskerLeft X _ _ f := ⟨X.obj ◁ f.1, GradedMonoidalSupercategory.whiskerLeft_mem_degree _ f.2⟩
  whiskerRight f Y := ⟨f.1 ▷ Y.obj, GradedMonoidalSupercategory.whiskerRight_mem_degree _ f.2⟩
  tensorHom f g :=
    ⟨f.1 ⊗ₘ g.1, by simpa using GradedMonoidalSupercategory.tensorHom_mem_degree f.2 g.2⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z := isoMk (α_ X.obj Y.obj Z.obj)
    (GradedMonoidalSupercategory.associator_hom_mem_degree _ _ _)
  leftUnitor X := isoMk (λ_ X.obj) (GradedMonoidalSupercategory.leftUnitor_hom_mem_degree _)
  rightUnitor X := isoMk (ρ_ X.obj) (GradedMonoidalSupercategory.rightUnitor_hom_mem_degree _)

@[simp] theorem tensorObj_obj (X Y : DegreeZero R C) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

@[simp] theorem tensorUnit_obj : (𝟙_ (DegreeZero R C)).obj = 𝟙_ C := rfl

@[simp] theorem whiskerLeft_val (X : DegreeZero R C) {Y Y' : DegreeZero R C} (f : Y ⟶ Y') :
    (X ◁ f).1 = X.obj ◁ f.1 := rfl

@[simp] theorem whiskerRight_val {X X' : DegreeZero R C} (f : X ⟶ X') (Y : DegreeZero R C) :
    (f ▷ Y).1 = f.1 ▷ Y.obj := rfl

@[simp] theorem tensorHom_val {X X' Y Y' : DegreeZero R C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g).1 = f.1 ⊗ₘ g.1 := rfl

@[simp] theorem associator_hom_val (X Y Z : DegreeZero R C) :
    (α_ X Y Z).hom.1 = (α_ X.obj Y.obj Z.obj).hom := rfl

@[simp] theorem leftUnitor_hom_val (X : DegreeZero R C) : (λ_ X).hom.1 = (λ_ X.obj).hom := rfl

@[simp] theorem rightUnitor_hom_val (X : DegreeZero R C) : (ρ_ X).hom.1 = (ρ_ X.obj).hom := rfl

/-- The morphisms of degree zero of a graded monoidal supercategory form a monoidal
supercategory. -/
instance instMonoidalSupercategory : MonoidalSupercategory R (DegreeZero R C) where
  tensorHom_def f g := Subtype.ext (MonoidalSupercategory.tensorHom_def (R := R) f.1 g.1)
  whiskerLeft_id X Y := Subtype.ext (MonoidalSupercategory.whiskerLeft_id (R := R) X.obj Y.obj)
  id_whiskerRight X Y := Subtype.ext (MonoidalSupercategory.id_whiskerRight (R := R) X.obj Y.obj)
  whiskerLeft_comp X _ _ _ f g :=
    Subtype.ext (MonoidalSupercategory.whiskerLeft_comp (R := R) X.obj f.1 g.1)
  comp_whiskerRight f g W :=
    Subtype.ext (MonoidalSupercategory.comp_whiskerRight (R := R) f.1 g.1 W.obj)
  whiskerLeft_add X _ _ f g :=
    Subtype.ext (MonoidalSupercategory.whiskerLeft_add (R := R) X.obj f.1 g.1)
  add_whiskerRight f g Z :=
    Subtype.ext (MonoidalSupercategory.add_whiskerRight (R := R) f.1 g.1 Z.obj)
  whiskerLeft_smul X _ _ r f :=
    Subtype.ext (MonoidalSupercategory.whiskerLeft_smul (R := R) X.obj r f.1)
  smul_whiskerRight r f Z :=
    Subtype.ext (MonoidalSupercategory.smul_whiskerRight (R := R) r f.1 Z.obj)
  whiskerLeft_mem X _ _ _ _ hf := mem_parity_iff.2
    (MonoidalSupercategory.whiskerLeft_mem (R := R) X.obj (mem_parity_iff.1 hf))
  whiskerRight_mem Z hf := mem_parity_iff.2
    (MonoidalSupercategory.whiskerRight_mem (R := R) Z.obj (mem_parity_iff.1 hf))
  super_interchange hf hg := Subtype.ext
    (MonoidalSupercategory.super_interchange (R := R) (mem_parity_iff.1 hf) (mem_parity_iff.1 hg))
  associator_naturality f₁ f₂ f₃ :=
    Subtype.ext (MonoidalSupercategory.associator_naturality (R := R) f₁.1 f₂.1 f₃.1)
  leftUnitor_naturality f := Subtype.ext (MonoidalSupercategory.leftUnitor_naturality (R := R) f.1)
  rightUnitor_naturality f :=
    Subtype.ext (MonoidalSupercategory.rightUnitor_naturality (R := R) f.1)
  pentagon W X Y Z :=
    Subtype.ext (MonoidalSupercategory.pentagon (R := R) W.obj X.obj Y.obj Z.obj)
  triangle X Y := Subtype.ext (MonoidalSupercategory.triangle (R := R) X.obj Y.obj)
  associator_hom_mem X Y Z :=
    mem_parity_iff.2 (MonoidalSupercategory.associator_hom_mem (R := R) X.obj Y.obj Z.obj)
  leftUnitor_hom_mem X := mem_parity_iff.2 (MonoidalSupercategory.leftUnitor_hom_mem (R := R) X.obj)
  rightUnitor_hom_mem X :=
    mem_parity_iff.2 (MonoidalSupercategory.rightUnitor_hom_mem (R := R) X.obj)

end GradedSupercategory.DegreeZero

universe u

variable {k : Type u} [CommRing k]

/-! ## The braiding has degree zero -/

namespace GradedSuperspace

/-- The braiding `c_{V,W}` of the underlying superspaces maps `Vᵣ ⊗ Wₛ` to `Wₛ ⊗ Vᵣ`: it is
homogeneous of degree `0`. -/
theorem braidingMap_mem_degHom (V W : GradedSuperspace k) :
    SVec.braidingMap V.toSVec W.toSVec ∈ degHom (V.tensorObj W) (W.tensorObj V) 0 := by
  intro m x hx
  refine (tensorDeg_le_iff V W
    (S := (W.tensorDeg V (m + 0)).comap
      (SVec.toLinearMap (SVec.braidingMap V.toSVec W.toSVec)))).2
    (fun r s hrs v hv w hw => ?_) hx
  rw [Submodule.mem_comap]
  change TensorProduct.comm k V.toSVec W.toSVec
    ((map (V.toSVec.proj 0) LinearMap.id + map (V.toSVec.proj 1) (W.toSVec.sgn 1) :
      V.toSVec ⊗[k] W.toSVec →ₗ[k] V.toSVec ⊗[k] W.toSVec) (v ⊗ₜ w)) ∈ _
  rw [LinearMap.add_apply, map_tmul, map_tmul, LinearMap.id_apply, map_add, comm_tmul,
    comm_tmul]
  subst hrs
  rw [add_zero, add_comm r s]
  exact Submodule.add_mem _ (tmul_mem_tensorDeg W V hw (V.proj_mem 0 hv))
    (tmul_mem_tensorDeg W V (W.sgn_mem hw) (V.proj_mem 1 hv))

end GradedSuperspace

/-! ## The braided monoidal supercategory `GSVec` -/

namespace GSVec

open GradedSuperspace GradedSubcategory

/-- The braiding `c_{V,W} : V ⊗ W ≅ W ⊗ V` of graded superspaces, that of the underlying
superspaces. -/
def braidingIso (V W : GSVec k) : tensorObj V W ≅ tensorObj W V :=
  isoMk (SVec.braidingIso V.as.toSVec W.as.toSVec) (braidingMap_mem_degHom V.as W.as)
    (braidingMap_mem_degHom W.as V.as)

/-- **Brundan–Ellis, §6 (before Definition 6.1).** `GSVec k` is a braided monoidal
supercategory, with the braiding of `SVec k`. -/
instance instBraidedMonoidalSupercategory : BraidedMonoidalSupercategory k (GSVec k) where
  braiding := braidingIso
  braiding_hom_mem V W := SVec.braidingMap_mem V.as.toSVec W.as.toSVec
  braiding_naturality_right X _ _ f :=
    Subtype.ext (SVec.braidingMap_naturality_right X.as.toSVec f.1)
  braiding_naturality_left f Z := Subtype.ext (SVec.braidingMap_naturality_left f.1 Z.as.toSVec)
  hexagon_forward X Y Z := Subtype.ext (SVec.hexagon_forward X.as.toSVec Y.as.toSVec Z.as.toSVec)
  hexagon_reverse X Y Z := Subtype.ext (SVec.hexagon_reverse X.as.toSVec Y.as.toSVec Z.as.toSVec)

@[simp] theorem braiding_hom_val (V W : GSVec k) :
    (BraidedMonoidalSupercategory.braiding (R := k) V W).hom.1 =
      SVec.braidingMap V.as.toSVec W.as.toSVec := rfl

@[simp] theorem braiding_inv_val (V W : GSVec k) :
    (BraidedMonoidalSupercategory.braiding (R := k) V W).inv.1 =
      SVec.braidingMap W.as.toSVec V.as.toSVec := rfl

/-- The braiding of `GSVec k` has degree zero. -/
theorem braiding_hom_mem_degree (V W : GSVec k) :
    (BraidedMonoidalSupercategory.braiding (R := k) V W).hom ∈
      GradedSupercategory.degree (R := k) (V ⊗ W) (W ⊗ V) 0 :=
  braidingMap_mem_degHom V.as W.as

/-- **Brundan–Ellis, §6.** The sign of the braiding of graded superspaces depends only on the
parities: `c_{V,W}(v ⊗ w) = (-1)^{|v||w|} w ⊗ v` for `v`, `w` of parities `|v|`, `|w|` (of
any degrees). -/
theorem braiding_hom_tmul {V W : GSVec k} {p q : ZMod 2} {v : V.as.toSVec} {w : W.as.toSVec}
    (hv : v ∈ V.as.toSVec.part p) (hw : w ∈ W.as.toSVec.part q) :
    (BraidedMonoidalSupercategory.braiding (R := k) V W).hom.1 (v ⊗ₜ w) =
      sign k (p * q) • (w ⊗ₜ v) :=
  SVec.braidingMap_tmul hv hw

/-- **The braiding of `GSVec k` is symmetric:** `c_{W,V} ∘ c_{V,W} = 1`. -/
theorem braiding_hom_comp_braiding_hom (V W : GSVec k) :
    (BraidedMonoidalSupercategory.braiding (R := k) V W).hom ≫
      (BraidedMonoidalSupercategory.braiding (R := k) W V).hom = 𝟙 (V ⊗ W) :=
  Subtype.ext (SVec.braidingMap_comp_braidingMap V.as.toSVec W.as.toSVec)

/-! ## The symmetric monoidal category `GSVec̲` -/

/-- The braiding of `GSVec k` restricted to the morphisms of degree zero. -/
instance instBraidedMonoidalSupercategoryDegreeZero :
    BraidedMonoidalSupercategory k (DegreeZero k (GSVec k)) where
  braiding X Y := DegreeZero.isoMk (BraidedMonoidalSupercategory.braiding (R := k) X.obj Y.obj)
    (braiding_hom_mem_degree X.obj Y.obj)
  braiding_hom_mem X Y := BraidedMonoidalSupercategory.braiding_hom_mem (R := k) X.obj Y.obj
  braiding_naturality_right X _ _ f :=
    Subtype.ext (BraidedMonoidalSupercategory.braiding_naturality_right (R := k) X.obj f.1)
  braiding_naturality_left f Z :=
    Subtype.ext (BraidedMonoidalSupercategory.braiding_naturality_left (R := k) f.1 Z.obj)
  hexagon_forward X Y Z :=
    Subtype.ext (BraidedMonoidalSupercategory.hexagon_forward (R := k) X.obj Y.obj Z.obj)
  hexagon_reverse X Y Z :=
    Subtype.ext (BraidedMonoidalSupercategory.hexagon_reverse (R := k) X.obj Y.obj Z.obj)

/-- **Brundan–Ellis, §6 (before Definition 6.1).** The underlying category `GSVec̲` of graded
superspaces and even linear maps of degree zero is a symmetric monoidal category, with the
braiding of `SVec̲`. -/
instance instSymmetricCategoryGUnderlying : SymmetricCategory (GUnderlying k (GSVec k)) where
  symmetry X Y := Subtype.ext (Subtype.ext (braiding_hom_comp_braiding_hom X.obj.obj Y.obj.obj))

end GSVec

end StringDiagrams

end
