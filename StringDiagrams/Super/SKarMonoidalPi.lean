import StringDiagrams.Super.SKarMonoidal

/-!
# `SKar(A)` is a monoidal Π-category

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §1.5:
"In case `A` is a monoidal supercategory, `SKar(A)` is a monoidal Π-category."

We show that a monoidal Π-category structure `(π, β, ξ)` (Definition 1.14) on a monoidal linear
category `D` extends to its additive envelope `Mat_ D` (`Mat_.instMonoidalPiCategory`) and to its
idempotent completion (`Karoubi.instMonoidalPiCategory`), with `π` the image of `π` and `β`, `ξ`
extended entrywise, resp. composed with the idempotents. Applied to the underlying monoidal
Π-category `A̲_π` of the monoidal Π-envelope (`MonoidalPiSupercategory.toMonoidalPiCategory`),
`SKar(A)` is a monoidal Π-category (`SKar.instMonoidalPiCategory`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Limits Idempotents

universe w v u

section Linear

variable {R : Type w} [CommRing R] {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear R D]

theorem tensor_smul' {W X Y Z : D} (f : W ⟶ X) (r : R) (g : Y ⟶ Z) :
    f ⊗ (r • g) = r • (f ⊗ g) := by
  rw [tensorHom_def, tensorHom_def, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]

theorem smul_tensor' {W X Y Z : D} (r : R) (f : W ⟶ X) (g : Y ⟶ Z) :
    (r • f) ⊗ g = r • (f ⊗ g) := by
  rw [tensorHom_def, tensorHom_def, MonoidalLinear.smul_whiskerRight, Linear.smul_comp]

instance Mat_.instMonoidalLinear : MonoidalLinear R (Mat_ D) where
  whiskerLeft_smul X Y Z r f := by
    ext i j
    exact tensor_smul' _ r _
  smul_whiskerRight r Y Z f X := by
    ext i j
    exact smul_tensor' r _ _

instance Karoubi.instMonoidalLinear : MonoidalLinear R (Karoubi D) where
  whiskerLeft_smul _ _ _ r _ := Idempotents.Karoubi.hom_ext _ _ (tensor_smul' _ r _)
  smul_whiskerRight r _ _ _ _ := Idempotents.Karoubi.hom_ext _ _ (smul_tensor' r _ _)

end Linear

/-! ## Half-braidings on the additive envelope -/

namespace Mat_

open CategoryTheory.Mat_

variable {D : Type u} [Category.{v} D] [Preadditive D] [MonoidalCategory D]
  [MonoidalPreadditive D]

/-- The index bijection `PUnit × ι ≃ ι × PUnit`. -/
def swapIdx (ι : Type) : PUnit × ι ≃ ι × PUnit :=
  (Equiv.punitProd ι).trans (Equiv.prodPUnit ι).symm

/-- The half-braiding of `X` extended to the additive envelope. -/
@[simps]
def halfBraidingIso {X : D} (b : HalfBraiding X) (M : Mat_ D) :
    (embedding D).obj X ⊗ M ≅ M ⊗ (embedding D).obj X where
  hom := permMat (X := fun x : PUnit × M.ι => X ⊗ M.X x.2) (Y := fun y : M.ι × PUnit => M.X y.1 ⊗ X)
    (swapIdx M.ι) fun x => (b.β (M.X x.2)).hom
  inv := permMat (X := fun y : M.ι × PUnit => M.X y.1 ⊗ X) (Y := fun x : PUnit × M.ι => X ⊗ M.X x.2)
    (swapIdx M.ι).symm fun y => (b.β (M.X y.1)).inv
  hom_inv_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.hom_inv_id _
  inv_hom_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.inv_hom_id _

/-- **A half-braiding extends to the additive envelope.** -/
def halfBraiding {X : D} (b : HalfBraiding X) : HalfBraiding ((embedding D).obj X) where
  β := halfBraidingIso b
  monoidal U U' := by
    change (halfBraidingIso b (tensorObj U U')).hom =
      (associator _ U U').inv ≫ tensorHom (halfBraidingIso b U).hom (𝟙 U') ≫
        (associator U _ U').hom ≫ tensorHom (𝟙 U) (halfBraidingIso b U').hom ≫
          (associator U U' _).inv
    rw [halfBraidingIso_hom, halfBraidingIso_hom, halfBraidingIso_hom, associator_inv,
      associator_hom, associator_inv, id_eq_permMat' U, id_eq_permMat' U', tensorHom_permMat,
      tensorHom_permMat, permMat_comp_permMat, permMat_comp_permMat, permMat_comp_permMat,
      permMat_comp_permMat]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    simp only [id_tensorHom, tensorHom_id, Category.assoc]
    exact b.monoidal _ _
  naturality {U U'} f := by
    refine hom_ext_equiv (swapIdx U'.ι) fun m i => ?_
    change (tensorHom (𝟙 _) f ≫ (halfBraidingIso b U').hom) m _ =
      ((halfBraidingIso b U).hom ≫ tensorHom f (𝟙 _)) m _
    rw [halfBraidingIso_hom, halfBraidingIso_hom]
    refine (comp_permMat_apply (X := fun x : PUnit × U'.ι => X ⊗ U'.X x.2)
      (Y := fun y : U'.ι × PUnit => U'.X y.1 ⊗ X) (swapIdx U'.ι)
      (fun x => (b.β (U'.X x.2)).hom) _ m i).trans ?_
    refine Eq.trans ?_ (permMat_comp_apply (X := fun x : PUnit × U.ι => X ⊗ U.X x.2)
      (Y := fun y : U.ι × PUnit => U.X y.1 ⊗ X) (swapIdx U.ι)
      (fun x => (b.β (U.X x.2)).hom) _ m _).symm
    obtain ⟨⟨⟩, m⟩ := m
    obtain ⟨⟨⟩, i⟩ := i
    rw [tensorHom_apply, tensorHom_apply]
    change (𝟙 ((embedding D).obj X) PUnit.unit PUnit.unit ⊗ f m i) ≫ _ =
      _ ≫ (f m i ⊗ 𝟙 ((embedding D).obj X) PUnit.unit PUnit.unit)
    rw [id_apply_self, id_tensorHom, tensorHom_id]
    exact b.naturality _

omit [MonoidalCategory D] [MonoidalPreadditive D] in
theorem permMat_neg {ι κ : Type} [Fintype ι] [Fintype κ] {X : ι → D} {Y : κ → D} (e : ι ≃ κ)
    (φ : ∀ i, X i ⟶ Y (e i)) : permMat e (fun i => -φ i) = -permMat e φ := by
  ext i j
  by_cases h : e i = j
  · subst h
    show _ = -(permMat e φ i (e i))
    rw [permMat_apply_self, permMat_apply_self]
  · show _ = -(permMat e φ i j)
    rw [permMat_apply_of_ne _ _ h, permMat_apply_of_ne _ _ h, neg_zero]

variable {R : Type w} [CommRing R] [Linear R D] [MonoidalLinear R D] [MonoidalPiCategory R D]

local notation "𝛑" => MonoidalPiCategory.pi (R := R) (D := D)

variable (R D) in
/-- `ξ : π ⊗ π ≅ 1` in the additive envelope. -/
@[simps]
def ξIso : (embedding D).obj 𝛑 ⊗ (embedding D).obj 𝛑 ≅ 𝟙_ (Mat_ D) where
  hom := permMat (X := fun _ : PUnit × PUnit => 𝛑 ⊗ 𝛑) (Y := fun _ : PUnit => 𝟙_ D)
    (Equiv.punitProd PUnit) fun _ => (MonoidalPiCategory.ξ (R := R)).hom
  inv := permMat (X := fun _ : PUnit => 𝟙_ D) (Y := fun _ : PUnit × PUnit => 𝛑 ⊗ 𝛑)
    (Equiv.punitProd PUnit).symm fun _ => (MonoidalPiCategory.ξ (R := R)).inv
  hom_inv_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.hom_inv_id _
  inv_hom_id := by
    rw [permMat_comp_permMat]
    exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by
      rw [eqToHom_refl, Category.comp_id]; exact Iso.inv_hom_id _

/-- **A monoidal Π-category structure extends to the additive envelope.** -/
instance instMonoidalPiCategory : MonoidalPiCategory R (Mat_ D) where
  pi := (embedding D).obj 𝛑
  β := halfBraiding (MonoidalPiCategory.β (R := R))
  β_pi := by
    change (halfBraidingIso _ _).hom = _
    rw [halfBraidingIso_hom, id_eq_permMat', ← permMat_neg]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    exact MonoidalPiCategory.β_pi
  ξ := ξIso (R := R) (D := D)
  ξ_comm M := by
    change tensorHom (ξIso (R := R) (D := D)).hom (𝟙 M) ≫ (leftUnitor M).hom ≫ (rightUnitor M).inv ≫
        tensorHom (𝟙 M) (ξIso (R := R) (D := D)).inv =
      (associator _ _ M).hom ≫ tensorHom (𝟙 _) (halfBraidingIso _ M).hom ≫
        (associator _ M _).inv ≫ tensorHom (halfBraidingIso _ M).hom (𝟙 _) ≫
          (associator M _ _).hom
    rw [ξIso_hom, ξIso_inv, leftUnitor_hom, rightUnitor_inv, associator_hom, associator_inv,
      associator_hom, halfBraidingIso_hom, id_eq_permMat' M, id_eq_permMat' ((embedding D).obj 𝛑),
      tensorHom_permMat, tensorHom_permMat, tensorHom_permMat, tensorHom_permMat,
      permMat_comp_permMat, permMat_comp_permMat, permMat_comp_permMat, permMat_comp_permMat,
      permMat_comp_permMat, permMat_comp_permMat, permMat_comp_permMat]
    refine permMat_congr (fun _ => rfl) _ _ fun x => ?_
    rw [eqToHom_refl, Category.comp_id]
    simp only [id_tensorHom, tensorHom_id, Category.assoc]
    exact MonoidalPiCategory.ξ_comm _

end Mat_

/-! ## Half-braidings on the idempotent completion -/

namespace Karoubi

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

omit [MonoidalCategory C] in
theorem comm_comp {X Y Z : C} {E : X ⟶ X} {E₁ : Y ⟶ Y} {E₂ : Z ⟶ Z} {ψ₁ : X ⟶ Y} {ψ₂ : Y ⟶ Z}
    (h₁ : E ≫ ψ₁ = ψ₁ ≫ E₁) (h₂ : E₁ ≫ ψ₂ = ψ₂ ≫ E₂) : E ≫ ψ₁ ≫ ψ₂ = (ψ₁ ≫ ψ₂) ≫ E₂ := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

@[reassoc]
theorem p_whiskerRight_idem (P : Karoubi C) (Y : C) : P.p ▷ Y ≫ P.p ▷ Y = P.p ▷ Y := by
  rw [← comp_whiskerRight, P.idem]

@[reassoc]
theorem whiskerLeft_p_idem (Y : C) (P : Karoubi C) : Y ◁ P.p ≫ Y ◁ P.p = Y ◁ P.p := by
  rw [← MonoidalCategory.whiskerLeft_comp, P.idem]

variable {X : C} (b : HalfBraiding X)

/-- The half-braiding extended to the idempotent completion:
`β_{(Y, p)} = β_Y ∘ (1 ⊗ p) = (p ⊗ 1) ∘ β_Y`. -/
@[simps]
def halfBraidingIso (P : Karoubi C) : (toKaroubi C).obj X ⊗ P ≅ P ⊗ (toKaroubi C).obj X where
  hom := ⟨(b.β P.X).hom ≫ (P.p ⊗ 𝟙 X), by
    change _ = (𝟙 X ⊗ P.p) ≫ ((b.β P.X).hom ≫ (P.p ⊗ 𝟙 X)) ≫ (P.p ⊗ 𝟙 X)
    rw [id_tensorHom, tensorHom_id, Category.assoc, b.naturality_assoc, p_whiskerRight_idem,
      p_whiskerRight_idem]⟩
  inv := ⟨(b.β P.X).inv ≫ (𝟙 X ⊗ P.p), by
    change _ = (P.p ⊗ 𝟙 X) ≫ ((b.β P.X).inv ≫ (𝟙 X ⊗ P.p)) ≫ (𝟙 X ⊗ P.p)
    have h : (P.p ⊗ 𝟙 X) ≫ (b.β P.X).inv = (b.β P.X).inv ≫ (𝟙 X ⊗ P.p) := by
      rw [Iso.comp_inv_eq, Category.assoc, id_tensorHom, b.naturality, tensorHom_id,
        Iso.inv_hom_id_assoc]
    rw [Category.assoc, reassoc_of% h, id_tensorHom, whiskerLeft_p_idem, whiskerLeft_p_idem]⟩
  hom_inv_id := Idempotents.Karoubi.hom_ext _ _ (by
    change ((b.β P.X).hom ≫ (P.p ⊗ 𝟙 X)) ≫ (b.β P.X).inv ≫ (𝟙 X ⊗ P.p) = 𝟙 X ⊗ P.p
    have h : (P.p ⊗ 𝟙 X) ≫ (b.β P.X).inv = (b.β P.X).inv ≫ (𝟙 X ⊗ P.p) := by
      rw [Iso.comp_inv_eq, Category.assoc, id_tensorHom, b.naturality, tensorHom_id,
        Iso.inv_hom_id_assoc]
    rw [Category.assoc, reassoc_of% h, Iso.hom_inv_id_assoc, id_tensorHom,
      ← MonoidalCategory.whiskerLeft_comp, P.idem])
  inv_hom_id := Idempotents.Karoubi.hom_ext _ _ (by
    change ((b.β P.X).inv ≫ (𝟙 X ⊗ P.p)) ≫ (b.β P.X).hom ≫ (P.p ⊗ 𝟙 X) = P.p ⊗ 𝟙 X
    rw [Category.assoc, id_tensorHom, b.naturality_assoc, Iso.inv_hom_id_assoc, tensorHom_id,
      ← comp_whiskerRight, P.idem])

/-- **A half-braiding extends to the idempotent completion.** -/
def halfBraiding : HalfBraiding ((toKaroubi C).obj X) where
  β := halfBraidingIso b
  monoidal U U' := Idempotents.Karoubi.hom_ext _ _ (by
    change (b.β (U.X ⊗ U'.X)).hom ≫ ((U.p ⊗ U'.p) ⊗ 𝟙 X) =
      ((α_ X U.X U'.X).inv ≫ ((𝟙 X ⊗ U.p) ⊗ U'.p)) ≫
        (((b.β U.X).hom ≫ (U.p ⊗ 𝟙 X)) ⊗ U'.p) ≫
          ((α_ U.X X U'.X).hom ≫ (U.p ⊗ (𝟙 X ⊗ U'.p))) ≫
            (U.p ⊗ ((b.β U'.X).hom ≫ (U'.p ⊗ 𝟙 X))) ≫
              ((α_ U.X U'.X X).inv ≫ ((U.p ⊗ U'.p) ⊗ 𝟙 X))
    have hn : ∀ (Y : Karoubi C), (𝟙 X ⊗ Y.p) ≫ (b.β Y.X).hom = (b.β Y.X).hom ≫ (Y.p ⊗ 𝟙 X) :=
      fun Y => by rw [id_tensorHom, tensorHom_id, b.naturality]
    have e2 : ((b.β U.X).hom ≫ (U.p ⊗ 𝟙 X)) ⊗ U'.p =
        ((b.β U.X).hom ⊗ 𝟙 U'.X) ≫ ((U.p ⊗ 𝟙 X) ⊗ U'.p) := by
      rw [← tensor_comp, Category.id_comp]
    have e4 : U.p ⊗ ((b.β U'.X).hom ≫ (U'.p ⊗ 𝟙 X)) =
        (𝟙 U.X ⊗ (b.β U'.X).hom) ≫ (U.p ⊗ (U'.p ⊗ 𝟙 X)) := by
      rw [← tensor_comp, Category.id_comp]
    have c12 : ((𝟙 X ⊗ U.p) ⊗ U'.p) ≫ ((b.β U.X).hom ⊗ 𝟙 U'.X) =
        ((b.β U.X).hom ⊗ 𝟙 U'.X) ≫ ((U.p ⊗ 𝟙 X) ⊗ U'.p) := by
      rw [← tensor_comp, ← tensor_comp, hn, Category.id_comp, Category.comp_id]
    have c23 : ((U.p ⊗ 𝟙 X) ⊗ U'.p) ≫ (α_ U.X X U'.X).hom =
        (α_ U.X X U'.X).hom ≫ (U.p ⊗ (𝟙 X ⊗ U'.p)) := associator_naturality _ _ _
    have c34 : (U.p ⊗ (𝟙 X ⊗ U'.p)) ≫ (𝟙 U.X ⊗ (b.β U'.X).hom) =
        (𝟙 U.X ⊗ (b.β U'.X).hom) ≫ (U.p ⊗ (U'.p ⊗ 𝟙 X)) := by
      rw [← tensor_comp, ← tensor_comp, hn, Category.id_comp, Category.comp_id]
    have c45 : (U.p ⊗ (U'.p ⊗ 𝟙 X)) ≫ (α_ U.X U'.X X).inv =
        (α_ U.X U'.X X).inv ≫ ((U.p ⊗ U'.p) ⊗ 𝟙 X) := associator_inv_naturality _ _ _
    have idem : ((U.p ⊗ U'.p) ⊗ 𝟙 X) ≫ ((U.p ⊗ U'.p) ⊗ 𝟙 X) = (U.p ⊗ U'.p) ⊗ 𝟙 X := by
      simp only [← tensor_comp, U.idem, U'.idem, Category.comp_id]
    rw [e2, e4, sandwich' _ _ _ _ c45 idem,
      sandwich' _ _ _ _ (comm_comp c34 c45) idem,
      sandwich' _ _ _ _ (comm_comp c23 (comm_comp c34 c45)) idem,
      sandwich' _ _ _ _ (comm_comp c12 (comm_comp c23 (comm_comp c34 c45))) idem]
    congr 1
    simp only [Category.assoc, tensorHom_id, id_tensorHom]
    exact b.monoidal _ _)
  naturality {U U'} f := Idempotents.Karoubi.hom_ext _ _ (by
    change (𝟙 X ⊗ f.f) ≫ (b.β U'.X).hom ≫ (U'.p ⊗ 𝟙 X) =
      ((b.β U.X).hom ≫ (U.p ⊗ 𝟙 X)) ≫ (f.f ⊗ 𝟙 X)
    rw [id_tensorHom, tensorHom_id, tensorHom_id, tensorHom_id, b.naturality_assoc,
      Category.assoc, ← comp_whiskerRight, ← comp_whiskerRight, Idempotents.Karoubi.comp_p,
      Idempotents.Karoubi.p_comp])

variable {R : Type w} [CommRing R] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C] [MonoidalPiCategory R C]

local notation "𝛑" => MonoidalPiCategory.pi (R := R) (D := C)

variable (R C) in
/-- `ξ : π ⊗ π ≅ 1` in the idempotent completion. -/
@[simps]
def ξMonoidalIso : (toKaroubi C).obj 𝛑 ⊗ (toKaroubi C).obj 𝛑 ≅ 𝟙_ (Karoubi C) where
  hom := ⟨(MonoidalPiCategory.ξ (R := R)).hom, by
    change _ = (𝟙 𝛑 ⊗ 𝟙 𝛑) ≫ (MonoidalPiCategory.ξ (R := R)).hom ≫ 𝟙 (𝟙_ C)
    rw [tensor_id, Category.id_comp, Category.comp_id]⟩
  inv := ⟨(MonoidalPiCategory.ξ (R := R)).inv, by
    change _ = 𝟙 (𝟙_ C) ≫ (MonoidalPiCategory.ξ (R := R)).inv ≫ (𝟙 𝛑 ⊗ 𝟙 𝛑)
    rw [tensor_id, Category.id_comp, Category.comp_id]⟩
  hom_inv_id := Idempotents.Karoubi.hom_ext _ _ (by
    change (MonoidalPiCategory.ξ (R := R)).hom ≫ (MonoidalPiCategory.ξ (R := R)).inv =
      (𝟙 𝛑 ⊗ 𝟙 𝛑 : 𝛑 ⊗ 𝛑 ⟶ 𝛑 ⊗ 𝛑)
    rw [Iso.hom_inv_id, tensor_id])
  inv_hom_id := Idempotents.Karoubi.hom_ext _ _ (Iso.inv_hom_id _)

set_option maxHeartbeats 1000000 in
/-- **A monoidal Π-category structure extends to the idempotent completion.** -/
instance instMonoidalPiCategory : MonoidalPiCategory R (Karoubi C) where
  pi := (toKaroubi C).obj 𝛑
  β := halfBraiding (MonoidalPiCategory.β (R := R))
  β_pi := Idempotents.Karoubi.hom_ext _ _ (by
    change ((MonoidalPiCategory.β (R := R)).β 𝛑).hom ≫ (𝟙 𝛑 ⊗ 𝟙 𝛑) = -(𝟙 𝛑 ⊗ 𝟙 𝛑)
    rw [MonoidalPiCategory.β_pi, tensor_id, Category.comp_id])
  ξ := ξMonoidalIso (R := R) (C := C)
  ξ_comm P := Idempotents.Karoubi.hom_ext _ _ (by
    let b := MonoidalPiCategory.β (R := R) (D := C)
    let ξ := MonoidalPiCategory.ξ (R := R) (D := C)
    change (ξ.hom ⊗ P.p) ≫ ((λ_ P.X).hom ≫ P.p) ≫ (P.p ≫ (ρ_ P.X).inv) ≫ (P.p ⊗ ξ.inv) =
      ((α_ 𝛑 𝛑 P.X).hom ≫ (𝟙 𝛑 ⊗ (𝟙 𝛑 ⊗ P.p))) ≫
        (𝟙 𝛑 ⊗ ((b.β P.X).hom ≫ (P.p ⊗ 𝟙 𝛑))) ≫
          ((α_ 𝛑 P.X 𝛑).inv ≫ ((𝟙 𝛑 ⊗ P.p) ⊗ 𝟙 𝛑)) ≫
            (((b.β P.X).hom ≫ (P.p ⊗ 𝟙 𝛑)) ⊗ 𝟙 𝛑) ≫
              ((α_ P.X 𝛑 𝛑).hom ≫ (P.p ⊗ (𝟙 𝛑 ⊗ 𝟙 𝛑)))
    have hn : (𝟙 𝛑 ⊗ P.p) ≫ (b.β P.X).hom = (b.β P.X).hom ≫ (P.p ⊗ 𝟙 𝛑) := by
      rw [id_tensorHom, tensorHom_id, b.naturality]
    have idem : (P.p ⊗ (𝟙 𝛑 ⊗ 𝟙 𝛑)) ≫ (P.p ⊗ (𝟙 𝛑 ⊗ 𝟙 𝛑)) = P.p ⊗ (𝟙 𝛑 ⊗ 𝟙 𝛑) := by
      simp only [← tensor_comp, P.idem, Category.comp_id]
    -- the left-hand side
    have l1 : ξ.hom ⊗ P.p = (ξ.hom ⊗ 𝟙 P.X) ≫ (𝟙 (𝟙_ C) ⊗ P.p) := by
      rw [← tensor_comp, Category.id_comp, Category.comp_id]
    have l3 : P.p ≫ (ρ_ P.X).inv = (ρ_ P.X).inv ≫ (P.p ⊗ 𝟙 (𝟙_ C)) := by
      rw [tensorHom_id, rightUnitor_inv_naturality]
    have l4 : P.p ⊗ ξ.inv = (𝟙 P.X ⊗ ξ.inv) ≫ (P.p ⊗ (𝟙 𝛑 ⊗ 𝟙 𝛑)) := by
      rw [← tensor_comp, tensor_id, Category.id_comp, Category.comp_id]
    have d12 : (𝟙 (𝟙_ C) ⊗ P.p) ≫ (λ_ P.X).hom = (λ_ P.X).hom ≫ P.p := by
      rw [id_tensorHom, leftUnitor_naturality]
    have d23 : P.p ≫ (ρ_ P.X).inv = (ρ_ P.X).inv ≫ (P.p ⊗ 𝟙 (𝟙_ C)) := l3
    have d34 : (P.p ⊗ 𝟙 (𝟙_ C)) ≫ (𝟙 P.X ⊗ ξ.inv) =
        (𝟙 P.X ⊗ ξ.inv) ≫ (P.p ⊗ (𝟙 𝛑 ⊗ 𝟙 𝛑)) := by
      rw [← tensor_comp, ← tensor_comp, tensor_id, Category.id_comp, Category.comp_id,
        Category.id_comp, Category.comp_id]
    rw [l1, l3, l4, sandwich' _ _ _ _ d34 idem, sandwich' _ _ _ _ (comm_comp d23 d34) idem,
      sandwich' _ _ _ _ (comm_comp d12 (comm_comp d23 d34)) idem]
    -- the right-hand side
    have r2 : 𝟙 𝛑 ⊗ ((b.β P.X).hom ≫ (P.p ⊗ 𝟙 𝛑)) =
        (𝟙 𝛑 ⊗ (b.β P.X).hom) ≫ (𝟙 𝛑 ⊗ (P.p ⊗ 𝟙 𝛑)) := by
      rw [← tensor_comp, Category.id_comp]
    have r4 : ((b.β P.X).hom ≫ (P.p ⊗ 𝟙 𝛑)) ⊗ 𝟙 𝛑 =
        ((b.β P.X).hom ⊗ 𝟙 𝛑) ≫ ((P.p ⊗ 𝟙 𝛑) ⊗ 𝟙 𝛑) := by
      rw [← tensor_comp, Category.id_comp]
    have e12 : (𝟙 𝛑 ⊗ (𝟙 𝛑 ⊗ P.p)) ≫ (𝟙 𝛑 ⊗ (b.β P.X).hom) =
        (𝟙 𝛑 ⊗ (b.β P.X).hom) ≫ (𝟙 𝛑 ⊗ (P.p ⊗ 𝟙 𝛑)) := by
      rw [← tensor_comp, ← tensor_comp, hn]
    have e23 : (𝟙 𝛑 ⊗ (P.p ⊗ 𝟙 𝛑)) ≫ (α_ 𝛑 P.X 𝛑).inv =
        (α_ 𝛑 P.X 𝛑).inv ≫ ((𝟙 𝛑 ⊗ P.p) ⊗ 𝟙 𝛑) := associator_inv_naturality _ _ _
    have e34 : ((𝟙 𝛑 ⊗ P.p) ⊗ 𝟙 𝛑) ≫ ((b.β P.X).hom ⊗ 𝟙 𝛑) =
        ((b.β P.X).hom ⊗ 𝟙 𝛑) ≫ ((P.p ⊗ 𝟙 𝛑) ⊗ 𝟙 𝛑) := by
      rw [← tensor_comp, ← tensor_comp, hn]
    have e45 : ((P.p ⊗ 𝟙 𝛑) ⊗ 𝟙 𝛑) ≫ (α_ P.X 𝛑 𝛑).hom =
        (α_ P.X 𝛑 𝛑).hom ≫ (P.p ⊗ (𝟙 𝛑 ⊗ 𝟙 𝛑)) := associator_naturality _ _ _
    rw [r2, r4, sandwich' _ _ _ _ e45 idem, sandwich' _ _ _ _ (comm_comp e34 e45) idem,
      sandwich' _ _ _ _ (comm_comp e23 (comm_comp e34 e45)) idem,
      sandwich' _ _ _ _ (comm_comp e12 (comm_comp e23 (comm_comp e34 e45))) idem]
    congr 1
    have := MonoidalPiCategory.ξ_comm (R := R) P.X
    simp only [tensorHom_id, id_tensorHom, Category.assoc] at this ⊢
    exact this)

end Karoubi

namespace SKar

variable (R : Type w) [CommRing R] (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]

/-- **Brundan–Ellis, §1.5.** For a monoidal supercategory `A`, `SKar(A)` is a monoidal
Π-category: the monoidal Π-category structure of `A̲_π` (Definition 1.14, from the monoidal
Π-supercategory `A_π` of Definition 1.16) extends to the additive Karoubi envelope. -/
instance instMonoidalPiCategory : MonoidalPiCategory R (SKar R C) := inferInstance

/-- The object `π` of the monoidal Π-category `SKar(A)` is `SKar.piObj`. -/
theorem monoidalPi_pi_eq : MonoidalPiCategory.pi (R := R) (D := SKar R C) = piObj R C := rfl

end SKar

end StringDiagrams
