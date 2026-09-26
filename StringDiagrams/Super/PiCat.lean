import StringDiagrams.Super.SCat
import StringDiagrams.Super.AssociatedFunctorial

/-!
# The categories `SCat`, `Π-SCat` and `Π-Cat`, and Theorem 1.9(2)

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
(1.5), Theorem 1.9 (second bullet), Definition 1.10, (5.1)–(5.2), Lemma 5.1 and Theorem 5.3.

* The bundled supercategories `SCat R` and Π-supercategories `PiSCat R` of
  `StringDiagrams.Super.SCat` are categories with superfunctors as morphisms (the underlying
  1-categories of the strict 2-supercategories `𝔖ℭ𝔞𝔱` and `Π-𝔖ℭ𝔞𝔱`): instances
  `Category (SCat R)`, `Category (PiSCat R)`.
* `PiCat R` is the category of (small, in fixed universes) Π-categories and linear Π-functors
  of Definition 1.6 (`PiCat.Hom`: a linear functor with a `PiFunctor` structure).
* `PiSCat.E₁ : PiSCat R ⥤ PiCat R` is the functor (2) of (1.5), i.e. `E₁` of (5.1):
  `(A, Π, ζ) ↦ (A̲, Π̲, ζζ)`, `F ↦ (F̲, β_F)`; `PiCat.D₁ : PiCat R ⥤ PiSCat R` is `D₁` of (5.2):
  `A ↦ Â`, `(F, β_F) ↦ F̂`.
* **Theorem 1.9(2) / Lemma 5.1.** `D₁` and `E₁` are mutually inverse equivalences of
  categories (`PiCat.equivalence : PiCat R ≌ PiSCat R`), with `E₁ ∘ D₁ ≅ 𝟭` given by the
  identifications `unit`, `counit` of `StringDiagrams.Super.Associated` (commuting with `Π`
  and `ξ` on the nose) and `D₁ ∘ E₁ ≅ 𝟭` by the isomorphisms `T_A` (natural in `A`).

The 2-categorical strengthening (Theorem 5.3) on 2-morphisms is in
`StringDiagrams.Super.AssociatedFunctorial`; the 2-categories `Π-ℭ𝔞𝔱`, `Π-𝔖ℭ𝔞𝔱` are not bundled
as Lean bicategories.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w v u

variable {R : Type w} [CommRing R]

/-! ## `SCat` and `Π-SCat` as categories -/

namespace SCat

/-- The category `SCat` of supercategories and superfunctors (Brundan–Ellis, before (1.5)):
the underlying category of the strict 2-supercategory `𝔖ℭ𝔞𝔱`. -/
instance : Category (SCat.{w, v, u} R) where
  toCategoryStruct := (inferInstance : BicategoryStruct (SCat.{w, v, u} R)).toCategoryStruct
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end SCat

namespace PiSCat

/-- The category `Π-SCat` of Π-supercategories and superfunctors (Brundan–Ellis, before
(1.5)): the underlying category of the strict 2-supercategory `Π-𝔖ℭ𝔞𝔱`. -/
instance : Category (PiSCat.{w, v, u} R) where
  toCategoryStruct := (inferInstance : BicategoryStruct (PiSCat.{w, v, u} R)).toCategoryStruct
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end PiSCat

/-! ## Π-functors -/

namespace PiFunctor

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [PiCategory R C]
  {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D] [PiCategory R D]

theorem ext {F : C ⥤ D} {hF hG : PiFunctor R F}
    (h : ∀ X, hF.β.hom.app X = hG.β.hom.app X) : hF = hG := by
  have hβ : hF.β = hG.β := Iso.ext (NatTrans.ext (funext h))
  cases hF
  cases hG
  dsimp only at hβ
  subst hβ
  rfl

end PiFunctor

/-! ## The category `Π-Cat` -/

variable (R) in
/-- A Π-category over `R` (Brundan–Ellis, Definition 1.6(i)), bundled: an `R`-linear category
with a Π-category structure. -/
structure PiCat where
  /-- The objects. -/
  carrier : Type u
  [str : Category.{v} carrier]
  [preadditive : Preadditive carrier]
  [linear : Linear R carrier]
  [pi : PiCategory R carrier]

namespace PiCat

attribute [instance] str preadditive linear pi

instance : CoeSort (PiCat.{w, v, u} R) (Type u) := ⟨PiCat.carrier⟩

variable (R) in
/-- The bundled Π-category of a Π-category. -/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [PiCategory R C] :
    PiCat.{w, v, u} R :=
  ⟨C⟩

/-- A morphism of `Π-Cat`: a linear Π-functor (Brundan–Ellis, Definition 1.6(ii)). -/
structure Hom (A B : PiCat.{w, v, u} R) where
  /-- The underlying functor. -/
  toFunctor : A ⥤ B
  [additive : toFunctor.Additive]
  [linear : toFunctor.Linear R]
  /-- The Π-functor structure `β`. -/
  piFunctor : PiFunctor R toFunctor

attribute [instance] Hom.additive Hom.linear

/-- Two Π-functors with the same underlying functor and the same `β` are equal. -/
theorem Hom.ext {A B : PiCat.{w, v, u} R} {F G : Hom A B} (h : F.toFunctor = G.toFunctor)
    (hβ : ∀ X, HEq (F.piFunctor.β.hom.app X) (G.piFunctor.β.hom.app X)) : F = G := by
  cases F
  cases G
  dsimp only at h hβ
  subst h
  congr
  exact PiFunctor.ext fun X => eq_of_heq (hβ X)

/-- The category `Π-Cat` of Π-categories and Π-functors (Brundan–Ellis, before (1.5)). -/
instance : Category (PiCat.{w, v, u} R) where
  Hom := Hom
  id A := ⟨𝟭 A, PiFunctor.id R A⟩
  comp F G := ⟨F.toFunctor ⋙ G.toFunctor, F.piFunctor.comp G.piFunctor⟩
  id_comp F := Hom.ext rfl fun X => heq_of_eq (by
    simp [PiFunctor.comp, PiFunctor.id])
  comp_id F := Hom.ext rfl fun X => heq_of_eq (by
    simp [PiFunctor.comp, PiFunctor.id])
  assoc F G H := Hom.ext rfl fun X => heq_of_eq (by
    simp [PiFunctor.comp])

variable {A B E : PiCat.{w, v, u} R}

theorem hom_def : (A ⟶ B) = Hom A B := rfl

@[simp] theorem id_toFunctor : (𝟙 A : A ⟶ A).toFunctor = 𝟭 A := rfl

@[simp] theorem comp_toFunctor (F : A ⟶ B) (G : B ⟶ E) :
    (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

@[simp] theorem id_piFunctor : (𝟙 A : A ⟶ A).piFunctor = PiFunctor.id R A := rfl

@[simp] theorem comp_piFunctor (F : A ⟶ B) (G : B ⟶ E) :
    (F ≫ G).piFunctor = F.piFunctor.comp G.piFunctor := rfl

end PiCat

/-! ## The functors `E₁` and `D₁` -/

namespace PiSCat

/-- **Brundan–Ellis, (1.5), (5.1).** The functor `E₁ : Π-SCat → Π-Cat`,
`(A, Π, ζ) ↦ (A̲, Π̲, ξ = ζζ)`, `F ↦ (F̲, β_F)`. -/
@[simps]
def E₁ : PiSCat.{w, v, u} R ⥤ PiCat.{w, v, u} R where
  obj A := PiCat.of R (Underlying R A)
  map F := ⟨Underlying.map F.toFunctor, Underlying.piFunctor F.toFunctor⟩
  map_id A := PiCat.Hom.ext rfl fun X => heq_of_eq (Subtype.ext (by
    change (PiSupercategory.β R (𝟭 A.carrier) X.obj).hom = 𝟙 _
    exact PiSupercategory.β_id (R := R) X.obj))
  map_comp F G := PiCat.Hom.ext rfl fun X => heq_of_eq (Subtype.ext (by
    change (PiSupercategory.β R (F.toFunctor ⋙ G.toFunctor) X.obj).hom =
      (PiSupercategory.β R G.toFunctor (F.obj X.obj)).hom ≫
        G.map (PiSupercategory.β R F.toFunctor X.obj).hom
    exact PiSupercategory.β_comp (R := R) (F := F.toFunctor) G.toFunctor X.obj))

end PiSCat

namespace Associated

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [PiCategory R C]

instance : (unit R C).Additive where
  map_add := Underlying.hom_ext (Associated.hom_ext rfl (by simp))

instance : (unit R C).Linear R where
  map_smul _ _ := Underlying.hom_ext (Associated.hom_ext rfl (by simp))

instance : (counit R C).Additive where
  map_add := rfl

instance : (counit R C).Linear R where
  map_smul _ _ := rfl

/-- The inverse of `ξ̂ = ξ` in `Â`. -/
theorem ξ_inv (X : Associated R C) :
    (PiSupercategory.ξ (R := R) X).inv =
      homMk (X := X)
        (Y := ⟨(PiCategory.pi (R := R)).obj ((PiCategory.pi (R := R)).obj X.obj)⟩)
        (PiCategory.ξApp (R := R) X.obj).inv 0 := by
  rw [← cancel_epi (PiSupercategory.ξ (R := R) X).hom, Iso.hom_inv_id, ξ_hom]
  ext <;> simp

variable (R C) in
/-- The identification `counit : E₁(D₁ A) → A` as a Π-functor with `β = 1`. -/
def counitPiFunctor : PiFunctor R (counit R C) where
  β := NatIso.ofComponents (fun X => Iso.refl _) fun {X Y} f => by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.refl_hom, Category.comp_id,
      Category.id_comp]
    change _ = (((PiSupercategory.pi (R := R)).map f.1)).1
    rw [pi_map_fst]
    rfl
  comm X := by
    simp only [Functor.comp_obj, NatIso.ofComponents_hom_app, Iso.refl_hom,
      CategoryTheory.Functor.map_id, Category.id_comp]
    change (PiCategory.ξ (R := R)).hom.app X.obj.obj ≫
      ((PiCategory.ξ (R := R)).inv.app X).1.1 = 𝟙 _
    rw [Underlying.ξ_inv_app_val, ξ_inv, homMk_fst, ← PiCategory.ξApp_hom, Iso.hom_inv_id]

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [PiSupercategory R A]

instance : (Tinv R A).Additive where
  map_add {X Y f g} := T_map_injective (by
    rw [T_map_Tinv_map, Functor.map_add, T_map_Tinv_map, T_map_Tinv_map])

instance : (Tinv R A).Linear R where
  map_smul {X Y} f r := T_map_injective (by
    rw [T_map_Tinv_map, Functor.map_smul, T_map_Tinv_map])

instance : IsSuperfunctor R (Tinv R A) where
  map_mem {X Y p f} hf := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [mem_parity_zero]
      exact Subtype.ext (by
        change proj R 1 f ≫ _ = 0
        rw [proj_of_mem_ne hf (by decide), Limits.zero_comp])
    · rw [mem_parity_one]
      exact Subtype.ext (by
        change proj R 0 f = 0
        exact proj_of_mem_ne hf (by decide))

end Associated

namespace PiCat

/-- **Brundan–Ellis, (5.2).** The functor `D₁ : Π-Cat → Π-SCat`, `A ↦ Â`, `(F, β_F) ↦ F̂`. -/
@[simps]
def D₁ : PiCat.{w, v, u} R ⥤ PiSCat.{w, v, u} R where
  obj A := PiSCat.of R (Associated R A)
  map F := ⟨Associated.map F.piFunctor⟩
  map_id _ := Superfunctor.ext Associated.map_id
  map_comp F G := Superfunctor.ext (Associated.map_comp F.piFunctor G.piFunctor)

/-- **Lemma 5.1, `E₁ ∘ D₁ = I`.** The identification `A ≅ E₁(D₁ A)` in `Π-Cat` given by
`unit` and `counit`. -/
def unitIsoApp (A : PiCat.{w, v, u} R) : A ≅ PiCat.of R (Underlying R (Associated R A)) where
  hom := ⟨Associated.unit R A, Associated.unitPiFunctor⟩
  inv := ⟨Associated.counit R A, Associated.counitPiFunctor R A⟩
  hom_inv_id := Hom.ext Associated.unit_comp_counit fun X => heq_of_eq (by
    simp [PiFunctor.comp, PiFunctor.id, Associated.counitPiFunctor, Associated.unitPiFunctor]
    rfl)
  inv_hom_id := Hom.ext Associated.counit_comp_unit fun X => heq_of_eq (by
    simp [PiFunctor.comp, PiFunctor.id, Associated.counitPiFunctor, Associated.unitPiFunctor]
    rfl)

variable (R) in
/-- **Lemma 5.1, `E₁ ∘ D₁ = I`.** The natural isomorphism `𝟭 ≅ D₁ ⋙ E₁`. -/
def unitIso : 𝟭 (PiCat.{w, v, u} R) ≅ D₁ ⋙ PiSCat.E₁ :=
  NatIso.ofComponents unitIsoApp fun {A B} F => by
    refine Hom.ext ?_ fun X => ?_
    · refine CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => ?_
      simp only [Functor.comp_obj, Functor.comp_map, eqToHom_refl, Category.comp_id,
        Category.id_comp]
      exact Underlying.hom_ext (Associated.hom_ext rfl (by simp [unitIsoApp]))
    · refine heq_of_eq (Underlying.hom_ext (Associated.hom_ext ?_ ?_))
      · simp [unitIsoApp, PiFunctor.comp, Associated.unitPiFunctor, Underlying.piFunctor,
          Associated.β_map]
      · simp [unitIsoApp, PiFunctor.comp, Associated.unitPiFunctor, Underlying.piFunctor,
          Associated.β_map]

/-- **Lemma 5.1, `D₁ ∘ E₁ ≅ I`.** The isomorphism `T_A : D₁(E₁ A) ≅ A` in `Π-SCat`. -/
def counitIsoApp (A : PiSCat.{w, v, u} R) :
    PiSCat.of R (Associated R (Underlying R A)) ≅ A where
  hom := ⟨Associated.T R A⟩
  inv := ⟨Associated.Tinv R A⟩
  hom_inv_id := Superfunctor.ext Associated.T_comp_Tinv
  inv_hom_id := Superfunctor.ext Associated.Tinv_comp_T

variable (R) in
/-- **Lemma 5.1, `D₁ ∘ E₁ ≅ I`.** The natural isomorphism `E₁ ⋙ D₁ ≅ 𝟭`, with components
`T_A`. -/
def counitIso : PiSCat.E₁ ⋙ D₁ ≅ 𝟭 (PiSCat.{w, v, u} R) :=
  NatIso.ofComponents counitIsoApp fun F =>
    Superfunctor.ext (Associated.T_naturality (R := R) F.toFunctor)

variable (R) in
/-- **Brundan–Ellis, Theorem 1.9 (second bullet) / Lemma 5.1.** The functors
`D₁ : Π-Cat → Π-SCat` and `E₁ : Π-SCat → Π-Cat` are mutually inverse equivalences of
categories. -/
def equivalence : PiCat.{w, v, u} R ≌ PiSCat.{w, v, u} R :=
  CategoryTheory.Equivalence.mk D₁ PiSCat.E₁ (unitIso R) (counitIso R)

@[simp] theorem equivalence_functor : (equivalence R).functor = D₁.{w, v, u} := rfl

@[simp] theorem equivalence_inverse : (equivalence R).inverse = PiSCat.E₁.{w, v, u} := rfl

/-- **Theorem 1.9 (second bullet).** The functor (2) of (1.5), `E₁ : Π-SCat → Π-Cat`, is an
equivalence of categories. -/
instance : PiSCat.E₁.{w, v, u} (R := R).IsEquivalence :=
  (equivalence R).isEquivalence_inverse

/-- The functor `D₁ : Π-Cat → Π-SCat` is an equivalence of categories. -/
instance : D₁.{w, v, u} (R := R).IsEquivalence :=
  (equivalence R).isEquivalence_functor

end PiCat

end StringDiagrams

end
