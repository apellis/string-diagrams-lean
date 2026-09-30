import StringDiagrams.Super.MonoidalEquivalence

/-!
# The quasi-inverse of a monoidal superequivalence

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, the
paragraph after Definition 1.4: monoidal supercategories `A`, `B` are monoidally
superequivalent if there are monoidal superfunctors `F : A → B`, `G : B → A` with `G ∘ F`,
`F ∘ G` isomorphic to the identities via monoidal natural transformations; *equivalently*,
there is a monoidal superfunctor `F : A → B` which is a superequivalence of the underlying
supercategories. One direction is `MonoidalSuperequivalence.superequivalence`; this file proves
the other.

Let `F` be a monoidal superfunctor with coherence maps `c_F`, `i_F`, and let
`(G, η, ε)` be a superequivalence structure on `F` (`Supercategory.Superequivalence`). Then `F`
is fully faithful (`Superequivalence.fullyFaithful`), and:

* `G` is a monoidal superfunctor (`Superequivalence.inverseMonoidal`), with `c_G` and `i_G` the
  unique (even) morphisms such that `F(c_G) = ε⁻¹ ∘ (ε ⊗ ε) ∘ c_F⁻¹` and
  `F(i_G) = ε⁻¹ ∘ i_F⁻¹` (`Superequivalence.map_inverseMonoidal_μIso_hom`,
  `Superequivalence.map_inverseMonoidal_εIso_hom`);
* the counit `ε : F ∘ G ≅ 1` is a monoidal natural isomorphism
  (`Superequivalence.counitMonoidalNatTrans`);
* the unit, adjusted to the counit so that the triangle identity holds (the unique `η'` with
  `F(η'_X) = ε⁻¹_{F X}`, `Superequivalence.adjointUnitIso`; it equals `η` when `(η, ε)` already
  satisfies the triangle identity, `Superequivalence.adjointUnitIso_eq`), is a monoidal natural
  isomorphism `1 ≅ G ∘ F` (`Superequivalence.unitMonoidalNatTrans`).

Hence `MonoidalSuperequivalence.ofSuperequivalence : MonoidalSuperequivalence R A B`, and the
two formulations of the paper agree
(`MonoidalSuperequivalence.nonempty_iff_exists_superequivalence`).

As in the non-super case the unit `η` itself need not be monoidal: the coherence maps of `G`
are forced by the requirement that `ε` be monoidal, and `η` is then monoidal only if it
satisfies the triangle identity with `ε`. All coherence maps are even, so the proofs are the
classical ones; the only point where parity enters is the naturality of `c_G` with respect to
arbitrary (not necessarily homogeneous) morphisms, which uses the interchange law without sign
for an even and an arbitrary morphism (`MonoidalSupercategory.interchange_even_left`,
`MonoidalSupercategory.interchange_even_right`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe w v₁ u₁ v₂ u₂

variable {R : Type w} [CommRing R]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [Supercategory R D]

/-! ## Superequivalences are fully faithful; the adjusted unit -/

namespace Supercategory.Superequivalence

variable {F : C ⥤ D} (e : Superequivalence R F)

/-- The superfunctor of a superequivalence is fully faithful. -/
def fullyFaithful : F.FullyFaithful :=
  (CategoryTheory.Equivalence.mk F e.inverse e.unitIso e.counitIso).fullyFaithfulFunctor

/-- Naturality of the counit: `F (G g) = ε_Y⁻¹ ∘ g ∘ ε_X`. -/
theorem map_inverse_map {X Y : D} (g : X ⟶ Y) :
    F.map (e.inverse.map g) = e.counitIso.hom.app X ≫ g ≫ e.counitIso.inv.app Y := by
  have h := e.counitIso.hom.naturality g
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h
  rw [← reassoc_of% h]
  simp

/-- The unit `η_X : X ≅ G F X` adjusted to the counit `ε`: the unique morphism with
`F(η_X) = ε⁻¹_{F X}`, so that `(η, ε)` satisfies the triangle identity
`ε_{F X} ∘ F(η_X) = 1`. -/
@[simps!]
def adjointUnitIso : 𝟭 C ≅ F ⋙ e.inverse :=
  NatIso.ofComponents (fun X => e.fullyFaithful.preimageIso (e.counitIso.app (F.obj X)).symm)
    (fun f => e.fullyFaithful.map_injective (by simp [map_inverse_map]))

theorem map_adjointUnitIso_hom_app (X : C) :
    F.map ((adjointUnitIso e).hom.app X) = e.counitIso.inv.app (F.obj X) := by
  simp

/-- If the unit and counit of `e` already satisfy the triangle identity, the adjusted unit is
the unit of `e`. -/
theorem adjointUnitIso_eq
    (h : ∀ X, F.map (e.unitIso.hom.app X) ≫ e.counitIso.hom.app (F.obj X) = 𝟙 (F.obj X)) :
    e.adjointUnitIso = e.unitIso := by
  ext X
  apply e.fullyFaithful.map_injective
  rw [map_adjointUnitIso_hom_app, ← cancel_mono (e.counitIso.hom.app (F.obj X)), h X,
    Iso.inv_hom_id_app]
  rfl

variable [F.Additive] [F.Linear R] [IsSuperfunctor R F] in
theorem adjointUnitIso_hom_app_mem (X : C) :
    (adjointUnitIso e).hom.app X ∈ parity (R := R) X (e.inverse.obj (F.obj X)) 0 := by
  have := e.fullyFaithful.faithful
  refine mem_of_map_mem F ?_
  rw [map_adjointUnitIso_hom_app]
  exact inv_mem (e.counitIso.app (F.obj X)) (e.counitIso_mem _)

end Supercategory.Superequivalence

variable [MonoidalCategoryStruct D]

/-! ## Interchange with an even morphism -/

namespace MonoidalSupercategory

variable [MonoidalSupercategory R D]

variable (R) in
include R in
@[reassoc]
theorem whiskerLeft_comp_eq_id (Z : D) {X Y : D} {f : X ⟶ Y} {g : Y ⟶ X} (h : f ≫ g = 𝟙 X) :
    Z ◁ f ≫ Z ◁ g = 𝟙 (Z ⊗ X) := by
  rw [← whiskerLeft_comp (R := R), h, whiskerLeft_id (R := R)]

variable (R) in
include R in
@[reassoc]
theorem whiskerRight_comp_eq_id {X Y : D} {f : X ⟶ Y} {g : Y ⟶ X} (h : f ≫ g = 𝟙 X) (Z : D) :
    f ▷ Z ≫ g ▷ Z = 𝟙 (X ⊗ Z) := by
  rw [← comp_whiskerRight (R := R), h, id_whiskerRight (R := R)]

variable (R) in
include R in
/-- The interchange law without sign when the left morphism is even and the right one is
arbitrary. -/
@[reassoc]
theorem interchange_even_left {X X' Y Y' : D} {f : X ⟶ X'} (hf : f ∈ parity (R := R) X X' 0)
    (g : Y ⟶ Y') : f ▷ Y ≫ X' ◁ g = X ◁ g ≫ f ▷ Y' := by
  refine Supercategory.induction_on (R := R) g ?_ (fun q g hg => ?_) (fun g h hg hh => ?_)
  · rw [whiskerLeft_zero R, whiskerLeft_zero R, Limits.comp_zero, Limits.zero_comp]
  · exact interchange_of_even_left hf hg
  · rw [whiskerLeft_add (R := R), whiskerLeft_add (R := R), Preadditive.comp_add,
      Preadditive.add_comp, hg, hh]

variable (R) in
include R in
/-- The interchange law without sign when the right morphism is even and the left one is
arbitrary. -/
@[reassoc]
theorem interchange_even_right {X X' Y Y' : D} (f : X ⟶ X') {g : Y ⟶ Y'}
    (hg : g ∈ parity (R := R) Y Y' 0) : f ▷ Y ≫ X' ◁ g = X ◁ g ≫ f ▷ Y' := by
  refine Supercategory.induction_on (R := R) f ?_ (fun q f hf => ?_) (fun f h hf hh => ?_)
  · rw [zero_whiskerRight R, zero_whiskerRight R, Limits.comp_zero, Limits.zero_comp]
  · exact interchange_of_even_right hf hg
  · rw [add_whiskerRight (R := R), add_whiskerRight (R := R), Preadditive.comp_add,
      Preadditive.add_comp, hf, hh]

end MonoidalSupercategory

namespace Supercategory.Superequivalence

section Counit

variable [MonoidalSupercategory R D] {F : C ⥤ D} (e : Superequivalence R F)

/-- The counit is even, so it satisfies the interchange law without sign. -/
@[reassoc]
theorem counit_interchange (A : D) {Y Y' : D} (g : Y ⟶ Y') :
    F.obj (e.inverse.obj A) ◁ g ≫ (e.counitIso.hom.app A : F.obj (e.inverse.obj A) ⟶ A) ▷ Y' =
      (e.counitIso.hom.app A : F.obj (e.inverse.obj A) ⟶ A) ▷ Y ≫ A ◁ g :=
  (MonoidalSupercategory.interchange_even_left R (e.counitIso_mem A) g).symm

@[reassoc]
theorem counit_interchange_hom (A B : D) :
    F.obj (e.inverse.obj A) ◁ (e.counitIso.hom.app B : F.obj (e.inverse.obj B) ⟶ B) ≫
      (e.counitIso.hom.app A : F.obj (e.inverse.obj A) ⟶ A) ▷ B =
      (e.counitIso.hom.app A : F.obj (e.inverse.obj A) ⟶ A) ▷ F.obj (e.inverse.obj B) ≫
        A ◁ (e.counitIso.hom.app B : F.obj (e.inverse.obj B) ⟶ B) :=
  (MonoidalSupercategory.interchange_even_left R (e.counitIso_mem A) _).symm

@[reassoc]
theorem counit_interchange_inv (A B : D) :
    F.obj (e.inverse.obj A) ◁ (e.counitIso.inv.app B : B ⟶ F.obj (e.inverse.obj B)) ≫
      (e.counitIso.hom.app A : F.obj (e.inverse.obj A) ⟶ A) ▷ F.obj (e.inverse.obj B) =
      (e.counitIso.hom.app A : F.obj (e.inverse.obj A) ⟶ A) ▷ B ≫
        A ◁ (e.counitIso.inv.app B : B ⟶ F.obj (e.inverse.obj B)) :=
  (MonoidalSupercategory.interchange_even_left R (e.counitIso_mem A) _).symm

@[reassoc]
theorem whiskerLeft_counit_inv_hom (A B : D) :
    A ◁ (e.counitIso.inv.app B : B ⟶ F.obj (e.inverse.obj B)) ≫
      A ◁ (e.counitIso.hom.app B : F.obj (e.inverse.obj B) ⟶ B) = 𝟙 (A ⊗ B) :=
  MonoidalSupercategory.whiskerLeft_comp_eq_id R A (e.counitIso.inv_hom_id_app B)

@[reassoc]
theorem counit_inv_hom_whiskerRight (A B : D) :
    (e.counitIso.inv.app A : A ⟶ F.obj (e.inverse.obj A)) ▷ B ≫
      (e.counitIso.hom.app A : F.obj (e.inverse.obj A) ⟶ A) ▷ B = 𝟙 (A ⊗ B) :=
  MonoidalSupercategory.whiskerRight_comp_eq_id R (e.counitIso.inv_hom_id_app A) B

end Counit

end Supercategory.Superequivalence

variable [MonoidalCategoryStruct C]

/-! ## Monoidal superfunctors applied to whiskerings and coherence maps -/

namespace MonoidalSuperfunctor

variable {F : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F]
  (cF : MonoidalSuperfunctor R F)

/-- `F(f ⊗ 1) = c_F ∘ (F f ⊗ 1) ∘ c_F⁻¹`. -/
theorem map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    F.map (f ▷ Z) = (cF.μIso X Z).inv ≫ F.map f ▷ F.obj Z ≫ (cF.μIso Y Z).hom := by
  rw [cF.μ_natural_left, Iso.inv_hom_id_assoc]

/-- `F(1 ⊗ f) = c_F ∘ (1 ⊗ F f) ∘ c_F⁻¹`. -/
theorem map_whiskerLeft (Z : C) {X Y : C} (f : X ⟶ Y) :
    F.map (Z ◁ f) = (cF.μIso Z X).inv ≫ F.obj Z ◁ F.map f ≫ (cF.μIso Z Y).hom := by
  rw [cF.μ_natural_right, Iso.inv_hom_id_assoc]

variable [MonoidalSupercategory R D]

/-- The image of the associator under a monoidal superfunctor. -/
theorem map_associator_hom (X Y Z : C) :
    F.map (α_ X Y Z).hom = (cF.μIso (X ⊗ Y) Z).inv ≫ (cF.μIso X Y).inv ▷ F.obj Z ≫
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (cF.μIso Y Z).hom ≫
        (cF.μIso X (Y ⊗ Z)).hom := by
  rw [← cF.associativity, ← Category.assoc ((cF.μIso X Y).inv ▷ F.obj Z),
    ← MonoidalSupercategory.comp_whiskerRight (R := R), Iso.inv_hom_id,
    MonoidalSupercategory.id_whiskerRight (R := R), Category.id_comp, Iso.inv_hom_id_assoc]

/-- The image of the left unitor under a monoidal superfunctor. -/
theorem map_leftUnitor_hom (X : C) :
    F.map (λ_ X).hom =
      (cF.μIso (𝟙_ C) X).inv ≫ cF.εIso.inv ▷ F.obj X ≫ (λ_ (F.obj X)).hom := by
  rw [cF.left_unitality, ← Category.assoc (cF.εIso.inv ▷ F.obj X),
    ← MonoidalSupercategory.comp_whiskerRight (R := R), Iso.inv_hom_id,
    MonoidalSupercategory.id_whiskerRight (R := R), Category.id_comp, Iso.inv_hom_id_assoc]

/-- The image of the right unitor under a monoidal superfunctor. -/
theorem map_rightUnitor_hom (X : C) :
    F.map (ρ_ X).hom =
      (cF.μIso X (𝟙_ C)).inv ≫ F.obj X ◁ cF.εIso.inv ≫ (ρ_ (F.obj X)).hom := by
  rw [cF.right_unitality, ← Category.assoc (F.obj X ◁ cF.εIso.inv),
    ← MonoidalSupercategory.whiskerLeft_comp (R := R), Iso.inv_hom_id,
    MonoidalSupercategory.whiskerLeft_id (R := R), Category.id_comp, Iso.inv_hom_id_assoc]

end MonoidalSuperfunctor

/-! ## The monoidal structure on the quasi-inverse -/

namespace Supercategory.Superequivalence

variable {F : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F]
  (cF : MonoidalSuperfunctor R F) (e : Superequivalence R F)

/-- The image under `F` of the coherence map `i_G : 1 ≅ G 1` of the quasi-inverse:
`F 1 ≅ 1 ≅ F G 1`. -/
@[simps!]
def inverseε : F.obj (𝟙_ C) ≅ F.obj (e.inverse.obj (𝟙_ D)) :=
  cF.εIso.symm ≪≫ (e.counitIso.app (𝟙_ D)).symm

theorem inverseε_hom_mem : (inverseε cF e).hom ∈ parity (R := R) _ _ 0 := by
  have h := comp_mem (inv_mem _ cF.ε_mem) (inv_mem (e.counitIso.app (𝟙_ D)) (e.counitIso_mem _))
  simpa using h

variable [MonoidalSupercategory R D]

/-- The image under `F` of the coherence map `c_G` of the quasi-inverse `G`:
`F(G X ⊗ G Y) ≅ F G X ⊗ F G Y ≅ X ⊗ Y ≅ F G (X ⊗ Y)`, built from `c_F⁻¹` and the counit. -/
@[simps]
def inverseμ (X Y : D) :
    F.obj (e.inverse.obj X ⊗ e.inverse.obj Y) ≅ F.obj (e.inverse.obj (X ⊗ Y)) where
  hom := (cF.μIso _ _).inv ≫ e.counitIso.hom.app X ▷ F.obj (e.inverse.obj Y) ≫
    X ◁ e.counitIso.hom.app Y ≫ e.counitIso.inv.app (X ⊗ Y)
  inv := e.counitIso.hom.app (X ⊗ Y) ≫ X ◁ e.counitIso.inv.app Y ≫
    e.counitIso.inv.app X ▷ F.obj (e.inverse.obj Y) ≫ (cF.μIso _ _).hom
  hom_inv_id := by
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      MonoidalSupercategory.whiskerLeft_comp_eq_id_assoc R _ (e.counitIso.hom_inv_id_app Y),
      MonoidalSupercategory.whiskerRight_comp_eq_id_assoc R (e.counitIso.hom_inv_id_app X),
      Iso.inv_hom_id]
  inv_hom_id := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      MonoidalSupercategory.whiskerRight_comp_eq_id_assoc R (e.counitIso.inv_hom_id_app X),
      MonoidalSupercategory.whiskerLeft_comp_eq_id_assoc R _ (e.counitIso.inv_hom_id_app Y),
      Iso.hom_inv_id_app, Functor.comp_obj]

theorem inverseμ_hom_mem (X Y : D) :
    (inverseμ cF e X Y).hom ∈ parity (R := R) _ _ 0 := by
  have h := comp_mem (inv_mem _ (cF.μ_mem _ _)) (comp_mem
    (MonoidalSupercategory.whiskerRight_mem (F.obj (e.inverse.obj Y)) (e.counitIso_mem X))
    (comp_mem (MonoidalSupercategory.whiskerLeft_mem X (e.counitIso_mem Y))
      (inv_mem (e.counitIso.app (X ⊗ Y)) (e.counitIso_mem (X ⊗ Y)))))
  simpa using h

/-- **Brundan–Ellis, after Definition 1.4.** The monoidal structure on the quasi-inverse `G` of
a monoidal superfunctor `F` which is a superequivalence: `c_G` and `i_G` are the unique
morphisms with `F(c_G) = ε⁻¹ ∘ (ε ⊗ ε) ∘ c_F⁻¹` and `F(i_G) = ε⁻¹ ∘ i_F⁻¹`, where `ε` is the
counit. -/
def inverseMonoidal : MonoidalSuperfunctor R e.inverse where
  μIso X Y := e.fullyFaithful.preimageIso (inverseμ cF e X Y)
  εIso := e.fullyFaithful.preimageIso (inverseε cF e)
  μ_mem X Y := by
    have := e.fullyFaithful.faithful
    exact mem_of_map_mem F (by simpa using inverseμ_hom_mem cF e X Y)
  ε_mem := by
    have := e.fullyFaithful.faithful
    exact mem_of_map_mem F (by simpa using inverseε_hom_mem cF e)
  μ_natural_left f X' := by
    apply e.fullyFaithful.map_injective
    simp only [Functor.map_comp, cF.map_whiskerRight, map_inverse_map,
      Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage, inverseμ_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc,
      MonoidalSupercategory.comp_whiskerRight (R := R),
      MonoidalSupercategory.whiskerRight_comp_eq_id_assoc R (e.counitIso.inv_hom_id_app _),
      Functor.comp_obj, Functor.id_obj]
    rw [MonoidalSupercategory.interchange_even_right_assoc R f (e.counitIso_mem X')]
  μ_natural_right X' f := by
    apply e.fullyFaithful.map_injective
    simp only [Functor.map_comp, cF.map_whiskerLeft, map_inverse_map,
      Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage, inverseμ_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc,
      MonoidalSupercategory.whiskerLeft_comp (R := R),
      Functor.comp_obj, Functor.id_obj]
    rw [counit_interchange_inv_assoc, whiskerLeft_counit_inv_hom_assoc, counit_interchange_assoc,
      counit_interchange_hom_assoc]
  associativity X Y Z := by
    apply e.fullyFaithful.map_injective
    simp only [Functor.map_comp, cF.map_whiskerLeft, cF.map_whiskerRight, map_inverse_map,
      cF.map_associator_hom,
      Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage, inverseμ_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc,
      MonoidalSupercategory.comp_whiskerRight (R := R),
      MonoidalSupercategory.whiskerLeft_comp (R := R),
      MonoidalSupercategory.whiskerRight_comp_eq_id_assoc R (e.counitIso.inv_hom_id_app _),
      MonoidalSupercategory.whiskerLeft_comp_eq_id_assoc R _ (Iso.hom_inv_id _),
      Functor.comp_obj, Functor.id_obj]
    have h := MonoidalSupercategory.associator_naturality (R := R) (e.counitIso.hom.app X)
      (e.counitIso.hom.app Y) (e.counitIso.hom.app Z)
    simp only [MonoidalSupercategory.tensorHom_def (R := R),
      MonoidalSupercategory.comp_whiskerRight (R := R),
      MonoidalSupercategory.whiskerLeft_comp (R := R), Category.assoc, Functor.comp_obj,
      Functor.id_obj] at h
    rw [counit_interchange_inv_assoc, whiskerLeft_counit_inv_hom_assoc, counit_interchange_assoc,
      counit_interchange_assoc, reassoc_of% h]
  left_unitality X := by
    apply e.fullyFaithful.map_injective
    simp only [Functor.map_comp, cF.map_whiskerRight, map_inverse_map,
      cF.map_leftUnitor_hom, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage, inverseμ_hom, inverseε_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc,
      MonoidalSupercategory.comp_whiskerRight (R := R),
      MonoidalSupercategory.whiskerRight_comp_eq_id_assoc R (e.counitIso.inv_hom_id_app _),
      Functor.comp_obj, Functor.id_obj]
    have h := MonoidalSupercategory.leftUnitor_naturality (R := R) (e.counitIso.hom.app X)
    simp only [Functor.comp_obj, Functor.id_obj] at h
    rw [reassoc_of% h]
    simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  right_unitality X := by
    apply e.fullyFaithful.map_injective
    simp only [Functor.map_comp, cF.map_whiskerLeft, map_inverse_map,
      cF.map_rightUnitor_hom, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage, inverseμ_hom, inverseε_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc,
      MonoidalSupercategory.whiskerLeft_comp (R := R),
      Functor.comp_obj, Functor.id_obj]
    have h := MonoidalSupercategory.rightUnitor_naturality (R := R) (e.counitIso.hom.app X)
    simp only [Functor.comp_obj, Functor.id_obj] at h
    rw [counit_interchange_inv_assoc, whiskerLeft_counit_inv_hom_assoc, reassoc_of% h]
    simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]

/-- `F(c_G) = ε⁻¹ ∘ (ε ⊗ ε) ∘ c_F⁻¹`. -/
theorem map_inverseMonoidal_μIso_hom (X Y : D) :
    F.map ((inverseMonoidal cF e).μIso X Y).hom = (inverseμ cF e X Y).hom :=
  e.fullyFaithful.map_preimage _

/-- `F(i_G) = ε⁻¹ ∘ i_F⁻¹`. -/
theorem map_inverseMonoidal_εIso_hom :
    F.map (inverseMonoidal cF e).εIso.hom = (inverseε cF e).hom :=
  e.fullyFaithful.map_preimage _

variable [MonoidalSupercategory R C]

/-- The unit `1 ⇒ G ∘ F` is a monoidal natural transformation. -/
def unitMonoidalNatTrans :
    MonoidalNatTrans R (MonoidalSuperfunctor.id (R := R) (C := C))
      (cF.comp (inverseMonoidal cF e)) where
  toNatTrans := (adjointUnitIso e).hom
  app_mem := adjointUnitIso_hom_app_mem e
  tensor X Y := by
    apply e.fullyFaithful.map_injective
    simp only [MonoidalSuperfunctor.id, MonoidalSuperfunctor.comp_μIso, Iso.refl_hom,
      Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.id_comp,
      MonoidalSupercategory.tensorHom_def (R := R), cF.map_whiskerLeft, cF.map_whiskerRight,
      map_adjointUnitIso_hom_app, map_inverseMonoidal_μIso_hom, inverseμ_hom, map_inverse_map,
      Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc, Functor.id_obj,
      Functor.comp_obj]
    rw [counit_interchange_inv_assoc, whiskerLeft_counit_inv_hom_assoc,
      counit_inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc]
  unit := by
    apply e.fullyFaithful.map_injective
    simp [MonoidalSuperfunctor.id, map_inverseMonoidal_εIso_hom, map_inverse_map]

/-- The counit `F ∘ G ⇒ 1` is a monoidal natural transformation. -/
def counitMonoidalNatTrans :
    MonoidalNatTrans R ((inverseMonoidal cF e).comp cF)
      (MonoidalSuperfunctor.id (R := R) (C := D)) where
  toNatTrans := e.counitIso.hom
  app_mem := e.counitIso_mem
  tensor X Y := by
    simp [MonoidalSuperfunctor.id, map_inverseMonoidal_μIso_hom,
      MonoidalSupercategory.tensorHom_def (R := R)]
  unit := by
    simp [MonoidalSuperfunctor.id, map_inverseMonoidal_εIso_hom]

end Supercategory.Superequivalence

/-! ## Monoidal superequivalences from superequivalences -/

namespace MonoidalSuperequivalence

variable [MonoidalSupercategory R C] [MonoidalSupercategory R D]

section

variable {F : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F]

/-- **Brundan–Ellis, after Definition 1.4.** A monoidal superfunctor `F` which is a
superequivalence of the underlying supercategories is a monoidal superequivalence: its
quasi-inverse `G` is a monoidal superfunctor (`Superequivalence.inverseMonoidal`), and the
counit `F ∘ G ≅ 1` and the unit `1 ≅ G ∘ F` (adjusted to satisfy the triangle identity,
`Superequivalence.adjointUnitIso`) are monoidal natural isomorphisms. -/
def ofSuperequivalence (cF : MonoidalSuperfunctor R F) (e : Superequivalence R F) :
    MonoidalSuperequivalence R C D where
  functor := F
  functorMonoidal := cF
  inverse := e.inverse
  inverseMonoidal := e.inverseMonoidal cF
  unitIso := MonoidalNatIso.ofNatIso (e.unitMonoidalNatTrans cF) e.adjointUnitIso rfl
  counitIso := MonoidalNatIso.ofNatIso (e.counitMonoidalNatTrans cF) e.counitIso rfl

variable (cF : MonoidalSuperfunctor R F) (e : Superequivalence R F)

@[simp] theorem ofSuperequivalence_functor : (ofSuperequivalence cF e).functor = F := rfl

@[simp] theorem ofSuperequivalence_inverse : (ofSuperequivalence cF e).inverse = e.inverse := rfl

theorem ofSuperequivalence_functorMonoidal :
    (ofSuperequivalence cF e).functorMonoidal = cF := rfl

theorem ofSuperequivalence_inverseMonoidal :
    (ofSuperequivalence cF e).inverseMonoidal = e.inverseMonoidal cF := rfl

theorem ofSuperequivalence_unitIso_toNatIso :
    (ofSuperequivalence cF e).unitIso.toNatIso = e.adjointUnitIso := rfl

theorem ofSuperequivalence_counitIso_toNatIso :
    (ofSuperequivalence cF e).counitIso.toNatIso = e.counitIso := rfl

end

/-- **Brundan–Ellis, after Definition 1.4.** Monoidal supercategories are monoidally
superequivalent if and only if there is a monoidal superfunctor between them which is a
superequivalence of the underlying supercategories. -/
theorem nonempty_iff_exists_superequivalence :
    Nonempty (MonoidalSuperequivalence R C D) ↔
      ∃ (F : C ⥤ D) (_ : F.Additive) (_ : F.Linear R) (_ : IsSuperfunctor R F),
        Nonempty (MonoidalSuperfunctor R F) ∧ Nonempty (Superequivalence R F) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.functor, inferInstance, inferInstance, inferInstance, ⟨e.functorMonoidal⟩,
      ⟨e.superequivalence⟩⟩
  · rintro ⟨F, _, _, _, ⟨cF⟩, ⟨e⟩⟩
    exact ⟨ofSuperequivalence cF e⟩

end MonoidalSuperequivalence

end StringDiagrams

end
