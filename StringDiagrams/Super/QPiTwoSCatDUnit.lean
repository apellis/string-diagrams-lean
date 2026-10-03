import StringDiagrams.Super.QPiTwoSCatD

/-!
# The §6 analogue of Lemma 5.4 as a natural isomorphism `𝟭 ≅ 𝔻 ⋙ 𝔼`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6, after
Definition 6.14 (the analogue of Theorem 5.5, left to the reader), for the `(Q, Π)`-2-functors
of `StringDiagrams.Super.QPiTwoFunctor`.

`𝔼(𝔻 𝔄)` is the `(Q, Π)`-2-category `GUnderlying2 R (QAssociated2 R 𝔄)`, a different type from
`𝔄`, so `𝔼 ∘ 𝔻 = 𝕀` is an isomorphism in `(Q, Π)-2-Cat`, natural in `(Q, Π)`-2-functors:

* the `β`, `ξ` and `γ` of `(𝔄̂)̲` are those of `𝔄` (`QAssociated2.β_hom_unit`,
  `QAssociated2.ξ_hom_unit`, `QAssociated2.γ_hom_unit`, from `Orbit2.β_hom_eq`,
  `Orbit2.ξ_hom_eq`, `Orbit2.γ_hom_eq` and `Associated2.β_hom_eq`, `Associated2.ξ_hom_eq`), so
  the identification `QAssociated2.unit` is a (strict) `(Q, Π)`-2-functor with `j = 1`, `k = 1`
  (`QAssociated2.unitQPiTwoFunctor`);
* it has the strict inverse `QAssociated2.counit` (the inverse `unitInv₂` of `x ↦ (x, 0)` on
  2-morphisms, `QAssociated2.counitQPiTwoFunctor`; as bundled `(Q, Π)`-2-functors
  `QAssociated2.unitBundled_comp_counitBundled`, `QAssociated2.counitBundled_comp_unitBundled`),
  giving `QPiTwoCat.unitIso`;
* it is natural: `𝔼(ℝ̂) ∘ unit = unit ∘ ℝ` (`QAssociated2.comp_unit`,
  `QAssociated2.comp_unitQPiTwoFunctor_j`, `QAssociated2.comp_unitQPiTwoFunctor_k`, bundled as
  `QAssociated2.comp_unitBundled`, from `StringDiagrams.Super.QAssociatedTwoMap`), giving
  `QPiTwoCat.unitNatIso : 𝟭 ≅ 𝔻 ⋙ 𝔼`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

/-! ## The §6 analogue of Lemma 5.4: `unit` as a `(Q, Π)`-2-functor, and its inverse -/

namespace QAssociated2

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [QPiTwoCategory R B]

set_option backward.isDefEq.respectTransparency false in
/-- The `β` of the underlying `(Q, Π)`-2-category of `𝔄̂` is `β` of `𝔄`. -/
theorem β_hom_unit {a b : B} (f : a ⟶ b) :
    (PiTwoCategory.β (R := R) ((unit R B).map f)).hom =
      (unit R B).map₂ (PiTwoCategory.β (R := R) f).hom := by
  apply Subtype.ext
  apply Subtype.ext
  change (PiTwoSupercategory.β (R := R) (hom1 (R := R) f)).hom = hom2 (PiTwoCategory.β (R := R) f).hom
  rw [Orbit2.β_hom_eq, Associated2.β_hom_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The `ξ` of the underlying `(Q, Π)`-2-category of `𝔄̂` is `ξ` of `𝔄`. -/
theorem ξ_hom_unit (a : B) :
    (PiTwoCategory.ξ (R := R) ((unit R B).obj a)).hom =
      (unit R B).map₂ (PiTwoCategory.ξ (R := R) a).hom := by
  apply Subtype.ext
  apply Subtype.ext
  change (PiTwoSupercategory.ξ (R := R) (⟨⟨a⟩⟩ : QAssociated2 R B)).hom =
    hom2 (PiTwoCategory.ξ (R := R) a).hom
  rw [Orbit2.ξ_hom_eq, Associated2.ξ_hom_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The `γ` of the underlying `(Q, Π)`-2-category of `𝔄̂` is `γ` of `𝔄`. -/
theorem γ_hom_unit {a b : B} (f : a ⟶ b) :
    (QPiTwoCategory.γ (R := R) ((unit R B).map f)).hom =
      (unit R B).map₂ (QPiTwoCategory.γ (R := R) f).hom := by
  apply Subtype.ext
  apply Subtype.ext
  change (QPiTwoSupercategory.γ (R := R) (hom1 (R := R) f)).hom = hom2 (QPiTwoCategory.γ (R := R) f).hom
  rw [Orbit2.γ_hom_eq, Associated2.centralShift_γ_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem hom2_smul {a b : B} {f g : a ⟶ b} (r : R) (η : f ⟶ g) :
    hom2 (R := R) (r • η) = r • hom2 η := by
  rw [hom2, hom2, ← Functor.map_smul]
  congr 1
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
theorem unit_γ_comm {a b : B} (f : a ⟶ b) :
    (unit R B).map f ◁ (Iso.refl (QPiTwoCategory.q (R := R) ((unit R B).obj b))).hom ≫
        ((unit R B).mapComp f (QPiTwoCategory.q (R := R) b)).inv ≫
          (unit R B).map₂ (QPiTwoCategory.γ (R := R) f).hom =
      (QPiTwoCategory.γ (R := R) ((unit R B).map f)).hom ≫
        (Iso.refl (QPiTwoCategory.q (R := R) ((unit R B).obj a))).hom ▷ (unit R B).map f ≫
          ((unit R B).mapComp (QPiTwoCategory.q (R := R) a) f).inv := by
  simp only [Iso.refl_hom, unit_mapComp, Iso.refl_inv, Bicategory.whiskerLeft_id,
    Bicategory.id_whiskerRight, Category.id_comp]
  erw [Category.id_comp, Category.comp_id]
  exact (γ_hom_unit f).symm

set_option backward.isDefEq.respectTransparency false in
/-- **`𝔼 ∘ 𝔻 = 𝕀` on objects.** The identification `QAssociated2.unit : 𝔄 → (𝔄̂)̲` is a (strict)
`(Q, Π)`-2-functor with `j = 1` and `k = 1`. -/
def unitQPiTwoFunctor : QPiTwoFunctor R (unit R B) where
  map₂_add η θ := by
    apply Subtype.ext
    apply Subtype.ext
    change hom2 (R := R) (η + θ) = hom2 η + hom2 θ
    rw [hom2, hom2, hom2, ← Functor.map_add]
    congr 1
    ext <;> simp
  map₂_smul r η := Subtype.ext (Subtype.ext (hom2_smul r η))
  j a := Iso.refl _
  β_comm f := by
    simp only [Iso.refl_hom, unit_mapComp, Iso.refl_inv, Bicategory.whiskerLeft_id,
      Bicategory.id_whiskerRight, Category.id_comp]
    erw [Category.id_comp, Category.comp_id]
    exact (β_hom_unit f).symm
  ξ_comm a := by
    simp only [Iso.refl_hom, unit_mapComp, unit_mapId, Iso.refl_inv, Bicategory.whiskerLeft_id,
      Bicategory.id_whiskerRight, Category.id_comp]
    erw [Category.id_comp, Category.comp_id]
    exact (ξ_hom_unit a).symm
  k a := Iso.refl _
  γ_comm f := unit_γ_comm f

theorem unit_map₂_unitInv₂ {a b : B} {f g : a ⟶ b} (x : hom1U (R := R) f ⟶ hom1U g) :
    (unit R B).map₂ (unitInv₂ x) = x :=
  hom2U_unitInv₂ x

theorem unitInv₂_eq {a b : B} {f g : a ⟶ b} {x : hom1U (R := R) f ⟶ hom1U g} {η : f ⟶ g}
    (h : x = (unit R B).map₂ η) : unitInv₂ x = η :=
  (unit_map₂_bijective (R := R) f g).1 ((unit_map₂_unitInv₂ x).trans h)

set_option backward.isDefEq.respectTransparency false in
theorem unitInv₂_whiskerLeft {a b c : B} (f : a ⟶ b) {g h : b ⟶ c}
    (x : hom1U (R := R) g ⟶ hom1U h) : unitInv₂ (hom1U (R := R) f ◁ x) = f ◁ unitInv₂ x := by
  refine unitInv₂_eq ?_
  rw [Pseudofunctor.map₂_whisker_left, unit_map₂_unitInv₂]
  rw [unit_mapComp, unit_mapComp, Iso.refl_hom, Iso.refl_inv]
  erw [Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem unitInv₂_whiskerRight {a b c : B} {f g : a ⟶ b} (x : hom1U (R := R) f ⟶ hom1U g)
    (h : b ⟶ c) : unitInv₂ (x ▷ hom1U (R := R) h) = unitInv₂ x ▷ h := by
  refine unitInv₂_eq ?_
  rw [Pseudofunctor.map₂_whisker_right, unit_map₂_unitInv₂]
  rw [unit_mapComp, unit_mapComp, Iso.refl_hom, Iso.refl_inv]
  erw [Category.id_comp, Category.comp_id]
  rfl

theorem unitInv₂_comp {a b : B} {f g h : a ⟶ b} (x : hom1U (R := R) f ⟶ hom1U g)
    (y : hom1U (R := R) g ⟶ hom1U h) : unitInv₂ (x ≫ y) = unitInv₂ x ≫ unitInv₂ y :=
  unitInv₂_eq (by rw [PrelaxFunctor.map₂_comp, unit_map₂_unitInv₂, unit_map₂_unitInv₂]; rfl)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
variable (R B) in
/-- The inverse of the identification `QAssociated2.unit : 𝔄 → (𝔄̂)̲`: the identity on objects and
1-morphisms, and the inverse `unitInv₂` of `x ↦ (x, 0)` on 2-morphisms, with identity coherence
maps. -/
def counit : Pseudofunctor (GUnderlying2 R (QAssociated2 R B)) B where
  obj a := a.obj.as.obj.obj
  map f := f.obj.obj.obj.obj
  map₂ x := unitInv₂ x
  map₂_id f := unitInv₂_eq ((unit R B).map₂_id _).symm
  map₂_comp x y := unitInv₂_comp x y
  mapId a := Iso.refl _
  mapComp f g := Iso.refl _
  map₂_whisker_left f g h x := by
    change unitInv₂ (f ◁ x) = 𝟙 _ ≫ f.obj.obj.obj.obj ◁ unitInv₂ x ≫ 𝟙 _
    erw [Category.id_comp, Category.comp_id]
    exact unitInv₂_whiskerLeft _ x
  map₂_whisker_right x h := by
    change unitInv₂ (x ▷ h) = 𝟙 _ ≫ unitInv₂ x ▷ h.obj.obj.obj.obj ≫ 𝟙 _
    erw [Category.id_comp, Category.comp_id]
    exact unitInv₂_whiskerRight x _
  map₂_associator f g h := by
    change unitInv₂ (α_ f g h).hom = 𝟙 _ ≫ 𝟙 _ ▷ h.obj.obj.obj.obj ≫
      (α_ f.obj.obj.obj.obj g.obj.obj.obj.obj h.obj.obj.obj.obj).hom ≫
        f.obj.obj.obj.obj ◁ 𝟙 _ ≫ 𝟙 _
    rw [Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id, Category.id_comp,
      Category.id_comp, Category.comp_id, Category.comp_id]
    exact unitInv₂_eq rfl
  map₂_left_unitor f := by
    change unitInv₂ (λ_ f).hom = 𝟙 _ ≫ 𝟙 _ ▷ f.obj.obj.obj.obj ≫ (λ_ f.obj.obj.obj.obj).hom
    rw [Bicategory.id_whiskerRight, Category.id_comp, Category.id_comp]
    exact unitInv₂_eq rfl
  map₂_right_unitor f := by
    change unitInv₂ (ρ_ f).hom = 𝟙 _ ≫ f.obj.obj.obj.obj ◁ 𝟙 _ ≫ (ρ_ f.obj.obj.obj.obj).hom
    rw [Bicategory.whiskerLeft_id, Category.id_comp, Category.id_comp]
    exact unitInv₂_eq rfl

@[simp] theorem counit_map₂ {a b : GUnderlying2 R (QAssociated2 R B)} {f g : a ⟶ b} (x : f ⟶ g) :
    (counit R B).map₂ x = unitInv₂ x := rfl

@[simp] theorem counit_mapComp {a b c : GUnderlying2 R (QAssociated2 R B)} (f : a ⟶ b)
    (g : b ⟶ c) : (counit R B).mapComp f g = Iso.refl _ := rfl

@[simp] theorem counit_mapId (a : GUnderlying2 R (QAssociated2 R B)) :
    (counit R B).mapId a = Iso.refl _ := rfl

theorem unitInv₂_add {a b : B} {f g : a ⟶ b} (x y : hom1U (R := R) f ⟶ hom1U g) :
    unitInv₂ (x + y) = unitInv₂ x + unitInv₂ y :=
  unitInv₂_eq (by
    rw [unitQPiTwoFunctor.map₂_add, unit_map₂_unitInv₂, unit_map₂_unitInv₂]
    rfl)

theorem unitInv₂_smul {a b : B} {f g : a ⟶ b} (r : R) (x : hom1U (R := R) f ⟶ hom1U g) :
    unitInv₂ (r • x) = r • unitInv₂ x :=
  unitInv₂_eq (by
    rw [unitQPiTwoFunctor.map₂_smul, unit_map₂_unitInv₂]
    rfl)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse of `QAssociated2.unit` is a (strict) `(Q, Π)`-2-functor with `j = 1`, `k = 1`. -/
def counitQPiTwoFunctor : QPiTwoFunctor R (counit R B) where
  map₂_add x y := unitInv₂_add x y
  map₂_smul r x := unitInv₂_smul r x
  j a := Iso.refl _
  β_comm f := by
    simp only [Iso.refl_hom, counit_mapComp, Iso.refl_inv, Bicategory.whiskerLeft_id,
      Bicategory.id_whiskerRight, Category.id_comp]
    erw [Category.comp_id, Category.id_comp]
    exact unitInv₂_eq (β_hom_unit f.obj.obj.obj.obj)
  ξ_comm a := by
    simp only [Iso.refl_hom, counit_mapComp, counit_mapId, Iso.refl_inv,
      Bicategory.whiskerLeft_id, Bicategory.id_whiskerRight, Category.id_comp]
    erw [Category.comp_id, Category.id_comp]
    exact unitInv₂_eq (ξ_hom_unit a.obj.as.obj.obj)
  k a := Iso.refl _
  γ_comm f := by
    simp only [Iso.refl_hom, counit_mapComp, Iso.refl_inv, Bicategory.whiskerLeft_id,
      Bicategory.id_whiskerRight, Category.id_comp]
    erw [Category.comp_id, Category.id_comp]
    exact unitInv₂_eq (γ_hom_unit f.obj.obj.obj.obj)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- `counit ∘ unit = 𝕀`. -/
theorem unit_comp_counit : (unit R B).comp (counit R B) = Pseudofunctor.id B := by
  refine pseudofunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b f g η
    exact unitInv₂_hom2U η
  · funext a b c f g
    apply Iso.ext
    change (counit R B).map₂ (𝟙 (hom1U (R := R) f ≫ hom1U g)) ≫ 𝟙 (f ≫ g) = 𝟙 (f ≫ g)
    erw [PrelaxFunctor.map₂_id, Category.comp_id]
    rfl
  · funext a
    apply Iso.ext
    change (counit R B).map₂ (𝟙 (𝟙 ((unit R B).obj a))) ≫ 𝟙 (𝟙 a) = 𝟙 (𝟙 a)
    erw [PrelaxFunctor.map₂_id, Category.comp_id]
    rfl

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- `unit ∘ counit = 𝕀`. -/
theorem counit_comp_unit :
    (counit R B).comp (unit R B) = Pseudofunctor.id (GUnderlying2 R (QAssociated2 R B)) := by
  refine pseudofunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b f g x
    exact unit_map₂_unitInv₂ x
  · funext a b c f g
    apply Iso.ext
    change (unit R B).map₂ (𝟙 (f.obj.obj.obj.obj ≫ g.obj.obj.obj.obj)) ≫ 𝟙 (f ≫ g) = 𝟙 (f ≫ g)
    erw [PrelaxFunctor.map₂_id, Category.comp_id]
    rfl
  · funext a
    apply Iso.ext
    change (unit R B).map₂ (𝟙 (𝟙 a.obj.as.obj.obj)) ≫ 𝟙 (𝟙 a) = 𝟙 (𝟙 a)
    erw [PrelaxFunctor.map₂_id, Category.comp_id]
    rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem unitQPiTwoFunctor_comp_counitQPiTwoFunctor_j (a : B) :
    ((unitQPiTwoFunctor.comp (counitQPiTwoFunctor (R := R) (B := B))).j a).hom = 𝟙 _ := by
  change 𝟙 _ ≫ (counit R B).map₂ (𝟙 (PiTwoCategory.pi (R := R) ((unit R B).obj a))) = 𝟙 _
  erw [PrelaxFunctor.map₂_id, Category.comp_id]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem unitQPiTwoFunctor_comp_counitQPiTwoFunctor_k (a : B) :
    ((unitQPiTwoFunctor.comp (counitQPiTwoFunctor (R := R) (B := B))).k a).hom = 𝟙 _ := by
  change 𝟙 _ ≫ (counit R B).map₂ (𝟙 (QPiTwoCategory.q (R := R) ((unit R B).obj a))) = 𝟙 _
  erw [PrelaxFunctor.map₂_id, Category.comp_id]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem counitQPiTwoFunctor_comp_unitQPiTwoFunctor_j (a : GUnderlying2 R (QAssociated2 R B)) :
    ((counitQPiTwoFunctor.comp (unitQPiTwoFunctor (R := R) (B := B))).j a).hom = 𝟙 _ := by
  change 𝟙 _ ≫ (unit R B).map₂ (𝟙 (PiTwoCategory.pi (R := R) ((counit R B).obj a))) = 𝟙 _
  erw [PrelaxFunctor.map₂_id, Category.comp_id]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem counitQPiTwoFunctor_comp_unitQPiTwoFunctor_k (a : GUnderlying2 R (QAssociated2 R B)) :
    ((counitQPiTwoFunctor.comp (unitQPiTwoFunctor (R := R) (B := B))).k a).hom = 𝟙 _ := by
  change 𝟙 _ ≫ (unit R B).map₂ (𝟙 (QPiTwoCategory.q (R := R) ((counit R B).obj a))) = 𝟙 _
  erw [PrelaxFunctor.map₂_id, Category.comp_id]

variable (R B) in
/-- `QAssociated2.unit` as a bundled `(Q, Π)`-2-functor. -/
abbrev unitBundled : BundledQPiTwoFunctor R B (GUnderlying2 R (QAssociated2 R B)) :=
  ⟨unit R B, unitQPiTwoFunctor⟩

variable (R B) in
/-- `QAssociated2.counit` as a bundled `(Q, Π)`-2-functor. -/
abbrev counitBundled : BundledQPiTwoFunctor R (GUnderlying2 R (QAssociated2 R B)) B :=
  ⟨counit R B, counitQPiTwoFunctor⟩

set_option backward.isDefEq.respectTransparency false in
/-- `counit ∘ unit = 𝕀` as bundled `(Q, Π)`-2-functors. -/
theorem unitBundled_comp_counitBundled :
    (unitBundled R B).comp (counitBundled R B) = BundledQPiTwoFunctor.id R B :=
  BundledQPiTwoFunctor.ext' unit_comp_counit
    (fun a => heq_of_eq (unitQPiTwoFunctor_comp_counitQPiTwoFunctor_j a))
    (fun a => heq_of_eq (unitQPiTwoFunctor_comp_counitQPiTwoFunctor_k a))

set_option backward.isDefEq.respectTransparency false in
/-- `unit ∘ counit = 𝕀` as bundled `(Q, Π)`-2-functors. -/
theorem counitBundled_comp_unitBundled :
    (counitBundled R B).comp (unitBundled R B) =
      BundledQPiTwoFunctor.id R (GUnderlying2 R (QAssociated2 R B)) :=
  BundledQPiTwoFunctor.ext' counit_comp_unit
    (fun a => heq_of_eq (counitQPiTwoFunctor_comp_unitQPiTwoFunctor_j a))
    (fun a => heq_of_eq (counitQPiTwoFunctor_comp_unitQPiTwoFunctor_k a))

variable {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [QPiTwoCategory R C]
  {F : Pseudofunctor B C} (hF : QPiTwoFunctor R F)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **`𝔼 ∘ 𝔻 = 𝕀` on 1-morphisms**: `𝔼(ℝ̂) ∘ unit = unit ∘ ℝ` as pseudofunctors. -/
theorem comp_unit :
    F.comp (unit R C) = (unit R B).comp (hF.mapQ.toDegreeZero2 hF.mapQ_isGraded).toPseudofunctor := by
  refine pseudofunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b f g η
    exact (hF.toQPiTwoFunctor_mapQ_map₂ η).symm
  · funext a b c f g
    apply Iso.ext
    change (unit R C).map₂ (F.mapComp f g).hom ≫ 𝟙 _ =
      (hF.mapQ.toDegreeZero2 hF.mapQ_isGraded).toPseudofunctor.map₂ (𝟙 _) ≫
        ((hF.mapQ.toDegreeZero2 hF.mapQ_isGraded).toPseudofunctor.mapComp
          ((unit R B).map f) ((unit R B).map g)).hom
    rw [PrelaxFunctor.map₂_id, hF.toQPiTwoFunctor_mapQ_mapComp]
    erw [Category.comp_id, Category.id_comp]
  · funext a
    apply Iso.ext
    rw [Pseudofunctor.comp_mapId, Pseudofunctor.comp_mapId, Iso.trans_hom, Iso.trans_hom,
      PrelaxFunctor.map₂Iso_hom, PrelaxFunctor.map₂Iso_hom, unit_mapId, unit_mapId, Iso.refl_hom,
      Iso.refl_hom]
    erw [PrelaxFunctor.map₂_id, Category.comp_id, Category.id_comp]
    exact (hF.toQPiTwoFunctor_mapQ_mapId a).symm

set_option backward.isDefEq.respectTransparency false in
/-- **`𝔼 ∘ 𝔻 = 𝕀` on 1-morphisms**, on the coherence maps `j`. -/
theorem comp_unitQPiTwoFunctor_j (a : B) :
    ((hF.comp unitQPiTwoFunctor).j a).hom =
      ((unitQPiTwoFunctor.comp (hF.mapQ.toQPiTwoFunctor hF.mapQ_isGraded)).j a).hom := by
  change 𝟙 _ ≫ (unit R C).map₂ (hF.j a).hom =
    ((hF.mapQ.toQPiTwoFunctor hF.mapQ_isGraded).j ((unit R B).obj a)).hom ≫
      (hF.mapQ.toDegreeZero2 hF.mapQ_isGraded).toPseudofunctor.map₂ (𝟙 _)
  rw [PrelaxFunctor.map₂_id, hF.toQPiTwoFunctor_mapQ_j]
  erw [Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **`𝔼 ∘ 𝔻 = 𝕀` on 1-morphisms**, on the coherence maps `k`. -/
theorem comp_unitQPiTwoFunctor_k (a : B) :
    ((hF.comp unitQPiTwoFunctor).k a).hom =
      ((unitQPiTwoFunctor.comp (hF.mapQ.toQPiTwoFunctor hF.mapQ_isGraded)).k a).hom := by
  change 𝟙 _ ≫ (unit R C).map₂ (hF.k a).hom =
    ((hF.mapQ.toQPiTwoFunctor hF.mapQ_isGraded).k ((unit R B).obj a)).hom ≫
      (hF.mapQ.toDegreeZero2 hF.mapQ_isGraded).toPseudofunctor.map₂ (𝟙 _)
  rw [PrelaxFunctor.map₂_id, hF.toQPiTwoFunctor_mapQ_k]
  erw [Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **`𝔼 ∘ 𝔻 = 𝕀` on 1-morphisms**, as bundled `(Q, Π)`-2-functors:
`𝔼(ℝ̂) ∘ unit = unit ∘ ℝ`. -/
theorem comp_unitBundled :
    (⟨F, hF⟩ : BundledQPiTwoFunctor R B C).comp (unitBundled R C) =
      (unitBundled R B).comp
        ⟨(hF.mapQ.toDegreeZero2 hF.mapQ_isGraded).toPseudofunctor,
          hF.mapQ.toQPiTwoFunctor hF.mapQ_isGraded⟩ :=
  BundledQPiTwoFunctor.ext' (comp_unit hF)
    (fun a => heq_of_eq (comp_unitQPiTwoFunctor_j hF a))
    (fun a => heq_of_eq (comp_unitQPiTwoFunctor_k hF a))

end QAssociated2

namespace QPiTwoCat

variable {R : Type w} [CommRing R]

/-- **The §6 analogue of Lemma 5.4, `𝔼 ∘ 𝔻 = 𝕀` on objects**, as an isomorphism
`𝔄 ≅ 𝔼(𝔻 𝔄)` in `(Q, Π)-2-Cat`: the identification `QAssociated2.unit` and its inverse
`QAssociated2.counit`. -/
def unitIso (B : QPiTwoCat.{w, w₁, v₁, u₁} R) :
    B ≅ QPiTwoCat.of R (GUnderlying2 R (QAssociated2 R B)) where
  hom := QAssociated2.unitBundled R B
  inv := QAssociated2.counitBundled R B
  hom_inv_id := QAssociated2.unitBundled_comp_counitBundled
  inv_hom_id := QAssociated2.counitBundled_comp_unitBundled

/-- **The §6 analogue of Lemma 5.4, `𝔼 ∘ 𝔻 = 𝕀`**, as a natural isomorphism `𝟭 ≅ 𝔻 ⋙ 𝔼` of
endofunctors of `(Q, Π)-2-Cat`. Naturality is `𝔼(𝔻 ℝ) ∘ unit = unit ∘ ℝ`
(`QAssociated2.comp_unitBundled`). -/
def unitNatIso :
    𝟭 (QPiTwoCat.{w, w₁, v₁, u₁} R) ≅ toQPiTwoGSCat ⋙ QPiTwoGSCat.toQPiTwoCat :=
  NatIso.ofComponents unitIso fun {_ _} P => QAssociated2.comp_unitBundled P.toQPiTwoFunctor

end QPiTwoCat

end StringDiagrams

end
