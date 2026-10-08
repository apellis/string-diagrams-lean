import StringDiagrams.Super.QPiCatBicategory
import StringDiagrams.Super.PiCatD1
import StringDiagrams.Super.QPiTwoSCat
import StringDiagrams.Super.GSCat

/-!
# Theorem 6.13: `𝔼` is a 2-equivalence `(Q, Π)-𝔊𝔖ℭ𝔄𝔗̲ ≃ (Q, Π)-ℭ𝔄𝔗`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (6.3) and
Theorem 6.13 (with the sketch of its proof), as a statement about bundled 2-functors between the
strict 2-categories `(Q, Π)-𝔊𝔖ℭ𝔄𝔗̲ = GUnderlying2 R (QPiGSCat R)` (graded `(Q, Π)`-supercategories,
graded superfunctors, even supernatural transformations of degree zero) and `(Q, Π)-ℭ𝔄𝔗`
(`QPiCat R`, `StringDiagrams.Super.QPiCatBicategory`).

* `QPiGSCatU.EPseudo`: the strict 2-functor `𝔼` of (6.3), `A ↦ A̲`, `F ↦ (F̲, β_F, γ_F)`,
  `x ↦ x̲`, with identity coherence isomorphisms (`QPiGSCatU.EPseudo_mapId`,
  `QPiGSCatU.EPseudo_mapComp`).
* `QPiCat.DStrict`, `QPiCat.DPseudo`: the strict 2-functor `𝔻` of the proof, `A ↦ Â`, `F ↦ F̂`,
  `x ↦ x̂` (a Mathlib `StrictPseudofunctor`), from `QAssociated.map`, `QAssociated.mapNat` and
  their strictness (`QAssociated.map_id`, `QAssociated.map_comp`, whiskering lemmas).
* `QPiCat.unitStrong : 𝕀 ⇒ 𝔼 ∘ 𝔻`: the identifications `unit : A ≅ E(D A)` (inverse `counit`,
  a `(Q, Π)`-functor with `β = γ = 1`: `QAssociated.counitQPiFunctor`), natural on the nose
  (`QPiCat.unit_naturality_eq`, from `β`, `γ` of `𝔻 F`: `QAssociated.β_map_unit`,
  `QAssociated.γ_map_unit`).
* `QPiGSCatU.counitStrong : 𝔻 ∘ 𝔼 ⇒ 𝕀`: the isomorphisms `T_B : D(E B) ≅ B`, natural on the nose
  (`QAssociated.T_naturality`) and in 2-morphisms (`QAssociated.T_map_mapNat_app`).
* **Theorem 6.13** (`QPiCat.theorem613`): both are strong transformations with identity
  naturality 2-morphisms and invertible components, so `𝔼` and `𝔻` are mutually inverse
  2-equivalences.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory GradedSupercategory

universe w v u

/-! ## `𝔼` as a pseudofunctor -/

namespace QPiGSCatU

variable {R : Type w} [CommRing R]

variable {A B C : GUnderlying2 R (QPiGSCat.{w, v, u} R)}

/-- The graded superfunctor underlying a 1-morphism of `(Q, Π)-𝔊𝔖ℭ𝔄𝔗̲`. -/
abbrev fun1 (F : A ⟶ B) : A.obj.as.carrier ⥤ B.obj.as.carrier := F.obj.obj.as.toFunctor

/-- A 2-morphism of `(Q, Π)-𝔊𝔖ℭ𝔄𝔗̲` (even of degree zero) is graded supernatural of parity and
degree zero. -/
theorem isGradedSupernatural₂ {F G : A ⟶ B} (η : F ⟶ G) :
    IsGradedSupernatural R 0 0 (F := fun1 F) (G := fun1 G) (η.1.1.1.app 0) :=
  GradedHom.mem_degree_iff.1 η.1.2 0

theorem app_one_eq_zero {F G : A ⟶ B} (η : F ⟶ G) (X : A.obj.as.carrier) : η.1.1.1.app 1 X = 0 :=
  Superfunctor.app_eq_zero_of_mem (R := R) η.2 (by decide) X

/-- 2-morphisms of `(Q, Π)-𝔊𝔖ℭ𝔄𝔗̲` are determined by their even components. -/
theorem hom₂_ext {F G : A ⟶ B} {x y : F ⟶ G}
    (h : ∀ X : A.obj.as.carrier, x.1.1.1.app 0 X = y.1.1.1.app 0 X) : x = y :=
  Subtype.ext (DegreeZero.hom_ext (Subtype.ext (Superfunctor.hom_ext_parity h fun X => by
    rw [app_one_eq_zero x X, app_one_eq_zero y X])))

@[simp] theorem comp₂_app_zero {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.obj.as.carrier) :
    (x ≫ y).1.1.1.app 0 X = x.1.1.1.app 0 X ≫ y.1.1.1.app 0 X := by
  change x.1.1.1.app 0 X ≫ y.1.1.1.app 0 X + x.1.1.1.app 1 X ≫ y.1.1.1.app 1 X = _
  rw [app_one_eq_zero x X, Limits.zero_comp, add_zero]

@[simp] theorem id₂_app_zero (F : A ⟶ B) (X : A.obj.as.carrier) :
    (𝟙 F : F ⟶ F).1.1.1.app 0 X = 𝟙 _ := rfl

@[simp] theorem whiskerLeft₂_app_zero (F : A ⟶ B) {G H : B ⟶ C} (y : G ⟶ H)
    (X : A.obj.as.carrier) : (F ◁ y).1.1.1.app 0 X = y.1.1.1.app 0 ((fun1 F).obj X) := rfl

@[simp] theorem whiskerRight₂_app_zero {F G : A ⟶ B} (x : F ⟶ G) (H : B ⟶ C)
    (X : A.obj.as.carrier) : (x ▷ H).1.1.1.app 0 X = (fun1 H).map (x.1.1.1.app 0 X) := rfl

@[simp] theorem associator₂_hom_app_zero {D : GUnderlying2 R (QPiGSCat.{w, v, u} R)} (F : A ⟶ B)
    (G : B ⟶ C) (H : C ⟶ D) (X : A.obj.as.carrier) : (α_ F G H).hom.1.1.1.app 0 X = 𝟙 _ := rfl

@[simp] theorem associator₂_inv_app_zero {D : GUnderlying2 R (QPiGSCat.{w, v, u} R)} (F : A ⟶ B)
    (G : B ⟶ C) (H : C ⟶ D) (X : A.obj.as.carrier) : (α_ F G H).inv.1.1.1.app 0 X = 𝟙 _ := rfl

@[simp] theorem leftUnitor₂_hom_app_zero (F : A ⟶ B) (X : A.obj.as.carrier) :
    (λ_ F).hom.1.1.1.app 0 X = 𝟙 _ := rfl

@[simp] theorem rightUnitor₂_hom_app_zero (F : A ⟶ B) (X : A.obj.as.carrier) :
    (ρ_ F).hom.1.1.1.app 0 X = 𝟙 _ := rfl

variable (R) in
/-- `𝔼` on 1-morphisms: the `(Q, Π)`-functor `(F̲, β_F, γ_F)` (Corollary 6.7(ii)). -/
abbrev Emap (F : A ⟶ B) :
    QPiCat.of R (GUnderlying R A.obj.as.carrier) ⟶ QPiCat.of R (GUnderlying R B.obj.as.carrier) :=
  ⟨GUnderlying.map R (fun1 F), GUnderlying.qpiFunctor (fun1 F)⟩

/-- `𝔼` on 2-morphisms (Corollary 6.7(iii)). -/
def Emap₂ {F G : A ⟶ B} (η : F ⟶ G) : Emap R F ⟶ Emap R G :=
  QPiCat.hom₂Mk (GUnderlying.natTrans (isGradedSupernatural₂ η))
    (GUnderlying.isQPiNatural (isGradedSupernatural₂ η))

@[simp] theorem Emap₂_app_val {F G : A ⟶ B} (η : F ⟶ G) (X : GUnderlying R A.obj.as.carrier) :
    ((QPiCat.Hom₂.natTrans (Emap₂ η)).app X).1.1 = η.1.1.1.app 0 X.obj.obj := rfl

omit [CommRing R] in
theorem _root_.StringDiagrams.QPiFunctor.isQPiNatural_id_of {R : Type w} [CommRing R]
    {C : Type*} [Category C] [Preadditive C] [Linear R C] [QPiCategory R C]
    {D : Type*} [Category D] [Preadditive D] [Linear R D] [QPiCategory R D]
    {F : C ⥤ D} {hF hG : QPiFunctor R F}
    (hβ : ∀ X, hF.β.hom.app X = hG.β.hom.app X) (hγ : ∀ X, hF.γ.hom.app X = hG.γ.hom.app X) :
    QPiFunctor.IsQPiNatural R hF hG (𝟙 F) :=
  ⟨fun X => by simp [hβ X], fun X => by simp [hγ X]⟩

theorem id_isQPiNatural (A : GUnderlying2 R (QPiGSCat.{w, v, u} R)) :
    QPiFunctor.IsQPiNatural R (Emap R (𝟙 A)).qpiFunctor
      (QPiFunctor.id R (GUnderlying R A.obj.as.carrier)) (Iso.refl (𝟭 _)).hom :=
  QPiFunctor.isQPiNatural_id_of
    (fun X => Underlying.hom_ext (DegreeZero.hom_ext (by
      rw [GUnderlying.qpiFunctor_β_hom_app_val]
      exact PiSupercategory.β_id (R := R) X.obj.obj)))
    (fun X => Underlying.hom_ext (DegreeZero.hom_ext (by
      rw [GUnderlying.qpiFunctor_γ_hom_app_val]
      exact QPiSupercategory.γ_id (R := R) X.obj.obj)))

theorem comp_isQPiNatural (F : A ⟶ B) (G : B ⟶ C) :
    QPiFunctor.IsQPiNatural R (Emap R (F ≫ G)).qpiFunctor (Emap R F ≫ Emap R G).qpiFunctor
      (Iso.refl _).hom :=
  QPiFunctor.isQPiNatural_id_of (GUnderlying.qpiFunctor_comp_β (fun1 F) (fun1 G))
    (GUnderlying.qpiFunctor_comp_γ (fun1 F) (fun1 G))

set_option linter.unusedSimpArgs false in
variable (R) in
/-- **Brundan–Ellis, (6.3).** The strict 2-functor `𝔼 : (Q, Π)-𝔊𝔖ℭ𝔄𝔗̲ → (Q, Π)-ℭ𝔄𝔗`: a graded
`(Q, Π)`-supercategory `A ↦ A̲`, `F ↦ (F̲, β_F, γ_F)`, `x ↦ x̲`, with identity coherence
isomorphisms. -/
def EPseudo : Pseudofunctor (GUnderlying2 R (QPiGSCat.{w, v, u} R)) (QPiCat.{w, v, u} R) where
  obj A := QPiCat.of R (GUnderlying R A.obj.as.carrier)
  map F := Emap R F
  map₂ η := Emap₂ η
  map₂_id _ := QPiCat.hom₂_ext fun _ => rfl
  map₂_comp η θ := QPiCat.hom₂_ext fun X => Underlying.hom_ext (DegreeZero.hom_ext (by
    simp only [QPiCat.comp₂_natTrans_app, QPiCat.iso₂Mk_hom_natTrans_app,
      QPiCat.iso₂Mk_inv_natTrans_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      QPiCat.whiskerLeft_natTrans_app, QPiCat.whiskerRight_natTrans_app, Emap₂_app_val,
      Underlying.comp_val, DegreeZero.comp_val, Underlying.id_val, DegreeZero.id_val,
      comp₂_app_zero, whiskerLeft₂_app_zero, whiskerRight₂_app_zero, associator₂_hom_app_zero,
      associator₂_inv_app_zero, leftUnitor₂_hom_app_zero, rightUnitor₂_hom_app_zero,
      QPiCat.associator_hom_natTrans_app, QPiCat.leftUnitor_hom_natTrans_app,
      QPiCat.rightUnitor_hom_natTrans_app]
    try rfl))
  mapId A := QPiCat.iso₂Mk (Iso.refl _) (id_isQPiNatural A)
  mapComp F G := QPiCat.iso₂Mk (Iso.refl _) (comp_isQPiNatural F G)
  map₂_whisker_left F _ _ η := QPiCat.hom₂_ext fun X => Underlying.hom_ext (DegreeZero.hom_ext (by
    simp only [QPiCat.comp₂_natTrans_app, QPiCat.iso₂Mk_hom_natTrans_app,
      QPiCat.iso₂Mk_inv_natTrans_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      QPiCat.whiskerLeft_natTrans_app, QPiCat.whiskerRight_natTrans_app, Emap₂_app_val,
      Underlying.comp_val, DegreeZero.comp_val, Underlying.id_val, DegreeZero.id_val,
      comp₂_app_zero, whiskerLeft₂_app_zero, whiskerRight₂_app_zero, associator₂_hom_app_zero,
      associator₂_inv_app_zero, leftUnitor₂_hom_app_zero, rightUnitor₂_hom_app_zero,
      QPiCat.associator_hom_natTrans_app, QPiCat.leftUnitor_hom_natTrans_app,
      QPiCat.rightUnitor_hom_natTrans_app]
    change η.1.1.1.app 0 _ = 𝟙 _ ≫ η.1.1.1.app 0 _ ≫ 𝟙 _
    simp))
  map₂_whisker_right η H := QPiCat.hom₂_ext fun X => Underlying.hom_ext (DegreeZero.hom_ext (by
    simp only [QPiCat.comp₂_natTrans_app, QPiCat.iso₂Mk_hom_natTrans_app,
      QPiCat.iso₂Mk_inv_natTrans_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      QPiCat.whiskerLeft_natTrans_app, QPiCat.whiskerRight_natTrans_app, Emap₂_app_val,
      Underlying.comp_val, DegreeZero.comp_val, Underlying.id_val, DegreeZero.id_val,
      comp₂_app_zero, whiskerLeft₂_app_zero, whiskerRight₂_app_zero, associator₂_hom_app_zero,
      associator₂_inv_app_zero, leftUnitor₂_hom_app_zero, rightUnitor₂_hom_app_zero,
      QPiCat.associator_hom_natTrans_app, QPiCat.leftUnitor_hom_natTrans_app,
      QPiCat.rightUnitor_hom_natTrans_app]
    change (fun1 H).map (η.1.1.1.app 0 _) = 𝟙 _ ≫ (fun1 H).map (η.1.1.1.app 0 _) ≫ 𝟙 _
    simp))
  map₂_associator F G H := QPiCat.hom₂_ext fun X => Underlying.hom_ext (DegreeZero.hom_ext (by
    simp only [QPiCat.comp₂_natTrans_app, QPiCat.iso₂Mk_hom_natTrans_app,
      QPiCat.iso₂Mk_inv_natTrans_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      QPiCat.whiskerLeft_natTrans_app, QPiCat.whiskerRight_natTrans_app, Emap₂_app_val,
      Underlying.comp_val, DegreeZero.comp_val, Underlying.id_val, DegreeZero.id_val,
      comp₂_app_zero, whiskerLeft₂_app_zero, whiskerRight₂_app_zero, associator₂_hom_app_zero,
      associator₂_inv_app_zero, leftUnitor₂_hom_app_zero, rightUnitor₂_hom_app_zero,
      QPiCat.associator_hom_natTrans_app, QPiCat.leftUnitor_hom_natTrans_app,
      QPiCat.rightUnitor_hom_natTrans_app]
    change 𝟙 _ = 𝟙 _ ≫ (fun1 H).map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp))
  map₂_left_unitor F := QPiCat.hom₂_ext fun X => Underlying.hom_ext (DegreeZero.hom_ext (by
    simp only [QPiCat.comp₂_natTrans_app, QPiCat.iso₂Mk_hom_natTrans_app,
      QPiCat.iso₂Mk_inv_natTrans_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      QPiCat.whiskerLeft_natTrans_app, QPiCat.whiskerRight_natTrans_app, Emap₂_app_val,
      Underlying.comp_val, DegreeZero.comp_val, Underlying.id_val, DegreeZero.id_val,
      comp₂_app_zero, whiskerLeft₂_app_zero, whiskerRight₂_app_zero, associator₂_hom_app_zero,
      associator₂_inv_app_zero, leftUnitor₂_hom_app_zero, rightUnitor₂_hom_app_zero,
      QPiCat.associator_hom_natTrans_app, QPiCat.leftUnitor_hom_natTrans_app,
      QPiCat.rightUnitor_hom_natTrans_app]
    change 𝟙 _ = 𝟙 _ ≫ (fun1 F).map (𝟙 _) ≫ 𝟙 _
    simp))
  map₂_right_unitor F := QPiCat.hom₂_ext fun X => Underlying.hom_ext (DegreeZero.hom_ext (by
    simp only [QPiCat.comp₂_natTrans_app, QPiCat.iso₂Mk_hom_natTrans_app,
      QPiCat.iso₂Mk_inv_natTrans_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      QPiCat.whiskerLeft_natTrans_app, QPiCat.whiskerRight_natTrans_app, Emap₂_app_val,
      Underlying.comp_val, DegreeZero.comp_val, Underlying.id_val, DegreeZero.id_val,
      comp₂_app_zero, whiskerLeft₂_app_zero, whiskerRight₂_app_zero, associator₂_hom_app_zero,
      associator₂_inv_app_zero, leftUnitor₂_hom_app_zero, rightUnitor₂_hom_app_zero,
      QPiCat.associator_hom_natTrans_app, QPiCat.leftUnitor_hom_natTrans_app,
      QPiCat.rightUnitor_hom_natTrans_app]
    change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp))

theorem EPseudo_map₂ {F G : A ⟶ B} (η : F ⟶ G) : (EPseudo R).map₂ η = Emap₂ η := rfl

theorem Emap_id (A : GUnderlying2 R (QPiGSCat.{w, v, u} R)) :
    Emap R (𝟙 A) = 𝟙 (QPiCat.of R (GUnderlying R A.obj.as.carrier)) :=
  QPiCat.Hom.ext rfl
    (fun X => heq_of_eq (Underlying.hom_ext (DegreeZero.hom_ext (by
      rw [GUnderlying.qpiFunctor_β_hom_app_val]
      exact PiSupercategory.β_id (R := R) X.obj.obj))))
    (fun X => heq_of_eq (Underlying.hom_ext (DegreeZero.hom_ext (by
      rw [GUnderlying.qpiFunctor_γ_hom_app_val]
      exact QPiSupercategory.γ_id (R := R) X.obj.obj))))

theorem Emap_comp (F : A ⟶ B) (G : B ⟶ C) : Emap R (F ≫ G) = Emap R F ≫ Emap R G :=
  QPiCat.Hom.ext rfl (fun X => heq_of_eq (GUnderlying.qpiFunctor_comp_β (fun1 F) (fun1 G) X))
    (fun X => heq_of_eq (GUnderlying.qpiFunctor_comp_γ (fun1 F) (fun1 G) X))

/-- `𝔼` is strict: its coherence isomorphisms `mapId` are `eqToIso`. -/
theorem EPseudo_mapId (A : GUnderlying2 R (QPiGSCat.{w, v, u} R)) :
    (EPseudo R).mapId A = eqToIso (Emap_id A) :=
  Iso.ext (QPiCat.hom₂_ext fun X => by
    erw [eqToIso.hom, QPiCat.eqToHom_natTrans_app, eqToHom_refl]
    rfl)

/-- `𝔼` is strict: its coherence isomorphisms `mapComp` are `eqToIso`. -/
theorem EPseudo_mapComp (F : A ⟶ B) (G : B ⟶ C) :
    (EPseudo R).mapComp F G = eqToIso (Emap_comp F G) :=
  Iso.ext (QPiCat.hom₂_ext fun X => by
    erw [eqToIso.hom, QPiCat.eqToHom_natTrans_app, eqToHom_refl]
    rfl)

end QPiGSCatU

/-! ## `β`, `γ` of `𝔻 F` and the inverse of `unit` -/

namespace QAssociated

open Orbit

variable {R : Type w} [CommRing R] {A : Type u} [Category.{v} A] [Preadditive A] [Linear R A]
  [QPiCategory R A] {A' : Type u} [Category.{v} A'] [Preadditive A'] [Linear R A']
  [QPiCategory R A']

set_option backward.isDefEq.respectTransparency false in
/-- `β` of `𝔻 F` at `unit X` is `β_F` (in degree zero). -/
theorem β_map_unit {F : A ⥤ A'} [F.Additive] [F.Linear R] (hF : QPiFunctor R F) (X : A) :
    (PiSupercategory.β R (map hF) ((unit R A).obj X).obj.obj).hom =
      ((unit R A').map (hF.β.hom.app X)).1.1 := by
  rw [unit_map_val, PiSupercategory.β_hom]
  simp only [Orbit.ζ_eq, Orbit.ζIso, Functor.mapIso_hom, Functor.mapIso_inv]
  erw [Orbit.map_ι_map]
  rw [← Functor.map_comp]
  congr 1
  exact Associated.β_map (hF := hF.toPiFunctor) (⟨X⟩ : Associated R A)

set_option backward.isDefEq.respectTransparency false in
/-- `γ` of `𝔻 F` at `unit X` is `γ_F` (in degree zero). -/
theorem γ_map_unit {F : A ⥤ A'} [F.Additive] [F.Linear R] (hF : QPiFunctor R F) (X : A) :
    (QPiSupercategory.γ R (map hF) ((unit R A).obj X).obj.obj).hom =
      ((unit R A').map (hF.γ.hom.app X)).1.1 := by
  rw [unit_map_val, QPiSupercategory.γ_hom, Orbit.σ_eq, Orbit.σ_eq]
  erw [Orbit.map_σIso_inv, Iso.hom_inv_id_assoc, shiftFunctor_γ_hom_app]
  rfl

instance : (unit R A).Additive :=
  inferInstanceAs ((Associated.unit R A ⋙ Underlying.map (R := R) (ιZ (shiftData R A))).Additive)

instance : (unit R A).Linear R :=
  inferInstanceAs ((Associated.unit R A ⋙ Underlying.map (R := R) (ιZ (shiftData R A))).Linear R)

theorem counit_map_eq {X Y : GUnderlying R (QAssociated R A)} (g : X ⟶ Y) :
    (unit R A).map ((counit R A).map g) = g := by
  have h := CategoryTheory.Functor.congr_hom (counit_comp_unit (R := R) (A := A)) g
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact h

theorem counit_map_unit {X Y : A} (f : X ⟶ Y) : (counit R A).map ((unit R A).map f) = f := by
  have h := CategoryTheory.Functor.congr_hom (unit_comp_counit (R := R) (A := A)) f
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact h

theorem unit_map_injective {X Y : A} {f f' : X ⟶ Y}
    (h : (unit R A).map f = (unit R A).map f') : f = f' := by
  rw [← counit_map_unit (R := R) f, h, counit_map_unit]

instance : (counit R A).Additive where
  map_add {X Y f g} := by
    apply unit_map_injective (R := R)
    rw [(unit R A).map_add, counit_map_eq, counit_map_eq, counit_map_eq]
    rfl

instance : (counit R A).Linear R where
  map_smul {X Y} f r := by
    apply unit_map_injective (R := R)
    rw [(unit R A).map_smul, counit_map_eq, counit_map_eq]
    rfl

theorem counit_map_pi {X Y : GUnderlying R (QAssociated R A)} (g : X ⟶ Y) :
    (counit R A).map ((PiCategory.pi (R := R)).map g) =
      (PiCategory.pi (R := R)).map ((counit R A).map g) := by
  apply unit_map_injective (R := R)
  erw [counit_map_eq, ← unit_map_pi, counit_map_eq]
  rfl

theorem counit_map_Q {X Y : GUnderlying R (QAssociated R A)} (g : X ⟶ Y) :
    (counit R A).map ((QPiCategory.Q (R := R)).map g) =
      (QPiCategory.Q (R := R)).map ((counit R A).map g) := by
  apply unit_map_injective (R := R)
  erw [counit_map_eq, ← unit_map_Q, counit_map_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (R A) in
/-- The inverse identification `counit` is a `(Q, Π)`-functor with `β = 1` and `γ = 1`. -/
def counitQPiFunctor : QPiFunctor R (counit R A) where
  β := NatIso.ofComponents (fun X => Iso.refl _) fun f => by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.refl_hom, Category.comp_id,
      Category.id_comp]
    exact (counit_map_pi f).symm
  comm X := by
    simp only [NatIso.ofComponents_hom_app, Iso.refl_hom, CategoryTheory.Functor.map_id,
      Category.id_comp]
    obtain ⟨⟨⟨⟨X⟩⟩⟩⟩ := X
    have h : (PiCategory.ξ (R := R)).inv.app ((unit R A).obj X) =
        (unit R A).map ((PiCategory.ξ (R := R)).inv.app X) := by
      rw [← cancel_epi ((PiCategory.ξ (R := R)).hom.app ((unit R A).obj X)), Iso.hom_inv_id_app]
      have e := ξ_unit (R := R) (A := A) X
      rw [PiCategory.ξApp_hom, PiCategory.ξApp_hom] at e
      erw [e, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
      rfl
    erw [h, counit_map_unit, Iso.hom_inv_id_app]
    rfl
  γ := NatIso.ofComponents (fun X => Iso.refl _) fun f => by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.refl_hom, Category.comp_id,
      Category.id_comp]
    exact (counit_map_Q f).symm
  isCompatible := by
    rw [QPiFunctorData.IsCompatible.iff]
    intro X
    simp only [NatIso.ofComponents_hom_app, Iso.refl_hom, Functor.comp_obj,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    obtain ⟨⟨⟨⟨X⟩⟩⟩⟩ := X
    erw [β_Q_unit, counit_map_unit]
    rfl

@[simp] theorem counitQPiFunctor_β_hom_app (X : GUnderlying R (QAssociated R A)) :
    (counitQPiFunctor R A).β.hom.app X = 𝟙 _ := rfl

@[simp] theorem counitQPiFunctor_γ_hom_app (X : GUnderlying R (QAssociated R A)) :
    (counitQPiFunctor R A).γ.hom.app X = 𝟙 _ := rfl

end QAssociated

/-! ## Strictness of `(Q, Π)-𝔊𝔖ℭ𝔄𝔗̲` -/

namespace DegreeZero2

variable {R : Type w} [CommRing R] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B]

theorem hom_eq {a b : DegreeZero2 R B} {f g : a ⟶ b} (h : f.obj = g.obj) : f = g := by
  cases f
  cases g
  cases h
  rfl

theorem eqToHom_val {a b : DegreeZero2 R B} {f g : a ⟶ b} (h : f = g) :
    (eqToHom h).1 = eqToHom (congrArg DegreeZero.obj h) := by
  subst h
  rfl

/-- The 2-supercategory of 2-morphisms of degree zero of a strict graded 2-supercategory is
strict. -/
instance instStrict [BicategoryStruct.Strict B] : BicategoryStruct.Strict (DegreeZero2 R B) where
  id_comp f := hom_eq (BicategoryStruct.Strict.id_comp f.obj)
  comp_id f := hom_eq (BicategoryStruct.Strict.comp_id f.obj)
  assoc f g h := hom_eq (BicategoryStruct.Strict.assoc f.obj g.obj h.obj)
  leftUnitor_eqToIso f := Iso.ext (DegreeZero.hom_ext (by
    rw [eqToIso.hom, eqToHom_val]
    exact congrArg Iso.hom (BicategoryStruct.Strict.leftUnitor_eqToIso f.obj)))
  rightUnitor_eqToIso f := Iso.ext (DegreeZero.hom_ext (by
    rw [eqToIso.hom, eqToHom_val]
    exact congrArg Iso.hom (BicategoryStruct.Strict.rightUnitor_eqToIso f.obj)))
  associator_eqToIso f g h := Iso.ext (DegreeZero.hom_ext (by
    rw [eqToIso.hom, eqToHom_val]
    exact congrArg Iso.hom (BicategoryStruct.Strict.associator_eqToIso f.obj g.obj h.obj)))

end DegreeZero2

/-! ## `𝔻` as a strict pseudofunctor -/

namespace QPiGSCatU

variable {R : Type w} [CommRing R] {A B C : GUnderlying2 R (QPiGSCat.{w, v, u} R)}

theorem hom1_eq_of_toFunctor_eq {F G : A ⟶ B} (h : fun1 F = fun1 G) : F = G := by
  obtain ⟨⟨⟨⟨⟨F, _, _, _⟩, _⟩⟩⟩⟩ := F
  obtain ⟨⟨⟨⟨⟨G, _, _, _⟩, _⟩⟩⟩⟩ := G
  cases h
  rfl

theorem eqToHom₂_app_zero {F G : A ⟶ B} (h : F = G) (X : A.obj.as.carrier) :
    (eqToHom h : F ⟶ G).1.1.1.app 0 X = eqToHom (by rw [h]) := by
  subst h
  rfl

end QPiGSCatU

namespace QPiCat

open QPiGSCatU

variable {R : Type w} [CommRing R] {A B C : QPiCat.{w, v, u} R}

variable (R) in
/-- `𝔻` on objects: the associated graded `(Q, Π)`-supercategory `Â`. -/
abbrev Dobj (A : QPiCat.{w, v, u} R) : GUnderlying2 R (QPiGSCat.{w, v, u} R) :=
  ⟨⟨QPiGSCat.of R (QAssociated R A)⟩⟩

/-- `𝔻` on 1-morphisms: `F ↦ F̂`. -/
abbrev Dhom (F : A ⟶ B) : Dobj R A ⟶ Dobj R B :=
  ⟨⟨GradedHom.of ⟨⟨QAssociated.map F.qpiFunctor⟩⟩⟩⟩

/-- `𝔻` on 2-morphisms: `x ↦ x̂`, even of degree zero. -/
def Dmap₂ {F G : A ⟶ B} (x : F ⟶ G) : Dhom F ⟶ Dhom G :=
  ⟨⟨GradedHom.ofHomogeneous (QAssociated.isGradedSupernatural_mapNat (Hom₂.isQPiNatural x)),
    GradedHom.ofHomogeneous_mem_degree
      (QAssociated.isGradedSupernatural_mapNat (Hom₂.isQPiNatural x))⟩,
    GradedHom.ofHomogeneous_mem (QAssociated.isGradedSupernatural_mapNat (Hom₂.isQPiNatural x))⟩

@[simp] theorem Dmap₂_app_zero {F G : A ⟶ B} (x : F ⟶ G) (X : QAssociated R A) :
    (Dmap₂ x).1.1.1.app 0 X = (QAssociated.mapNat (Hom₂.isQPiNatural x)).app X := by
  change (if (0 : ZMod 2) = 0 then (QAssociated.mapNat (Hom₂.isQPiNatural x)).app X else 0) = _
  rfl

variable (R) in
/-- **Brundan–Ellis, proof of Theorem 6.13.** The strict 2-functor
`𝔻 : (Q, Π)-ℭ𝔄𝔗 → (Q, Π)-𝔊𝔖ℭ𝔄𝔗̲`: `A ↦ Â`, `F ↦ F̂`, `x ↦ x̂` (a strict pseudofunctor). -/
def DStrict : StrictPseudofunctor (QPiCat.{w, v, u} R) (GUnderlying2 R (QPiGSCat.{w, v, u} R)) :=
  StrictPseudofunctor.mk''
    { obj A := Dobj R A
      map F := Dhom F
      map₂ x := Dmap₂ x
      map₂_id F := QPiGSCatU.hom₂_ext fun X => by
        rw [Dmap₂_app_zero, QPiGSCatU.id₂_app_zero]
        exact congrArg (fun y => y.app X) (QAssociated.mapNat_id F.qpiFunctor)
      map₂_comp x y := QPiGSCatU.hom₂_ext fun X => by
        rw [QPiGSCatU.comp₂_app_zero, Dmap₂_app_zero, Dmap₂_app_zero, Dmap₂_app_zero]
        exact congrArg (fun z => z.app X)
          (QAssociated.mapNat_comp (Hom₂.isQPiNatural x) (Hom₂.isQPiNatural y))
      map_id A := QPiGSCatU.hom1_eq_of_toFunctor_eq (QAssociated.map_id (R := R) (A := A))
      map_comp F G := QPiGSCatU.hom1_eq_of_toFunctor_eq
        (QAssociated.map_comp F.qpiFunctor G.qpiFunctor)
      map₂_whisker_left F G H y := QPiGSCatU.hom₂_ext fun X => by
        rw [QPiGSCatU.comp₂_app_zero, QPiGSCatU.comp₂_app_zero, QPiGSCatU.eqToHom₂_app_zero,
          QPiGSCatU.eqToHom₂_app_zero, QPiGSCatU.whiskerLeft₂_app_zero, Dmap₂_app_zero,
          Dmap₂_app_zero]
        erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
        exact QAssociated.mapNat_whiskerLeft_app F.qpiFunctor (Hom₂.isQPiNatural y) X
      map₂_whisker_right x H := QPiGSCatU.hom₂_ext fun X => by
        rw [QPiGSCatU.comp₂_app_zero, QPiGSCatU.comp₂_app_zero, QPiGSCatU.eqToHom₂_app_zero,
          QPiGSCatU.eqToHom₂_app_zero, QPiGSCatU.whiskerRight₂_app_zero, Dmap₂_app_zero,
          Dmap₂_app_zero]
        erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
        exact QAssociated.mapNat_whiskerRight_app H.qpiFunctor (Hom₂.isQPiNatural x) X }

variable (R) in
/-- `𝔻` as a pseudofunctor. -/
abbrev DPseudo : Pseudofunctor (QPiCat.{w, v, u} R) (GUnderlying2 R (QPiGSCat.{w, v, u} R)) :=
  (DStrict R).toPseudofunctor

/-- The identification `unit : A → E(D A)` as a morphism of `(Q, Π)-Cat`. -/
def unitHom' (A : QPiCat.{w, v, u} R) : A ⟶ QPiCat.of R (GUnderlying R (QAssociated R A)) :=
  ⟨QAssociated.unit R A, QAssociated.unitQPiFunctor R A⟩

/-- The identification `counit : E(D A) → A` as a morphism of `(Q, Π)-Cat`. -/
def unitInvHom' (A : QPiCat.{w, v, u} R) : QPiCat.of R (GUnderlying R (QAssociated R A)) ⟶ A :=
  ⟨QAssociated.counit R A, QAssociated.counitQPiFunctor R A⟩

variable (R) in
/-- The component `A → E(D A)` of the unit (`𝔼 ∘ 𝔻 = I`, the identification `unit`). -/
def unitHom (A : QPiCat.{w, v, u} R) :
    (Pseudofunctor.id (QPiCat.{w, v, u} R)).obj A ⟶
      ((DPseudo R).comp (QPiGSCatU.EPseudo R)).obj A :=
  unitHom' A

variable (R) in
/-- The inverse `E(D A) → A` of `unitHom`. -/
def unitInvHom (A : QPiCat.{w, v, u} R) :
    ((DPseudo R).comp (QPiGSCatU.EPseudo R)).obj A ⟶
      (Pseudofunctor.id (QPiCat.{w, v, u} R)).obj A :=
  unitInvHom' A

theorem unitHom'_inv (A : QPiCat.{w, v, u} R) :
    unitHom' A ≫ unitInvHom' A = 𝟙 A ∧ unitInvHom' A ≫ unitHom' A = 𝟙 _ := by
  refine ⟨Hom.ext QAssociated.unit_comp_counit (fun X => ?_) (fun X => ?_),
    Hom.ext QAssociated.counit_comp_unit (fun X => ?_) (fun X => ?_)⟩
  all_goals refine heq_of_eq ?_
  all_goals simp only [unitHom', unitInvHom', comp_qpiFunctor, id_qpiFunctor,
    QPiFunctor.comp_β_hom_app, QPiFunctor.comp_γ_hom_app, QPiFunctor.id_β_hom_app,
    QPiFunctor.id_γ_hom_app, QAssociated.unitQPiFunctor_β_hom_app,
    QAssociated.unitQPiFunctor_γ_hom_app, QAssociated.counitQPiFunctor_β_hom_app,
    QAssociated.counitQPiFunctor_γ_hom_app]
  all_goals repeat erw [CategoryTheory.Functor.map_id]
  all_goals repeat erw [Category.id_comp]
  all_goals rfl

theorem unitHom_inv (A : QPiCat.{w, v, u} R) :
    unitHom R A ≫ unitInvHom R A = 𝟙 _ ∧ unitInvHom R A ≫ unitHom R A = 𝟙 _ :=
  unitHom'_inv A

/-- `𝔼(𝔻 F)` as a morphism of `(Q, Π)-Cat`. -/
abbrev EDhom {A B : QPiCat.{w, v, u} R} (F : A ⟶ B) :
    QPiCat.of R (GUnderlying R (QAssociated R A)) ⟶ QPiCat.of R (GUnderlying R (QAssociated R B)) :=
  ⟨GUnderlying.map R (QAssociated.map F.qpiFunctor),
    GUnderlying.qpiFunctor (QAssociated.map F.qpiFunctor)⟩

theorem unit_naturality_eq' {A B : QPiCat.{w, v, u} R} (F : A ⟶ B) :
    F ≫ unitHom' B = unitHom' A ≫ EDhom F :=
  Hom.ext (QAssociated.unit_comp_map F.qpiFunctor).symm
    (fun X => heq_of_eq (by
      simp [unitHom']
      erw [Category.id_comp, Category.comp_id]
      apply Underlying.hom_ext; apply DegreeZero.hom_ext
      exact (QAssociated.β_map_unit F.qpiFunctor X).symm))
    (fun X => heq_of_eq (by
      simp [unitHom']
      erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
      apply Underlying.hom_ext; apply DegreeZero.hom_ext
      exact (QAssociated.γ_map_unit F.qpiFunctor X).symm))

theorem unit_naturality_eq {A B : QPiCat.{w, v, u} R} (F : A ⟶ B) :
    (Pseudofunctor.id (QPiCat.{w, v, u} R)).map F ≫ unitHom R B =
      unitHom R A ≫ ((DPseudo R).comp (QPiGSCatU.EPseudo R)).map F :=
  unit_naturality_eq' F

theorem DPseudo_mapComp_hom {A B C : QPiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) :
    ((DPseudo R).mapComp F G).hom =
      eqToHom (QPiGSCatU.hom1_eq_of_toFunctor_eq (QAssociated.map_comp F.qpiFunctor G.qpiFunctor)) :=
  rfl

theorem DPseudo_mapId_hom (A : QPiCat.{w, v, u} R) :
    ((DPseudo R).mapId A).hom =
      eqToHom (QPiGSCatU.hom1_eq_of_toFunctor_eq (QAssociated.map_id (R := R) (A := A))) := rfl

theorem ED_mapId_app (A : QPiCat.{w, v, u} R)
    (Y : (((DPseudo R).comp (QPiGSCatU.EPseudo R)).obj A).carrier) :
    (Hom₂.natTrans (((DPseudo R).comp (QPiGSCatU.EPseudo R)).mapId A).hom).app Y = 𝟙 _ := by
  apply Underlying.hom_ext; apply DegreeZero.hom_ext
  refine Eq.trans (?_ : _ = (eqToHom (QPiGSCatU.hom1_eq_of_toFunctor_eq (F := Dhom (𝟙 A))
    (G := 𝟙 (Dobj R A)) (QAssociated.map_id (R := R) (A := A))) :
      Dhom (𝟙 A) ⟶ 𝟙 (Dobj R A)).1.1.1.app 0 _ ≫ 𝟙 _) ?_
  · rfl
  · exact ((congrArg (fun z => z ≫ 𝟙 _) (QPiGSCatU.eqToHom₂_app_zero _ _)).trans
      (Category.comp_id _)).trans rfl

theorem ED_mapComp_app {A B C : QPiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (Y : (((DPseudo R).comp (QPiGSCatU.EPseudo R)).obj A).carrier) :
    (Hom₂.natTrans (((DPseudo R).comp (QPiGSCatU.EPseudo R)).mapComp F G).hom).app Y =
      𝟙 _ := by
  apply Underlying.hom_ext; apply DegreeZero.hom_ext
  refine Eq.trans (?_ : _ = (eqToHom (QPiGSCatU.hom1_eq_of_toFunctor_eq (F := Dhom (F ≫ G))
    (G := Dhom F ≫ Dhom G) (QAssociated.map_comp F.qpiFunctor G.qpiFunctor)) :
      Dhom (F ≫ G) ⟶ Dhom F ≫ Dhom G).1.1.1.app 0 _ ≫ 𝟙 _) ?_
  · rfl
  · exact ((congrArg (fun z => z ≫ 𝟙 _) (QPiGSCatU.eqToHom₂_app_zero _ _)).trans
      (Category.comp_id _)).trans rfl

theorem ED_map_id (A : QPiCat.{w, v, u} R) :
    ((DPseudo R).comp (QPiGSCatU.EPseudo R)).map (𝟙 A) =
      𝟙 (((DPseudo R).comp (QPiGSCatU.EPseudo R)).obj A) :=
  (congrArg (QPiGSCatU.Emap R) ((DStrict R).map_id A)).trans (QPiGSCatU.Emap_id _)

theorem ED_map_comp {A B C : QPiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) :
    ((DPseudo R).comp (QPiGSCatU.EPseudo R)).map (F ≫ G) =
      ((DPseudo R).comp (QPiGSCatU.EPseudo R)).map F ≫
        ((DPseudo R).comp (QPiGSCatU.EPseudo R)).map G :=
  (congrArg (QPiGSCatU.Emap R) ((DStrict R).map_comp F G)).trans (QPiGSCatU.Emap_comp _ _)

/-- `𝔼 ∘ 𝔻` is strict on identities. -/
theorem ED_mapId (A : QPiCat.{w, v, u} R) :
    ((DPseudo R).comp (QPiGSCatU.EPseudo R)).mapId A = eqToIso (ED_map_id A) :=
  Iso.ext (hom₂_ext fun Y => (ED_mapId_app A Y).trans (by
    erw [eqToIso.hom, eqToHom_natTrans_app, eqToHom_refl]))

set_option maxHeartbeats 4000000 in
/-- `𝔼 ∘ 𝔻` is strict on composites. -/
theorem ED_mapComp {A B C : QPiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) :
    ((DPseudo R).comp (QPiGSCatU.EPseudo R)).mapComp F G = eqToIso (ED_map_comp F G) := by
  ext1
  simp only [Pseudofunctor.comp_mapComp, (DStrict R).mapComp_eq_eqToIso,
    QPiGSCatU.EPseudo_mapComp, eqToIso.hom]
  erw [Iso.trans_hom, PrelaxFunctor.map₂Iso_hom, eqToIso.hom, eqToIso.hom,
    PrelaxFunctor.map₂_eqToHom, eqToHom_trans]

set_option maxHeartbeats 4000000 in
variable (R) in
/-- **Theorem 6.13, `𝔼 ∘ 𝔻 = 𝕀`.** The identification `A ≅ E(D A)` as a strong transformation
`𝕀 ⇒ 𝔼 ∘ 𝔻` with identity naturality 2-morphisms. -/
def unitStrong : Pseudofunctor.StrongTrans (Pseudofunctor.id (QPiCat.{w, v, u} R))
    ((DPseudo R).comp (QPiGSCatU.EPseudo R)) where
  app A := unitHom R A
  naturality F := eqToIso (unit_naturality_eq F)
  naturality_naturality {a b f g} y := by
    ext X
    simp only [comp₂_natTrans, NatTrans.comp_app, whiskerRight_natTrans_app,
      whiskerLeft_natTrans_app, eqToIso.hom, eqToHom_natTrans_app]
    erw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl
  naturality_id A := by
    simp only [ED_mapId, Pseudofunctor.id_mapId, eqToIso.hom, Iso.refl_hom,
      Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso, eqToIso.inv,
      Bicategory.whiskerLeft_eqToHom, eqToHom_trans]
    erw [Bicategory.id_whiskerRight]
    exact (Category.id_comp _).symm
  naturality_comp {a b c} F G := by
    simp only [ED_mapComp, Pseudofunctor.id_mapComp, eqToIso.hom, eqToIso.inv, Iso.refl_hom,
      Strict.associator_eqToIso, Bicategory.whiskerLeft_eqToHom,
      Bicategory.eqToHom_whiskerRight, eqToHom_trans]
    erw [Bicategory.id_whiskerRight]
    exact (Category.id_comp _).symm

end QPiCat

/-! ## `𝔻 ∘ 𝔼 ≅ 𝕀` -/

namespace QPiGSCatU

open QPiCat

variable {R : Type w} [CommRing R]

/-- `T_B : 𝔻(𝔼 B) → B` as a 1-morphism of `(Q, Π)-𝔊𝔖ℭ𝔄𝔗̲`. -/
def counitHom' (B : GUnderlying2 R (QPiGSCat.{w, v, u} R)) :
    QPiCat.Dobj R (QPiCat.of R (GUnderlying R B.obj.as.carrier)) ⟶ B :=
  ⟨⟨GradedHom.of ⟨⟨QAssociated.T R B.obj.as.carrier⟩⟩⟩⟩

/-- `T_B⁻¹ : B → 𝔻(𝔼 B)` as a 1-morphism of `(Q, Π)-𝔊𝔖ℭ𝔄𝔗̲`. -/
def counitInvHom' (B : GUnderlying2 R (QPiGSCat.{w, v, u} R)) :
    B ⟶ QPiCat.Dobj R (QPiCat.of R (GUnderlying R B.obj.as.carrier)) :=
  ⟨⟨GradedHom.of ⟨⟨QAssociated.Tinv R B.obj.as.carrier⟩⟩⟩⟩

variable (R) in
/-- The component `T_B : 𝔻(𝔼 B) → B` of the counit. -/
def counitHom (B : GUnderlying2 R (QPiGSCat.{w, v, u} R)) :
    ((EPseudo R).comp (DPseudo R)).obj B ⟶ (Pseudofunctor.id _).obj B :=
  counitHom' B

variable (R) in
/-- The inverse `T_B⁻¹` of `counitHom`. -/
def counitInvHom (B : GUnderlying2 R (QPiGSCat.{w, v, u} R)) :
    (Pseudofunctor.id _).obj B ⟶ ((EPseudo R).comp (DPseudo R)).obj B :=
  counitInvHom' B

theorem counitHom_inv (B : GUnderlying2 R (QPiGSCat.{w, v, u} R)) :
    counitHom R B ≫ counitInvHom R B = 𝟙 _ ∧ counitInvHom R B ≫ counitHom R B = 𝟙 _ :=
  ⟨hom1_eq_of_toFunctor_eq (QAssociated.T_comp_Tinv (R := R) (B := B.obj.as.carrier)),
    hom1_eq_of_toFunctor_eq (QAssociated.Tinv_comp_T (R := R) (B := B.obj.as.carrier))⟩

theorem counit_naturality_eq {A B : GUnderlying2 R (QPiGSCat.{w, v, u} R)} (F : A ⟶ B) :
    ((EPseudo R).comp (DPseudo R)).map F ≫ counitHom R B =
      counitHom R A ≫ (Pseudofunctor.id _).map F :=
  hom1_eq_of_toFunctor_eq (QAssociated.T_naturality (R := R) (fun1 F))

theorem DE_map_id (B : GUnderlying2 R (QPiGSCat.{w, v, u} R)) :
    ((EPseudo R).comp (DPseudo R)).map (𝟙 B) = 𝟙 (((EPseudo R).comp (DPseudo R)).obj B) :=
  (congrArg (DStrict R).map (Emap_id B)).trans ((DStrict R).map_id _)

theorem DE_map_comp {A B C : GUnderlying2 R (QPiGSCat.{w, v, u} R)} (F : A ⟶ B) (G : B ⟶ C) :
    ((EPseudo R).comp (DPseudo R)).map (F ≫ G) =
      ((EPseudo R).comp (DPseudo R)).map F ≫ ((EPseudo R).comp (DPseudo R)).map G :=
  (congrArg (DStrict R).map (Emap_comp F G)).trans ((DStrict R).map_comp _ _)

set_option maxHeartbeats 4000000 in
/-- `𝔻 ∘ 𝔼` is strict on identities. -/
theorem DE_mapId (B : GUnderlying2 R (QPiGSCat.{w, v, u} R)) :
    ((EPseudo R).comp (DPseudo R)).mapId B = eqToIso (DE_map_id B) := by
  ext1
  simp only [Pseudofunctor.comp_mapId, EPseudo_mapId, (DStrict R).mapId_eq_eqToIso,
    eqToIso.hom]
  erw [Iso.trans_hom, PrelaxFunctor.map₂Iso_hom, eqToIso.hom, eqToIso.hom,
    PrelaxFunctor.map₂_eqToHom, eqToHom_trans]

set_option maxHeartbeats 4000000 in
/-- `𝔻 ∘ 𝔼` is strict on composites. -/
theorem DE_mapComp {A B C : GUnderlying2 R (QPiGSCat.{w, v, u} R)} (F : A ⟶ B) (G : B ⟶ C) :
    ((EPseudo R).comp (DPseudo R)).mapComp F G = eqToIso (DE_map_comp F G) := by
  ext1
  simp only [Pseudofunctor.comp_mapComp, EPseudo_mapComp, (DStrict R).mapComp_eq_eqToIso,
    eqToIso.hom]
  erw [Iso.trans_hom, PrelaxFunctor.map₂Iso_hom, eqToIso.hom, eqToIso.hom,
    PrelaxFunctor.map₂_eqToHom, eqToHom_trans]

set_option maxHeartbeats 4000000 in
variable (R) in
/-- **Theorem 6.13, `𝔻 ∘ 𝔼 ≅ 𝕀`.** The isomorphisms `T_B : 𝔻(𝔼 B) ≅ B` as a strong
transformation `𝔻 ∘ 𝔼 ⇒ 𝕀` with identity naturality 2-morphisms. -/
def counitStrong : Pseudofunctor.StrongTrans ((EPseudo R).comp (DPseudo R))
    (Pseudofunctor.id (GUnderlying2 R (QPiGSCat.{w, v, u} R))) where
  app B := counitHom R B
  naturality F := eqToIso (counit_naturality_eq F)
  naturality_naturality {a b f g} η := by
    apply hom₂_ext
    intro X
    erw [comp₂_app_zero, comp₂_app_zero, whiskerRight₂_app_zero, whiskerLeft₂_app_zero,
      eqToIso.hom, eqToIso.hom, eqToHom₂_app_zero (counit_naturality_eq f),
      eqToHom₂_app_zero (counit_naturality_eq g), eqToHom_refl, eqToHom_refl, Category.comp_id,
      Category.id_comp]
    obtain ⟨⟨X⟩⟩ := X
    change (QAssociated.T R b.obj.as.carrier).map
      ((QAssociated.mapNat (GUnderlying.isQPiNatural (isGradedSupernatural₂ η))).app _) =
        η.1.1.1.app 0 _
    exact QAssociated.T_map_mapNat_app (fun1 f) (isGradedSupernatural₂ η) _
  naturality_id A := by
    simp only [DE_mapId, Pseudofunctor.id_mapId, eqToIso.hom, Iso.refl_hom,
      Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso, eqToIso.inv,
      Bicategory.eqToHom_whiskerRight, eqToHom_trans]
    erw [Bicategory.whiskerLeft_id]
    exact Category.comp_id _
  naturality_comp {a b c} F G := by
    simp only [DE_mapComp, Pseudofunctor.id_mapComp, eqToIso.hom, eqToIso.inv, Iso.refl_hom,
      Strict.associator_eqToIso, Bicategory.whiskerLeft_eqToHom,
      Bicategory.eqToHom_whiskerRight, eqToHom_trans]
    erw [Bicategory.whiskerLeft_id]
    exact Category.comp_id _

end QPiGSCatU

/-! ## Theorem 6.13 -/

namespace QPiCat

variable (R : Type w) [CommRing R]

/-- **Brundan–Ellis, Theorem 6.13.** The strict 2-functor
`𝔼 : (Q, Π)-𝔊𝔖ℭ𝔄𝔗̲ → (Q, Π)-ℭ𝔄𝔗` of (6.3) (`QPiGSCatU.EPseudo`) is a 2-equivalence of
2-categories, with inverse the strict 2-functor `𝔻` of the proof (`QPiCat.DStrict`,
`QPiCat.DPseudo`): there are strong transformations `𝕀 ⇒ 𝔼 ∘ 𝔻` (`QPiCat.unitStrong`) and
`𝔻 ∘ 𝔼 ⇒ 𝕀` (`QPiGSCatU.counitStrong`) with identity naturality 2-morphisms whose components
(`A ≅ E(D A)`, and `T_B : D(E B) ≅ B`) are invertible 1-morphisms. As in the proof of
Theorem 5.3, the composites are isomorphic, not only equivalent, to the identities. Here
`(Q, Π)`-functors include the compatibility of `γ_F` with `β` (erratum 4 to §6). -/
theorem theorem613 :
    (∀ {A B : QPiCat.{w, v, u} R} (F : A ⟶ B),
        (unitStrong R).naturality F = eqToIso (unit_naturality_eq F)) ∧
      (∀ A : QPiCat.{w, v, u} R, ∃ g : ((DPseudo R).comp (QPiGSCatU.EPseudo R)).obj A ⟶ A,
        (unitStrong R).app A ≫ g = 𝟙 _ ∧ g ≫ (unitStrong R).app A = 𝟙 _) ∧
      (∀ {A B : GUnderlying2 R (QPiGSCat.{w, v, u} R)} (F : A ⟶ B),
        (QPiGSCatU.counitStrong R).naturality F = eqToIso (QPiGSCatU.counit_naturality_eq F)) ∧
      (∀ B : GUnderlying2 R (QPiGSCat.{w, v, u} R),
        ∃ g : B ⟶ ((QPiGSCatU.EPseudo R).comp (DPseudo R)).obj B,
          (QPiGSCatU.counitStrong R).app B ≫ g = 𝟙 _ ∧ g ≫ (QPiGSCatU.counitStrong R).app B = 𝟙 _) :=
  ⟨fun _ => rfl, fun A => ⟨_, (unitHom_inv A).1, (unitHom_inv A).2⟩, fun _ => rfl,
    fun B => ⟨_, (QPiGSCatU.counitHom_inv B).1, (QPiGSCatU.counitHom_inv B).2⟩⟩

end QPiCat

end StringDiagrams

end
