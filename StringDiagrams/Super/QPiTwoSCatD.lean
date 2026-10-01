import StringDiagrams.Super.QPiTwoSCat
import StringDiagrams.Super.QAssociatedTwoMap

/-!
# `D₂` and `𝔻` as functors

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (5.5) and
§6 (the analogue of (5.5) after Definition 6.14).

* `D₂` of (5.5) on Π-2-functors (`PiTwoFunctor.mapTwo`) preserves identities and composition:
  `D₂(𝕀) = 𝕀` and `D₂(𝕊 ∘ ℝ) = D₂ 𝕊 ∘ D₂ ℝ`, as equalities of 2-superfunctors
  (`PiTwoFunctor.mapTwo_id`, `PiTwoFunctor.mapTwo_comp`). On odd 2-morphisms this is
  `j_{𝕊ℝ}⁻¹ ∘ c_{𝕊ℝ}⁻¹ = (j_𝕊⁻¹ ∘ c_𝕊⁻¹) ∘ 𝕊(j_ℝ⁻¹ ∘ c_ℝ⁻¹)` for the composite coherence maps
  `j_{𝕊ℝ} = 𝕊(j_ℝ) ∘ j_𝕊` (`PiTwoFunctor.comp`). Hence `D₂` is a functor
  `PiTwoCat.toPiTwoSCat : Π-2-Cat ⥤ Π-2-SCat`.
* Likewise `𝔻` on `(Q, Π)`-2-functors (`QPiTwoFunctor.mapQ`) preserves identities and
  composition (`QPiTwoFunctor.mapQ_id`, `QPiTwoFunctor.mapQ_comp`): the morphisms of shift data
  `homShiftFunctor` of a composite induce the composite orbit functors (`Orbit.map_comp`), since
  `γ̂_{𝕊ℝ}` is the composite of the `γ̂` (`k_{𝕊ℝ} = 𝕊(k_ℝ) ∘ k_𝕊`). Hence `𝔻` is a functor
  `QPiTwoCat.toQPiTwoGSCat : (Q, Π)-2-Cat ⥤ (Q, Π)-2-GSCat`.
* **Lemma 5.4, `E₂ ∘ D₂ = I`, as a natural isomorphism.** `E₂(D₂ 𝔄)` is the Π-2-category
  `Underlying2 R (Associated2 R 𝔄)`, a different type from `𝔄`, so the identity `E₂ ∘ D₂ = I` of
  the paper is an isomorphism in `Π-2-Cat`: the identification `Associated2.unit` has the strict
  inverse `Associated2.counit` (`x ↦ x₀`, a Π-2-functor with `j = 1`,
  `Associated2.counitPiTwoFunctor`), giving `PiTwoCat.unitIso`, and it is natural
  (`Associated2.comp_unit`, `Associated2.comp_unitPiTwoFunctor_j`, from `ĵ = j`), giving
  `PiTwoCat.unitNatIso : 𝟭 ≅ D₂ ⋙ E₂`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃

/-! ## `D₂` preserves identities and composition -/

namespace PiTwoFunctor

variable {R : Type w} [CommRing R]
  {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [PiTwoCategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [PiTwoCategory R C]
  {D : Type u₃} [Bicategory.{w₃, v₃} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)] [PreadditiveBicategory D]
  [LinearBicategory R D] [PiTwoCategory R D]

open Associated2

set_option backward.isDefEq.respectTransparency false in
/-- `D₂(𝕀) = 𝕀` on 2-morphisms. -/
theorem mapTwo_id_map₂ {a b : Associated2 R B} {f g : a ⟶ b} (x : f ⟶ g) :
    (PiTwoFunctor.id R B).mapTwo.map₂ x = x := by
  apply hom₂_ext
  · rfl
  · change x.2 ≫ (𝟙 _ ≫ g.obj ◁ 𝟙 _) = x.2
    simp

set_option backward.isDefEq.respectTransparency false in
variable (R B) in
/-- **`D₂` preserves identities**: `D₂(𝕀) = 𝕀`. -/
theorem mapTwo_id : (PiTwoFunctor.id R B).mapTwo = TwoSuperfunctor.id R (Associated2 R B) := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    exact mapTwo_id_map₂ x
  · funext a b c f g
    exact Iso.ext (hom₂_ext rfl rfl)
  · funext a
    exact Iso.ext (hom₂_ext rfl rfl)

variable {F : Pseudofunctor B C} {G : Pseudofunctor C D} (hF : PiTwoFunctor R F)
  (hG : PiTwoFunctor R G)

set_option backward.isDefEq.respectTransparency false in
/-- `D₂(𝕊 ∘ ℝ) = D₂ 𝕊 ∘ D₂ ℝ` on 2-morphisms. On an odd 2-morphism `x̂`, coming from
`x : F ⇒ π_μ G`, this is `j_{𝕊ℝ}⁻¹ ∘ c_{𝕊ℝ}⁻¹ ∘ 𝕊ℝx = j_𝕊⁻¹ ∘ c_𝕊⁻¹ ∘ 𝕊(j_ℝ⁻¹ ∘ c_ℝ⁻¹ ∘ ℝx)`. -/
theorem mapTwo_comp_map₂ {a b : Associated2 R B} {f g : a ⟶ b} (x : f ⟶ g) :
    (hF.comp hG).mapTwo.map₂ x = hG.mapTwo.map₂ (hF.mapTwo.map₂ x) := by
  apply hom₂_ext
  · rfl
  · simp only [mapTwo_map₂, Associated.map_map, Associated.homMk_snd, homFunctor_map,
      homPi_β_inv_app, βHom_inv, comp_j, Iso.trans_inv, PrelaxFunctor.map₂Iso_inv,
      Pseudofunctor.comp_mapComp, Iso.trans_hom, PrelaxFunctor.map₂Iso_hom,
      PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_left, Bicategory.whiskerLeft_comp,
      Category.assoc]
    erw [Iso.inv_hom_id_assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- `D₂(𝕊 ∘ ℝ) = D₂ 𝕊 ∘ D₂ ℝ` on the coherence maps `c`. -/
theorem mapTwo_comp_mapComp_hom {a b c : Associated2 R B} (f : a ⟶ b) (g : b ⟶ c) :
    ((hF.comp hG).mapTwo.mapComp f g).hom =
      (hG.mapTwo.mapComp (hF.mapTwo.map f) (hF.mapTwo.map g)).hom ≫
        hG.mapTwo.map₂ (hF.mapTwo.mapComp f g).hom := by
  apply hom₂_ext
  · simp
    rfl
  · simp
    erw [hG.map₂_zero]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- `D₂(𝕊 ∘ ℝ) = D₂ 𝕊 ∘ D₂ ℝ` on the coherence maps `i`. -/
theorem mapTwo_comp_mapId_hom (a : Associated2 R B) :
    ((hF.comp hG).mapTwo.mapId a).hom =
      (hG.mapTwo.mapId (hF.mapTwo.obj a)).hom ≫ hG.mapTwo.map₂ (hF.mapTwo.mapId a).hom := by
  apply hom₂_ext
  · simp
    rfl
  · simp
    erw [hG.map₂_zero]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- **`D₂` preserves composition**: `D₂(𝕊 ∘ ℝ) = D₂ 𝕊 ∘ D₂ ℝ`. -/
theorem mapTwo_comp : (hF.comp hG).mapTwo = hF.mapTwo.comp hG.mapTwo := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    exact mapTwo_comp_map₂ hF hG x
  · funext a b c f g
    exact Iso.ext (mapTwo_comp_mapComp_hom hF hG f g)
  · funext a
    exact Iso.ext (mapTwo_comp_mapId_hom hF hG a)

end PiTwoFunctor

/-! ## `𝔻` preserves identities and composition -/

namespace QPiTwoFunctor

variable {R : Type w} [CommRing R]
  {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [QPiTwoCategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [QPiTwoCategory R C]
  {D : Type u₃} [Bicategory.{w₃, v₃} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)] [PreadditiveBicategory D]
  [LinearBicategory R D] [QPiTwoCategory R D]

open Associated2 CentralShift

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of shift data `homShiftFunctor` of the identity `(Q, Π)`-2-functor induces the
identity orbit functor. -/
theorem orbitMap_homShiftFunctor_id (a b : Associated2 R B) :
    Orbit.map ((QPiTwoFunctor.id R B).homShiftFunctor R a b) =
      Orbit.map (ShiftFunctor.id (homShift R a b)) := by
  refine Orbit.map_congr' (fun _ => rfl) (fun x => ?_) (fun g => ?_)
  · erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact PiTwoFunctor.mapTwo_id_map₂ x
  · erw [eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [ShiftFunctor.id_γ_hom_app]
    apply hom₂_ext
    · change g.obj ◁ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp
    · rfl

set_option backward.isDefEq.respectTransparency false in
/-- `𝔻(𝕀) = 𝕀` on 2-morphisms. -/
theorem mapQ_id_map₂ {a b : QAssociated2 R B} {f g : a ⟶ b} (x : f ⟶ g) :
    (QPiTwoFunctor.id R B).mapQ.map₂ x = x := by
  have h := CategoryTheory.Functor.congr_hom (orbitMap_homShiftFunctor_id a.obj b.obj) x
  rw [Orbit.map_map_id] at h
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
variable (R B) in
/-- **`𝔻` preserves identities**: `𝔻(𝕀) = 𝕀`. -/
theorem mapQ_id : (QPiTwoFunctor.id R B).mapQ = TwoSuperfunctor.id R (QAssociated2 R B) := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    exact mapQ_id_map₂ x
  · funext a b c f g
    apply Iso.ext
    have e : ((PiTwoFunctor.id R B).mapTwo.mapComp f.obj g.obj).hom = 𝟙 _ := hom₂_ext rfl rfl
    rw [mapQ_mapComp_hom']
    erw [e, CategoryTheory.Functor.map_id]
    rfl
  · funext a
    apply Iso.ext
    have e : ((PiTwoFunctor.id R B).mapTwo.mapId a.obj).hom = 𝟙 _ := hom₂_ext rfl rfl
    rw [mapQ_mapId_hom']
    erw [e, CategoryTheory.Functor.map_id]
    rfl

variable {F : Pseudofunctor B C} {G : Pseudofunctor C D} (hF : QPiTwoFunctor R F)
  (hG : QPiTwoFunctor R G)

set_option backward.isDefEq.respectTransparency false in
/-- The `γ` of a composite on a hom category: `c_{𝕊ℝ} ∘ (𝕊ℝG) k_{𝕊ℝ} = 𝕊(c_ℝ ∘ (ℝG) k_ℝ) ∘ c_𝕊 ∘
(𝕊ℝG) k_𝕊`. -/
theorem γHom_comp_hom {a b : B} (g : a ⟶ b) :
    ((hF.comp hG).γHom g).hom = (hG.γHom (F.map g)).hom ≫ G.map₂ (hF.γHom g).hom := by
  change G.map (F.map g) ◁ ((hG.k (F.obj b)).hom ≫ G.map₂ (hF.k b).hom) ≫
      ((G.mapComp (F.map g) (F.map (QPiTwoCategory.q (R := R) b))).inv ≫
        G.map₂ (F.mapComp g (QPiTwoCategory.q (R := R) b)).inv) = _
  rw [γHom_hom, γHom_hom]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of shift data `homShiftFunctor` of a composite of `(Q, Π)`-2-functors induces
the composite of the orbit functors: `γ̂_{𝕊ℝ} = 𝕊̂(γ̂_ℝ) ∘ γ̂_𝕊`, since
`k_{𝕊ℝ} = 𝕊(k_ℝ) ∘ k_𝕊`. -/
theorem orbitMap_homShiftFunctor_comp (a b : Associated2 R B) :
    Orbit.map ((hF.comp hG).homShiftFunctor R a b) =
      Orbit.map ((hF.homShiftFunctor R a b).comp
        (hG.homShiftFunctor R (hF.mapTwo.obj a) (hF.mapTwo.obj b))) := by
  refine Orbit.map_congr' (fun _ => rfl) (fun x => ?_) (fun g => ?_)
  · erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact PiTwoFunctor.mapTwo_comp_map₂ hF.toPiTwoFunctor hG.toPiTwoFunctor x
  · erw [eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [ShiftFunctor.comp_γ_hom_app]
    apply hom₂_ext
    · simp only [homShiftFunctor_γ_hom_app, γhat_hom_app_fst, homShiftFunctor_F,
        TwoSuperfunctor.mapFunctor_map, comp₂_fst, γhat_hom_app_snd, PiTwoFunctor.mapTwo_map₂,
        Associated.map_map, Associated.homMk_fst, Associated.homMk_snd,
        PiTwoFunctor.homFunctor_map, Limits.zero_comp, sub_zero]
      exact γHom_comp_hom hF hG g.obj
    · simp only [homShiftFunctor_γ_hom_app, γhat_hom_app_fst, homShiftFunctor_F,
        TwoSuperfunctor.mapFunctor_map, comp₂_snd, γhat_hom_app_snd, PiTwoFunctor.mapTwo_map₂,
        Associated.map_map, Associated.homMk_fst, Associated.homMk_snd,
        PiTwoFunctor.homFunctor_map, Limits.zero_comp, add_zero]
      erw [hG.toPiTwoFunctor.map₂_zero]
      simp

set_option backward.isDefEq.respectTransparency false in
/-- `𝔻(𝕊 ∘ ℝ) = 𝔻 𝕊 ∘ 𝔻 ℝ` on 2-morphisms. -/
theorem mapQ_comp_map₂ {a b : QAssociated2 R B} {f g : a ⟶ b} (x : f ⟶ g) :
    (hF.comp hG).mapQ.map₂ x = hG.mapQ.map₂ (hF.mapQ.map₂ x) := by
  have h := CategoryTheory.Functor.congr_hom (orbitMap_homShiftFunctor_comp hF hG a.obj b.obj) x
  rw [← Orbit.map_map_comp] at h
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- **`𝔻` preserves composition**: `𝔻(𝕊 ∘ ℝ) = 𝔻 𝕊 ∘ 𝔻 ℝ`. -/
theorem mapQ_comp : (hF.comp hG).mapQ = hF.mapQ.comp hG.mapQ := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    exact mapQ_comp_map₂ hF hG x
  · funext a b c f g
    apply Iso.ext
    rw [TwoSuperfunctor.comp_mapComp, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom,
      mapQ_mapComp_hom', mapQ_mapComp_hom', mapQ_mapComp_hom', mapQ_map₂]
    erw [Orbit.map_ι_map, ← CategoryTheory.Functor.map_comp]
    exact congrArg (Orbit.ι _).map
      (PiTwoFunctor.mapTwo_comp_mapComp_hom hF.toPiTwoFunctor hG.toPiTwoFunctor f.obj g.obj)
  · funext a
    apply Iso.ext
    rw [TwoSuperfunctor.comp_mapId, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom,
      mapQ_mapId_hom', mapQ_mapId_hom', mapQ_mapId_hom', mapQ_map₂]
    erw [Orbit.map_ι_map, ← CategoryTheory.Functor.map_comp]
    exact congrArg (Orbit.ι _).map
      (PiTwoFunctor.mapTwo_comp_mapId_hom hF.toPiTwoFunctor hG.toPiTwoFunctor a.obj)

end QPiTwoFunctor

/-! ## Lemma 5.4: the inverse of the identification `unit` -/

namespace Associated2

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [PiTwoCategory R B]

set_option backward.isDefEq.respectTransparency false in
variable (R B) in
/-- The inverse of the identification `Associated2.unit : 𝔄 → E₂(𝔄̂)` of Lemma 5.4: the identity
on objects and 1-morphisms, and `x ↦ x₀` on (even) 2-morphisms, with identity coherence maps. -/
@[simps]
def counit : Pseudofunctor (Underlying2 R (Associated2 R B)) B where
  obj a := a.obj.obj
  map f := f.obj.obj
  map₂ x := x.1.1
  map₂_id f := rfl
  map₂_comp x y := by
    change (x.1 ≫ y.1).1 = x.1.1 ≫ y.1.1
    rw [comp₂_fst, Associated.mem_parity_zero.1 x.2]
    simp
  mapId a := Iso.refl _
  mapComp f g := Iso.refl _
  map₂_whisker_left f g h x := by
    change f.obj.obj ◁ x.1.1 = 𝟙 _ ≫ f.obj.obj ◁ x.1.1 ≫ 𝟙 _
    simp
  map₂_whisker_right x h := by
    change x.1.1 ▷ h.obj.obj = 𝟙 _ ≫ x.1.1 ▷ h.obj.obj ≫ 𝟙 _
    simp
  map₂_associator f g h := by
    change (α_ f.obj.obj g.obj.obj h.obj.obj).hom = 𝟙 _ ≫ 𝟙 _ ▷ h.obj.obj ≫
      (α_ f.obj.obj g.obj.obj h.obj.obj).hom ≫ f.obj.obj ◁ 𝟙 _ ≫ 𝟙 _
    simp
  map₂_left_unitor f := by
    change (λ_ f.obj.obj).hom = 𝟙 _ ≫ 𝟙 _ ▷ f.obj.obj ≫ (λ_ f.obj.obj).hom
    simp
  map₂_right_unitor f := by
    change (ρ_ f.obj.obj).hom = 𝟙 _ ≫ f.obj.obj ◁ 𝟙 _ ≫ (ρ_ f.obj.obj).hom
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of `unit` is a (strict) Π-2-functor with `j = 1`. -/
def counitPiTwoFunctor : PiTwoFunctor R (counit R B) where
  map₂_add _ _ := rfl
  map₂_smul _ _ := rfl
  j a := Iso.refl _
  β_comm {a b} f := by
    change f.obj.obj ◁ 𝟙 _ ≫ 𝟙 _ ≫ (PiTwoSupercategory.β (R := R) f.obj).hom.1 =
      (PiTwoCategory.β (R := R) f.obj.obj).hom ≫ 𝟙 _ ▷ f.obj.obj ≫ 𝟙 _
    rw [β_hom_eq]
    simp
  ξ_comm a := by
    change 𝟙 _ ▷ PiTwoCategory.pi (R := R) a.obj.obj ≫
        PiTwoCategory.pi (R := R) a.obj.obj ◁ 𝟙 _ ≫ 𝟙 _ ≫
          (PiTwoSupercategory.ξ (R := R) a.obj).hom.1 =
      (PiTwoCategory.ξ (R := R) a.obj.obj).hom ≫ 𝟙 _
    rw [ξ_hom_eq]
    simp

variable {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [PiTwoCategory R C]
  {F : Pseudofunctor B C} (hF : PiTwoFunctor R F)

set_option backward.isDefEq.respectTransparency false in
/-- **Lemma 5.4, `E₂ ∘ D₂ = I` on morphisms**: `E₂(ℝ̂) ∘ unit = unit ∘ ℝ` as pseudofunctors. -/
theorem comp_unit : F.comp (unit R C) = (unit R B).comp hF.mapTwo.toPseudofunctor := by
  refine pseudofunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b f g η
    apply Subtype.ext
    apply hom₂_ext
    · rfl
    · change (0 : _) = F.map₂ (0 : f ⟶ g ≫ PiTwoCategory.pi (R := R) b) ≫ (hF.βHom g).inv
      rw [hF.map₂_zero, Limits.zero_comp]
  · funext a b c f g
    apply Iso.ext
    apply Subtype.ext
    apply hom₂_ext
    · simp
      erw [F.map₂_id, Category.id_comp, Category.comp_id]
      rfl
    · simp
      erw [hF.map₂_zero]
      simp
  · funext a
    apply Iso.ext
    apply Subtype.ext
    apply hom₂_ext
    · simp
      erw [F.map₂_id, Category.id_comp, Category.comp_id]
      rfl
    · simp
      erw [hF.map₂_zero]
      simp

set_option backward.isDefEq.respectTransparency false in
/-- **Lemma 5.4, `E₂ ∘ D₂ = I` on morphisms**, on the coherence maps `j`. -/
theorem comp_unitPiTwoFunctor_j (a : B) :
    ((hF.comp unitPiTwoFunctor).j a).hom =
      ((unitPiTwoFunctor.comp hF.mapTwo.toPiTwoFunctor).j a).hom := by
  rw [PiTwoFunctor.comp_j, PiTwoFunctor.comp_j]
  apply Subtype.ext
  change (𝟙 _ ≫ (unit R C).map₂ (hF.j a).hom).1 =
    ((hF.mapTwo.toPiTwoFunctor.j ⟨⟨a⟩⟩).hom ≫ hF.mapTwo.toPseudofunctor.map₂ (𝟙 _)).1
  rw [Category.id_comp, PrelaxFunctor.map₂_id, Category.comp_id,
    TwoSuperfunctor.toPiTwoFunctor_j_hom_val, hF.jIso_mapTwo_hom]
  rfl

end Associated2

namespace PiTwoCat

variable {R : Type w} [CommRing R]

/-- **Brundan–Ellis, (5.5).** The functor `D₂ : Π-2-Cat → Π-2-SCat`, sending a Π-2-category `𝔄`
to the Π-2-supercategory `𝔄̂` (`Associated2.instPiTwoSupercategory`) and a Π-2-functor `ℝ` to
`ℝ̂` (`PiTwoFunctor.mapTwo`). -/
def toPiTwoSCat : PiTwoCat.{w, w₁, v₁, u₁} R ⥤ PiTwoSCat.{w, w₁, v₁, u₁} R where
  obj B := PiTwoSCat.of R (Associated2 R B)
  map P := P.toPiTwoFunctor.mapTwo
  map_id B := PiTwoFunctor.mapTwo_id R B
  map_comp P Q := PiTwoFunctor.mapTwo_comp P.toPiTwoFunctor Q.toPiTwoFunctor

@[simp] theorem toPiTwoSCat_obj (B : PiTwoCat.{w, w₁, v₁, u₁} R) :
    toPiTwoSCat.obj B = PiTwoSCat.of R (Associated2 R B) := rfl

@[simp] theorem toPiTwoSCat_map {B C : PiTwoCat.{w, w₁, v₁, u₁} R} (P : B ⟶ C) :
    toPiTwoSCat.map P = P.toPiTwoFunctor.mapTwo := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Lemma 5.4, `E₂ ∘ D₂ = I` on objects**, as an isomorphism `𝔄 ≅ E₂(D₂ 𝔄)` in `Π-2-Cat`:
the identification `Associated2.unit` and its inverse `Associated2.counit`. -/
def unitIso (B : PiTwoCat.{w, w₁, v₁, u₁} R) :
    B ≅ PiTwoCat.of R (Underlying2 R (Associated2 R B)) where
  hom := ⟨Associated2.unit R B, Associated2.unitPiTwoFunctor⟩
  inv := ⟨Associated2.counit R B, Associated2.counitPiTwoFunctor⟩
  hom_inv_id := BundledPiTwoFunctor.ext'
    (pseudofunctor_ext rfl HEq.rfl HEq.rfl
      (heq_of_eq (funext fun _ => funext fun _ => funext fun _ => funext fun _ => funext fun _ =>
        Iso.ext (Category.comp_id _)))
      (heq_of_eq (funext fun _ => Iso.ext (Category.comp_id _))))
    fun _ => heq_of_eq (Category.comp_id _)
  inv_hom_id := BundledPiTwoFunctor.ext'
    (pseudofunctor_ext rfl HEq.rfl
      (heq_of_eq (funext fun _ => funext fun _ => funext fun _ => funext fun _ => funext fun x =>
        Subtype.ext (Associated2.hom₂_ext rfl (Associated.mem_parity_zero.1 x.2).symm)))
      (heq_of_eq (funext fun _ => funext fun _ => funext fun _ => funext fun _ => funext fun _ =>
        Iso.ext (Category.comp_id _)))
      (heq_of_eq (funext fun _ => Iso.ext (Category.comp_id _))))
    fun _ => heq_of_eq (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
/-- **Lemma 5.4, `E₂ ∘ D₂ = I`**, as a natural isomorphism `𝟭 ≅ D₂ ⋙ E₂` of endofunctors of
`Π-2-Cat`. Naturality is `E₂(D₂ ℝ) ∘ unit = unit ∘ ℝ`, using `ĵ = j`
(`PiTwoFunctor.jIso_mapTwo_hom`). -/
def unitNatIso :
    𝟭 (PiTwoCat.{w, w₁, v₁, u₁} R) ≅ toPiTwoSCat ⋙ PiTwoSCat.toPiTwoCat :=
  NatIso.ofComponents unitIso fun {_ _} P => BundledPiTwoFunctor.ext'
    (Associated2.comp_unit P.toPiTwoFunctor) fun a =>
      heq_of_eq (Associated2.comp_unitPiTwoFunctor_j P.toPiTwoFunctor a)

end PiTwoCat

namespace QPiTwoCat

variable {R : Type w} [CommRing R]

/-- **Brundan–Ellis, §6 (the analogue of (5.5) after Definition 6.14).** The functor
`𝔻 : (Q, Π)-2-Cat → (Q, Π)-2-GSCat`, sending a `(Q, Π)`-2-category `𝔄` to the associated graded
`(Q, Π)`-2-supercategory `𝔄̂` (`QAssociated2`) and a `(Q, Π)`-2-functor `ℝ` to the graded
2-superfunctor `ℝ̂` (`QPiTwoFunctor.mapQ`, `QPiTwoFunctor.mapQ_isGraded`). -/
def toQPiTwoGSCat : QPiTwoCat.{w, w₁, v₁, u₁} R ⥤ QPiTwoGSCat.{w, w₁, v₁, u₁} R where
  obj B := QPiTwoGSCat.of R (QAssociated2 R B)
  map P := ⟨P.toQPiTwoFunctor.mapQ, P.toQPiTwoFunctor.mapQ_isGraded⟩
  map_id B := Subtype.ext (QPiTwoFunctor.mapQ_id R B)
  map_comp P Q := Subtype.ext (QPiTwoFunctor.mapQ_comp P.toQPiTwoFunctor Q.toQPiTwoFunctor)

@[simp] theorem toQPiTwoGSCat_obj (B : QPiTwoCat.{w, w₁, v₁, u₁} R) :
    toQPiTwoGSCat.obj B = QPiTwoGSCat.of R (QAssociated2 R B) := rfl

@[simp] theorem toQPiTwoGSCat_map {B C : QPiTwoCat.{w, w₁, v₁, u₁} R} (P : B ⟶ C) :
    (toQPiTwoGSCat.map P).1 = P.toQPiTwoFunctor.mapQ := rfl

end QPiTwoCat

end StringDiagrams

end
