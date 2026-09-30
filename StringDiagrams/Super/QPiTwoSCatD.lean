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
