import StringDiagrams.Super.QAssociatedTwoMap

/-!
# `𝔻` on (Q, Π)-2-natural transformations, naturality of `𝕋`, and the §6 analogue of Theorem 5.5

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6, the
discussion after Definition 6.14 (the analogue of Theorem 5.5, which the paper leaves to the
reader), for the `(Q, Π)`-2-functors and `(Q, Π)`-2-natural transformations of
`StringDiagrams.Super.QPiTwoFunctor` (definitions not given in the paper).

* **`𝔻` on 2-morphisms** (`QPiTwoFunctor.mapQNat`): a `(Q, Π)`-2-natural transformation
  `(Y, y) : ℝ ⇒ 𝕊` gives the 2-natural transformation `(Ŷ, ŷ) : ℝ̂ ⇒ 𝕊̂` with `Ŷ_λ = Y_λ` and
  `ŷ_F = (y_F, 0)` in degree zero (`QPiTwoFunctor.mapQNat_isGraded`). Its supernaturality with
  respect to the 2-morphisms `σ` of degree `-1` is the `q`-condition of a
  `(Q, Π)`-2-natural transformation (`QPiTwoFunctor.natHom_γ`,
  `QPiTwoFunctor.natHomQ_compat`); with respect to 2-morphisms of degree zero it is the
  supernaturality of `D₂(Y, y)` (`PiTwoFunctor.mapTwoNat`).
* **`𝔼 ∘ 𝔻 = 𝕀` on 2-morphisms**: `QPiTwoFunctor.mapQNat_X_eq`, `QPiTwoFunctor.mapQNat_x_eq`,
  and in terms of `𝔼`: `QPiTwoFunctor.toOplax_mapQNat_app`,
  `QPiTwoFunctor.toOplax_mapQNat_naturality`.
* **`𝔻` preserves identities and vertical composition** of 2-morphisms
  (`QPiTwoFunctor.mapQNat_id`, `QPiTwoFunctor.mapQNat_vcomp`; the `(Q, Π)`-2-natural
  transformations are closed under both: `QPiTwoFunctor.isQPiTwoNatural_id`,
  `QPiTwoFunctor.IsQPiTwoNatural.vcomp`).
* **Naturality of `𝕋_𝔅`** (`𝔻 ∘ 𝔼 ≅ 𝕀`, `StringDiagrams.Super.QAssociatedTwoT`): for a graded
  2-superfunctor `ℝ : 𝔅 → 𝔅'` between graded `(Q, Π)`-2-supercategories,
  `𝕋_{𝔅'} ∘ 𝔻(𝔼 ℝ) = ℝ ∘ 𝕋_𝔅` on 2-morphisms (`QAssociated2.T_map₂_mapQ`) and on the coherence
  maps (`QAssociated2.T_map₂_mapQ_mapComp`, `QAssociated2.T_map₂_mapQ_mapId`); both composites
  are `ℝ` on objects and 1-morphisms. The proof uses that `ℝ` is a morphism of trivialized shift
  data on the morphism supercategories (`TwoSuperfunctor.homShiftFunctor`,
  `TwoSuperfunctor.homShiftFunctor_trivCompat`), so that it commutes with the evaluation of orbit
  supercategories (`Orbit.eval_map_map`). For a graded 2-natural transformation `(X, x)`,
  `𝕋_{𝔅'}(𝔻 𝔼 (X, x)) = (X, x) 𝕋_𝔅` (`QAssociated2.T_map₂_mapQNat`).

## Not formalized

As for §5 (`StringDiagrams.Super.AssociatedTwoNat`), the strict 2-categories
`(Q, Π)-2-ℭ𝔄𝔗` and `(Q, Π)-2-𝔊𝔖ℭ𝔄𝔗` (composition of `(Q, Π)`-2-functors, whiskering of
2-morphisms by 1-morphisms) are not constructed, so the analogue of Theorem 5.5 is not stated as
a 2-equivalence of Lean bicategories; the compatibility of `𝔼` with identities and vertical
composition of graded 2-natural transformations is that of `TwoNatTrans.toOplaxTrans` on the
2-morphisms of degree zero and is not restated.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

/-! ### `𝔻` on `(Q, Π)`-2-natural transformations -/

namespace QPiTwoFunctor

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [QPiTwoCategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [QPiTwoCategory R C]
  {F G H : Pseudofunctor B C} {hF : QPiTwoFunctor R F} {hG : QPiTwoFunctor R G}
  {hH : QPiTwoFunctor R H} {η : Oplax.OplaxTrans F.toOplax G.toOplax}

open PiTwoCategory QPiTwoCategory

local notation "𝐪" => QPiTwoCategory.q (R := R)
local notation "𝛄" => QPiTwoCategory.γ (R := R)

/-- The components `x_F` of a `(Q, Π)`-2-natural transformation are compatible with `γHom`
(from the axiom `x_{q_λ} ∘ X_λ k ∘ γ_{X_λ} = k X_λ`): the `q`-analogue of
`PiTwoFunctor.natHom_isPiNatural`. -/
theorem natHom_γ (hη : hF.IsQPiTwoNatural hG η) {a b : B} (f : a ⟶ b) :
    (α_ (F.map f) (η.app b) (𝐪 (G.obj b))).hom ≫ F.map f ◁ (𝛄 (η.app b)).hom ≫
        (α_ (F.map f) (𝐪 (F.obj b)) (η.app b)).inv ≫ (hF.γHom f).hom ▷ η.app b ≫
          η.naturality (f ≫ 𝐪 b) =
      η.naturality f ▷ 𝐪 (G.obj b) ≫ (α_ (η.app a) (G.map f) (𝐪 (G.obj b))).hom ≫
        η.app a ◁ (hG.γHom f).hom := by
  have hc : (F.mapComp f (𝐪 b)).inv ▷ η.app b ≫ η.naturality (f ≫ 𝐪 b) =
      (α_ (F.map f) (F.map (𝐪 b)) (η.app b)).hom ≫ F.map f ◁ η.naturality (𝐪 b) ≫
        (α_ (F.map f) (η.app b) (G.map (𝐪 b))).inv ≫ η.naturality f ▷ G.map (𝐪 b) ≫
          (α_ (η.app a) (G.map f) (G.map (𝐪 b))).hom ≫ η.app a ◁ (G.mapComp f (𝐪 b)).inv := by
    have e := η.naturality_comp f (𝐪 b)
    simp only [Pseudofunctor.toOplax_mapComp, Pseudofunctor.toOplax_toPrelaxFunctor] at e
    rw [← cancel_mono (η.app a ◁ (G.mapComp f (𝐪 b)).hom)]
    simp only [Category.assoc, Bicategory.whiskerLeft_inv_hom, Category.comp_id]
    rw [e, Bicategory.inv_hom_whiskerRight_assoc]
  rw [γHom_hom, Bicategory.comp_whiskerRight, Category.assoc, hc]
  simp only [Pseudofunctor.toOplax_toPrelaxFunctor]
  calc _ = (α_ (F.map f) (η.app b) (𝐪 (G.obj b))).hom ≫
        F.map f ◁ ((𝛄 (η.app b)).hom ≫ (hF.k b).hom ▷ η.app b ≫ η.naturality (𝐪 b)) ≫
          (α_ (F.map f) (η.app b) (G.map (𝐪 b))).inv ≫ η.naturality f ▷ G.map (𝐪 b) ≫
            (α_ (η.app a) (G.map f) (G.map (𝐪 b))).hom ≫
              η.app a ◁ (G.mapComp f (𝐪 b)).inv := by
        bicategory
    _ = (α_ (F.map f) (η.app b) (𝐪 (G.obj b))).hom ≫ F.map f ◁ (η.app b ◁ (hG.k b).hom) ≫
          (α_ (F.map f) (η.app b) (G.map (𝐪 b))).inv ≫ η.naturality f ▷ G.map (𝐪 b) ≫
            (α_ (η.app a) (G.map f) (G.map (𝐪 b))).hom ≫
              η.app a ◁ (G.mapComp f (𝐪 b)).inv := by
        rw [hη.2 b]
    _ = ((F.map f ≫ η.app b) ◁ (hG.k b).hom ≫ η.naturality f ▷ G.map (𝐪 b)) ≫
          (α_ (η.app a) (G.map f) (G.map (𝐪 b))).hom ≫
            η.app a ◁ (G.mapComp f (𝐪 b)).inv := by
        bicategory
    _ = (η.naturality f ▷ 𝐪 (G.obj b) ≫ (η.app a ≫ G.map f) ◁ (hG.k b).hom) ≫
          (α_ (η.app a) (G.map f) (G.map (𝐪 b))).hom ≫
            η.app a ◁ (G.mapComp f (𝐪 b)).inv := by
        rw [whisker_exchange]
        rfl
    _ = _ := by
        rw [γHom_hom]
        bicategory

open CentralShift Orbit

variable (hη : hF.IsQPiTwoNatural hG η)

/-- The components `ŷ_F = (y_F, 0)` of `D₂(Y, y)`, as a natural transformation between composite
morphisms of shift data. -/
noncomputable def natHomQ (a b : Associated2 R B) :
    ((hF.homShiftFunctor R a b).comp (postShift R _
      ((PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).X b))).F ⟶
      ((hG.homShiftFunctor R a b).comp (preShift R _
        ((PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).X a))).F where
  app f := (PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).x f
  naturality _ _ θ := (PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).naturality θ

theorem natHomQ_compat (a b : Associated2 R B) (f : a ⟶ b) :
    ((hF.homShiftFunctor R a b).comp (postShift R _
        ((PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).X b))).γ.hom.app f ≫
      (natHomQ hη a b).app ((homShift R a b).Q.obj f) =
    (homShift R _ _).Q.map ((natHomQ hη a b).app f) ≫
      ((hG.homShiftFunctor R a b).comp (preShift R _
        ((PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).X a))).γ.hom.app f := by
  apply Associated2.hom₂_ext
  · simp only [natHomQ, ShiftFunctor.comp_γ_hom_app, preShift_γ_hom_app, postShift_γ_hom_app,
      QPiTwoFunctor.homShiftFunctor_γ_hom_app, QPiTwoFunctor.homShiftFunctor_F, preShift_F,
      postShift_F, TwoSuperfunctor.mapFunctor_map, TwoSuperfunctor.mapFunctor_obj,
      TwoSupercategory.postcomp_map, TwoSupercategory.postcomp_obj, TwoSupercategory.precomp_map,
      TwoSupercategory.precomp_obj, homShift_Q, Iso.symm_hom, PiTwoFunctor.homFunctor_map,
      Functor.comp_obj, γR_hom, Associated2.comp₂_fst, Associated2.comp₂_snd,
      Associated2.whiskerLeft_fst, Associated2.whiskerLeft_snd, Associated2.whiskerRight_fst,
      Associated2.whiskerRight_snd, Associated2.associator_hom_fst, Associated2.associator_hom_snd,
      Associated2.associator_inv_fst, Associated2.associator_inv_snd,
      Associated2.centralShift_γ_eq, Associated2.γhat_hom_fst, Associated2.γhat_hom_snd,
      QPiTwoFunctor.γhat_hom_app_fst, QPiTwoFunctor.γhat_hom_app_snd,
      PiTwoFunctor.mapTwoNat_x, PiTwoFunctor.mapTwoNat_X_obj, PiTwoFunctor.mapTwo_map_obj,
      Associated.homMk_fst, Associated.homMk_snd, Limits.zero_comp, Limits.comp_zero,
      PreadditiveBicategory.whiskerLeft_zero, PreadditiveBicategory.zero_whiskerRight, sub_zero,
      add_zero, zero_add, Functor.map_zero, Category.assoc]
    exact natHom_γ hη f.obj
  · simp only [natHomQ, ShiftFunctor.comp_γ_hom_app, preShift_γ_hom_app, postShift_γ_hom_app,
      QPiTwoFunctor.homShiftFunctor_γ_hom_app, QPiTwoFunctor.homShiftFunctor_F, preShift_F,
      postShift_F, TwoSuperfunctor.mapFunctor_map, TwoSuperfunctor.mapFunctor_obj,
      TwoSupercategory.postcomp_map, TwoSupercategory.postcomp_obj, TwoSupercategory.precomp_map,
      TwoSupercategory.precomp_obj, homShift_Q, Iso.symm_hom, PiTwoFunctor.homFunctor_map,
      Functor.comp_obj, γR_hom, Associated2.comp₂_fst, Associated2.comp₂_snd,
      Associated2.whiskerLeft_fst, Associated2.whiskerLeft_snd, Associated2.whiskerRight_fst,
      Associated2.whiskerRight_snd, Associated2.associator_hom_fst, Associated2.associator_hom_snd,
      Associated2.associator_inv_fst, Associated2.associator_inv_snd,
      Associated2.centralShift_γ_eq, Associated2.γhat_hom_fst, Associated2.γhat_hom_snd,
      QPiTwoFunctor.γhat_hom_app_fst, QPiTwoFunctor.γhat_hom_app_snd,
      PiTwoFunctor.mapTwoNat_x, PiTwoFunctor.mapTwoNat_X_obj, PiTwoFunctor.mapTwo_map_obj,
      Associated.homMk_fst, Associated.homMk_snd, Limits.zero_comp, Limits.comp_zero,
      PreadditiveBicategory.whiskerLeft_zero, PreadditiveBicategory.zero_whiskerRight, sub_zero,
      add_zero, zero_add, Functor.map_zero, Category.assoc]

set_option maxHeartbeats 1000000 in
/-- **`𝔻` on 2-morphisms** (the §6 analogue of (5.6)): a `(Q, Π)`-2-natural transformation
`(Y, y) : ℝ ⇒ 𝕊` gives the 2-natural transformation `(Ŷ, ŷ) : ℝ̂ ⇒ 𝕊̂` of the associated graded
`(Q, Π)`-2-supercategories, `Ŷ_λ := Y_λ` and `ŷ_F := (y_F, 0)` in degree zero. Its
supernaturality with respect to the 2-morphisms `σ` is the condition
`y_{q_λ} ∘ Y_λ k ∘ γ_{Y_λ} = k Y_λ` (`natHom_γ`). -/
noncomputable def mapQNat : TwoNatTrans hF.mapQ hG.mapQ where
  X a := ⟨(PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).X a.obj⟩
  x {a b} f := (Orbit.ι (homShift R (hF.mapQ.obj a).obj (hG.mapQ.obj b).obj)).map
    ((PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).x f.obj)
  x_mem {a b} f := map_mem (Orbit.ι (homShift R (hF.mapQ.obj a).obj (hG.mapQ.obj b).obj))
    ((PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).x_mem f.obj)
  naturality {a b f g} θ := by
    have e := map_map_comp_ι_map (natHomQ hη a.obj b.obj) (natHomQ_compat hη a.obj b.obj) θ
    rw [← map_map_comp, ← map_map_comp] at e
    exact e
  x_comp {a b c} f g := by
    simp only [Functor.mapIso_hom, mapQ_mapComp_hom']
    rw [Orbit2.whiskerRight_ι, Orbit2.whiskerLeft_ι, Orbit2.whiskerRight_ι, Orbit2.whiskerLeft_ι,
      Orbit2.associator_hom_def, Orbit2.associator_inv_def, Orbit2.associator_hom_def]
    simp only [← Functor.map_comp]
    exact congrArg (Orbit.ι (homShift R (hF.mapQ.obj a).obj (hG.mapQ.obj c).obj)).map
      ((PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).x_comp f.obj g.obj)
  x_id a := by
    simp only [Functor.mapIso_hom, mapQ_mapId_hom']
    rw [Orbit2.whiskerRight_ι, Orbit2.whiskerLeft_ι, Orbit2.rightUnitor_hom_def,
      Orbit2.leftUnitor_inv_def]
    simp only [← Functor.map_comp]
    exact congrArg (Orbit.ι (homShift R (hF.mapQ.obj a).obj (hG.mapQ.obj a).obj)).map
      ((PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).x_id a.obj)

theorem mapQNat_x {a b : QAssociated2 R B} (f : a ⟶ b) :
    (mapQNat hη).x f = (Orbit.ι (homShift R (hF.mapQ.obj a).obj (hG.mapQ.obj b).obj)).map
      ((PiTwoFunctor.mapTwoNat hF.toPiTwoFunctor hG.toPiTwoFunctor hη.1).x f.obj) := rfl

/-- `𝔻(Y, y)` is a graded 2-natural transformation (its components have degree zero). -/
theorem mapQNat_isGraded : (mapQNat hη).IsGraded := fun _ => Orbit.ι_map_mem_degree _

open QAssociated2 in
/-- **`𝔼 ∘ 𝔻 = 𝕀` on 2-morphisms**: the components of `𝔻(Y, y)` are `Y_λ` and `(y_F, 0)` in
degree zero. -/
theorem mapQNat_X_eq (a : B) : (mapQNat hη).X (⟨⟨a⟩⟩ : QAssociated2 R B) = hom1 (η.app a) := rfl

open QAssociated2 in
theorem mapQNat_x_eq {a b : B} (f : a ⟶ b) :
    (mapQNat hη).x (hom1 (R := R) f) = hom2 (η.naturality f) := rfl

/-- **`𝔼 ∘ 𝔻 = 𝕀` on 2-morphisms**, in terms of `𝔼`: under the identifications
`QAssociated2.unit`, the oplax transformation `𝔼(𝔻(Y, y))` has the components of `(Y, y)`. -/
theorem toOplax_mapQNat_naturality {a b : B} (f : a ⟶ b) :
    (((mapQNat hη).toDegreeZero2 hF.mapQ_isGraded hG.mapQ_isGraded
        (mapQNat_isGraded hη)).toOplaxTrans).naturality ((QAssociated2.unit R B).map f) =
      (QAssociated2.unit R C).map₂ (η.naturality f) := rfl

theorem toOplax_mapQNat_app (a : B) :
    (((mapQNat hη).toDegreeZero2 hF.mapQ_isGraded hG.mapQ_isGraded
        (mapQNat_isGraded hη)).toOplaxTrans).app ((QAssociated2.unit R B).obj a) =
      (QAssociated2.unit R C).map (η.app a) := rfl

omit hη in
/-- **`𝔻` preserves identity 2-morphisms.** -/
theorem mapQNat_id (hF : QPiTwoFunctor R F) :
    mapQNat (isQPiTwoNatural_id hF) = TwoNatTrans.id hF.mapQ := by
  refine TwoNatTrans.ext_of_eq rfl fun {a b} f => ?_
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rw [mapQNat_x, TwoNatTrans.id_x, Orbit2.rightUnitor_hom_def, Orbit2.leftUnitor_inv_def,
    ← Functor.map_comp]
  refine congrArg (Orbit.ι (homShift R (hF.mapQ.obj a).obj (hF.mapQ.obj b).obj)).map ?_
  simp only [PiTwoFunctor.mapTwoNat_x, Oplax.OplaxTrans.id]
  apply Associated2.hom₂_ext
  · simp
    rfl
  · simp

omit hη in
/-- **`𝔻` preserves vertical composition of 2-morphisms.** -/
theorem mapQNat_vcomp {η : Oplax.OplaxTrans F.toOplax G.toOplax}
    {θ : Oplax.OplaxTrans G.toOplax H.toOplax} (hη : hF.IsQPiTwoNatural hG η)
    (hθ : hG.IsQPiTwoNatural hH θ) :
    mapQNat (hη.vcomp hθ) = (mapQNat hη).vcomp (mapQNat hθ) := by
  refine TwoNatTrans.ext_of_eq rfl fun {a b} f => ?_
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rw [TwoNatTrans.vcomp_x, mapQNat_x, mapQNat_x, mapQNat_x, Orbit2.whiskerRight_ι,
    Orbit2.whiskerLeft_ι, Orbit2.associator_inv_def, Orbit2.associator_hom_def,
    Orbit2.associator_inv_def]
  simp only [← Functor.map_comp]
  refine congrArg (Orbit.ι (homShift R (hF.mapQ.obj a).obj (hH.mapQ.obj b).obj)).map ?_
  simp only [PiTwoFunctor.mapTwoNat_x, Oplax.OplaxTrans.vcomp]
  apply Associated2.hom₂_ext
  · simp only [Associated2.comp₂_fst, Associated2.whiskerLeft_fst, Associated2.whiskerLeft_snd,
      Associated2.whiskerRight_fst, Associated2.whiskerRight_snd, Associated2.associator_hom_fst,
      Associated2.associator_hom_snd, Associated2.associator_inv_fst,
      Associated2.associator_inv_snd, Associated.homMk_fst, Associated.homMk_snd,
      PreadditiveBicategory.zero_whiskerRight, PreadditiveBicategory.whiskerLeft_zero,
      Limits.zero_comp, Limits.comp_zero, sub_zero, Category.assoc,
      Pseudofunctor.toOplax_toPrelaxFunctor]
    rfl
  · simp only [Associated2.comp₂_snd, Associated2.whiskerLeft_fst, Associated2.whiskerLeft_snd,
      Associated2.whiskerRight_fst, Associated2.whiskerRight_snd, Associated2.associator_hom_fst,
      Associated2.associator_hom_snd, Associated2.associator_inv_fst,
      Associated2.associator_inv_snd, Associated.homMk_fst, Associated.homMk_snd,
      PreadditiveBicategory.zero_whiskerRight, PreadditiveBicategory.whiskerLeft_zero,
      Limits.zero_comp, Limits.comp_zero, add_zero, zero_add, PiTwoCategory.pi_map]

end QPiTwoFunctor

/-! ### Naturality of `𝕋` in 1-morphisms -/

namespace TwoSuperfunctor

open Supercategory GradedSupercategory BicategoryStruct TwoSupercategory CentralShift

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [∀ a b : A, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A] [GradedTwoSupercategory R A] [QPiTwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [∀ a b : A', GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A'] [GradedTwoSupercategory R A'] [QPiTwoSupercategory R A']
  (G : TwoSuperfunctor R A A')

attribute [local instance] QPiTwoSupercategory.centralShift

local notation "𝐪" => QPiTwoSupercategory.q (R := R)
local notation "𝛔" => QPiTwoSupercategory.σ (R := R)

/-- A 2-superfunctor between graded `(Q, Π)`-2-supercategories as a morphism of shift data
`(- q_μ) → (- q_{ℝμ})` on the morphism supercategories, with `γ = c ∘ (ℝX) k`. -/
noncomputable def homShiftFunctor (a b : A) :
    ShiftFunctor R (homShift R a b) (homShift R (G.obj a) (G.obj b)) where
  F := G.mapFunctor a b
  γ := NatIso.ofComponents
    (fun X => whiskerLeftIso (R := R) (G.map X) (G.kIso b) ≪≫ G.mapComp X (𝐪 b))
    (fun {X Y} x => by
      simp only [Functor.comp_obj, Functor.comp_map, mapFunctor_obj, mapFunctor_map, homShift_Q,
        postcomp_obj, postcomp_map, Iso.trans_hom, TwoSupercategory.whiskerLeftIso_hom,
        Category.assoc, QPiTwoSupercategory.centralShift_q]
      rw [whisker_exchange_of_even_right_assoc _ (G.kIso_hom_mem b),
        G.mapComp_naturality_left])
  γ_mem X := by
    simpa using comp_mem (whiskerLeft_mem (G.map X) (G.kIso_hom_mem b))
      (G.mapComp_hom_mem X (𝐪 b))

theorem homShiftFunctor_γ_hom_app {a b : A} (X : a ⟶ b) :
    (G.homShiftFunctor a b).γ.hom.app X = G.map X ◁ (G.kIso b).hom ≫ (G.mapComp X (𝐪 b)).hom :=
  rfl

theorem homShiftFunctor_F_map {a b : A} {X Y : a ⟶ b} (x : X ⟶ Y) :
    (G.homShiftFunctor a b).F.map x = G.map₂ x := rfl

/-- `ℝ` is compatible with the trivializations `σ_F = F σ_μ` of the shift data. -/
theorem homShiftFunctor_trivCompat (a b : A) :
    Orbit.IsTrivCompatible (QPiTwoSupercategory.homTriv R a b)
      (QPiTwoSupercategory.homTriv R (G.obj a) (G.obj b)) (G.homShiftFunctor a b) := fun X => by
  have h1 : (G.kIso b).inv ≫ (𝛔 (G.obj b)).hom = G.map₂ (𝛔 b).hom ≫ (G.mapId b).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, kIso_hom_comp_map₂_σ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h2 : (G.mapComp X (𝟙 b)).hom ≫ G.map₂ (rightUnitor X).hom =
      G.map X ◁ (G.mapId b).inv ≫ (rightUnitor (G.map X)).hom := by
    rw [← G.map₂_rightUnitor X, TwoSupercategory.whiskerLeft_inv_hom_assoc R]
  change ((G.mapComp X (𝐪 b)).inv ≫ G.map X ◁ (G.kIso b).inv) ≫ G.map X ◁ (𝛔 (G.obj b)).hom ≫
      (rightUnitor (G.map X)).hom = G.map₂ (X ◁ (𝛔 b).hom ≫ (rightUnitor X).hom)
  rw [G.map₂_comp, Category.assoc, ← whiskerLeft_comp'_assoc R, h1, whiskerLeft_comp'_assoc R,
    ← h2, G.mapComp_naturality_right_assoc, Iso.inv_hom_id_assoc]

end TwoSuperfunctor

namespace QAssociated2

open Supercategory GradedSupercategory BicategoryStruct TwoSupercategory CentralShift Orbit

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B] [QPiTwoSupercategory R B]
  {B' : Type u₂} [BicategoryStruct.{w₂, v₂} B']
  [∀ a b : B', Preadditive (a ⟶ b)] [∀ a b : B', Linear R (a ⟶ b)]
  [∀ a b : B', Supercategory R (a ⟶ b)] [∀ a b : B', GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B'] [GradedTwoSupercategory R B'] [QPiTwoSupercategory R B']
  (G : TwoSuperfunctor R B B') (hG : G.IsGraded)

attribute [local instance] QPiTwoSupercategory.centralShift

theorem TΦ_comp_γ_hom_app {a b : Associated2 R (GUnderlying2 R B)} {S : Type*} [Category S]
    [Preadditive S] [Linear R S] [Supercategory R S] {d : ShiftData R S}
    (Ψ : ShiftFunctor R (homShift R (bo a) (bo b)) d) (X : a ⟶ b) :
    ((TΦ R B a b).comp Ψ).γ.hom.app X = Ψ.γ.hom.app ((TF R B a b).obj X) := by
  rw [ShiftFunctor.comp_γ_hom_app, TΦ_γ_hom_app]
  exact (congrArg (Ψ.γ.hom.app ((TΦ R B a b).F.obj X) ≫ ·) (Ψ.F.map_id _)).trans
    (Category.comp_id _)

/-- The two morphisms of shift data underlying `𝕋 ∘ 𝔻(𝔼 ℝ)` and `ℝ ∘ 𝕋` agree. -/
theorem map_DE_comp_TΦ (a b : Associated2 R (GUnderlying2 R B)) :
    Orbit.map (((G.toQPiTwoFunctor hG).homShiftFunctor R a b).comp
      (TΦ R B' ((G.toQPiTwoFunctor hG).mapTwo.obj a) ((G.toQPiTwoFunctor hG).mapTwo.obj b))) =
    Orbit.map ((TΦ R B a b).comp (G.homShiftFunctor (bo a) (bo b))) := by
  refine Orbit.map_congr' (fun _ => rfl) (fun y => ?_) fun X => ?_
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact congrArg Subtype.val (Associated2.T_map₂_mapTwo (G.toDegreeZero2 hG) y)
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    rw [TΦ_comp_γ_hom_app, ShiftFunctor.comp_γ_hom_app, TΦ_γ_hom_app, Category.id_comp]
    erw [TF_map]
    simp only [Associated2.T_map₂, QPiTwoFunctor.homShiftFunctor_γ_hom_app,
      QPiTwoFunctor.γhat_hom_app_fst, QPiTwoFunctor.γhat_hom_app_snd, Underlying2.zero₂_val,
      Limits.zero_comp, add_zero]
    rfl

set_option maxHeartbeats 1000000 in
/-- **Naturality of `𝕋` in 1-morphisms** (the §6 analogue of Lemma 5.4 / Theorem 5.5): for a
graded 2-superfunctor `ℝ : 𝔅 → 𝔅'` between graded `(Q, Π)`-2-supercategories,
`𝕋_{𝔅'} ∘ 𝔻(𝔼 ℝ) = ℝ ∘ 𝕋_𝔅` on 2-morphisms (both are `ℝ` on objects and 1-morphisms). -/
theorem T_map₂_mapQ {a b : QAssociated2 R (GUnderlying2 R B)} {f g : a ⟶ b} (x : f ⟶ g) :
    (T R B').map₂ ((G.toQPiTwoFunctor hG).mapQ.map₂ x) = G.map₂ ((T R B).map₂ x) := by
  change (Orbit.eval (QPiTwoSupercategory.homTriv R (G.obj (bo a.obj)) (G.obj (bo b.obj)))).map
      ((Orbit.map (TΦ R B' ((G.toQPiTwoFunctor hG).mapTwo.obj a.obj)
        ((G.toQPiTwoFunctor hG).mapTwo.obj b.obj))).map
        ((Orbit.map ((G.toQPiTwoFunctor hG).homShiftFunctor R a.obj b.obj)).map x)) =
    (G.homShiftFunctor (bo a.obj) (bo b.obj)).F.map
      ((Orbit.eval (QPiTwoSupercategory.homTriv R (bo a.obj) (bo b.obj))).map
        ((Orbit.map (TΦ R B a.obj b.obj)).map x))
  rw [← eval_map_map (G.homShiftFunctor_trivCompat (bo a.obj) (bo b.obj))]
  rw [map_map_comp]
  rw [map_map_comp (TΦ R B a.obj b.obj) (G.homShiftFunctor (bo a.obj) (bo b.obj)) x]
  have key := CategoryTheory.Functor.congr_hom (map_DE_comp_TΦ G hG a.obj b.obj) x
  rw [key]
  simp

/-- **Naturality of `𝕋` in 1-morphisms**, on the coherence maps `c`: both composites have the
coherence maps `c` of `ℝ`. -/
theorem T_map₂_mapQ_mapComp {a b c : QAssociated2 R (GUnderlying2 R B)} (f : a ⟶ b)
    (g : b ⟶ c) :
    (T R B').map₂ ((G.toQPiTwoFunctor hG).mapQ.mapComp f g).hom =
      (G.mapComp f.obj.obj.obj.obj g.obj.obj.obj.obj).hom := by
  rw [T_map₂, QPiTwoFunctor.mapQ_mapComp_hom', Thom_ι_map, TF_map]
  simp [Associated2.T_map₂]

/-- **Naturality of `𝕋` in 1-morphisms**, on the coherence maps `i`. -/
theorem T_map₂_mapQ_mapId (a : QAssociated2 R (GUnderlying2 R B)) :
    (T R B').map₂ ((G.toQPiTwoFunctor hG).mapQ.mapId a).hom = (G.mapId a.obj.obj.obj.as).hom := by
  rw [T_map₂, QPiTwoFunctor.mapQ_mapId_hom', Thom_ι_map, TF_map]
  simp [Associated2.T_map₂]

/-- **Naturality of `𝕋` in 2-morphisms** (the §6 analogue of Theorem 5.5): for a graded 2-natural
transformation `(X, x) : ℝ ⇒ ℝ'` between graded 2-superfunctors of graded
`(Q, Π)`-2-supercategories, `𝕋_{𝔅'}(𝔻 𝔼 (X, x)) = (X, x) 𝕋_𝔅`: the components `X_λ` agree (by
definition) and `𝕋_{𝔅'}` sends `(x_F, 0)` in degree zero to `x_F`. -/
theorem T_map₂_mapQNat {G' : TwoSuperfunctor R B B'} (hG' : G'.IsGraded) (θ : TwoNatTrans G G')
    (hθ : θ.IsGraded) {a b : QAssociated2 R (GUnderlying2 R B)} (f : a ⟶ b) :
    (T R B').map₂ ((QPiTwoFunctor.mapQNat (θ.isQPiTwoNatural hG hG' hθ)).x f) =
      θ.x f.obj.obj.obj.obj := by
  rw [T_map₂, QPiTwoFunctor.mapQNat_x, Thom_ι_map, TF_map]
  simp [Associated2.T_map₂]

end QAssociated2

end StringDiagrams

end
