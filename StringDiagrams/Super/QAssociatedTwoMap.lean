import StringDiagrams.Super.QPiTwoFunctor
import StringDiagrams.Super.QAssociatedTwoT

/-!
# `𝔻` on (Q, Π)-2-functors, and the §6 analogue of Theorem 5.5 on 1-morphisms

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6, the
discussion after Definition 6.14 (the analogue of Theorem 5.5, which the paper leaves to the
reader), for the `(Q, Π)`-2-functors of `StringDiagrams.Super.QPiTwoFunctor` (a definition not
given in the paper).

* A `(Q, Π)`-2-functor `ℝ : 𝔄 → 𝔅` gives, for all objects `λ, μ` of the Π-2-supercategory `𝔄̂`
  of (5.5), a morphism of shift data `(- q_μ) → (- q_{ℝμ})` on the morphism supercategories
  (`QPiTwoFunctor.homShiftFunctor`): the superfunctor `ℋom_𝔄̂(λ, μ) → ℋom_𝔅̂(ℝλ, ℝμ)` of
  `D₂ ℝ` (`PiTwoFunctor.mapTwo`) with the even isomorphism `γ̂_G = (c ∘ (ℝG) k, 0)`
  (`QPiTwoFunctor.γhat`). Its naturality with respect to the odd 2-morphisms of `𝔄̂` is the
  compatibility of `k` with `j` (`QPiTwoFunctor.j_comm`, through `QPiTwoFunctor.homQPi`).
* **`𝔻` on 1-morphisms** (`QPiTwoFunctor.mapQ`): the 2-superfunctor
  `ℝ̂ : 𝔄̂ → 𝔅̂` between the associated graded `(Q, Π)`-2-supercategories
  (`QAssociated2`, the orbit 2-supercategories of `StringDiagrams.Super.OrbitTwo`): `ℝ` on
  objects and 1-morphisms, the orbit functors of `homShiftFunctor` on 2-morphisms, and the
  coherence maps of `D₂ ℝ` in degree zero. The coherence maps are natural with respect to all
  2-morphisms, including the 2-morphisms `σ` of degree `-1`: for `c` in the second variable this
  is the axiom `QPiTwoFunctor.γ_comm` (`QPiTwoFunctor.mapCompLeft_γ`). `ℝ̂` is graded
  (`QPiTwoFunctor.mapQ_isGraded`).
* **`𝔼 ∘ 𝔻 = 𝕀` on 1-morphisms**: under the identifications `QAssociated2.unit` (the identity on
  objects and 1-morphisms), `𝔼(ℝ̂)` agrees with `ℝ` on 2-morphisms, on the coherence maps and on
  `j` and `k` (`QPiTwoFunctor.mapQ_map₂_hom2`, `QPiTwoFunctor.mapQ_mapComp_hom`,
  `QPiTwoFunctor.mapQ_mapId_hom`, `QPiTwoFunctor.jIso_mapQ_hom`, `QPiTwoFunctor.kIso_mapQ_hom`,
  and in terms of `𝔼` of `StringDiagrams.Super.QPiTwoFunctor`:
  `QPiTwoFunctor.toQPiTwoFunctor_mapQ_map₂`, `QPiTwoFunctor.toQPiTwoFunctor_mapQ_mapComp`,
  `QPiTwoFunctor.toQPiTwoFunctor_mapQ_mapId`, `QPiTwoFunctor.toQPiTwoFunctor_mapQ_j`,
  `QPiTwoFunctor.toQPiTwoFunctor_mapQ_k`).
* **Naturality of `𝕋` in 1-morphisms**: for a graded 2-superfunctor `ℝ : 𝔅 → 𝔅'` between graded
  `(Q, Π)`-2-supercategories, `𝕋_{𝔅'} ∘ 𝔻(𝔼 ℝ) = ℝ ∘ 𝕋_𝔅` on 2-morphisms
  (`QAssociated2.T_map₂_mapQ`) and on the coherence maps (`QAssociated2.T_map₂_mapQ_mapComp`,
  `QAssociated2.T_map₂_mapQ_mapId`); both composites are `ℝ` on objects and 1-morphisms. The
  proof uses that `ℝ` is a morphism of trivialized shift data on the morphism supercategories
  (`TwoSuperfunctor.homShiftFunctor`, `TwoSuperfunctor.homShiftFunctor_trivCompat`), so that it
  commutes with the evaluation of orbit supercategories (`Orbit.eval_map_map`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace QPiTwoFunctor

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [QPiTwoCategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [QPiTwoCategory R C]
  {F : Pseudofunctor B C} (hF : QPiTwoFunctor R F)

open PiTwoCategory QPiTwoCategory

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝐪" => QPiTwoCategory.q (R := R)
local notation "𝛄" => QPiTwoCategory.γ (R := R)

/-! ### The coherence maps `c` and the isomorphisms `γHom` -/

/-- The coherence map `c` in the second variable is compatible with `γ` (from the axiom
`γ_comm`): the `q`-analogue of `PiTwoFunctor.mapCompLeft_isPiNatural`. -/
theorem mapCompLeft_γ {a b c : B} (f : a ⟶ b) (h : b ⟶ c) :
    (α_ (F.map f) (F.map h) (𝐪 (F.obj c))).hom ≫ F.map f ◁ (𝛄 (F.map h)).hom ≫
        (α_ (F.map f) (𝐪 (F.obj b)) (F.map h)).inv ≫ (hF.γHom f).hom ▷ F.map h ≫
          (F.mapComp (f ≫ 𝐪 b) h).inv =
      (F.mapComp f h).inv ▷ 𝐪 (F.obj c) ≫ (hF.γHom (f ≫ h)).hom ≫
        F.map₂ ((α_ f h (𝐪 c)).hom ≫ f ◁ (𝛄 h).hom ≫ (α_ f (𝐪 b) h).inv) := by
  have hγ : F.map h ◁ (hF.k c).hom ≫ (F.mapComp h (𝐪 c)).inv ≫ F.map₂ (𝛄 h).hom ≫
      (F.mapComp (𝐪 b) h).hom = (𝛄 (F.map h)).hom ≫ (hF.k b).hom ▷ F.map h := by
    rw [reassoc_of% (hF.γ_comm h)]
    simp
  rw [γHom_hom, γHom_hom, F.map₂_comp, F.map₂_comp, Pseudofunctor.map₂_associator,
    Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_associator_inv']
  simp only [Bicategory.comp_whiskerRight, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_assoc (F.mapComp f h).inv (hF.k c).hom,
    Bicategory.inv_hom_whiskerRight_assoc]
  calc _ = (α_ (F.map f) (F.map h) (𝐪 (F.obj c))).hom ≫
        F.map f ◁ ((𝛄 (F.map h)).hom ≫ (hF.k b).hom ▷ F.map h) ≫
          (α_ (F.map f) (F.map (𝐪 b)) (F.map h)).inv ≫ (F.mapComp f (𝐪 b)).inv ▷ F.map h ≫
            (F.mapComp (f ≫ 𝐪 b) h).inv := by
        bicategory
    _ = (α_ (F.map f) (F.map h) (𝐪 (F.obj c))).hom ≫
        F.map f ◁ (F.map h ◁ (hF.k c).hom ≫ (F.mapComp h (𝐪 c)).inv ≫ F.map₂ (𝛄 h).hom ≫
          (F.mapComp (𝐪 b) h).hom) ≫
          (α_ (F.map f) (F.map (𝐪 b)) (F.map h)).inv ≫ (F.mapComp f (𝐪 b)).inv ▷ F.map h ≫
            (F.mapComp (f ≫ 𝐪 b) h).inv := by
        rw [hγ]
    _ = _ := by bicategory

/-- The coherence map `c` in the first variable is compatible with `γ` (a coherence statement):
the `q`-analogue of `PiTwoFunctor.mapCompRight_isPiNatural`. -/
theorem mapCompRight_γ {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (α_ (F.map f) (F.map g) (𝐪 (F.obj c))).hom ≫ F.map f ◁ (hF.γHom g).hom ≫
        (F.mapComp f (g ≫ 𝐪 c)).inv =
      (F.mapComp f g).inv ▷ 𝐪 (F.obj c) ≫ (hF.γHom (f ≫ g)).hom ≫ F.map₂ (α_ f g (𝐪 c)).hom := by
  rw [γHom_hom, γHom_hom, Pseudofunctor.map₂_associator]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_assoc (F.mapComp f g).inv (hF.k c).hom,
    Bicategory.inv_hom_whiskerRight_assoc]
  bicategory

/-! ### The morphisms of shift data -/

open CentralShift Associated2

/-- `γ̂_G := (c ∘ (ℝG) k, 0) : (ℝ̂G) q_{ℝμ} ≅ ℝ̂(G q_μ)`, an even isomorphism of `𝔅̂`, natural with
respect to all 2-morphisms of `𝔄̂` (for the odd ones, by the compatibility of `k` with `j`). -/
noncomputable def γhat (a b : Associated2 R B) :
    hF.mapTwo.mapFunctor a b ⋙ (homShift R (hF.mapTwo.obj a) (hF.mapTwo.obj b)).Q ≅
      (homShift R a b).Q ⋙ hF.mapTwo.mapFunctor a b :=
  NatIso.ofComponents (fun g => Associated.evenIso (hF.γHom g.obj)) (fun {g g'} x => by
    have e := Associated.map_naturality (hF.homQPi R a.obj b.obj).isCompatible x
    rw [← map_map_map, ← map_map_map] at e
    exact e)

@[simp] theorem γhat_hom_app_fst {a b : Associated2 R B} (g : a ⟶ b) :
    ((hF.γhat a b).hom.app g).1 = (hF.γHom g.obj).hom := rfl

@[simp] theorem γhat_hom_app_snd {a b : Associated2 R B} (g : a ⟶ b) :
    ((hF.γhat a b).hom.app g).2 = 0 := rfl

variable (R) in
/-- The morphism of shift data `(- q_μ) → (- q_{ℝμ})` given by `D₂ ℝ` on `ℋom_𝔄̂(λ, μ)`, with
`γ = γ̂`. -/
noncomputable def homShiftFunctor (a b : Associated2 R B) :
    ShiftFunctor R (homShift R a b) (homShift R (hF.mapTwo.obj a) (hF.mapTwo.obj b)) where
  F := hF.mapTwo.mapFunctor a b
  γ := hF.γhat a b
  γ_mem _ := Associated.mem_parity_zero.2 rfl

@[simp] theorem homShiftFunctor_F (a b : Associated2 R B) :
    (hF.homShiftFunctor R a b).F = hF.mapTwo.mapFunctor a b := rfl

@[simp] theorem homShiftFunctor_γ_hom_app {a b : Associated2 R B} (g : a ⟶ b) :
    (hF.homShiftFunctor R a b).γ.hom.app g = (hF.γhat a b).hom.app g := rfl

/-- `c : (ℝ̂F)(ℝ̂H) ⇒ ℝ̂(F H)` as a natural transformation in `F` between the composite morphisms
of shift data. -/
noncomputable def mapCompLeftNat (a : Associated2 R B) {b c : Associated2 R B} (h : b ⟶ c) :
    ((hF.homShiftFunctor R a b).comp (postShift R _ (hF.mapTwo.map h))).F ⟶
      ((postShift R a h).comp (hF.homShiftFunctor R a c)).F where
  app f := (hF.mapTwo.mapComp f h).hom
  naturality _ _ x := hF.mapTwo.mapComp_naturality_left x h

theorem mapCompLeftNat_compat (a : Associated2 R B) {b c : Associated2 R B} (h : b ⟶ c)
    (f : a ⟶ b) :
    ((hF.homShiftFunctor R a b).comp (postShift R _ (hF.mapTwo.map h))).γ.hom.app f ≫
        (hF.mapCompLeftNat a h).app ((homShift R a b).Q.obj f) =
      (homShift R _ _).Q.map ((hF.mapCompLeftNat a h).app f) ≫
        ((postShift R a h).comp (hF.homShiftFunctor R a c)).γ.hom.app f := by
  apply hom₂_ext
  · simp only [ShiftFunctor.comp_γ_hom_app, postShift_γ_hom_app, homShiftFunctor_γ_hom_app,
      homShiftFunctor_F, postShift_F, TwoSuperfunctor.mapFunctor_map,
      TwoSuperfunctor.mapFunctor_obj, TwoSupercategory.postcomp_map, TwoSupercategory.postcomp_obj,
      homShift_Q, mapCompLeftNat, Iso.symm_hom, PiTwoFunctor.homFunctor_map, Functor.comp_obj,
      γR_hom, comp₂_fst, comp₂_snd, whiskerLeft_fst, whiskerLeft_snd, whiskerRight_fst,
      whiskerRight_snd, associator_hom_fst, associator_hom_snd, associator_inv_fst,
      associator_inv_snd, centralShift_γ_eq, Associated2.γhat_hom_fst, Associated2.γhat_hom_snd,
      γhat_hom_app_fst, γhat_hom_app_snd, PiTwoFunctor.mapTwo_mapComp, Associated.evenIso_hom,
      Associated.homMk_fst, Associated.homMk_snd, PiTwoFunctor.mapTwo_map₂, Associated.map_map,
      Limits.zero_comp, Limits.comp_zero, PreadditiveBicategory.whiskerLeft_zero,
      PreadditiveBicategory.zero_whiskerRight, sub_zero, add_zero, zero_add, Functor.map_zero,
      Category.assoc]
    exact hF.mapCompLeft_γ f.obj h.obj
  · simp only [ShiftFunctor.comp_γ_hom_app, postShift_γ_hom_app, homShiftFunctor_γ_hom_app,
      homShiftFunctor_F, postShift_F, TwoSuperfunctor.mapFunctor_map,
      TwoSuperfunctor.mapFunctor_obj, TwoSupercategory.postcomp_map, TwoSupercategory.postcomp_obj,
      homShift_Q, mapCompLeftNat, Iso.symm_hom, PiTwoFunctor.homFunctor_map, Functor.comp_obj,
      γR_hom, comp₂_fst, comp₂_snd, whiskerLeft_fst, whiskerLeft_snd, whiskerRight_fst,
      whiskerRight_snd, associator_hom_fst, associator_hom_snd, associator_inv_fst,
      associator_inv_snd, centralShift_γ_eq, Associated2.γhat_hom_fst, Associated2.γhat_hom_snd,
      γhat_hom_app_fst, γhat_hom_app_snd, PiTwoFunctor.mapTwo_mapComp, Associated.evenIso_hom,
      Associated.homMk_fst, Associated.homMk_snd, PiTwoFunctor.mapTwo_map₂, Associated.map_map,
      Limits.zero_comp, Limits.comp_zero, PreadditiveBicategory.whiskerLeft_zero,
      PreadditiveBicategory.zero_whiskerRight, add_zero, zero_add, Functor.map_zero]
    rw [hF.toPiTwoFunctor.map₂_zero]
    simp

/-- `c : (ℝ̂F)(ℝ̂G) ⇒ ℝ̂(F G)` as a natural transformation in `G` between the composite morphisms
of shift data. -/
noncomputable def mapCompRightNat (c : Associated2 R B) {a b : Associated2 R B} (f : a ⟶ b) :
    ((hF.homShiftFunctor R b c).comp (preShift R _ (hF.mapTwo.map f))).F ⟶
      ((preShift R c f).comp (hF.homShiftFunctor R a c)).F where
  app g := (hF.mapTwo.mapComp f g).hom
  naturality _ _ x := hF.mapTwo.mapComp_naturality_right f x

theorem mapCompRightNat_compat (c : Associated2 R B) {a b : Associated2 R B} (f : a ⟶ b)
    (g : b ⟶ c) :
    ((hF.homShiftFunctor R b c).comp (preShift R _ (hF.mapTwo.map f))).γ.hom.app g ≫
        (hF.mapCompRightNat c f).app ((homShift R b c).Q.obj g) =
      (homShift R _ _).Q.map ((hF.mapCompRightNat c f).app g) ≫
        ((preShift R c f).comp (hF.homShiftFunctor R a c)).γ.hom.app g := by
  apply hom₂_ext
  · simp only [mapCompRightNat, ShiftFunctor.comp_γ_hom_app, preShift_γ_hom_app, postShift_γ_hom_app,
      homShiftFunctor_γ_hom_app, homShiftFunctor_F, preShift_F, postShift_F,
      TwoSuperfunctor.mapFunctor_map, TwoSuperfunctor.mapFunctor_obj,
      TwoSupercategory.postcomp_map, TwoSupercategory.postcomp_obj, TwoSupercategory.precomp_map,
      TwoSupercategory.precomp_obj, homShift_Q, Iso.symm_hom, PiTwoFunctor.homFunctor_map,
      Functor.comp_obj, γR_hom, comp₂_fst, comp₂_snd, whiskerLeft_fst, whiskerLeft_snd,
      whiskerRight_fst, whiskerRight_snd, associator_hom_fst, associator_hom_snd,
      associator_inv_fst, associator_inv_snd, centralShift_γ_eq, Associated2.γhat_hom_fst,
      Associated2.γhat_hom_snd, γhat_hom_app_fst, γhat_hom_app_snd, PiTwoFunctor.mapTwo_mapComp,
      Associated.evenIso_hom, Associated.homMk_fst, Associated.homMk_snd,
      PiTwoFunctor.mapTwo_map₂, Associated.map_map, Limits.zero_comp, Limits.comp_zero,
      PreadditiveBicategory.whiskerLeft_zero, PreadditiveBicategory.zero_whiskerRight, sub_zero,
      add_zero, zero_add, Functor.map_zero, Category.assoc]
    exact hF.mapCompRight_γ f.obj g.obj
  · simp only [mapCompRightNat, ShiftFunctor.comp_γ_hom_app, preShift_γ_hom_app, postShift_γ_hom_app,
      homShiftFunctor_γ_hom_app, homShiftFunctor_F, preShift_F, postShift_F,
      TwoSuperfunctor.mapFunctor_map, TwoSuperfunctor.mapFunctor_obj,
      TwoSupercategory.postcomp_map, TwoSupercategory.postcomp_obj, TwoSupercategory.precomp_map,
      TwoSupercategory.precomp_obj, homShift_Q, Iso.symm_hom, PiTwoFunctor.homFunctor_map,
      Functor.comp_obj, γR_hom, comp₂_fst, comp₂_snd, whiskerLeft_fst, whiskerLeft_snd,
      whiskerRight_fst, whiskerRight_snd, associator_hom_fst, associator_hom_snd,
      associator_inv_fst, associator_inv_snd, centralShift_γ_eq, Associated2.γhat_hom_fst,
      Associated2.γhat_hom_snd, γhat_hom_app_fst, γhat_hom_app_snd, PiTwoFunctor.mapTwo_mapComp,
      Associated.evenIso_hom, Associated.homMk_fst, Associated.homMk_snd,
      PiTwoFunctor.mapTwo_map₂, Associated.map_map, Limits.zero_comp, Limits.comp_zero,
      PreadditiveBicategory.whiskerLeft_zero, PreadditiveBicategory.zero_whiskerRight, sub_zero,
      add_zero, zero_add, Functor.map_zero, Category.assoc]
    rw [hF.toPiTwoFunctor.map₂_zero]
    simp

set_option maxHeartbeats 1000000 in
open Orbit in
/-- **`𝔻` on 1-morphisms** (the §6 analogue of (5.5); the paper leaves it to the reader): a
`(Q, Π)`-2-functor `ℝ : 𝔄 → 𝔅` gives the 2-superfunctor `ℝ̂ : 𝔄̂ → 𝔅̂` between the associated
graded `(Q, Π)`-2-supercategories: `ℝ` on objects and 1-morphisms, the orbit functors of
`homShiftFunctor` on 2-morphisms (`ℝ̂ x = (ℝ x, 0)` in degree zero, and `ℝ̂ σ` given by `k`), and
the coherence maps of `D₂ ℝ` in degree zero. -/
noncomputable def mapQ : TwoSuperfunctor R (QAssociated2 R B) (QAssociated2 R C) where
  obj a := ⟨hF.mapTwo.obj a.obj⟩
  map f := ⟨hF.mapTwo.map f.obj⟩
  map₂ {a b _ _} x := (Orbit.map (hF.homShiftFunctor R a.obj b.obj)).map x
  map₂_id {a b} f := (Orbit.map (hF.homShiftFunctor R a.obj b.obj)).map_id f
  map₂_comp {a b _ _ _} x y := (Orbit.map (hF.homShiftFunctor R a.obj b.obj)).map_comp x y
  map₂_add {a b _ _} _ _ := (Orbit.map (hF.homShiftFunctor R a.obj b.obj)).map_add
  map₂_smul {a b _ _} r x :=
    Functor.Linear.map_smul (F := Orbit.map (hF.homShiftFunctor R a.obj b.obj)) x r
  map₂_mem {a b _ _ _ _} hx := map_mem (Orbit.map (hF.homShiftFunctor R a.obj b.obj)) hx
  mapComp {a b c} f g := (Orbit.ι (homShift R (hF.mapTwo.obj a.obj) (hF.mapTwo.obj c.obj))).mapIso
    (hF.mapTwo.mapComp f.obj g.obj)
  mapId a := (Orbit.ι (homShift R (hF.mapTwo.obj a.obj) (hF.mapTwo.obj a.obj))).mapIso
    (hF.mapTwo.mapId a.obj)
  mapComp_hom_mem {a b c} f g := map_mem
    (Orbit.ι (homShift R (hF.mapTwo.obj a.obj) (hF.mapTwo.obj c.obj)))
    (hF.mapTwo.mapComp_hom_mem f.obj g.obj)
  mapId_hom_mem a := map_mem (Orbit.ι (homShift R (hF.mapTwo.obj a.obj) (hF.mapTwo.obj a.obj)))
    (hF.mapTwo.mapId_hom_mem a.obj)
  mapComp_naturality_left {a b c f f'} x h := by
    have e := map_map_comp_ι_map (hF.mapCompLeftNat a.obj h.obj)
      (hF.mapCompLeftNat_compat a.obj h.obj) x
    rw [← map_map_comp, ← map_map_comp] at e
    exact e
  mapComp_naturality_right {a b c} f g g' x := by
    have e := map_map_comp_ι_map (hF.mapCompRightNat c.obj f.obj)
      (hF.mapCompRightNat_compat c.obj f.obj) x
    rw [← map_map_comp, ← map_map_comp] at e
    exact e
  map₂_associator {a b c d} f g h := by
    simp only [Functor.mapIso_hom]
    rw [Orbit2.whiskerLeft_ι, Orbit2.associator_inv_def, map_ι_map, Orbit2.associator_inv_def,
      Orbit2.whiskerRight_ι, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp]
    exact congrArg (Orbit.ι (homShift R (hF.mapTwo.obj a.obj) (hF.mapTwo.obj d.obj))).map
      (hF.mapTwo.map₂_associator f.obj g.obj h.obj)
  map₂_leftUnitor {a b} f := by
    simp only [Functor.mapIso_hom]
    erw [Orbit2.whiskerRight_ι, Orbit2.leftUnitor_hom_def, map_ι_map, Orbit2.leftUnitor_hom_def,
      ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Orbit.ι (homShift R (hF.mapTwo.obj a.obj) (hF.mapTwo.obj b.obj))).map
      (hF.mapTwo.map₂_leftUnitor f.obj)
  map₂_rightUnitor {a b} f := by
    simp only [Functor.mapIso_hom]
    erw [Orbit2.whiskerLeft_ι, Orbit2.rightUnitor_hom_def, map_ι_map, Orbit2.rightUnitor_hom_def,
      ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Orbit.ι (homShift R (hF.mapTwo.obj a.obj) (hF.mapTwo.obj b.obj))).map
      (hF.mapTwo.map₂_rightUnitor f.obj)

theorem mapQ_map₂ {a b : QAssociated2 R B} {f g : a ⟶ b} (x : f ⟶ g) :
    hF.mapQ.map₂ x = (Orbit.map (hF.homShiftFunctor R a.obj b.obj)).map x := rfl

theorem mapQ_mapComp_hom' {a b c : QAssociated2 R B} (f : a ⟶ b) (g : b ⟶ c) :
    (hF.mapQ.mapComp f g).hom = (Orbit.ι _).map (hF.mapTwo.mapComp f.obj g.obj).hom := rfl

theorem mapQ_mapId_hom' (a : QAssociated2 R B) :
    (hF.mapQ.mapId a).hom = (Orbit.ι _).map (hF.mapTwo.mapId a.obj).hom := rfl

open Orbit in
/-- **`𝔻 ℝ` is a graded 2-superfunctor** (Definition 6.3). -/
theorem mapQ_isGraded : hF.mapQ.IsGraded where
  map₂_mem_degree {a b _ _ _ _} hx :=
    GradedSupercategory.map_mem_degree (Orbit.map (hF.homShiftFunctor R a.obj b.obj)) hx
  mapComp_hom_mem_degree _ _ := ι_map_mem_degree _
  mapId_hom_mem_degree _ := ι_map_mem_degree _

/-! ### `𝔼 ∘ 𝔻 = 𝕀` on 1-morphisms -/

/-- `k = ℝλ ∘ c ∘ (ℝ1) k ∘ i q_{ℝλ} ∘ λ⁻¹` (pseudofunctor coherence). -/
theorem k_eq_γHom_id (a : B) :
    (λ_ (𝐪 (F.obj a))).inv ≫ (F.mapId a).inv ▷ 𝐪 (F.obj a) ≫ (hF.γHom (𝟙 a)).hom ≫
        F.map₂ (λ_ (𝐪 a)).hom = (hF.k a).hom := by
  rw [γHom_hom, Pseudofunctor.map₂_left_unitor]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_assoc, Bicategory.inv_hom_whiskerRight_assoc,
    Bicategory.leftUnitor_naturality, Iso.inv_hom_id_assoc]

open QAssociated2

/-- **`𝔼 ∘ 𝔻 = 𝕀` on 2-morphisms of 1-morphisms**: `ℝ̂(x, 0) = (ℝx, 0)` in degree zero. -/
theorem mapQ_map₂_hom2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    hF.mapQ.map₂ (hom2 (R := R) η) = hom2 (F.map₂ η) := by
  rw [mapQ_map₂, hom2, Orbit.map_ι_map]
  congr 1
  apply Associated2.hom₂_ext
  · rfl
  · simp only [homShiftFunctor_F, TwoSuperfunctor.mapFunctor_map, PiTwoFunctor.mapTwo_map₂,
      Associated.map_map, Associated.homMk_snd, Functor.map_zero, Limits.zero_comp]

/-- **`𝔼 ∘ 𝔻 = 𝕀`, the coherence maps `c`.** -/
theorem mapQ_mapComp_hom {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (hF.mapQ.mapComp (hom1 (R := R) f) (hom1 g)).hom = hom2 (F.mapComp f g).inv := rfl

/-- **`𝔼 ∘ 𝔻 = 𝕀`, the coherence maps `i`.** -/
theorem mapQ_mapId_hom (a : B) :
    (hF.mapQ.mapId (⟨⟨a⟩⟩ : QAssociated2 R B)).hom = hom2 (F.mapId a).inv := rfl

theorem jIso_mapQ_hom' (a : QAssociated2 R B) :
    (hF.mapQ.jIso a).hom = (Orbit.ι _).map (hF.mapTwo.jIso a.obj).hom := by
  rw [TwoSuperfunctor.jIso_hom, TwoSuperfunctor.jIso_hom, Functor.map_comp, Functor.map_comp,
    mapQ_map₂]
  erw [Orbit.map_ι_map]
  rfl

/-- **`𝔼 ∘ 𝔻 = 𝕀`, the coherence maps `j`**: the `j` of `𝔼(ℝ̂)` is `j`. -/
theorem jIso_mapQ_hom (a : B) :
    (hF.mapQ.jIso (⟨⟨a⟩⟩ : QAssociated2 R B)).hom = hom2 (hF.j a).hom := by
  rw [jIso_mapQ_hom', hF.toPiTwoFunctor.jIso_mapTwo_hom]
  rfl

/-- **`𝔼 ∘ 𝔻 = 𝕀`, the coherence maps `k`**: the `k` of `𝔼(ℝ̂)`, `(ℝ̂σ)⁻¹ ∘ i ∘ σ`, is `k`. -/
theorem kIso_mapQ_hom (a : B) :
    (hF.mapQ.kIso (⟨⟨a⟩⟩ : QAssociated2 R B)).hom = hom2 (hF.k a).hom := by
  have e : (QPiTwoSupercategory.σ (R := R) (⟨⟨a⟩⟩ : QAssociated2 R B)).inv =
      (Orbit.σIso (⟨𝟙 (⟨a⟩ : Associated2 R B)⟩ : (⟨⟨a⟩⟩ : QAssociated2 R B) ⟶ ⟨⟨a⟩⟩)).inv ≫
        (Orbit.ι (homShift R (⟨a⟩ : Associated2 R B) ⟨a⟩)).map
          (BicategoryStruct.leftUnitor (CentralShift.q (R := R) (⟨a⟩ : Associated2 R B))).hom := by
    simp [Orbit2.σ_eq, Orbit2.σ]
  rw [TwoSuperfunctor.kIso_hom]
  change (QPiTwoSupercategory.σ (R := R) (⟨hF.mapTwo.obj ⟨a⟩⟩ : QAssociated2 R C)).hom ≫
    (Orbit.ι (homShift R (hF.mapTwo.obj (⟨a⟩ : Associated2 R B))
      (hF.mapTwo.obj (⟨a⟩ : Associated2 R B)))).map (hF.mapTwo.mapId ⟨a⟩).hom ≫
    (Orbit.map (hF.homShiftFunctor R ⟨a⟩ ⟨a⟩)).map
      (QPiTwoSupercategory.σ (R := R) (⟨⟨a⟩⟩ : QAssociated2 R B)).inv = _
  rw [e, Orbit2.σ_eq, Orbit2.σ_hom, Functor.map_comp, Orbit.map_σIso_inv, Orbit.map_ι_map]
  simp only [Category.assoc]
  have hn : (Orbit.σIso (⟨𝟙 (hF.mapTwo.obj (⟨a⟩ : Associated2 R B))⟩ :
      Orbit (homShift R (hF.mapTwo.obj (⟨a⟩ : Associated2 R B))
        (hF.mapTwo.obj (⟨a⟩ : Associated2 R B))))).hom ≫
      (Orbit.ι (homShift R (hF.mapTwo.obj (⟨a⟩ : Associated2 R B))
        (hF.mapTwo.obj (⟨a⟩ : Associated2 R B)))).map (hF.mapTwo.mapId ⟨a⟩).hom =
      (Orbit.ι (homShift R (hF.mapTwo.obj (⟨a⟩ : Associated2 R B))
        (hF.mapTwo.obj (⟨a⟩ : Associated2 R B)))).map
          ((homShift R _ _).Q.map (hF.mapTwo.mapId ⟨a⟩).hom) ≫
        (Orbit.σIso (⟨hF.mapTwo.map (𝟙 (⟨a⟩ : Associated2 R B))⟩ :
          Orbit (homShift R (hF.mapTwo.obj (⟨a⟩ : Associated2 R B))
            (hF.mapTwo.obj (⟨a⟩ : Associated2 R B))))).hom :=
    Orbit.σIso_hom_naturality _
  rw [reassoc_of% hn]
  simp only [homShiftFunctor_F, TwoSuperfunctor.mapFunctor_obj]
  rw [Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  refine congrArg (Orbit.ι (homShift R (hF.mapTwo.obj (⟨a⟩ : Associated2 R B))
    (hF.mapTwo.obj (⟨a⟩ : Associated2 R B)))).map ?_
  apply Associated2.hom₂_ext
  · simp only [comp₂_fst, comp₂_snd, Associated2.leftUnitor_inv_fst,
      Associated2.leftUnitor_inv_snd, Associated2.leftUnitor_hom_fst, Associated2.leftUnitor_hom_snd,
      homShift_Q, TwoSupercategory.postcomp_map, whiskerRight_fst, whiskerRight_snd,
      homShiftFunctor_γ_hom_app, γhat_hom_app_fst, γhat_hom_app_snd, PiTwoFunctor.mapTwo_mapId,
      Associated.evenIso_hom, Associated.homMk_fst, Associated.homMk_snd, Iso.symm_hom,
      TwoSuperfunctor.mapFunctor_map, PiTwoFunctor.mapTwo_map₂, Associated.map_map,
      PiTwoFunctor.homFunctor_map, Limits.zero_comp, Limits.comp_zero,
      PreadditiveBicategory.zero_whiskerRight, sub_zero, add_zero, zero_add, Functor.map_zero,
      Category.assoc]
    exact hF.k_eq_γHom_id a
  · simp only [comp₂_fst, comp₂_snd, Associated2.leftUnitor_inv_fst,
      Associated2.leftUnitor_inv_snd, Associated2.leftUnitor_hom_fst, Associated2.leftUnitor_hom_snd,
      homShift_Q, TwoSupercategory.postcomp_map, whiskerRight_fst, whiskerRight_snd,
      homShiftFunctor_γ_hom_app, γhat_hom_app_fst, γhat_hom_app_snd, PiTwoFunctor.mapTwo_mapId,
      Associated.evenIso_hom, Associated.homMk_fst, Associated.homMk_snd, Iso.symm_hom,
      TwoSuperfunctor.mapFunctor_map, PiTwoFunctor.mapTwo_map₂, Associated.map_map,
      PiTwoFunctor.homFunctor_map, Limits.zero_comp, Limits.comp_zero,
      PreadditiveBicategory.zero_whiskerRight, sub_zero, add_zero, zero_add, Functor.map_zero,
      Category.assoc]
    rw [hF.toPiTwoFunctor.map₂_zero]
    simp

/-! #### In terms of the 2-functor `𝔼` -/

/-- **`𝔼 ∘ 𝔻 = 𝕀` on 1-morphisms**, on 2-morphisms: `𝔼(ℝ̂) ∘ unit = unit ∘ ℝ`. -/
theorem toQPiTwoFunctor_mapQ_map₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    (hF.mapQ.toDegreeZero2 hF.mapQ_isGraded).toPseudofunctor.map₂
        ((QAssociated2.unit R B).map₂ η) = (QAssociated2.unit R C).map₂ (F.map₂ η) :=
  Subtype.ext (Subtype.ext (hF.mapQ_map₂_hom2 η))

/-- **`𝔼 ∘ 𝔻 = 𝕀` on 1-morphisms**, the coherence maps `c` (`unit` is strict). -/
theorem toQPiTwoFunctor_mapQ_mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    ((hF.mapQ.toDegreeZero2 hF.mapQ_isGraded).toPseudofunctor.mapComp
        ((QAssociated2.unit R B).map f) ((QAssociated2.unit R B).map g)).hom =
      (QAssociated2.unit R C).map₂ (F.mapComp f g).hom := rfl

/-- **`𝔼 ∘ 𝔻 = 𝕀` on 1-morphisms**, the coherence maps `i`. -/
theorem toQPiTwoFunctor_mapQ_mapId (a : B) :
    ((hF.mapQ.toDegreeZero2 hF.mapQ_isGraded).toPseudofunctor.mapId
        ((QAssociated2.unit R B).obj a)).hom = (QAssociated2.unit R C).map₂ (F.mapId a).hom := rfl

/-- **`𝔼 ∘ 𝔻 = 𝕀` on 1-morphisms**, the coherence maps `j`. -/
theorem toQPiTwoFunctor_mapQ_j (a : B) :
    ((hF.mapQ.toQPiTwoFunctor hF.mapQ_isGraded).j ((QAssociated2.unit R B).obj a)).hom =
      (QAssociated2.unit R C).map₂ (hF.j a).hom :=
  Subtype.ext (Subtype.ext (hF.jIso_mapQ_hom a))

/-- **`𝔼 ∘ 𝔻 = 𝕀` on 1-morphisms**, the coherence maps `k`. -/
theorem toQPiTwoFunctor_mapQ_k (a : B) :
    ((hF.mapQ.toQPiTwoFunctor hF.mapQ_isGraded).k ((QAssociated2.unit R B).obj a)).hom =
      (QAssociated2.unit R C).map₂ (hF.k a).hom :=
  Subtype.ext (Subtype.ext (hF.kIso_mapQ_hom a))

end QPiTwoFunctor

end StringDiagrams

end
