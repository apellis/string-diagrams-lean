import StringDiagrams.Super.QAssociatedTwoMap

/-!
# `𝔻` on (Q, Π)-2-natural transformations, naturality of `𝕋`, and the §6 analogue of Theorem 5.5

DOC
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

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

end QAssociated2

end StringDiagrams

end
