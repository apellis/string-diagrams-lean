import StringDiagrams.Super.TwoHom
import StringDiagrams.Super.TwoFunctorStrict
import StringDiagrams.Super.TwoEnvelopeEquivalence

/-!
# Theorem 4.9 as a 2-superequivalence `𝔥𝔬𝔪(𝔄, ν𝔅) → 𝔥𝔬𝔪(𝔄_π, 𝔅)`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Theorem 4.9 and Remark 4.10.

For a 2-supercategory `𝔄` and a 2-supercategory `𝔅` whose morphism supercategories carry
Π-supercategory structures (in particular a Π-2-supercategory `𝔅`), the extension of
Lemma 4.7 and Theorem 4.9,

  `ℝ ↦ ℝ̃`, `(X, x) ↦ (X̃, x̃)`, `α ↦ α̃`

(`TwoEnvelope.extend`, `TwoEnvelope.extendTwoNatTrans`, `TwoEnvelope.extendSupermodification`
of `StringDiagrams.Super.TwoEnvelopeUniversal`), is a strict 2-superfunctor
`𝔥𝔬𝔪(𝔄, ν𝔅) → 𝔥𝔬𝔪(𝔄_π, 𝔅)` between the 2-supercategories of `StringDiagrams.Super.TwoHom`
(`TwoEnvelope.extendTwoHom`, `TwoEnvelope.extendTwoHom_isStrict`; its strictness is the
functoriality `TwoEnvelope.extendTwoNatTrans_id`, `TwoEnvelope.extendTwoNatTrans_vcomp` of
`StringDiagrams.Super.TwoEnvelopeEquivalence`). It is a 2-superequivalence in the second
formulation of Definition 2.2 (`TwoEnvelope.extendTwoHom_isLocalTwoSuperequivalence`): it is a
superequivalence `ℋom(ℝ, 𝕊) → ℋom(ℝ̃, 𝕊̃)` on each morphism supercategory
(`TwoEnvelope.extendHomSuperequivalence`, the equivalence of Theorem 4.9), and every
2-superfunctor `𝕋 : 𝔄_π → 𝔅` is superequivalent to `(𝕋𝕁)~` in `𝔥𝔬𝔪(𝔄_π, 𝔅)`
(`TwoEnvelope.extendRestrictNatTrans` with `TwoEnvelope.extendRestrictCounitIso`,
`TwoEnvelope.extendRestrictUnitIso`). This is the 2-superequivalence of Remark 4.10
(`TwoEnvelope.localTwoSuperequivalent_twoHom`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace TwoNatTrans

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

/-- Supermodifications between equal 2-natural transformations with heterogeneously equal
components are heterogeneously equal. -/
theorem hom_heq {F G : TwoSuperfunctor R B C} {θ₁ θ₁' θ₂ θ₂' : TwoNatTrans F G}
    (h₁ : θ₁ = θ₁') (h₂ : θ₂ = θ₂') {α : θ₁ ⟶ θ₂} {β : θ₁' ⟶ θ₂'}
    (h : ∀ a, HEq (α.app a) (β.app a)) : HEq α β := by
  subst h₁ h₂
  exact heq_of_eq (hom_ext fun a => eq_of_heq (h a))

end TwoNatTrans

namespace TwoEnvelope

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  [∀ a b : C, PiSupercategory R (a ⟶ b)]

/-- `TwoEnvelope.extendTwoNatTrans_vcomp` for the composition of `𝔥𝔬𝔪(𝔄, ν𝔅)`. -/
theorem extendTwoNatTrans_comp {F G H : TwoSuperfunctor R B C} (θ : F ⟶ G) (ψ : G ⟶ H) :
    @Eq (extend F ⟶ extend H) (extendTwoNatTrans (θ ≫ ψ))
      (extendTwoNatTrans θ ≫ extendTwoNatTrans ψ) :=
  extendTwoNatTrans_vcomp θ ψ

/-- `TwoEnvelope.extendTwoNatTrans_id` for the identity of `𝔥𝔬𝔪(𝔄, ν𝔅)`. -/
theorem extendTwoNatTrans_id' (F : TwoSuperfunctor R B C) :
    @Eq (extend F ⟶ extend F) (extendTwoNatTrans (𝟙 F)) (𝟙 (extend F)) :=
  extendTwoNatTrans_id

variable (R B C) in
/-- The strict data of the 2-superfunctor `𝔥𝔬𝔪(𝔄, ν𝔅) → 𝔥𝔬𝔪(𝔄_π, 𝔅)`, `ℝ ↦ ℝ̃`,
`(X, x) ↦ (X̃, x̃)`, `α ↦ α̃`. -/
def extendCore :
    TwoSuperfunctor.StrictCore R (TwoSuperfunctor R B C) (TwoSuperfunctor R (TwoEnvelope R B) C) where
  obj := extend
  map := extendTwoNatTrans
  map₂ := extendSupermodification
  map₂_id _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_comp _ _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_add _ _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_smul _ _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_mem hα a := hα a.as
  map_comp θ ψ := extendTwoNatTrans_comp θ ψ
  map_id F := extendTwoNatTrans_id' F
  map₂_whiskerLeft θ _ _ α :=
    TwoNatTrans.hom_heq (extendTwoNatTrans_comp θ _) (extendTwoNatTrans_comp θ _)
      fun _ => HEq.rfl
  map₂_whiskerRight α ψ :=
    TwoNatTrans.hom_heq (extendTwoNatTrans_comp _ ψ) (extendTwoNatTrans_comp _ ψ)
      fun _ => HEq.rfl
  map₂_associator θ ψ φ :=
    TwoNatTrans.hom_heq (by rw [extendTwoNatTrans_comp, extendTwoNatTrans_comp])
      (by rw [extendTwoNatTrans_comp, extendTwoNatTrans_comp]) fun _ => HEq.rfl
  map₂_leftUnitor θ :=
    TwoNatTrans.hom_heq (by rw [extendTwoNatTrans_comp, extendTwoNatTrans_id']) rfl
      fun _ => HEq.rfl
  map₂_rightUnitor θ :=
    TwoNatTrans.hom_heq (by rw [extendTwoNatTrans_comp, extendTwoNatTrans_id']) rfl
      fun _ => HEq.rfl

variable (R B C) in
/-- **Theorem 4.9 / Remark 4.10.** The strict 2-superfunctor `𝔥𝔬𝔪(𝔄, ν𝔅) → 𝔥𝔬𝔪(𝔄_π, 𝔅)`,
`ℝ ↦ ℝ̃`, `(X, x) ↦ (X̃, x̃)`, `α ↦ α̃`. -/
def extendTwoHom :
    TwoSuperfunctor R (TwoSuperfunctor R B C) (TwoSuperfunctor R (TwoEnvelope R B) C) :=
  (extendCore R B C).toTwoSuperfunctor

@[simp] theorem extendTwoHom_obj (F : TwoSuperfunctor R B C) :
    (extendTwoHom R B C).obj F = extend F := rfl

@[simp] theorem extendTwoHom_map {F G : TwoSuperfunctor R B C} (θ : F ⟶ G) :
    (extendTwoHom R B C).map θ = extendTwoNatTrans θ := rfl

@[simp] theorem extendTwoHom_map₂ {F G : TwoSuperfunctor R B C} {θ θ' : F ⟶ G} (α : θ ⟶ θ') :
    (extendTwoHom R B C).map₂ α = extendSupermodification α := rfl

/-- The 2-superfunctor `𝔥𝔬𝔪(𝔄, ν𝔅) → 𝔥𝔬𝔪(𝔄_π, 𝔅)` is strict. -/
theorem extendTwoHom_isStrict : (extendTwoHom R B C).IsStrict :=
  (extendCore R B C).isStrict

/-- Every 2-superfunctor `𝕋 : 𝔄_π → 𝔅` is superequivalent to `(𝕋𝕁)~` in `𝔥𝔬𝔪(𝔄_π, 𝔅)`, by the
2-natural transformation `(𝕋𝕁)~ ⇒ 𝕋` of Theorem 4.9. -/
theorem extendRestrictNatTrans_isSuperequivalence (T : TwoSuperfunctor R (TwoEnvelope R B) C) :
    IsSuperequivalence R (B := TwoSuperfunctor R (TwoEnvelope R B) C)
      (extendRestrictNatTrans T) :=
  ⟨extendRestrictNatTransInv T, extendRestrictCounitIso T, extendRestrictUnitIso T,
    extendRestrictCounitIso_hom_mem T, extendRestrictUnitIso_hom_mem T⟩

/-- **Remark 4.10.** The 2-superfunctor `𝔥𝔬𝔪(𝔄, ν𝔅) → 𝔥𝔬𝔪(𝔄_π, 𝔅)` is a 2-superequivalence
(second formulation of Definition 2.2): it is a superequivalence `ℋom(ℝ, 𝕊) → ℋom(ℝ̃, 𝕊̃)` on each
morphism supercategory (Theorem 4.9), and every `𝕋 : 𝔄_π → 𝔅` is superequivalent to `(𝕋𝕁)~`. -/
theorem extendTwoHom_isLocalTwoSuperequivalence :
    (extendTwoHom R B C).IsLocalTwoSuperequivalence where
  hom F G := ⟨extendHomSuperequivalence F G⟩
  essSurj T := ⟨restrict T, extendRestrictNatTrans T, extendRestrictNatTrans_isSuperequivalence T⟩

variable (R B C) in
/-- **Remark 4.10.** `𝔥𝔬𝔪(𝔄, ν𝔅)` and `𝔥𝔬𝔪(𝔄_π, 𝔅)` are 2-superequivalent (second formulation
of Definition 2.2). -/
theorem localTwoSuperequivalent_twoHom :
    TwoSuperfunctor.LocalTwoSuperequivalent R (TwoSuperfunctor R B C)
      (TwoSuperfunctor R (TwoEnvelope R B) C) :=
  ⟨extendTwoHom R B C, extendTwoHom_isLocalTwoSuperequivalence⟩

end TwoEnvelope

end StringDiagrams

end
