import StringDiagrams.Super.TwoEnvelopeUniversal
import StringDiagrams.Super.TwoFunctorComp
import Mathlib.Tactic.CategoryTheory.BicategoryCoherence

/-!
# Theorem 4.9 with composites of 2-natural transformations

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Theorem 4.9.

The 2-natural transformations `(𝕋𝕁)~ ⇒ 𝕋` and `𝕋 ⇒ (𝕋𝕁)~` of
`StringDiagrams.Super.TwoEnvelopeUniversal` (`TwoEnvelope.extendRestrictNatTrans`,
`TwoEnvelope.extendRestrictNatTransInv`) are mutually inverse up to invertible even
supermodifications: their vertical composites (`TwoNatTrans.vcomp`) are isomorphic in
`ℋom((𝕋𝕁)~, (𝕋𝕁)~)` and `ℋom(𝕋, 𝕋)` to the identity 2-natural transformations
(`TwoEnvelope.extendRestrictCounitIso`, `TwoEnvelope.extendRestrictUnitIso`), by the unitors
`1 1 ≅ 1`. Together with `TwoEnvelope.extendTwoNatTransEquiv` this is the equivalence of
Theorem 4.9 in the non-strict setting (where composition of 2-natural transformations is
associative and unital only up to such isomorphisms).

The extension of 2-natural transformations is functorial (`TwoEnvelope.extendTwoNatTrans_id`,
`TwoEnvelope.extendTwoNatTrans_vcomp`). `𝕁` is a strict 2-superfunctor (`TwoEnvelope.twoJ_isStrict`). We also record `ℝ = ℝ̃ 𝕁` as an equality of 2-superfunctors (`TwoEnvelope.twoJ_comp_extend`,
Lemma 4.7(i)) and that the restriction `TwoEnvelope.restrict 𝕋` is the composite `𝕋 ∘ 𝕁`
(`TwoEnvelope.restrict_eq_comp`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace TwoSupercategory

variable {R : Type w} [CommRing R]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

variable (R) in
include R in
/-- A coherence identity for the vertical composite of two 2-natural transformations with
identity 1-morphisms. -/
theorem vcomp_unit_coherence {a b : C} (A : a ⟶ b) :
    (associator A (𝟙 b) (𝟙 b)).inv ≫ (rightUnitor A).hom ▷ 𝟙 b ≫ (leftUnitor A).inv ▷ 𝟙 b ≫
        (associator (𝟙 a) A (𝟙 b)).hom ≫ 𝟙 a ◁ (rightUnitor A).hom ≫
        𝟙 a ◁ (leftUnitor A).inv ≫ (associator (𝟙 a) (𝟙 a) A).inv ≫
        (leftUnitor (𝟙 a)).hom ▷ A =
      A ◁ (leftUnitor (𝟙 b)).hom ≫ (rightUnitor A).hom ≫ (leftUnitor A).inv := by
  have h : ∀ (A' : (⟨a⟩ : Underlying2 R C) ⟶ ⟨b⟩),
      (Bicategory.associator A' (𝟙 _) (𝟙 _)).inv ≫ Bicategory.whiskerRight (Bicategory.rightUnitor A').hom (𝟙 _) ≫
        Bicategory.whiskerRight (Bicategory.leftUnitor A').inv (𝟙 _) ≫
        (Bicategory.associator (𝟙 _) A' (𝟙 _)).hom ≫
        Bicategory.whiskerLeft (𝟙 _) (Bicategory.rightUnitor A').hom ≫
        Bicategory.whiskerLeft (𝟙 _) (Bicategory.leftUnitor A').inv ≫
        (Bicategory.associator (𝟙 _) (𝟙 _) A').inv ≫
        Bicategory.whiskerRight (Bicategory.leftUnitor (𝟙 _)).hom A' =
      Bicategory.whiskerLeft A' (Bicategory.leftUnitor (𝟙 _)).hom ≫ (Bicategory.rightUnitor A').hom ≫
        (Bicategory.leftUnitor A').inv := by
    intro A'
    bicategory_coherence
  have h' := congrArg Subtype.val (h (Underlying2.hom1 A))
  simp only [Underlying2.comp₂_val, Underlying2.whiskerLeft_val, Underlying2.whiskerRight_val,
    Underlying2.associator_hom_val, Underlying2.associator_inv_val, Underlying2.leftUnitor_hom_val,
    Underlying2.leftUnitor_inv_val, Underlying2.rightUnitor_hom_val, Underlying2.hom1_obj,
    Underlying2.id_obj] at h'
  exact h'

variable (R) in
include R in
/-- The supermodification condition for the unitor `1 1 ≅ 1` between the vertical composite of
two 2-natural transformations with identity 1-morphisms and mutually inverse components, and
the identity 2-natural transformation. -/
theorem vcomp_unitors_naturality {a b : C} {A B : a ⟶ b} (φ : A ⟶ B) (ψ : B ⟶ A)
    (h : φ ≫ ψ = 𝟙 A) :
    ((associator A (𝟙 b) (𝟙 b)).inv ≫
        ((rightUnitor A).hom ≫ φ ≫ (leftUnitor B).inv) ▷ 𝟙 b ≫
        (associator (𝟙 a) B (𝟙 b)).hom ≫ 𝟙 a ◁ ((rightUnitor B).hom ≫ ψ ≫ (leftUnitor A).inv) ≫
        (associator (𝟙 a) (𝟙 a) A).inv) ≫ (leftUnitor (𝟙 a)).hom ▷ A =
      A ◁ (leftUnitor (𝟙 b)).hom ≫ (rightUnitor A).hom ≫ (leftUnitor A).inv := by
  have nat : φ ▷ 𝟙 b ≫ (leftUnitor B).inv ▷ 𝟙 b ≫ (associator (𝟙 a) B (𝟙 b)).hom ≫
      𝟙 a ◁ (rightUnitor B).hom = (leftUnitor A).inv ▷ 𝟙 b ≫ (associator (𝟙 a) A (𝟙 b)).hom ≫
      𝟙 a ◁ (rightUnitor A).hom ≫ 𝟙 a ◁ φ := by
    rw [← Category.assoc, ← comp_whiskerRight (R := R), leftUnitor_inv_naturality R,
      comp_whiskerRight (R := R), Category.assoc, associator_naturality_middle_assoc R,
      ← whiskerLeft_comp (R := R), rightUnitor_naturality R, whiskerLeft_comp (R := R)]
  simp only [comp_whiskerRight (R := R), whiskerLeft_comp (R := R), Category.assoc]
  rw [reassoc_of% nat, TwoEnvelope.whiskerLeft_comp_comp R (𝟙 a) φ ψ, h,
    whiskerLeft_id (R := R), Category.id_comp]
  simpa only [Category.assoc] using vcomp_unit_coherence R A

end TwoSupercategory

namespace TwoEnvelope

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  [∀ a b : C, PiSupercategory R (a ⟶ b)]
  (T : TwoSuperfunctor R (TwoEnvelope R B) C)

theorem extendRestrictApp_comp_inv {a b : TwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictApp T f ≫ extendRestrictAppInv T f = 𝟙 _ :=
  (Envelope.extendRestrictIso (homFunctor T a b)).hom_inv_id_app f

theorem extendRestrictAppInv_comp {a b : TwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictAppInv T f ≫ extendRestrictApp T f = 𝟙 _ :=
  (Envelope.extendRestrictIso (homFunctor T a b)).inv_hom_id_app f

/-- An isomorphism in `ℋom(ℝ, 𝕊)` given by even 2-isomorphisms `e_λ : X_λ ≅ Y_λ` satisfying
the supermodification condition. -/
def supermodificationIso {F G : TwoSuperfunctor R (TwoEnvelope R B) C} {θ θ' : TwoNatTrans F G}
    (e : ∀ a, θ.X a ≅ θ'.X a)
    (nat : ∀ {a b} (f : a ⟶ b), θ.x f ≫ (e a).hom ▷ G.map f = F.map f ◁ (e b).hom ≫ θ'.x f) :
    θ ≅ θ' where
  hom := ⟨fun a => (e a).hom, nat⟩
  inv := ⟨fun a => (e a).inv, fun {a b} f => by
    rw [← cancel_epi (whiskerLeftIso (R := R) (F.map f) (e b)).hom]
    show F.map f ◁ (e b).hom ≫ θ'.x f ≫ (e a).inv ▷ G.map f =
      F.map f ◁ (e b).hom ≫ F.map f ◁ (e b).inv ≫ θ.x f
    rw [← Category.assoc, ← nat, Category.assoc, hom_inv_whiskerRight R, Category.comp_id,
      ← Category.assoc, whiskerLeft_hom_inv R, Category.id_comp]⟩
  hom_inv_id := TwoNatTrans.hom_ext fun a => (e a).hom_inv_id
  inv_hom_id := TwoNatTrans.hom_ext fun a => (e a).inv_hom_id

/-- **Theorem 4.9.** The composite `(𝕋𝕁)~ ⇒ 𝕋 ⇒ (𝕋𝕁)~` is isomorphic to the identity in
`ℋom((𝕋𝕁)~, (𝕋𝕁)~)`, by the even unitors `1 1 ≅ 1`. -/
def extendRestrictCounitIso :
    TwoNatTrans.vcomp (extendRestrictNatTrans T) (extendRestrictNatTransInv T) ≅
      TwoNatTrans.id (extend (restrict T)) :=
  supermodificationIso (fun a => leftUnitor (𝟙 (T.obj a))) fun f =>
    vcomp_unitors_naturality R _ _ (extendRestrictApp_comp_inv T f)

/-- **Theorem 4.9.** The composite `𝕋 ⇒ (𝕋𝕁)~ ⇒ 𝕋` is isomorphic to the identity in
`ℋom(𝕋, 𝕋)`, by the even unitors `1 1 ≅ 1`. -/
def extendRestrictUnitIso :
    TwoNatTrans.vcomp (extendRestrictNatTransInv T) (extendRestrictNatTrans T) ≅
      TwoNatTrans.id T :=
  supermodificationIso (fun a => leftUnitor (𝟙 (T.obj a))) fun f =>
    vcomp_unitors_naturality R _ _ (extendRestrictAppInv_comp T f)

theorem extendRestrictCounitIso_hom_mem :
    (extendRestrictCounitIso T).hom ∈ parity (R := R) _ _ 0 :=
  fun _ => leftUnitor_hom_mem (R := R) _

theorem extendRestrictUnitIso_hom_mem :
    (extendRestrictUnitIso T).hom ∈ parity (R := R) _ _ 0 :=
  fun _ => leftUnitor_hom_mem (R := R) _

omit [TwoSupercategory R C] [∀ a b : C, PiSupercategory R (a ⟶ b)] in
/-- `𝕁 : 𝔄 → 𝔄_π` is a strict 2-superfunctor. -/
theorem twoJ_isStrict : (twoJ R B).IsStrict where
  map_comp _ _ := rfl
  map_id _ := rfl
  mapComp_eq _ _ := Iso.ext rfl
  mapId_eq _ := Iso.ext rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] [∀ a b : C, PiSupercategory R (a ⟶ b)] in
/-- Two 2-superfunctors with the same data are equal. -/
theorem twoSuperfunctor_ext {F G : TwoSuperfunctor R B C} (h_obj : F.obj = G.obj)
    (h_map : HEq @F.map @G.map) (h_map₂ : HEq @F.map₂ @G.map₂)
    (h_comp : HEq @F.mapComp @G.mapComp) (h_id : HEq F.mapId G.mapId) : F = G := by
  obtain ⟨obj, map, map₂, _, _, _, _, _, mapComp, mapId, _, _, _, _, _, _, _⟩ := F
  obtain ⟨obj', map', map₂', _, _, _, _, _, mapComp', mapId', _, _, _, _, _, _, _⟩ := G
  dsimp only at h_obj h_map h_map₂ h_comp h_id
  subst h_obj
  cases h_map
  cases h_map₂
  cases h_comp
  cases h_id
  rfl

/-- **Lemma 4.7(i).** `ℝ = ℝ̃ 𝕁` as 2-superfunctors. -/
theorem twoJ_comp_extend (F : TwoSuperfunctor R B C) : (twoJ R B).comp (extend F) = F := by
  refine twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b f g η
    show 𝟙 _ ≫ F.map₂ η ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
  · funext a b c f g
    apply Iso.ext
    show (extendComp F (Jm (R := R) f) (Jm g)).hom ≫
      (extend F).map₂ (𝟙 (Jm (R := R) f ≫ Jm g)) = _
    rw [(extend F).map₂_id]
    erw [Category.comp_id]
    exact extendComp_J F (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩) f g
  · funext a
    apply Iso.ext
    show (F.mapId a).hom ≫ (extend F).map₂ (𝟙 (𝟙 (⟨a⟩ : TwoEnvelope R B))) = _
    rw [(extend F).map₂_id]
    erw [Category.comp_id]

omit [∀ a b : C, PiSupercategory R (a ⟶ b)] in
/-- The restriction `𝕋𝕁` of `StringDiagrams.Super.TwoEnvelopeUniversal` is the composite of
`𝕁` and `𝕋`. -/
theorem restrict_eq_comp : restrict T = (twoJ R B).comp T := by
  refine twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    apply Iso.ext
    show (T.mapComp (Jm (R := R) f) (Jm g)).hom = (T.mapComp (Jm f) (Jm g)).hom ≫
      T.map₂ (𝟙 (Jm (R := R) f ≫ Jm g))
    rw [T.map₂_id]
    erw [Category.comp_id]
  · funext a
    apply Iso.ext
    show (T.mapId ⟨a⟩).hom = (T.mapId ⟨a⟩).hom ≫ T.map₂ (𝟙 (𝟙 (⟨a⟩ : TwoEnvelope R B)))
    rw [T.map₂_id]
    erw [Category.comp_id]

section Functoriality

variable {F G H : TwoSuperfunctor R B C}

/-- **Theorem 4.9**, functoriality: `1̃ = 1`. -/
theorem extendTwoNatTrans_id : extendTwoNatTrans (TwoNatTrans.id F) = TwoNatTrans.id (extend F) := by
  rw [← extendTwoNatTrans_restrictTwoNatTrans (TwoNatTrans.id (extend F))]
  congr 1

/-- **Theorem 4.9**, functoriality: `(X', x') ∘ (X, x)` extends to `(X̃', x̃') ∘ (X̃, x̃)`. -/
theorem extendTwoNatTrans_vcomp (θ : TwoNatTrans F G) (θ' : TwoNatTrans G H) :
    extendTwoNatTrans (TwoNatTrans.vcomp θ θ') =
      TwoNatTrans.vcomp (extendTwoNatTrans θ) (extendTwoNatTrans θ') := by
  rw [← extendTwoNatTrans_restrictTwoNatTrans
    (TwoNatTrans.vcomp (extendTwoNatTrans θ) (extendTwoNatTrans θ'))]
  congr 1
  refine twoNatTrans_ext rfl fun {a b} f => heq_of_eq ?_
  rw [restrictTwoNatTrans_x, TwoNatTrans.vcomp_x, TwoNatTrans.vcomp_x]
  have h₁ : (extendTwoNatTrans θ).x
      ((Envelope.J R (a ⟶ b)).obj f : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩) = θ.x f :=
    extendX_J (a := (⟨a⟩ : TwoEnvelope R B)) (b := ⟨b⟩) θ f
  have h₂ : (extendTwoNatTrans θ').x
      ((Envelope.J R (a ⟶ b)).obj f : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩) = θ'.x f :=
    extendX_J (a := (⟨a⟩ : TwoEnvelope R B)) (b := ⟨b⟩) θ' f
  rw [h₁, h₂]
  rfl

end Functoriality

end TwoEnvelope

end StringDiagrams

end
