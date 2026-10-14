import StringDiagrams.Super.TwoEnvelopeTransformationLift

/-!
# Even isomorphisms of 2-natural transformations

For 2-natural transformations `θ ψ : F ⟹ G` between 2-superfunctors into a graded
2-supercategory, `EvenIso θ ψ` is an isomorphism `θ ≅ ψ` in the category of transformations and
modifications whose two modifications are homogeneous of parity zero and degree zero. These are
the 2-cells of the graded 2-supercategory of graded 2-superfunctors (arXiv:1701.04133v2,
Definition 6.3 and the remarks following it). An adjoint biequivalence in that 2-supercategory
has its invertible unit, counit and triangle modifications of this form.

This file gives the operations on even isomorphisms needed to paste triangle identities:
composition (`EvenIso.trans`), transport along equalities (`EvenIso.cast`, `EvenIso.ofHEq`,
`EvenIso.rebaseCancel`), whiskering by a transformation (`EvenIso.whiskerLeft`,
`EvenIso.whiskerRight`), whiskering by a 2-superfunctor (`EvenIso.postcomposeCancel`,
`EvenIso.precomposeCancel`) and extension to Π-envelopes (`EvenIso.mapPi`,
`EvenIso.mapPiCancel`). The postcomposition of an identity transformation is identified with the
identity by `TwoNatTrans.postcomposeIdIso`, through the identity comparison of the
postcomposing 2-superfunctor.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe r u v w u' v' w' u'' v'' w''
variable {R : Type r} [CommRing R]
  {A : Type u} [BicategoryStruct.{w, v} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A]
  {B : Type u'} [BicategoryStruct.{w', v'} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u''} [BicategoryStruct.{w'', v''} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

/-- An isomorphism of transformations whose modifications are even of degree zero. -/
def EvenIso [∀ a b : B, GradedSupercategory R (a ⟶ b)] {F G : TwoSuperfunctor R A B}
    (θ ψ : TwoNatTrans F G) :=
  {e : θ ≅ ψ // e.hom.IsHomogeneous 0 0 ∧ e.inv.IsHomogeneous 0 0}

omit [TwoSupercategory R A] in
/-- The inverse of a homogeneous isomorphism of degree zero and parity zero is homogeneous of
degree zero and parity zero. -/
theorem TwoNatTrans.inv_isHomogeneous_of_hom [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    {F G : TwoSuperfunctor R A B} {θ ψ : TwoNatTrans F G} (e : θ ≅ ψ)
    (h : e.hom.IsHomogeneous 0 0) : e.inv.IsHomogeneous 0 0 := by
  intro a
  let c : θ.X a ≅ ψ.X a :=
    { hom := e.hom.app a
      inv := e.inv.app a
      hom_inv_id := congrArg (fun α : θ ⟶ θ => α.app a) e.hom_inv_id
      inv_hom_id := congrArg (fun α : ψ ⟶ ψ => α.app a) e.inv_hom_id }
  exact ⟨inv_mem c (h a).1, by
    simpa only [neg_zero] using GradedSupercategory.inv_mem_degree c (h a).2⟩

namespace EvenIso

section Basic
variable [∀ a b : B, GradedSupercategory R (a ⟶ b)] {F G : TwoSuperfunctor R A B}

/-- Composition of even isomorphisms. -/
def trans {θ ψ χ : TwoNatTrans F G} (e : EvenIso θ ψ) (d : EvenIso ψ χ) : EvenIso θ χ :=
  ⟨e.1 ≪≫ d.1, fun a => ⟨by simpa only [add_zero] using! comp_mem (e.2.1 a).1 (d.2.1 a).1,
      by simpa only [add_zero] using! comp_mem_degree (e.2.1 a).2 (d.2.1 a).2⟩,
    fun a => ⟨by simpa only [add_zero] using! comp_mem (d.2.2 a).1 (e.2.2 a).1,
      by simpa only [add_zero] using! comp_mem_degree (d.2.2 a).2 (e.2.2 a).2⟩⟩

/-- Transport an even isomorphism along equalities of transformations. -/
def cast {θ ψ θ' ψ' : TwoNatTrans F G} (h : θ = θ') (j : ψ = ψ')
    (e : EvenIso θ ψ) : EvenIso θ' ψ' := by
  subst θ' ψ'
  exact e

/-- Transport an even isomorphism along equalities of 2-superfunctors and heterogeneous
equalities of transformations. -/
def ofHEq {F' G' : TwoSuperfunctor R A B} (p : F = F') (q : G = G')
    {θ ψ : TwoNatTrans F G} {θ' ψ' : TwoNatTrans F' G'}
    (hθ : HEq θ θ') (hψ : HEq ψ ψ') (e : EvenIso θ ψ) : EvenIso θ' ψ' := by
  subst F' G'
  cases eq_of_heq hθ
  cases eq_of_heq hψ
  exact e

/-- Transport an isomorphism `θ ∘ ψ ≅ 1` along equalities of both endpoints. -/
def rebaseCancel {F' G' : TwoSuperfunctor R A B} (h : F = F') (j : G = G')
    (θ : TwoNatTrans F G) (ψ : TwoNatTrans G F)
    (e : EvenIso (θ.vcomp ψ) (TwoNatTrans.id F)) :
    EvenIso ((TwoNatTrans.rebase h j θ).vcomp (TwoNatTrans.rebase j h ψ))
      (TwoNatTrans.id F') := by
  subst F' G'
  exact e
end Basic

section Whisker
variable [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [GradedTwoSupercategory R B] {F G H : TwoSuperfunctor R A B}

/-- Whisker an even isomorphism `θ ≅ θ'` on the right by a transformation `ψ`. -/
def whiskerRight {θ θ' : TwoNatTrans F G}
    (e : EvenIso θ θ') (ψ : TwoNatTrans G H) : EvenIso (θ.vcomp ψ) (θ'.vcomp ψ) := by
  let d : θ.vcomp ψ ≅ θ'.vcomp ψ := {
    hom := TwoNatTrans.whiskerRight e.1.hom ψ
    inv := TwoNatTrans.whiskerRight e.1.inv ψ
    hom_inv_id := TwoNatTrans.hom_ext fun a => by
      change e.1.hom.app a ▷ ψ.X a ≫ e.1.inv.app a ▷ ψ.X a = 𝟙 _
      rw [← comp_whiskerRight (R := R)]
      have h := congrArg (fun α : θ ⟶ θ => α.app a) e.1.hom_inv_id
      change e.1.hom.app a ≫ e.1.inv.app a = 𝟙 _ at h
      rw [h, id_whiskerRight (R := R)]
    inv_hom_id := TwoNatTrans.hom_ext fun a => by
      change e.1.inv.app a ▷ ψ.X a ≫ e.1.hom.app a ▷ ψ.X a = 𝟙 _
      rw [← comp_whiskerRight (R := R)]
      have h := congrArg (fun α : θ' ⟶ θ' => α.app a) e.1.inv_hom_id
      change e.1.inv.app a ≫ e.1.hom.app a = 𝟙 _ at h
      rw [h, id_whiskerRight (R := R)] }
  exact ⟨d, fun a => ⟨whiskerRight_mem (ψ.X a) (e.2.1 a).1,
      GradedTwoSupercategory.whiskerRight_mem_degree (ψ.X a) (e.2.1 a).2⟩,
    fun a => ⟨whiskerRight_mem (ψ.X a) (e.2.2 a).1,
      GradedTwoSupercategory.whiskerRight_mem_degree (ψ.X a) (e.2.2 a).2⟩⟩

/-- Whisker an even isomorphism `ψ ≅ ψ'` on the left by a transformation `θ`. -/
def whiskerLeft (θ : TwoNatTrans F G)
    {ψ ψ' : TwoNatTrans G H} (e : EvenIso ψ ψ') : EvenIso (θ.vcomp ψ) (θ.vcomp ψ') := by
  let d : θ.vcomp ψ ≅ θ.vcomp ψ' := {
    hom := TwoNatTrans.whiskerLeft θ e.1.hom
    inv := TwoNatTrans.whiskerLeft θ e.1.inv
    hom_inv_id := TwoNatTrans.hom_ext fun a => by
      change θ.X a ◁ e.1.hom.app a ≫ θ.X a ◁ e.1.inv.app a = 𝟙 _
      rw [← whiskerLeft_comp (R := R)]
      have h := congrArg (fun α : ψ ⟶ ψ => α.app a) e.1.hom_inv_id
      change e.1.hom.app a ≫ e.1.inv.app a = 𝟙 _ at h
      rw [h, whiskerLeft_id (R := R)]
    inv_hom_id := TwoNatTrans.hom_ext fun a => by
      change θ.X a ◁ e.1.inv.app a ≫ θ.X a ◁ e.1.hom.app a = 𝟙 _
      rw [← whiskerLeft_comp (R := R)]
      have h := congrArg (fun α : ψ' ⟶ ψ' => α.app a) e.1.inv_hom_id
      change e.1.inv.app a ≫ e.1.hom.app a = 𝟙 _ at h
      rw [h, whiskerLeft_id (R := R)] }
  exact ⟨d, fun a => ⟨whiskerLeft_mem (θ.X a) (e.2.1 a).1,
      GradedTwoSupercategory.whiskerLeft_mem_degree (θ.X a) (e.2.1 a).2⟩,
    fun a => ⟨whiskerLeft_mem (θ.X a) (e.2.2 a).1,
      GradedTwoSupercategory.whiskerLeft_mem_degree (θ.X a) (e.2.2 a).2⟩⟩
end Whisker

section Envelope
variable [∀ a b : B, GradedSupercategory R (a ⟶ b)] {F G : TwoSuperfunctor R A B}

/-- Extension of an even isomorphism to the Π-envelopes. -/
def mapPi {θ ψ : TwoNatTrans F G} (e : EvenIso θ ψ) :
    EvenIso (TwoEnvelope.mapPiNatTrans θ) (TwoEnvelope.mapPiNatTrans ψ) :=
  ⟨TwoEnvelope.mapPiModifications.mapIso e.1,
    TwoEnvelope.mapPiSupermodification_isHomogeneous e.2.1,
    TwoEnvelope.mapPiSupermodification_isHomogeneous e.2.2⟩

/-- Extension of an isomorphism `θ ∘ ψ ≅ 1` to the Π-envelopes. -/
def mapPiCancel (θ : TwoNatTrans F G) (ψ : TwoNatTrans G F)
    (e : EvenIso (θ.vcomp ψ) (TwoNatTrans.id F)) :
    EvenIso ((TwoEnvelope.mapPiNatTrans θ).vcomp (TwoEnvelope.mapPiNatTrans ψ))
      (TwoNatTrans.id (TwoEnvelope.mapPi F)) :=
  cast (TwoEnvelope.mapPiNatTrans_vcomp θ ψ) TwoEnvelope.mapPiNatTrans_id (mapPi e)
end Envelope
end EvenIso

section Postcompose

/-- Postcomposing the identity transformation of `F` with `H` gives the identity of
`F ⋙ H`, through the identity comparisons of `H`. -/
def TwoNatTrans.postcomposeIdIso (H : TwoSuperfunctor R B C) (F : TwoSuperfunctor R A B) :
    TwoNatTrans.postcompose H (TwoNatTrans.id F) ≅ TwoNatTrans.id (F.comp H) := by
  let e (a : A) := (H.mapId (F.obj a)).symm
  have nat : ∀ {a b : A} (f : a ⟶ b),
      (TwoNatTrans.postcompose H (TwoNatTrans.id F)).x f ≫
        (e a).hom ▷ (F.comp H).map f =
      (F.comp H).map f ◁ (e b).hom ≫ (TwoNatTrans.id (F.comp H)).x f := by
    intro a b f
    change ((H.mapComp _ _).hom ≫
      H.map₂ ((BicategoryStruct.rightUnitor _).hom ≫ (BicategoryStruct.leftUnitor _).inv) ≫
      (H.mapComp _ _).inv) ≫ (H.mapId _).inv ▷ _ =
        _ ◁ (H.mapId _).inv ≫ (BicategoryStruct.rightUnitor _).hom ≫ (BicategoryStruct.leftUnitor _).inv
    simp only [H.map₂_comp, Category.assoc]
    rw [← cancel_mono (whiskerRightIso (R := R) (H.mapId (F.obj a))
      (H.map (F.map f))).hom]
    dsimp only [whiskerRightIso]
    simp only [Category.assoc]
    rw [inv_hom_whiskerRight R]
    rw [← cancel_epi (whiskerLeftIso (R := R) (H.map (F.map f))
      (H.mapId (F.obj b))).hom]
    dsimp only [whiskerLeftIso]
    rw [whiskerLeft_hom_inv_assoc R, H.map₂_rightUnitor_assoc]
    rw [← cancel_mono (H.mapComp (𝟙 (F.obj a)) (F.map f)).hom]
    simp only [Category.assoc, Category.id_comp, Iso.inv_hom_id]
    rw [← cancel_mono (H.map₂Iso (BicategoryStruct.leftUnitor (F.map f))).hom]
    dsimp only [TwoSuperfunctor.map₂Iso]
    simp only [Category.assoc]
    rw [H.map₂_leftUnitor]
    simp only [Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    rw [← H.map₂_comp, Iso.inv_hom_id, H.map₂_id, Category.comp_id]
  exact {
    hom := ⟨fun a => (e a).hom, nat⟩
    inv := ⟨fun a => (e a).inv, fun {a b} f => by
      let xx : H.map (F.map f) ≫ H.map (𝟙 (F.obj b)) ⟶
          H.map (𝟙 (F.obj a)) ≫ H.map (F.map f) :=
        (TwoNatTrans.postcompose H (TwoNatTrans.id F)).x f
      let yy : H.map (F.map f) ≫ 𝟙 (H.obj (F.obj b)) ⟶
          𝟙 (H.obj (F.obj a)) ≫ H.map (F.map f) := (TwoNatTrans.id (F.comp H)).x f
      have hn : xx ≫ (e a).hom ▷ H.map (F.map f) =
          H.map (F.map f) ◁ (e b).hom ≫ yy := nat f
      change yy ≫ (e a).inv ▷ H.map (F.map f) = H.map (F.map f) ◁ (e b).inv ≫ xx
      rw [← cancel_epi (whiskerLeftIso (R := R) (H.map (F.map f)) (e b)).hom]
      change H.map (F.map f) ◁ (e b).hom ≫ yy ≫ (e a).inv ▷ _ =
        H.map (F.map f) ◁ (e b).hom ≫ H.map (F.map f) ◁ (e b).inv ≫ xx
      rw [← Category.assoc, ← hn, Category.assoc, hom_inv_whiskerRight R, Category.comp_id,
        ← Category.assoc, whiskerLeft_hom_inv R, Category.id_comp]⟩
    hom_inv_id := TwoNatTrans.hom_ext fun a => (e a).hom_inv_id
    inv_hom_id := TwoNatTrans.hom_ext fun a => (e a).inv_hom_id }

variable [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [∀ a b : C, GradedSupercategory R (a ⟶ b)]

/-- `TwoNatTrans.postcomposeIdIso` is even for a graded 2-superfunctor. -/
def EvenIso.postcomposeId (H : TwoSuperfunctor R B C) (hH : H.IsGraded)
    (F : TwoSuperfunctor R A B) :
    EvenIso (TwoNatTrans.postcompose H (TwoNatTrans.id F)) (TwoNatTrans.id (F.comp H)) :=
  ⟨TwoNatTrans.postcomposeIdIso H F, fun a => ⟨inv_mem _ (H.mapId_hom_mem _), by
      simpa only [neg_zero] using! inv_mem_degree (H.mapId (F.obj a)) (hH.mapId_hom_mem_degree _)⟩,
    fun a => ⟨H.mapId_hom_mem _, hH.mapId_hom_mem_degree _⟩⟩

/-- Postcompose an isomorphism `θ ∘ ψ ≅ 1` with a graded 2-superfunctor `H`. -/
def EvenIso.postcomposeCancel (H : TwoSuperfunctor R B C) (hH : H.IsGraded)
    {F G : TwoSuperfunctor R A B} (θ : TwoNatTrans F G) (ψ : TwoNatTrans G F)
    (e : EvenIso (θ.vcomp ψ) (TwoNatTrans.id F)) :
    EvenIso ((TwoNatTrans.postcompose H θ).vcomp (TwoNatTrans.postcompose H ψ))
      (TwoNatTrans.id (F.comp H)) :=
  EvenIso.trans ⟨TwoNatTrans.postcomposeVcompIso H θ ψ,
      TwoNatTrans.postcomposeVcompIso_hom_isHomogeneous H θ ψ hH,
      TwoNatTrans.postcomposeVcompIso_inv_isHomogeneous H θ ψ hH⟩
    (EvenIso.trans ⟨(TwoNatTrans.postcomposition H F F).mapIso e.1,
      TwoNatTrans.postcomposeModification_isHomogeneous H hH e.2.1,
      TwoNatTrans.postcomposeModification_isHomogeneous H hH e.2.2⟩
      (EvenIso.postcomposeId H hH F))

omit [∀ a b : B, GradedSupercategory R (a ⟶ b)] in
/-- Precompose an isomorphism `θ ∘ ψ ≅ 1` with a 2-superfunctor `P`. -/
def EvenIso.precomposeCancel (P : TwoSuperfunctor R A B) {F G : TwoSuperfunctor R B C}
    (θ : TwoNatTrans F G) (ψ : TwoNatTrans G F)
    (e : EvenIso (θ.vcomp ψ) (TwoNatTrans.id F)) :
    EvenIso ((TwoNatTrans.precompose P θ).vcomp (TwoNatTrans.precompose P ψ))
      (TwoNatTrans.id (P.comp F)) :=
  ⟨(TwoNatTrans.precomposition P F F).mapIso e.1,
    TwoNatTrans.precomposeModification_isHomogeneous P e.2.1,
    TwoNatTrans.precomposeModification_isHomogeneous P e.2.2⟩
end Postcompose
end StringDiagrams
