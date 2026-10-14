import StringDiagrams.Super.GradedTwoEnvelopeTransformation
import StringDiagrams.Super.TwoNatTransRebase

/-!
# The Π-envelope extension of transformations, modifications and whiskering

For 2-superfunctors `F G : 𝔅 → ℭ`, `TwoEnvelope.mapPiNatTrans` extends a 2-natural
transformation `θ : F ⟹ G` to `mapPi F ⟹ mapPi G` on the Π-envelopes
(arXiv:1701.04133v2, §9, before Lemma 9.1). This file records:
* the extension preserves strength (`TwoEnvelope.mapPiNatTrans_isStrong`);
* the extension on modifications is a functor
  (`TwoEnvelope.mapPiModifications`) preserving homogeneous modifications of degree zero
  and parity zero (`TwoEnvelope.mapPiSupermodification_isHomogeneous`);
* the extension commutes with whiskering by a 2-superfunctor, up to the equalities
  `mapPi (F ⋙ H) = mapPi F ⋙ mapPi H`
  (`TwoEnvelope.mapPiNatTrans_postcompose_heq`, `TwoEnvelope.mapPiNatTrans_precompose_heq`).

They are used to extend the unit and counit of the Chevalley involution of
arXiv:1701.04133v2, Proposition 9.3, from `𝔘(𝔤)_q` to `𝔘(𝔤)_{q,π}`.
-/

noncomputable section
namespace StringDiagrams.TwoEnvelope
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

/-- Invertible naturality cells remain invertible in the Π-envelope. -/
theorem mapPiNatTrans_isStrong {F G : TwoSuperfunctor R A B}
    {θ : TwoNatTrans F G} (hθ : θ.IsStrong) : (mapPiNatTrans θ).IsStrong := by
  intro a b f
  let e : F.map f.obj ≫ θ.X b.as ≅ θ.X a.as ≫ G.map f.obj :=
    @asIso _ _ _ _ (θ.x f.obj) (hθ f.obj)
  let eπ : (mapPi F).map f ≫ (mapPiNatTrans θ).X b ≅
      (mapPiNatTrans θ).X a ≫ (mapPi G).map f :=
    Envelope.isoOfIso e
  exact eπ.isIso_hom

/-- The extension to Π-envelopes as a functor between categories of transformations
and modifications. -/
def mapPiModifications {F G : TwoSuperfunctor R A B} :
    TwoNatTrans F G ⥤ TwoNatTrans (mapPi F) (mapPi G) where
  obj := mapPiNatTrans
  map := mapPiSupermodification
  map_id _ := TwoNatTrans.hom_ext fun _ => rfl
  map_comp _ _ := TwoNatTrans.hom_ext fun _ => rfl

theorem mapPiSupermodification_isHomogeneous [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    {F G : TwoSuperfunctor R A B} {θ ψ : TwoNatTrans F G} {α : θ ⟶ ψ}
    (h : α.IsHomogeneous 0 0) : (mapPiSupermodification α).IsHomogeneous 0 0 := by
  intro a
  constructor
  · change α.app a.as ∈ parity (R := R) (C := F.obj a.as ⟶ G.obj a.as)
      (θ.X a.as) (ψ.X a.as) (0 + (0 + 0))
    simpa only [add_zero] using (h a.as).1
  · exact (h a.as).2

theorem mapPiNatTrans_heq {F G F' G' : TwoSuperfunctor R A B}
    (hF : F = F') (hG : G = G') {θ : TwoNatTrans F G} {ψ : TwoNatTrans F' G'}
    (h : HEq θ ψ) : HEq (mapPiNatTrans θ) (mapPiNatTrans ψ) := by
  subst F' G'
  cases eq_of_heq h
  rfl

theorem mapPiNatTrans_postcompose_heq {F G : TwoSuperfunctor R A B}
    (H : TwoSuperfunctor R B C) (θ : TwoNatTrans F G) :
    HEq (mapPiNatTrans (TwoNatTrans.postcompose H θ))
      (TwoNatTrans.postcompose (mapPi H) (mapPiNatTrans θ)) := by
  apply TwoNatTrans.hext (mapPi_comp F H) (mapPi_comp G H)
  · intro a
    rfl
  · intro a b f
    rfl

theorem mapPiNatTrans_precompose_heq (P : TwoSuperfunctor R A B)
    {F G : TwoSuperfunctor R B C} (θ : TwoNatTrans F G) :
    HEq (mapPiNatTrans (TwoNatTrans.precompose P θ))
      (TwoNatTrans.precompose (mapPi P) (mapPiNatTrans θ)) := by
  apply TwoNatTrans.hext (mapPi_comp P F) (mapPi_comp P G)
  · intro a
    rfl
  · intro a b f
    rfl
end StringDiagrams.TwoEnvelope
