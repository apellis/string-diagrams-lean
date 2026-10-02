import StringDiagrams.Super.GradedTwoEnvelopeTransformation

/-!
# Coherence of the graded envelope action

Full supermodification whiskering laws use the equality transports supplied by
`mapQPiNatTrans_vcomp`. The canonical inclusion is natural on actual transformations.
This is local coherence toward §6, not a global graded 2-functor or 2-adjunction.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁ w₂ v₂ u₂
variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  {F G H : TwoSuperfunctor R B C}
namespace QPiTwoEnvelope

set_option backward.isDefEq.respectTransparency false in
/-- Left whiskering, as an equality of complete transported supermodifications. -/
theorem mapQPiSupermodification_whiskerLeft (θ : TwoNatTrans F G)
    {ψ ψ' : TwoNatTrans G H} (α : ψ ⟶ ψ') :
    mapQPiSupermodification (TwoNatTrans.whiskerLeft θ α) =
      eqToHom (mapQPiNatTrans_vcomp θ ψ) ≫
        TwoNatTrans.whiskerLeft (mapQPiNatTrans θ) (mapQPiSupermodification α) ≫
          eqToHom (mapQPiNatTrans_vcomp θ ψ').symm := by
  apply TwoNatTrans.hom_ext
  intro a
  simp only [TwoNatTrans.comp_app, TwoNatTrans.eqToHom_app]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Envelope.hom_ext
  exact mapQPiSupermodification_whiskerLeft_app θ α a

set_option backward.isDefEq.respectTransparency false in
/-- Right whiskering, as an equality of complete transported supermodifications. -/
theorem mapQPiSupermodification_whiskerRight {θ θ' : TwoNatTrans F G}
    (α : θ ⟶ θ') (ψ : TwoNatTrans G H) :
    mapQPiSupermodification (TwoNatTrans.whiskerRight α ψ) =
      eqToHom (mapQPiNatTrans_vcomp θ ψ) ≫
        TwoNatTrans.whiskerRight (mapQPiSupermodification α) (mapQPiNatTrans ψ) ≫
          eqToHom (mapQPiNatTrans_vcomp θ' ψ).symm := by
  apply TwoNatTrans.hom_ext
  intro a
  simp only [TwoNatTrans.comp_app, TwoNatTrans.eqToHom_app]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Envelope.hom_ext
  exact mapQPiSupermodification_whiskerRight_app α ψ a

/-- Naturality of the canonical inclusion on complete 2-superfunctor records. -/
theorem twoJ_naturality (F : TwoSuperfunctor R B C) :
    (twoJ R B).comp (mapQPi F) = F.comp (twoJ R C) := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    apply Iso.ext
    apply Envelope.hom_ext
    change (F.mapComp f g).hom ≫ F.map₂ (𝟙 (f ≫ g)) = 𝟙 _ ≫ (F.mapComp f g).hom
    rw [F.map₂_id, Category.comp_id, Category.id_comp]
  · funext a
    apply Iso.ext
    apply Envelope.hom_ext
    change (F.mapId a).hom ≫ F.map₂ (𝟙 (𝟙 a)) = 𝟙 _ ≫ (F.mapId a).hom
    rw [F.map₂_id, Category.comp_id, Category.id_comp]

/-- Composition with `J` evaluates coherence without an extra identity factor. -/
theorem precomposeTwoJ_mapComp_hom (S : TwoSuperfunctor R (QPiTwoEnvelope R B) C)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (((twoJ R B).comp S).mapComp f g).hom = (S.mapComp (Jm f) (Jm g)).hom := by
  change _ ≫ S.map₂ (𝟙 _) = _
  rw [S.map₂_id, Category.comp_id]
  rfl

theorem precomposeTwoJ_mapId_hom (S : TwoSuperfunctor R (QPiTwoEnvelope R B) C) (a : B) :
    (((twoJ R B).comp S).mapId a).hom = (S.mapId ⟨⟨a⟩⟩).hom := by
  change _ ≫ S.map₂ (𝟙 _) = _
  rw [S.map₂_id, Category.comp_id]
  rfl

omit [TwoSupercategory R B] in
theorem postcomposeTwoJ_mapComp_hom (F : TwoSuperfunctor R B C)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    ((F.comp (twoJ R C)).mapComp f g).hom = J2 (F.mapComp f g).hom :=
  Category.id_comp _

omit [TwoSupercategory R B] in
theorem postcomposeTwoJ_mapId_hom (F : TwoSuperfunctor R B C) (a : B) :
    ((F.comp (twoJ R C)).mapId a).hom = J2 (F.mapId a).hom :=
  Category.id_comp _

/-- Precomposition with the canonical inclusion on actual transformations.
Unlike `restrictTwoNatTrans`, this is not restricted to extension functors. -/
def precomposeTwoJ {S T : TwoSuperfunctor R (QPiTwoEnvelope R B) C}
    (θ : TwoNatTrans S T) : TwoNatTrans ((twoJ R B).comp S) ((twoJ R B).comp T) where
  X a := θ.X ⟨⟨a⟩⟩
  x f := θ.x (Jm f)
  x_mem f := θ.x_mem (Jm f)
  naturality η := θ.naturality (J2 η)
  x_comp f g := by
    rw [precomposeTwoJ_mapComp_hom, precomposeTwoJ_mapComp_hom]
    exact θ.x_comp (Jm f) (Jm g)
  x_id a := by
    rw [precomposeTwoJ_mapId_hom, precomposeTwoJ_mapId_hom]
    exact θ.x_id ⟨⟨a⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition with the canonical inclusion on actual transformations. -/
def postcomposeTwoJ (θ : TwoNatTrans F G) :
    TwoNatTrans (F.comp (twoJ R C)) (G.comp (twoJ R C)) where
  X a := Jm (θ.X a)
  x f := J2 (θ.x f)
  x_mem f := (mapQPiNatTrans θ).x_mem (Jm f)
  naturality η := (mapQPiNatTrans θ).naturality (J2 η)
  x_comp f g := by
    rw [postcomposeTwoJ_mapComp_hom, postcomposeTwoJ_mapComp_hom]
    exact (mapQPiNatTrans θ).x_comp (Jm f) (Jm g)
  x_id a := by
    rw [postcomposeTwoJ_mapId_hom, postcomposeTwoJ_mapId_hom]
    exact (mapQPiNatTrans θ).x_id ⟨⟨a⟩⟩

end QPiTwoEnvelope

namespace TwoNatTrans
omit [TwoSupercategory R B] [TwoSupercategory R C] in
/-- Extensionality with explicitly identified endpoint functors. -/
theorem hext_of_eq {F' G' : TwoSuperfunctor R B C} (hF : F = F') (hG : G = G')
    {θ : TwoNatTrans F G} {ψ : TwoNatTrans F' G'} (hX : HEq θ.X ψ.X)
    (hx : ∀ {a b : B} (f : a ⟶ b), HEq (θ.x f) (ψ.x f)) : HEq θ ψ := by
  subst F'
  subst G'
  exact heq_of_eq (TwoEnvelope.twoNatTrans_ext (eq_of_heq hX) hx)
end TwoNatTrans

namespace QPiTwoEnvelope
/-- Naturality of `J` on complete transformation records, after the functor
naturality equalities identify both endpoints. -/
theorem twoJ_naturality_natTrans (θ : TwoNatTrans F G) :
    cast (congrArg₂ (fun S T => TwoNatTrans S T) (twoJ_naturality F) (twoJ_naturality G))
      (precomposeTwoJ (mapQPiNatTrans θ)) = postcomposeTwoJ θ := by
  apply eq_of_heq
  exact (cast_heq _ _).trans
    (TwoNatTrans.hext_of_eq (twoJ_naturality F) (twoJ_naturality G) HEq.rfl
      (fun _ => HEq.rfl))

/-- Restriction along `J` preserves the actual degree-zero transformation predicate. -/
theorem precomposeTwoJ_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)]
    {S T : TwoSuperfunctor R (QPiTwoEnvelope R B) C} {θ : TwoNatTrans S T}
    (hθ : θ.IsGraded) : (precomposeTwoJ θ).IsGraded := fun f => hθ (Jm f)

/-- Postcomposition with `J` preserves and reflects graded transformations. -/
theorem postcomposeTwoJ_isGraded_iff [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] (θ : TwoNatTrans F G) :
    (postcomposeTwoJ θ).IsGraded ↔ θ.IsGraded := by
  constructor
  · intro h a b f
    exact h f
  · intro h a b f
    exact h f

/-- Naturality of `J` on actual graded transformations, not just their components. -/
theorem twoJ_naturality_gradedNatTrans [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)]
    (θ : {θ : TwoNatTrans F G // θ.IsGraded}) :
    (⟨cast (congrArg₂ (fun S T => TwoNatTrans S T) (twoJ_naturality F) (twoJ_naturality G))
      (precomposeTwoJ (mapGradedTwoNatTrans θ).1), by
        dsimp only [mapGradedTwoNatTrans]
        rw [twoJ_naturality_natTrans]
        exact (postcomposeTwoJ_isGraded_iff θ.1).2 θ.2⟩ :
      {ψ : TwoNatTrans (F.comp (twoJ R C)) (G.comp (twoJ R C)) // ψ.IsGraded}) =
    ⟨postcomposeTwoJ θ.1, (postcomposeTwoJ_isGraded_iff θ.1).2 θ.2⟩ := by
  apply Subtype.ext
  exact twoJ_naturality_natTrans θ.1
end QPiTwoEnvelope

namespace GTwoSCat
/-- The canonical inclusion packaged as a natural transformation of 1-truncations.
Its actual-transformation naturality is `twoJ_naturality_gradedNatTrans` above;
this is not a claim of a global 2-adjunction. -/
def envelopeUnit : 𝟭 (GTwoSCat.{w, w₁, v₁, u₁} R) ⟶ envelope ⋙ QPiTwoGSCat.forget where
  app B := ⟨QPiTwoEnvelope.twoJ R B, QPiTwoEnvelope.twoJ_isGraded⟩
  naturality {_ _} F := Subtype.ext (QPiTwoEnvelope.twoJ_naturality F.1).symm
end GTwoSCat
end StringDiagrams
