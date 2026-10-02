import StringDiagrams.Super.GradedTwoEnvelopeFunctor
import StringDiagrams.Super.GradedTwoEnvelopeUniversal
import StringDiagrams.Super.TwoHom

/-!
# Graded envelope action on 2-natural transformations

For the envelope functors of Brundan–Ellis, *Monoidal supercategories*, §6 (6.2),
`mapQPiNatTrans` sends an existing `TwoNatTrans F G` to an actual transformation
between `mapQPi F` and `mapQPi G`. Its object components are `Q⁰Π⁰X`, and its
coherence at `QᵐΠᵃf` is the original `x_f` with the same shift and parity labels
on source and target. The naturality axiom includes arbitrary 2-morphisms.

The existing definition of a graded transformation requires its already even
coherence `x_f` to have degree zero; it does not assign an arbitrary degree to a
transformation. This predicate is preserved and reflected. In contrast,
supermodifications may have arbitrary parity and integer degree, both of which
are preserved and reflected by `mapQPiSupermodification`.

The identity and vertical-composition laws are equalities of full transformation
records. `mapQPiHom` consumes the supermodification action as a linear superfunctor;
the whiskering lemmas compare its components after forgetting envelope labels.
They use the existing signed Π-whiskering, not an unsigned replacement. In
particular the ambient horizontal sign remains `b|x| + |y|c + bc + ab`, and the
ambient degree of `x^{n,b}_{m,a}` remains `deg x + n - m`.

No strictness, completeness, invertibility of transformation coherence, or
equivalence hypothesis is imposed. This is not a bundled 2-functor between the
2-categories of graded 2-supercategories, nor a construction of the full
2-adjunction: its global unit/counit and triangle/naturality coherence remain.
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

namespace TwoNatTrans

set_option backward.isDefEq.respectTransparency false in
/-- Identity transformations have degree-zero coherence. -/
theorem id_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R C] :
    (id F).IsGraded := by
  intro a b f
  rw [id_x]
  simpa only [add_zero, id_X] using comp_mem_degree
    (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) (F.map f))
    (GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := R) (F.map f))

set_option backward.isDefEq.respectTransparency false in
/-- Vertical composition preserves the existing graded-transformation predicate. -/
theorem IsGraded.vcomp [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R C]
    {θ : TwoNatTrans F G} {ψ : TwoNatTrans G H} (hθ : θ.IsGraded) (hψ : ψ.IsGraded) :
    (vcomp θ ψ).IsGraded := by
  intro a b f
  rw [vcomp_x]
  simpa only [add_zero, vcomp_X] using comp_mem_degree
    (GradedTwoSupercategory.associator_inv_mem_degree (R := R) _ _ _)
    (comp_mem_degree (GradedTwoSupercategory.whiskerRight_mem_degree _ (hθ f))
      (comp_mem_degree (GradedTwoSupercategory.associator_hom_mem_degree (R := R) _ _ _)
        (comp_mem_degree (GradedTwoSupercategory.whiskerLeft_mem_degree _ (hψ f))
          (GradedTwoSupercategory.associator_inv_mem_degree (R := R) _ _ _))))

end TwoNatTrans

namespace QTwoEnvelope

/-- The Q-envelope action on actual 2-natural transformations. -/
def mapQNatTrans (θ : TwoNatTrans F G) : TwoNatTrans (mapQ F) (mapQ G) where
  X a := ⟨0, θ.X a.as⟩
  x f := QEnvelope.ofHom (θ.x f.obj)
  x_mem f := θ.x_mem f.obj
  naturality η := θ.naturality (QEnvelope.toHom η)
  x_comp f g := θ.x_comp f.obj g.obj
  x_id a := θ.x_id a.as

theorem mapQNatTrans_id : mapQNatTrans (TwoNatTrans.id F) = TwoNatTrans.id (mapQ F) := by
  apply TwoNatTrans.ext_of_eq rfl
  intro a b f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem mapQNatTrans_vcomp (θ : TwoNatTrans F G) (ψ : TwoNatTrans G H) :
    mapQNatTrans (TwoNatTrans.vcomp θ ψ) = TwoNatTrans.vcomp (mapQNatTrans θ) (mapQNatTrans ψ) := by
  apply TwoNatTrans.ext_of_eq rfl
  intro a b f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem mapQNatTrans_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] {θ : TwoNatTrans F G} (hθ : θ.IsGraded) :
    (mapQNatTrans θ).IsGraded := by
  intro a b f
  change θ.x f.obj ∈ degree (R := R) (F.map f.obj ≫ θ.X b.as) (θ.X a.as ≫ G.map f.obj)
    (0 + ((f.shift + 0) - (0 + f.shift)))
  simpa only [add_zero, zero_add, sub_self] using hθ f.obj

/-- The Q-envelope action on supermodifications, without a homogeneity restriction. -/
def mapQSupermodification {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') :
    mapQNatTrans θ ⟶ mapQNatTrans θ' where
  app a := QEnvelope.ofHom (α.app a.as)
  naturality f := α.naturality f.obj
end QTwoEnvelope

namespace TwoEnvelope
set_option backward.isDefEq.respectTransparency false in
theorem mapPiNatTrans_id : mapPiNatTrans (TwoNatTrans.id F) = TwoNatTrans.id (mapPi F) := by
  apply TwoNatTrans.ext_of_eq rfl
  intro a b f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem mapPiNatTrans_vcomp (θ : TwoNatTrans F G) (ψ : TwoNatTrans G H) :
    mapPiNatTrans (TwoNatTrans.vcomp θ ψ) = TwoNatTrans.vcomp (mapPiNatTrans θ) (mapPiNatTrans ψ) := by
  apply TwoNatTrans.ext_of_eq (by
    funext a
    change Envelope.mk 0 _ = Envelope.mk (0 + 0) _
    simp only [add_zero]
    rfl)
  intro a b f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Envelope.hom_ext
  rw [toHom_mapPiNatTrans_x, TwoNatTrans.vcomp_x, TwoNatTrans.vcomp_x]
  repeat rw [Envelope.toHom_comp]
  rw [toHom_whiskerRight_of_par_zero _ _ rfl, toHom_whiskerLeft_of_par_zero _ rfl]
  rfl

theorem mapPiNatTrans_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] {θ : TwoNatTrans F G} (hθ : θ.IsGraded) :
    (mapPiNatTrans θ).IsGraded := fun f => hθ f.obj
end TwoEnvelope

namespace QPiTwoEnvelope

/-- Envelope action with components Q⁰Π⁰X and underlying coherence x. -/
def mapQPiNatTrans (θ : TwoNatTrans F G) : TwoNatTrans (mapQPi F) (mapQPi G) :=
  TwoEnvelope.mapPiNatTrans (QTwoEnvelope.mapQNatTrans θ)

theorem mapQPiNatTrans_id : mapQPiNatTrans (TwoNatTrans.id F) = TwoNatTrans.id (mapQPi F) := by
  rw [mapQPiNatTrans, QTwoEnvelope.mapQNatTrans_id, TwoEnvelope.mapPiNatTrans_id]
  rfl

theorem mapQPiNatTrans_vcomp (θ : TwoNatTrans F G) (ψ : TwoNatTrans G H) :
    mapQPiNatTrans (TwoNatTrans.vcomp θ ψ) = TwoNatTrans.vcomp (mapQPiNatTrans θ) (mapQPiNatTrans ψ) := by
  rw [mapQPiNatTrans, QTwoEnvelope.mapQNatTrans_vcomp, TwoEnvelope.mapPiNatTrans_vcomp]
  rfl

theorem mapQPiNatTrans_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] {θ : TwoNatTrans F G} (hθ : θ.IsGraded) :
    (mapQPiNatTrans θ).IsGraded :=
  TwoEnvelope.mapPiNatTrans_isGraded (QTwoEnvelope.mapQNatTrans_isGraded hθ)

@[simp] theorem mapQPiNatTrans_X (θ : TwoNatTrans F G) (a : QPiTwoEnvelope R B) :
    (mapQPiNatTrans θ).X a = ⟨0, ⟨0, θ.X a.as.as⟩⟩ := rfl

/-- At arbitrary integer shift and parity label the underlying coherence is unchanged. -/
theorem toHom_mapQPiNatTrans_x (θ : TwoNatTrans F G) {a b : QPiTwoEnvelope R B}
    (f : a ⟶ b) : toHom ((mapQPiNatTrans θ).x f) = θ.x f.obj.obj := rfl

/-- Naturality holds for all 2-morphisms, not just the even degree-zero ones. -/
theorem mapQPiNatTrans_naturality (θ : TwoNatTrans F G) {a b : QPiTwoEnvelope R B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    (mapQPi F).map₂ η ▷ (mapQPiNatTrans θ).X b ≫ (mapQPiNatTrans θ).x g =
      (mapQPiNatTrans θ).x f ≫ (mapQPiNatTrans θ).X a ◁ (mapQPi G).map₂ η :=
  (mapQPiNatTrans θ).naturality η

/-- The envelope reflects, as well as preserves, degree-zero coherence. -/
theorem mapQPiNatTrans_isGraded_iff [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] (θ : TwoNatTrans F G) :
    (mapQPiNatTrans θ).IsGraded ↔ θ.IsGraded := by
  refine ⟨?_, mapQPiNatTrans_isGraded⟩
  intro h a b f
  exact h (Jm f)

/-- Action on the existing predicate of graded 2-natural transformations. -/
def mapGradedTwoNatTrans [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)]
    (θ : {θ : TwoNatTrans F G // θ.IsGraded}) :
    {ψ : TwoNatTrans (mapQPi F) (mapQPi G) // ψ.IsGraded} :=
  ⟨mapQPiNatTrans θ.1, mapQPiNatTrans_isGraded θ.2⟩

/-- The envelope action on actual supermodifications. -/
def mapQPiSupermodification {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') :
    mapQPiNatTrans θ ⟶ mapQPiNatTrans θ' :=
  TwoEnvelope.mapPiSupermodification (QTwoEnvelope.mapQSupermodification α)

@[simp] theorem toHom_mapQPiSupermodification_app {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ')
    (a : QPiTwoEnvelope R B) : toHom ((mapQPiSupermodification α).app a) = α.app a.as.as := rfl

variable (F G) in
/-- A genuine functor on transformation categories, whose morphisms are supermodifications. -/
def mapQPiHom : TwoNatTrans F G ⥤ TwoNatTrans (mapQPi F) (mapQPi G) where
  obj := mapQPiNatTrans
  map := mapQPiSupermodification
  map_id _ := TwoNatTrans.hom_ext fun _ => rfl
  map_comp _ _ := TwoNatTrans.hom_ext fun _ => rfl

instance : (mapQPiHom F G).Additive where
  map_add := TwoNatTrans.hom_ext fun _ => rfl

instance : (mapQPiHom F G).Linear R where
  map_smul _ _ := TwoNatTrans.hom_ext fun _ => rfl

instance : IsSuperfunctor R (mapQPiHom F G) where
  map_mem {X Y p α} hα a := by
    change α.app a.as.as ∈ parity (R := R) (X.X a.as.as) (Y.X a.as.as) (p + (0 + 0))
    simpa only [add_zero] using hα a.as.as

/-- Supermodifications retain their arbitrary parity and integer degree. -/
theorem mapQPiSupermodification_isHomogeneous_iff
    [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)]
    {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') (p : ZMod 2) (n : ℤ) :
    (mapQPiSupermodification α).IsHomogeneous p n ↔ α.IsHomogeneous p n := by
  constructor
  · intro h a
    have ha := h ⟨⟨a⟩⟩
    change α.app a ∈ parity (R := R) (θ.X a) (θ'.X a) (p + (0 + 0)) ∧
      α.app a ∈ degree (R := R) (θ.X a) (θ'.X a) (n + (0 - 0)) at ha
    simpa only [add_zero, sub_self] using ha
  · intro h a
    change α.app a.as.as ∈ parity (R := R) (θ.X a.as.as) (θ'.X a.as.as) (p + (0 + 0)) ∧
      α.app a.as.as ∈ degree (R := R) (θ.X a.as.as) (θ'.X a.as.as) (n + (0 - 0))
    simpa only [add_zero, sub_self] using h a.as.as

/-- A componentwise left-whiskering consumer with arbitrary supermodifications. -/
theorem mapQPiSupermodification_whiskerLeft_app (θ : TwoNatTrans F G)
    {ψ ψ' : TwoNatTrans G H} (α : ψ ⟶ ψ') (a : QPiTwoEnvelope R B) :
    toHom ((mapQPiSupermodification (TwoNatTrans.whiskerLeft θ α)).app a) =
      toHom ((TwoNatTrans.whiskerLeft (mapQPiNatTrans θ) (mapQPiSupermodification α)).app a) := by
  change _ = QEnvelope.toHom (Envelope.toHom ((mapQPiNatTrans θ).X a ◁
    (mapQPiSupermodification α).app a))
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
  rfl

/-- A componentwise right-whiskering consumer with arbitrary supermodifications. -/
theorem mapQPiSupermodification_whiskerRight_app {θ θ' : TwoNatTrans F G}
    (α : θ ⟶ θ') (ψ : TwoNatTrans G H) (a : QPiTwoEnvelope R B) :
    toHom ((mapQPiSupermodification (TwoNatTrans.whiskerRight α ψ)).app a) =
      toHom ((TwoNatTrans.whiskerRight (mapQPiSupermodification α) (mapQPiNatTrans ψ)).app a) := by
  change _ = QEnvelope.toHom (Envelope.toHom ((mapQPiSupermodification α).app a ▷
    (mapQPiNatTrans ψ).X a))
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  rfl
end QPiTwoEnvelope

end StringDiagrams
