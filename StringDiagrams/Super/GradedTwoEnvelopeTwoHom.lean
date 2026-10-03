import StringDiagrams.Super.GradedTwoHom
import StringDiagrams.Super.TwoSuperequivalenceWhitehead

/-!
# The graded envelope hom 2-superequivalence

The graded analogue following Brundan–Ellis, *Monoidal supercategories*, Lemma
6.11 and Remark 4.10: extension is a strict 2-superfunctor between the actual
hom 2-supercategories of graded functors and all graded oplax transformations.
It is locally a superequivalence and dense on objects up to superequivalence;
Whitehead gives `IsTwoSuperequivalence`. All supermodifications are retained,
and their homogeneous parity/degree is preserved and reflected explicitly.

The target is any graded 2-supercategory whose homs have `(Q, Π)` structures
(in particular the hom structures of a `(Q, Π)`-2-supercategory). The base ring
is any commutative ring. No strongness or strictness assumption is added.
This hom universal property is not a global 3-supercategory or 2-adjunction.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁ w₂ v₂ u₂

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R C] [GradedTwoSupercategory R C]

namespace GradedTwoHom
/-- Equality transport of arbitrary modifications is detected componentwise. -/
theorem hom_heq {F G : GradedTwoHom R B C} {θ₁ θ₁' θ₂ θ₂' : F ⟶ G}
    (h₁ : θ₁ = θ₁') (h₂ : θ₂ = θ₂') {α : θ₁ ⟶ θ₂} {β : θ₁' ⟶ θ₂'}
    (h : ∀ a, HEq (α.app a) (β.app a)) : HEq α β := by
  subst h₁ h₂
  exact heq_of_eq (TwoNatTrans.hom_ext fun a => eq_of_heq (h a))
end GradedTwoHom

namespace QPiTwoEnvelope
variable [∀ a b : C, QPiSupercategory R (a ⟶ b)]

/-- Extension of a bundled graded functor. -/
def extendGraded (F : GradedTwoHom R B C) : GradedTwoHom R (QPiTwoEnvelope R B) C :=
  ⟨extend F.toTwoSuperfunctor, extend_isGraded _ F.isGraded⟩

/-- Extension of every graded oplax transformation, not just strong ones. -/
def extendGradedNatTrans {F G : GradedTwoHom R B C} (θ : F ⟶ G) :
    extendGraded F ⟶ extendGraded G :=
  ⟨extendTwoNatTrans θ.val, extendTwoNatTrans_isGraded θ.property⟩

theorem extendGradedNatTrans_comp {F G H : GradedTwoHom R B C} (θ : F ⟶ G) (ψ : G ⟶ H) :
    extendGradedNatTrans (θ ≫ ψ) = extendGradedNatTrans θ ≫ extendGradedNatTrans ψ :=
  Subtype.ext (extendTwoNatTrans_vcomp θ.val ψ.val)

theorem extendGradedNatTrans_id (F : GradedTwoHom R B C) :
    extendGradedNatTrans (𝟙 F) = 𝟙 (extendGraded F) :=
  Subtype.ext extendTwoNatTrans_id

variable (R B C) in
/-- Strict data of graded envelope extension on the hom 2-supercategories. -/
def extendGradedCore :
    TwoSuperfunctor.StrictCore R (GradedTwoHom R B C) (GradedTwoHom R (QPiTwoEnvelope R B) C) where
  obj := extendGraded
  map := extendGradedNatTrans
  map₂ := extendSupermodification
  map₂_id _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_comp _ _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_add _ _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_smul _ _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_mem hα a := hα a.as.as
  map_comp := extendGradedNatTrans_comp
  map_id := extendGradedNatTrans_id
  map₂_whiskerLeft θ _ _ α :=
    GradedTwoHom.hom_heq (extendGradedNatTrans_comp θ _) (extendGradedNatTrans_comp θ _)
      fun _ => HEq.rfl
  map₂_whiskerRight α ψ :=
    GradedTwoHom.hom_heq (extendGradedNatTrans_comp _ ψ) (extendGradedNatTrans_comp _ ψ)
      fun _ => HEq.rfl
  map₂_associator θ ψ φ :=
    GradedTwoHom.hom_heq
      (show extendGradedNatTrans ((θ ≫ ψ) ≫ φ) =
          (extendGradedNatTrans θ ≫ extendGradedNatTrans ψ) ≫ extendGradedNatTrans φ from
        by rw [extendGradedNatTrans_comp, extendGradedNatTrans_comp])
      (show extendGradedNatTrans (θ ≫ ψ ≫ φ) =
          extendGradedNatTrans θ ≫ extendGradedNatTrans ψ ≫ extendGradedNatTrans φ from
        by rw [extendGradedNatTrans_comp, extendGradedNatTrans_comp]) fun _ => HEq.rfl
  map₂_leftUnitor θ :=
    GradedTwoHom.hom_heq
      (show extendGradedNatTrans (𝟙 _ ≫ θ) = 𝟙 _ ≫ extendGradedNatTrans θ from
        by rw [extendGradedNatTrans_comp, extendGradedNatTrans_id])
      (show extendGradedNatTrans θ = extendGradedNatTrans θ from rfl) fun _ => HEq.rfl
  map₂_rightUnitor θ :=
    GradedTwoHom.hom_heq
      (show extendGradedNatTrans (θ ≫ 𝟙 _) = extendGradedNatTrans θ ≫ 𝟙 _ from
        by rw [extendGradedNatTrans_comp, extendGradedNatTrans_id])
      (show extendGradedNatTrans θ = extendGradedNatTrans θ from rfl) fun _ => HEq.rfl

variable (R B C) in
/-- The graded envelope extension as an actual 2-superfunctor on hom 2-supercategories. -/
def extendGradedTwoHom :
    TwoSuperfunctor R (GradedTwoHom R B C) (GradedTwoHom R (QPiTwoEnvelope R B) C) :=
  (extendGradedCore R B C).toTwoSuperfunctor

@[simp] theorem extendGradedTwoHom_obj (F : GradedTwoHom R B C) :
    (extendGradedTwoHom R B C).obj F = extendGraded F := rfl

@[simp] theorem extendGradedTwoHom_map {F G : GradedTwoHom R B C} (θ : F ⟶ G) :
    (extendGradedTwoHom R B C).map θ = extendGradedNatTrans θ := rfl

@[simp] theorem extendGradedTwoHom_map₂ {F G : GradedTwoHom R B C}
    {θ ψ : F ⟶ G} (α : θ ⟶ ψ) :
    (extendGradedTwoHom R B C).map₂ α = extendSupermodification α := rfl

/-- Extension is strict as a functor between these (possibly weak) hom 2-supercategories. -/
theorem extendGradedTwoHom_isStrict : (extendGradedTwoHom R B C).IsStrict :=
  (extendGradedCore R B C).isStrict

/-- The packaged action retains, preserves and reflects every modification bidegree. -/
theorem extendGradedTwoHom_map₂_isHomogeneous_iff {F G : GradedTwoHom R B C}
    {θ ψ : F ⟶ G} (α : θ ⟶ ψ) (p : ZMod 2) (n : ℤ) :
    ((extendGradedTwoHom R B C).map₂ α).IsHomogeneous p n ↔ α.IsHomogeneous p n :=
  extendSupermodification_isHomogeneous_iff α p n

instance (F G : GradedTwoHom R B C) : ((extendGradedTwoHom R B C).mapFunctor F G).Faithful where
  map_injective h := (extendHom F.toTwoSuperfunctor G.toTwoSuperfunctor).map_injective h

instance (F G : GradedTwoHom R B C) : ((extendGradedTwoHom R B C).mapFunctor F G).Full where
  map_surjective := (extendHom F.toTwoSuperfunctor G.toTwoSuperfunctor).map_surjective

/-- Restriction of graded transformations witnesses density of the local functor. -/
theorem extendGradedTwoHom_evenlyDense (F G : GradedTwoHom R B C) :
    EvenlyDense R ((extendGradedTwoHom R B C).mapFunctor F G) := fun ψ =>
  ⟨⟨restrictTwoNatTrans ψ.val, restrictTwoNatTrans_isGraded ψ.property⟩,
    GradedTwoHom.isoMk (eqToIso (extendTwoNatTrans_restrictTwoNatTrans ψ.val)),
    TwoEnvelope.eqToHom_mem (extendTwoNatTrans_restrictTwoNatTrans ψ.val)⟩

/-- The local superequivalence includes every graded oplax transformation and all modifications. -/
def extendGradedHomSuperequivalence (F G : GradedTwoHom R B C) :
    Superequivalence R ((extendGradedTwoHom R B C).mapFunctor F G) :=
  Superequivalence.ofFullyFaithful _ (extendGradedTwoHom_evenlyDense F G)

variable [GradedTwoSupercategory R B]

/-- Restriction of a bundled graded functor along the envelope inclusion. -/
def restrictGraded (T : GradedTwoHom R (QPiTwoEnvelope R B) C) : GradedTwoHom R B C :=
  ⟨restrict T.toTwoSuperfunctor, restrict_isGraded T.isGraded⟩

/-- The graded counit transformation witnesses object density. -/
def extendRestrictGradedNatTrans (T : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    extendGraded (restrictGraded T) ⟶ T :=
  ⟨extendRestrictNatTrans T.toTwoSuperfunctor T.isGraded,
    extendRestrictNatTrans_isGraded T.toTwoSuperfunctor T.isGraded⟩

/-- The inverse graded transformation for the object-density witness. -/
def extendRestrictGradedNatTransInv (T : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    T ⟶ extendGraded (restrictGraded T) :=
  ⟨extendRestrictNatTransInv T.toTwoSuperfunctor T.isGraded,
    extendRestrictNatTransInv_isGraded T.toTwoSuperfunctor T.isGraded⟩

/-- The object-density counit, in the actual full category of graded transformations. -/
def extendRestrictGradedCounitIso (T : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    extendRestrictGradedNatTrans T ≫ extendRestrictGradedNatTransInv T ≅ 𝟙 _ :=
  GradedTwoHom.isoMk (extendRestrictCounitIso T.toTwoSuperfunctor T.isGraded)

/-- The object-density unit, in the actual full category of graded transformations. -/
def extendRestrictGradedUnitIso (T : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    extendRestrictGradedNatTransInv T ≫ extendRestrictGradedNatTrans T ≅ 𝟙 T :=
  GradedTwoHom.isoMk (extendRestrictUnitIso T.toTwoSuperfunctor T.isGraded)

/-- The density counit is even and has degree zero. -/
theorem extendRestrictGradedCounitIso_hom_isHomogeneous
    (T : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    (extendRestrictGradedCounitIso T).hom.IsHomogeneous 0 0 :=
  extendRestrictCounitIso_hom_isHomogeneous T.toTwoSuperfunctor T.isGraded

/-- The density unit is even and has degree zero. -/
theorem extendRestrictGradedUnitIso_hom_isHomogeneous
    (T : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    (extendRestrictGradedUnitIso T).hom.IsHomogeneous 0 0 :=
  extendRestrictUnitIso_hom_isHomogeneous T.toTwoSuperfunctor T.isGraded

/-- Density uses graded inverse transformations and even degree-zero comparison modifications. -/
theorem extendRestrictGradedNatTrans_isSuperequivalence
    (T : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    IsSuperequivalence R (extendRestrictGradedNatTrans T) :=
  ⟨extendRestrictGradedNatTransInv T, extendRestrictGradedCounitIso T,
    extendRestrictGradedUnitIso T,
    fun a => (extendRestrictGradedCounitIso_hom_isHomogeneous T a).1,
    fun a => (extendRestrictGradedUnitIso_hom_isHomogeneous T a).1⟩

/-- **Graded analogue of Remark 4.10 (following Lemma 6.11).** Extension is locally a
superequivalence and every graded functor on the envelope is equivalent to an extension. -/
theorem extendGradedTwoHom_isLocalTwoSuperequivalence :
    (extendGradedTwoHom R B C).IsLocalTwoSuperequivalence where
  hom F G := ⟨extendGradedHomSuperequivalence F G⟩
  essSurj T := ⟨restrictGraded T, extendRestrictGradedNatTrans T,
    extendRestrictGradedNatTrans_isSuperequivalence T⟩

/-- Whitehead upgrades the hom universal property to the quasi-inverse formulation of
2-superequivalence. This is not a global 3-categorical adjunction assertion. -/
theorem extendGradedTwoHom_isTwoSuperequivalence :
    (extendGradedTwoHom R B C).IsTwoSuperequivalence :=
  extendGradedTwoHom_isLocalTwoSuperequivalence.isTwoSuperequivalence

end QPiTwoEnvelope
end StringDiagrams
end
