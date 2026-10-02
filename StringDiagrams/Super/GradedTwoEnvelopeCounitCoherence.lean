import StringDiagrams.Super.GradedTwoEnvelopeCounit
import StringDiagrams.Super.TwoHom

/-!
# Invertible supermodifications for the evaluation comparisons

The density comparisons are inverse up to actual supermodifications. Their
components compose as 1-morphisms in the target, so associators and unitors
must be retained. No strict naturality or global graded 2-adjunction is asserted.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁
variable {R : Type w} [CommRing R]

namespace TwoNatTrans
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R} {C : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  {S T E E' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}

/-- Cancel the middle pair of a four-transformation composite, with the
necessary associators and unitors, then cancel the remaining pair. -/
def cancelComparison (a : TwoNatTrans S E) (b : TwoNatTrans E S)
    (c : TwoNatTrans T E) (d : TwoNatTrans E T)
    (eS : vcomp a b ≅ id S) (eE : vcomp d c ≅ id E) :
    vcomp (vcomp a d) (vcomp c b) ≅ id S :=
  associator a d (vcomp c b) ≪≫
    TwoSupercategory.whiskerLeftIso (R := R)
      (B := TwoSuperfunctor R (QPiTwoEnvelope R B) C) a (associator d c b).symm ≪≫
    TwoSupercategory.whiskerLeftIso (R := R)
      (B := TwoSuperfunctor R (QPiTwoEnvelope R B) C) a
      (TwoSupercategory.whiskerRightIso (R := R)
        (B := TwoSuperfunctor R (QPiTwoEnvelope R B) C) eE b) ≪≫
    TwoSupercategory.whiskerLeftIso (R := R)
      (B := TwoSuperfunctor R (QPiTwoEnvelope R B) C) a (leftUnitor b) ≪≫ eS

/-- All the coherence factors are even of degree zero. -/
theorem cancelComparison_hom_isHomogeneous (a : TwoNatTrans S E) (b : TwoNatTrans E S)
    (c : TwoNatTrans T E) (d : TwoNatTrans E T)
    (eS : vcomp a b ≅ id S) (eE : vcomp d c ≅ id E)
    (hS : eS.hom.IsHomogeneous 0 0) (hE : eE.hom.IsHomogeneous 0 0) :
    (cancelComparison a b c d eS eE).hom.IsHomogeneous 0 0 := by
  intro x
  constructor
  · simpa only [zero_add] using! comp_mem
      (associator_hom_mem (R := R) (a.X x) (d.X x) ((vcomp c b).X x))
      (comp_mem (whiskerLeft_mem (a.X x)
        (inv_mem _ (associator_hom_mem (R := R) (d.X x) (c.X x) (b.X x))))
        (comp_mem (whiskerLeft_mem (a.X x) (whiskerRight_mem (b.X x) (hE x).1))
          (comp_mem (whiskerLeft_mem (a.X x) (leftUnitor_hom_mem (R := R) (b.X x)))
            (hS x).1)))
  · simpa only [zero_add] using! comp_mem_degree
      (GradedTwoSupercategory.associator_hom_mem_degree (R := R)
        (a.X x) (d.X x) ((vcomp c b).X x))
      (comp_mem_degree (GradedTwoSupercategory.whiskerLeft_mem_degree (a.X x)
        (GradedTwoSupercategory.associator_inv_mem_degree (R := R) (d.X x) (c.X x) (b.X x)))
        (comp_mem_degree (GradedTwoSupercategory.whiskerLeft_mem_degree (a.X x)
          (GradedTwoSupercategory.whiskerRight_mem_degree (b.X x) (hE x).2))
          (comp_mem_degree (GradedTwoSupercategory.whiskerLeft_mem_degree (a.X x)
            (GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) (b.X x))) (hS x).2)))

/-- The inverse of an even degree-zero invertible supermodification is again
 even of degree zero. -/
theorem iso_inv_isHomogeneous {θ ψ : TwoNatTrans S T} (e : θ ≅ ψ)
    (he : e.hom.IsHomogeneous 0 0) : e.inv.IsHomogeneous 0 0 := by
  intro x
  let ex : θ.X x ≅ ψ.X x :=
    { hom := e.hom.app x
      inv := e.inv.app x
      hom_inv_id := congrArg (fun α : θ ⟶ θ => α.app x) e.hom_inv_id
      inv_hom_id := congrArg (fun α : ψ ⟶ ψ => α.app x) e.inv_hom_id }
  exact ⟨inv_mem ex (he x).1, by simpa using inv_mem_degree ex (he x).2⟩

/-- Cancellation is stable under the equality identifying the two common
extensions; the transformations themselves are not identified strictly. -/
def cancelComparisonTransport (h : E' = E)
    (a : TwoNatTrans S E) (b : TwoNatTrans E S)
    (c : TwoNatTrans T E') (d : TwoNatTrans E' T)
    (eS : vcomp a b ≅ id S) (eE : vcomp d c ≅ id E') :
    vcomp (vcomp a (transportSource h d))
      (vcomp c (transportSource h.symm b)) ≅ id S := by
  cases h
  exact cancelComparison a b c d eS eE

theorem cancelComparisonTransport_hom_isHomogeneous (h : E' = E)
    (a : TwoNatTrans S E) (b : TwoNatTrans E S)
    (c : TwoNatTrans T E') (d : TwoNatTrans E' T)
    (eS : vcomp a b ≅ id S) (eE : vcomp d c ≅ id E')
    (hS : eS.hom.IsHomogeneous 0 0) (hE : eE.hom.IsHomogeneous 0 0) :
    (cancelComparisonTransport h a b c d eS eE).hom.IsHomogeneous 0 0 := by
  cases h
  exact cancelComparison_hom_isHomogeneous a b c d eS eE hS hE
end TwoNatTrans

namespace QPiTwoEnvelope
section Comparison
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R} {C : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  (S T : TwoSuperfunctor R (QPiTwoEnvelope R B) C)
  (hS : S.IsGraded) (hT : T.IsGraded) (h : restrict S = restrict T)

/-- A comparison followed by its reverse is isomorphic to the identity,
by a genuine invertible supermodification, not a strict equality. -/
def comparisonCompInvIso :
    TwoNatTrans.vcomp (comparison S T hS hT h) (comparison T S hT hS h.symm) ≅
      TwoNatTrans.id S := by
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
    fun a b => QPiTwoSupercategory.homQPiLeft a b
  exact TwoNatTrans.cancelComparisonTransport (congrArg extend h.symm)
    (extendRestrictNatTransInv S hS) (extendRestrictNatTrans S hS)
    (extendRestrictNatTransInv T hT) (extendRestrictNatTrans T hT)
    (extendRestrictUnitIso S hS) (extendRestrictCounitIso T hT)

/-- The reverse composite has its own actual inverse law. -/
def comparisonInvCompIso :
    TwoNatTrans.vcomp (comparison T S hT hS h.symm) (comparison S T hS hT h) ≅
      TwoNatTrans.id T :=
  comparisonCompInvIso T S hT hS h.symm

theorem comparisonCompInvIso_hom_isHomogeneous :
    (comparisonCompInvIso S T hS hT h).hom.IsHomogeneous 0 0 := by
  let : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
    fun a b => QPiTwoSupercategory.homQPiLeft a b
  exact TwoNatTrans.cancelComparisonTransport_hom_isHomogeneous _ _ _ _ _ _ _
    (extendRestrictUnitIso_hom_isHomogeneous S hS)
    (extendRestrictCounitIso_hom_isHomogeneous T hT)

theorem comparisonCompInvIso_inv_isHomogeneous :
    (comparisonCompInvIso S T hS hT h).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _ (comparisonCompInvIso_hom_isHomogeneous S T hS hT h)

theorem comparisonInvCompIso_hom_isHomogeneous :
    (comparisonInvCompIso S T hS hT h).hom.IsHomogeneous 0 0 :=
  comparisonCompInvIso_hom_isHomogeneous T S hT hS h.symm

theorem comparisonInvCompIso_inv_isHomogeneous :
    (comparisonInvCompIso S T hS hT h).inv.IsHomogeneous 0 0 :=
  comparisonCompInvIso_inv_isHomogeneous T S hT hS h.symm

end Comparison

set_option backward.isDefEq.respectTransparency false

theorem counitNaturalityInv_isGraded {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    (counitNaturalityInv F).IsGraded := comparison_isGraded _ _ _ _ _

theorem counitNaturalityInv_isStrong {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    (counitNaturalityInv F).IsStrong := comparison_isStrong _ _ _ _ _

/-- The CompInv inverse law for the counit comparison, as an invertible
supermodification with all associators and unitors retained. -/
def counitNaturalityCompInvIso {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    TwoNatTrans.vcomp (counitNaturality F) (counitNaturalityInv F) ≅
      TwoNatTrans.id ((mapQPi F.1).comp (counit C)) :=
  comparisonCompInvIso _ _ _ _ _

theorem counitNaturalityCompInvIso_hom_isHomogeneous {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    (counitNaturalityCompInvIso F).hom.IsHomogeneous 0 0 :=
  comparisonCompInvIso_hom_isHomogeneous _ _ _ _ _

theorem counitNaturalityCompInvIso_inv_isHomogeneous {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    (counitNaturalityCompInvIso F).inv.IsHomogeneous 0 0 :=
  comparisonCompInvIso_inv_isHomogeneous _ _ _ _ _

/-- The InvComp inverse law for the counit comparison, as an invertible
supermodification with all associators and unitors retained. -/
def counitNaturalityInvCompIso {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    TwoNatTrans.vcomp (counitNaturalityInv F) (counitNaturality F) ≅
      TwoNatTrans.id ((counit B).comp F.1) :=
  comparisonInvCompIso _ _ _ _ _

theorem counitNaturalityInvCompIso_hom_isHomogeneous {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    (counitNaturalityInvCompIso F).hom.IsHomogeneous 0 0 :=
  comparisonInvCompIso_hom_isHomogeneous _ _ _ _ _

theorem counitNaturalityInvCompIso_inv_isHomogeneous {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    (counitNaturalityInvCompIso F).inv.IsHomogeneous 0 0 :=
  comparisonInvCompIso_inv_isHomogeneous _ _ _ _ _

/-- The CompInv inverse law for the counit comparison, as an invertible
supermodification with all associators and unitors retained. -/
def counitLeftTriangleCompInvIso (B : GTwoSCat.{w, w₁, v₁, u₁} R) :
    TwoNatTrans.vcomp (counitLeftTriangle B) (counitLeftTriangleInv B) ≅
      TwoNatTrans.id ((mapQPi (twoJ R B)).comp (counit (GTwoSCat.envelope.obj B))) :=
  comparisonCompInvIso (B := B) (C := GTwoSCat.envelope.obj B) _ _ _ _ _

theorem counitLeftTriangleCompInvIso_hom_isHomogeneous (B : GTwoSCat.{w, w₁, v₁, u₁} R) :
    (counitLeftTriangleCompInvIso B).hom.IsHomogeneous 0 0 :=
  comparisonCompInvIso_hom_isHomogeneous (B := B) (C := GTwoSCat.envelope.obj B) _ _ _ _ _

theorem counitLeftTriangleCompInvIso_inv_isHomogeneous (B : GTwoSCat.{w, w₁, v₁, u₁} R) :
    (counitLeftTriangleCompInvIso B).inv.IsHomogeneous 0 0 :=
  comparisonCompInvIso_inv_isHomogeneous (B := B) (C := GTwoSCat.envelope.obj B) _ _ _ _ _

/-- The InvComp inverse law for the counit comparison, as an invertible
supermodification with all associators and unitors retained. -/
def counitLeftTriangleInvCompIso (B : GTwoSCat.{w, w₁, v₁, u₁} R) :
    TwoNatTrans.vcomp (counitLeftTriangleInv B) (counitLeftTriangle B) ≅
      TwoNatTrans.id (TwoSuperfunctor.id R (QPiTwoEnvelope R B)) :=
  comparisonInvCompIso (B := B) (C := GTwoSCat.envelope.obj B) _ _ _ _ _

theorem counitLeftTriangleInvCompIso_hom_isHomogeneous (B : GTwoSCat.{w, w₁, v₁, u₁} R) :
    (counitLeftTriangleInvCompIso B).hom.IsHomogeneous 0 0 :=
  comparisonInvCompIso_hom_isHomogeneous (B := B) (C := GTwoSCat.envelope.obj B) _ _ _ _ _

theorem counitLeftTriangleInvCompIso_inv_isHomogeneous (B : GTwoSCat.{w, w₁, v₁, u₁} R) :
    (counitLeftTriangleInvCompIso B).inv.IsHomogeneous 0 0 :=
  comparisonInvCompIso_inv_isHomogeneous (B := B) (C := GTwoSCat.envelope.obj B) _ _ _ _ _

end QPiTwoEnvelope
end StringDiagrams
