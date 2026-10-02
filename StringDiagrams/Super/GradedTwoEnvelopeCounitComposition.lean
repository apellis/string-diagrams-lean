import StringDiagrams.Super.GradedTwoEnvelopeCounitCoherence

/-!
# Composition and identity coherence for density comparisons

Pasting two density comparisons cancels the *middle* density pair and gives
an invertible supermodification to the direct comparison. The identity
counit square is normalized by equalities of its boundary functors, not by
pretending that its comparison transformation is strictly the identity.
This is local coherence, not a global graded 2-adjunction or a general
functor-whiskering composition law for two arbitrary counit squares.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁
variable {R : Type w} [CommRing R]

namespace TwoNatTrans
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R} {C : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  {S T U E E' E'' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}

/-- Compose comparisons by cancelling their middle density pair. -/
def pasteComparison (a : TwoNatTrans S E) (b : TwoNatTrans E T)
    (c : TwoNatTrans T E) (d : TwoNatTrans E U)
    (e : vcomp b c ≅ id E) :
    vcomp (vcomp a b) (vcomp c d) ≅ vcomp a d :=
  associator a b (vcomp c d) ≪≫
    TwoSupercategory.whiskerLeftIso (R := R)
      (B := TwoSuperfunctor R (QPiTwoEnvelope R B) C) a (associator b c d).symm ≪≫
    TwoSupercategory.whiskerLeftIso (R := R)
      (B := TwoSuperfunctor R (QPiTwoEnvelope R B) C) a
      (TwoSupercategory.whiskerRightIso (R := R)
        (B := TwoSuperfunctor R (QPiTwoEnvelope R B) C) e d) ≪≫
    TwoSupercategory.whiskerLeftIso (R := R)
      (B := TwoSuperfunctor R (QPiTwoEnvelope R B) C) a (leftUnitor d)

theorem pasteComparison_hom_isHomogeneous (a : TwoNatTrans S E) (b : TwoNatTrans E T)
    (c : TwoNatTrans T E) (d : TwoNatTrans E U)
    (e : vcomp b c ≅ id E) (he : e.hom.IsHomogeneous 0 0) :
    (pasteComparison a b c d e).hom.IsHomogeneous 0 0 := by
  intro x
  constructor
  · simpa only [zero_add] using! comp_mem
      (associator_hom_mem (R := R) (a.X x) (b.X x) ((vcomp c d).X x))
      (comp_mem (whiskerLeft_mem (a.X x)
        (inv_mem _ (associator_hom_mem (R := R) (b.X x) (c.X x) (d.X x))))
        (comp_mem (whiskerLeft_mem (a.X x) (whiskerRight_mem (d.X x) (he x).1))
          (whiskerLeft_mem (a.X x) (leftUnitor_hom_mem (R := R) (d.X x)))))
  · simpa only [zero_add] using! comp_mem_degree
      (GradedTwoSupercategory.associator_hom_mem_degree (R := R)
        (a.X x) (b.X x) ((vcomp c d).X x))
      (comp_mem_degree (GradedTwoSupercategory.whiskerLeft_mem_degree (a.X x)
        (GradedTwoSupercategory.associator_inv_mem_degree (R := R) (b.X x) (c.X x) (d.X x)))
        (comp_mem_degree (GradedTwoSupercategory.whiskerLeft_mem_degree (a.X x)
          (GradedTwoSupercategory.whiskerRight_mem_degree (d.X x) (he x).2))
          (GradedTwoSupercategory.whiskerLeft_mem_degree (a.X x)
            (GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) (d.X x)))))

/-- Transport all common-extension boundaries before pasting. -/
def pasteComparisonTransport (h : E' = E) (k : E'' = E')
    (a : TwoNatTrans S E) (b : TwoNatTrans E' T)
    (c : TwoNatTrans T E') (d : TwoNatTrans E'' U)
    (e : vcomp b c ≅ id E') :
    vcomp (vcomp a (transportSource h b)) (vcomp c (transportSource k d)) ≅
      vcomp a (transportSource (k.trans h) d) := by
  cases h
  cases k
  exact pasteComparison a b c d e

theorem pasteComparisonTransport_hom_isHomogeneous (h : E' = E) (k : E'' = E')
    (a : TwoNatTrans S E) (b : TwoNatTrans E' T)
    (c : TwoNatTrans T E') (d : TwoNatTrans E'' U)
    (e : vcomp b c ≅ id E') (he : e.hom.IsHomogeneous 0 0) :
    (pasteComparisonTransport h k a b c d e).hom.IsHomogeneous 0 0 := by
  cases h
  cases k
  exact pasteComparison_hom_isHomogeneous a b c d e he

/-- Normalize both boundary functors of a comparison square. -/
def transportBoundary {S' T' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}
    (h : S = S') (k : T = T') (θ : TwoNatTrans S T) : TwoNatTrans S' T' := by
  cases h
  cases k
  exact θ

/-- Retype an invertible supermodification along equalities of transformations. -/
def transportIso {θ θ' ψ ψ' : TwoNatTrans S T}
    (h : θ = θ') (k : ψ = ψ') (e : θ' ≅ ψ) : θ ≅ ψ' :=
  eqToIso h ≪≫ e ≪≫ eqToIso k

theorem transportIso_hom_isHomogeneous {θ θ' ψ ψ' : TwoNatTrans S T}
    (h : θ = θ') (k : ψ = ψ') (e : θ' ≅ ψ) (he : e.hom.IsHomogeneous 0 0) :
    (transportIso h k e).hom.IsHomogeneous 0 0 := by
  cases h
  cases k
  intro x
  simpa only [transportIso, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    TwoNatTrans.comp_app, TwoNatTrans.id_app, Category.id_comp, Category.comp_id] using he x
end TwoNatTrans

namespace QPiTwoEnvelope
section Comparison
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R} {C : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  (S T U : TwoSuperfunctor R (QPiTwoEnvelope R B) C)
  (hS : S.IsGraded) (hT : T.IsGraded) (hU : U.IsGraded)
  (h : restrict S = restrict T) (k : restrict T = restrict U)

/-- The actual supermodification from pasted comparisons to the direct one. -/
def comparisonCompIso :
    TwoNatTrans.vcomp (comparison S T hS hT h) (comparison T U hT hU k) ≅
      comparison S U hS hU (h.trans k) := by
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
    fun a b => QPiTwoSupercategory.homQPiLeft a b
  exact TwoNatTrans.pasteComparisonTransport (congrArg extend h.symm) (congrArg extend k.symm)
    (extendRestrictNatTransInv S hS) (extendRestrictNatTrans T hT)
    (extendRestrictNatTransInv T hT) (extendRestrictNatTrans U hU)
    (extendRestrictCounitIso T hT)

theorem comparisonCompIso_hom_isHomogeneous :
    (comparisonCompIso S T U hS hT hU h k).hom.IsHomogeneous 0 0 := by
  let : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
    fun a b => QPiTwoSupercategory.homQPiLeft a b
  exact TwoNatTrans.pasteComparisonTransport_hom_isHomogeneous _ _ _ _ _ _ _
    (extendRestrictCounitIso_hom_isHomogeneous T hT)

theorem comparisonCompIso_inv_isHomogeneous :
    (comparisonCompIso S T U hS hT hU h k).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _
    (comparisonCompIso_hom_isHomogeneous S T U hS hT hU h k)

/-- A reflexive density comparison has its specified unit supermodification. -/
def comparisonIdIso : comparison S S hS hS rfl ≅ TwoNatTrans.id S := by
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
    fun a b => QPiTwoSupercategory.homQPiLeft a b
  exact extendRestrictUnitIso S hS

theorem comparisonIdIso_hom_isHomogeneous :
    (comparisonIdIso S hS).hom.IsHomogeneous 0 0 := by
  let : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
    fun a b => QPiTwoSupercategory.homQPiLeft a b
  exact extendRestrictUnitIso_hom_isHomogeneous S hS

/-- Density comparison commutes with boundary normalization. -/
theorem comparison_transportBoundary
    {S' T' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}
    (p : S = S') (q : T = T') (hS' : S'.IsGraded) (hT' : T'.IsGraded)
    (h' : restrict S' = restrict T') :
    TwoNatTrans.transportBoundary p q (comparison S T hS hT h) =
      comparison S' T' hS' hT' h' := by
  cases p
  cases q
  rfl
end Comparison

set_option backward.isDefEq.respectTransparency false

/-- The source boundary of the identity counit square is the counit. -/
theorem counitNaturality_id_source (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (mapQPi (𝟙 B : B ⟶ B).1).comp (counit B) = counit B := by
  change (mapQPi (TwoSuperfunctor.id R B)).comp (counit B) = _
  rw [mapQPi_id, TwoSuperfunctor.id_comp]

/-- The target boundary of the identity counit square is the counit. -/
theorem counitNaturality_id_target (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (counit B).comp (𝟙 B : B ⟶ B).1 = counit B :=
  TwoSuperfunctor.comp_id _

/-- The actual identity square with normalized boundaries. -/
def counitNaturalityId (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    TwoNatTrans (counit B) (counit B) :=
  TwoNatTrans.transportBoundary (counitNaturality_id_source B)
    (counitNaturality_id_target B) (counitNaturality (𝟙 B))

theorem counitNaturalityId_eq_comparison (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    counitNaturalityId B = comparison (B := B.toGTwoSCat) (counit B) (counit B)
      (counit_isGraded B) (counit_isGraded B) rfl :=
  comparison_transportBoundary _ _ _ _ _ _ _ _ _ rfl

/-- Identity-functor coherence for the actual counit comparison. -/
def counitNaturalityIdIso (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    counitNaturalityId B ≅ TwoNatTrans.id (counit B) :=
  TwoNatTrans.transportIso (counitNaturalityId_eq_comparison B) rfl
    (comparisonIdIso (B := B.toGTwoSCat) (counit B) (counit_isGraded B))

theorem counitNaturalityIdIso_hom_isHomogeneous (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (counitNaturalityIdIso B).hom.IsHomogeneous 0 0 :=
  TwoNatTrans.transportIso_hom_isHomogeneous _ _ _
    (comparisonIdIso_hom_isHomogeneous (B := B.toGTwoSCat) (counit B) (counit_isGraded B))

theorem counitNaturalityIdIso_inv_isHomogeneous (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (counitNaturalityIdIso B).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _ (counitNaturalityIdIso_hom_isHomogeneous B)

/-- Pasting two actual normalized identity counit squares is compared to the
single identity square by the new density composition modification. -/
def counitNaturalityIdCompIso (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    TwoNatTrans.vcomp (counitNaturalityId B) (counitNaturalityId B) ≅
      counitNaturalityId B :=
  TwoNatTrans.transportIso
    (congrArg (fun θ => TwoNatTrans.vcomp θ θ) (counitNaturalityId_eq_comparison B))
    (counitNaturalityId_eq_comparison B).symm
    (comparisonCompIso (B := B.toGTwoSCat) (counit B) (counit B) (counit B)
      (counit_isGraded B) (counit_isGraded B) (counit_isGraded B) rfl rfl)

theorem counitNaturalityIdCompIso_hom_isHomogeneous (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (counitNaturalityIdCompIso B).hom.IsHomogeneous 0 0 :=
  TwoNatTrans.transportIso_hom_isHomogeneous _ _ _
    (comparisonCompIso_hom_isHomogeneous (B := B.toGTwoSCat)
      (counit B) (counit B) (counit B)
      (counit_isGraded B) (counit_isGraded B) (counit_isGraded B) rfl rfl)

theorem counitNaturalityIdCompIso_inv_isHomogeneous (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (counitNaturalityIdCompIso B).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _ (counitNaturalityIdCompIso_hom_isHomogeneous B)

end QPiTwoEnvelope
end StringDiagrams
