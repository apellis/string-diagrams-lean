import StringDiagrams.Super.GradedTwoEnvelopeCounitPostcomposeComposition

/-!
# Actual postcomposition of inverse density

The inverse-density prerequisite for right counit-paste. This module keeps the
original inverse transformation, arbitrary postcomposition constraints, and the
coherent inverse bridge. It does not assert the full right-paste comparison.
-/
noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁
variable {R : Type w} [CommRing R]
namespace QPiTwoEnvelope
set_option backward.isDefEq.respectTransparency false
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R}
  {C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  (T : TwoSuperfunctor R (QPiTwoEnvelope R B) C) (hT : T.IsGraded)
  (G : C ⟶ D)
local instance : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b
local instance : ∀ a b : D, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b

/-- The density cell after mapping its middle factor, with target unitors. -/
def postcomposeInverseDensityX {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    G.1.map (T.map f) ≫ 𝟙 (G.1.obj (T.obj b)) ⟶
      𝟙 (G.1.obj (T.obj a)) ≫ G.1.map ((extend (restrict T)).map f) :=
  (rightUnitor _).hom ≫ G.1.map₂ (extendRestrictAppInv T hT f) ≫ (leftUnitor _).inv

theorem postcomposeInverseDensityX_mem {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    postcomposeInverseDensityX T hT G f ∈ parity (R := R) _ _ 0 := by
  simpa only [postcomposeInverseDensityX, zero_add] using! comp_mem
    (rightUnitor_hom_mem (R := R) _)
    (comp_mem (G.1.map₂_mem (extendRestrictAppInv_mem T hT f))
      (inv_mem _ (leftUnitor_hom_mem (R := R) _)))

/-- Naturality includes odd and nonzero-degree input 2-morphisms. -/
theorem postcomposeInverseDensityX_naturality {a b : QPiTwoEnvelope R B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    G.1.map₂ (T.map₂ η) ▷ 𝟙 (G.1.obj (T.obj b)) ≫
        postcomposeInverseDensityX T hT G g =
      postcomposeInverseDensityX T hT G f ≫ 𝟙 (G.1.obj (T.obj a)) ◁ G.1.map₂ ((extend (restrict T)).map₂ η) := by
  unfold postcomposeInverseDensityX
  erw [rightUnitor_naturality_assoc R, ← reassoc_of% G.1.map₂_comp,
    extendRestrictAppInv_naturality, G.1.map₂_comp]
  simp only [Category.assoc]
  erw [leftUnitor_inv_naturality R (G.1.map₂ ((extend (restrict T)).map₂ η))]
  rfl

/-- The actual mapped inverse density, normalized by the unit constraint of `G`. -/
def postcomposeInverseDensity :
    TwoNatTrans (T.comp G.1) ((extend (restrict T)).comp G.1) where
  X a := 𝟙 (G.1.obj (T.obj a))
  x f := postcomposeInverseDensityX T hT G f
  x_mem f := postcomposeInverseDensityX_mem T hT G f
  naturality η := postcomposeInverseDensityX_naturality T hT G η
  x_comp f g := xcomp_of_J (F' := T.comp G.1) (G' := (extend (restrict T)).comp G.1)
    (fun a => 𝟙 (G.1.obj (T.obj a))) (fun f => postcomposeInverseDensityX T hT G f)
    (fun f => postcomposeInverseDensityX_mem T hT G f)
    (fun η => postcomposeInverseDensityX_naturality T hT G η)
    (fun {a b c} f g => by
      have h₁ : ((T.comp G.1).mapComp (Jm (R := R) f) (Jm g)).hom =
          (((extend (restrict T)).comp G.1).mapComp (Jm f) (Jm g)).hom := by
        simp only [TwoSuperfunctor.comp, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom,
          extendComp_J, restrict_mapComp]
        rfl
      have h₂ := extendRestrictAppInv_J T hT (a := (⟨⟨a⟩⟩ : QPiTwoEnvelope R B))
        (b := (⟨⟨c⟩⟩ : QPiTwoEnvelope R B)) (f ≫ g)
      have h₃ := extendRestrictAppInv_J T hT (a := (⟨⟨a⟩⟩ : QPiTwoEnvelope R B))
        (b := (⟨⟨b⟩⟩ : QPiTwoEnvelope R B)) f
      have h₄ := extendRestrictAppInv_J T hT (a := (⟨⟨b⟩⟩ : QPiTwoEnvelope R B))
        (b := (⟨⟨c⟩⟩ : QPiTwoEnvelope R B)) g
      simp only [xcompL, xcompR, postcomposeInverseDensityX]
      erw [h₂, h₃, h₄, G.1.map₂_id, G.1.map₂_id, G.1.map₂_id]
      simp only [Category.id_comp]
      erw [h₁]
      exact TwoEnvelope.unit_coherence R (G.1.map (T.map (Jm f)))
        (G.1.map (T.map (Jm g))) (((extend (restrict T)).comp G.1).mapComp (Jm f) (Jm g)).hom) f g
  x_id a := by
    have h : extendRestrictAppInv T hT (𝟙 a) = 𝟙 _ := extendRestrictAppInv_J T hT (𝟙 a.as.as)
    show _ ≫ _ ≫ _ ≫ (rightUnitor _).hom ≫ G.1.map₂ (extendRestrictAppInv T hT (𝟙 a)) ≫
      (leftUnitor _).inv = _
    erw [h, G.1.map₂_id, Category.id_comp, rightUnitor_naturality_assoc R]
    erw [leftUnitor_inv_naturality R]
    erw [unitors_inv_equal R]
    simp only [Iso.hom_inv_id_assoc]
    erw [Iso.hom_inv_id_assoc]
    rfl

theorem postcomposeInverseDensity_isGraded : (postcomposeInverseDensity T hT G).IsGraded := by
  intro a b f
  simpa only [postcomposeInverseDensity, postcomposeInverseDensityX, zero_add] using! comp_mem_degree
    (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) _)
    (comp_mem_degree (G.2.map₂_mem_degree (extendRestrictAppInv_mem_degree T hT f))
      (GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := R) _))

/-- Invertibility of all normalized inverse-density cells, for arbitrary graded `G`. -/
theorem postcomposeInverseDensity_isStrong : (postcomposeInverseDensity T hT G).IsStrong := by
  intro a b f
  change IsIso ((rightUnitor _).hom ≫ G.1.map₂ (extendRestrictAppInv T hT f) ≫
    (leftUnitor _).inv)
  have := hT.isGradedSuperfunctor a b
  have : IsIso (extendRestrictAppInv T hT f) :=
    inferInstanceAs (IsIso ((QPiEnvelope.extendRestrictIso (homFunctor T a b)).app f).inv)
  have : IsIso (G.1.map₂ (extendRestrictAppInv T hT f)) :=
    (G.1.mapFunctor _ _).map_isIso _
  infer_instance

/-- Mapping the inverse density transformation is isomorphic, not equal, to its unit
normalization. The components are precisely the inverses of `G.mapId`. -/
def postcomposeInverseDensityIso :
    TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT) ≅
      postcomposeInverseDensity T hT G :=
  TwoEnvelope.supermodificationIso (fun a => (G.1.mapId (T.obj a)).symm) (by
    intro a b f
    change ((G.1.mapComp _ _).hom ≫
      G.1.map₂ ((rightUnitor _).hom ≫ extendRestrictAppInv T hT f ≫ (leftUnitor _).inv) ≫
      (G.1.mapComp _ _).inv) ≫ (G.1.mapId _).inv ▷ _ =
        _ ◁ (G.1.mapId _).inv ≫ (rightUnitor _).hom ≫
          G.1.map₂ (extendRestrictAppInv T hT f) ≫ (leftUnitor _).inv
    simp only [G.1.map₂_comp, Category.assoc]
    rw [← cancel_mono (whiskerRightIso (R := R) (G.1.mapId (T.obj a))
      (G.1.map ((extend (restrict T)).map f))).hom]
    dsimp only [whiskerRightIso]
    simp only [Category.assoc]
    erw [inv_hom_whiskerRight R]
    rw [← cancel_epi (whiskerLeftIso (R := R)
      (G.1.map (T.map f)) (G.1.mapId (T.obj b))).hom]
    dsimp only [whiskerLeftIso]
    erw [whiskerLeft_hom_inv_assoc R]
    erw [reassoc_of% G.1.map₂_rightUnitor]
    rw [← cancel_mono (G.1.mapComp (𝟙 (T.obj a)) ((extend (restrict T)).map f)).hom]
    simp only [Category.assoc]
    erw [Category.id_comp, Iso.inv_hom_id]
    rw [← cancel_mono (G.1.map₂Iso (leftUnitor ((extend (restrict T)).map f))).hom]
    dsimp only [TwoSuperfunctor.map₂Iso]
    simp only [Category.assoc]
    erw [G.1.map₂_leftUnitor]
    simp only [Iso.inv_hom_id, Category.comp_id]
    erw [Category.id_comp, ← G.1.map₂_comp, Iso.inv_hom_id, G.1.map₂_id, Category.comp_id])

theorem postcomposeInverseDensityIso_hom_isHomogeneous :
    (postcomposeInverseDensityIso T hT G).hom.IsHomogeneous 0 0 := by
  intro a
  exact ⟨inv_mem _ (G.1.mapId_hom_mem (T.obj a)), by
    simpa using! inv_mem_degree _ (G.2.mapId_hom_mem_degree (T.obj a))⟩

theorem postcomposeInverseDensityIso_inv_isHomogeneous :
    (postcomposeInverseDensityIso T hT G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _ (postcomposeInverseDensityIso_hom_isHomogeneous T hT G)

/-- Both normalized transformations use the original mutually inverse density cells. -/
def postcomposeDensityCounitIso :
    TwoNatTrans.vcomp (postcomposeDensity T hT G) (postcomposeInverseDensity T hT G) ≅
      TwoNatTrans.id ((extend (restrict T)).comp G.1) :=
  TwoEnvelope.supermodificationIso (fun a => leftUnitor (𝟙 (G.1.obj (T.obj a)))) fun f =>
    vcomp_unitors_naturality R _ _ (by
      rw [← G.1.map₂_comp, extendRestrictApp_comp_inv, G.1.map₂_id]
      rfl)

def postcomposeDensityUnitIso :
    TwoNatTrans.vcomp (postcomposeInverseDensity T hT G) (postcomposeDensity T hT G) ≅
      TwoNatTrans.id (T.comp G.1) :=
  TwoEnvelope.supermodificationIso (fun a => leftUnitor (𝟙 (G.1.obj (T.obj a)))) fun f =>
    vcomp_unitors_naturality R _ _ (by
      rw [← G.1.map₂_comp, extendRestrictAppInv_comp, G.1.map₂_id]
      rfl)

theorem postcomposeDensityCounitIso_hom_isHomogeneous :
    (postcomposeDensityCounitIso T hT G).hom.IsHomogeneous 0 0 := fun _ =>
  ⟨leftUnitor_hom_mem (R := R) _, GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) _⟩

theorem postcomposeDensityUnitIso_hom_isHomogeneous :
    (postcomposeDensityUnitIso T hT G).hom.IsHomogeneous 0 0 := fun _ =>
  ⟨leftUnitor_hom_mem (R := R) _, GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) _⟩

/-- The reverse bridge: chosen forward density, then the actual normalized inverse.
The order is forced by its endpoints; the following two isomorphisms verify that
it is a coherent inverse of the pre-existing `postcomposeDensityBridge`. -/
def postcomposeDensityBridgeInv :
    TwoNatTrans (extend (restrict (T.comp G.1))) ((extend (restrict T)).comp G.1) :=
  TwoNatTrans.vcomp (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2))
    (postcomposeInverseDensity T hT G)

theorem postcomposeDensityBridgeInv_isGraded :
    (postcomposeDensityBridgeInv T hT G).IsGraded :=
  TwoNatTrans.IsGraded.vcomp (extendRestrictNatTrans_isGraded _ _)
    (postcomposeInverseDensity_isGraded T hT G)

/-- The original forward bridge followed by the inverse bridge cancels coherently. -/
def postcomposeDensityBridgeCounitIso :
    TwoNatTrans.vcomp (postcomposeDensityBridge T hT G) (postcomposeDensityBridgeInv T hT G) ≅
      TwoNatTrans.id ((extend (restrict T)).comp G.1) :=
  TwoNatTrans.cancelComparison _ _ _ _ (postcomposeDensityCounitIso T hT G)
    (extendRestrictUnitIso (T.comp G.1) (hT.comp G.2))

/-- The reverse order also cancels, without strictifying any constraint. -/
def postcomposeDensityBridgeUnitIso :
    TwoNatTrans.vcomp (postcomposeDensityBridgeInv T hT G) (postcomposeDensityBridge T hT G) ≅
      TwoNatTrans.id (extend (restrict (T.comp G.1))) :=
  TwoNatTrans.cancelComparison _ _ _ _
    (extendRestrictCounitIso (T.comp G.1) (hT.comp G.2)) (postcomposeDensityUnitIso T hT G)

theorem postcomposeDensityBridgeCounitIso_hom_isHomogeneous :
    (postcomposeDensityBridgeCounitIso T hT G).hom.IsHomogeneous 0 0 :=
  TwoNatTrans.cancelComparison_hom_isHomogeneous _ _ _ _ _ _
    (postcomposeDensityCounitIso_hom_isHomogeneous T hT G)
    (extendRestrictUnitIso_hom_isHomogeneous _ _)

theorem postcomposeDensityBridgeUnitIso_hom_isHomogeneous :
    (postcomposeDensityBridgeUnitIso T hT G).hom.IsHomogeneous 0 0 :=
  TwoNatTrans.cancelComparison_hom_isHomogeneous _ _ _ _ _ _
    (extendRestrictCounitIso_hom_isHomogeneous _ _)
    (postcomposeDensityUnitIso_hom_isHomogeneous T hT G)

/-- Cancel inverse density followed by forward density before the reverse bridge. -/
def postcomposeInverseDensityBridgeCollapseIso :
    TwoNatTrans.vcomp (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
      (postcomposeDensityBridgeInv T hT G) ≅ postcomposeInverseDensity T hT G :=
  (associator (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D)
    (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
    (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2))
    (postcomposeInverseDensity T hT G)).symm ≪≫
  TwoSupercategory.whiskerRightIso (R := R)
    (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D)
    (extendRestrictUnitIso (T.comp G.1) (hT.comp G.2)) (postcomposeInverseDensity T hT G) ≪≫
  leftUnitor (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D) (postcomposeInverseDensity T hT G)

theorem postcomposeInverseDensityBridgeCollapseIso_hom_isHomogeneous :
    (postcomposeInverseDensityBridgeCollapseIso T hT G).hom.IsHomogeneous 0 0 := by
  intro a
  constructor
  · simpa only [zero_add] using! comp_mem
      (inv_mem _ (associator_hom_mem (R := R) _ _ ((postcomposeInverseDensity T hT G).X a)))
      (comp_mem (whiskerRight_mem _
        (extendRestrictUnitIso_hom_isHomogeneous (T.comp G.1) (hT.comp G.2) a).1)
        (leftUnitor_hom_mem (R := R) _))
  · simpa only [zero_add] using! comp_mem_degree
      (GradedTwoSupercategory.associator_inv_mem_degree (R := R) _ _
        ((postcomposeInverseDensity T hT G).X a))
      (comp_mem_degree (GradedTwoSupercategory.whiskerRight_mem_degree _
        (extendRestrictUnitIso_hom_isHomogeneous (T.comp G.1) (hT.comp G.2) a).2)
        (GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) _))

/-- Factor the original postcomposed inverse density, not a replacement:
first inverse density of `T.comp G`, then the coherent inverse bridge. -/
def postcomposeInverseDensityFactorizationIso :
    TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT) ≅
      TwoNatTrans.vcomp (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
        (postcomposeDensityBridgeInv T hT G) :=
  postcomposeInverseDensityIso T hT G ≪≫ (postcomposeInverseDensityBridgeCollapseIso T hT G).symm

theorem postcomposeInverseDensityFactorizationIso_hom_isHomogeneous :
    (postcomposeInverseDensityFactorizationIso T hT G).hom.IsHomogeneous 0 0 := by
  intro a
  have h := TwoNatTrans.iso_inv_isHomogeneous _
    (postcomposeInverseDensityBridgeCollapseIso_hom_isHomogeneous T hT G) a
  exact ⟨by simpa only [zero_add] using!
      comp_mem (postcomposeInverseDensityIso_hom_isHomogeneous T hT G a).1 h.1,
    by simpa only [zero_add] using!
      comp_mem_degree (postcomposeInverseDensityIso_hom_isHomogeneous T hT G a).2 h.2⟩

theorem postcomposeInverseDensityFactorizationIso_inv_isHomogeneous :
    (postcomposeInverseDensityFactorizationIso T hT G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _
    (postcomposeInverseDensityFactorizationIso_hom_isHomogeneous T hT G)

/-- The unit constraint is not silently replaced by an identity. -/
theorem postcomposeInverseDensityIso_hom_app (a : QPiTwoEnvelope R B) :
    (postcomposeInverseDensityIso T hT G).hom.app a = (G.1.mapId (T.obj a)).inv := rfl

/-- Both arbitrary shifted cells and the full postcomposition compositor survive. -/
theorem postcomposeInverseDensityFactorizationIso_hom_naturality
    {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).x f ≫
        (postcomposeInverseDensityFactorizationIso T hT G).hom.app a ▷
          ((extend (restrict T)).comp G.1).map f =
      (T.comp G.1).map f ◁ (postcomposeInverseDensityFactorizationIso T hT G).hom.app b ≫
        (TwoNatTrans.vcomp (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
          (postcomposeDensityBridgeInv T hT G)).x f :=
  (postcomposeInverseDensityFactorizationIso T hT G).hom.naturality f

theorem postcomposeInverseDensityFactorizationIso_inv_naturality
    {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (TwoNatTrans.vcomp (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
        (postcomposeDensityBridgeInv T hT G)).x f ≫
        (postcomposeInverseDensityFactorizationIso T hT G).inv.app a ▷
          ((extend (restrict T)).comp G.1).map f =
      (T.comp G.1).map f ◁ (postcomposeInverseDensityFactorizationIso T hT G).inv.app b ≫
        (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).x f :=
  (postcomposeInverseDensityFactorizationIso T hT G).inv.naturality f

theorem postcomposeInverseDensityFactorizationIso_hom_inv_id :
    (postcomposeInverseDensityFactorizationIso T hT G).hom ≫
      (postcomposeInverseDensityFactorizationIso T hT G).inv =
        𝟙 (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)) :=
  (postcomposeInverseDensityFactorizationIso T hT G).hom_inv_id

theorem postcomposeInverseDensityFactorizationIso_inv_hom_id :
    (postcomposeInverseDensityFactorizationIso T hT G).inv ≫
      (postcomposeInverseDensityFactorizationIso T hT G).hom =
        𝟙 (TwoNatTrans.vcomp (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
          (postcomposeDensityBridgeInv T hT G)) :=
  (postcomposeInverseDensityFactorizationIso T hT G).inv_hom_id

/-- Naturality of the original transformation for every 2-morphism, including odd ones. -/
theorem postcomposeActualInverseDensity_naturality
    {a b : QPiTwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    (T.comp G.1).map₂ η ▷ (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).X b ≫
        (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).x g =
      (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).x f ≫
        (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).X a ◁
          ((extend (restrict T)).comp G.1).map₂ η :=
  (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).naturality η

section ComparisonConsumer
variable (S : TwoSuperfunctor R (QPiTwoEnvelope R B) C)
  (hS : S.IsGraded) (h : restrict S = restrict T)

/-- The original density pair with only its inverse-density leg factored.
The forward leg's actual source transport is deliberately retained. -/
def postcomposeComparisonInverseFactoredPair : TwoNatTrans (S.comp G.1) (T.comp G.1) :=
  TwoNatTrans.vcomp
    (TwoNatTrans.vcomp (extendRestrictNatTransInv (S.comp G.1) (hS.comp G.2))
      (postcomposeDensityBridgeInv S hS G))
    (TwoNatTrans.postcompose G.1
      (TwoNatTrans.transportSource (congrArg extend h.symm) (extendRestrictNatTrans T hT)))

/-- Apply the inverse-density factorization to the existing, actual separated pair. -/
def postcomposeComparisonDensityPairInverseIso :
    postcomposeComparisonDensityPair S T hS hT h G ≅
      postcomposeComparisonInverseFactoredPair T hT G S hS h :=
  TwoSupercategory.whiskerRightIso (R := R)
    (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D)
    (postcomposeInverseDensityFactorizationIso S hS G) _

theorem postcomposeComparisonDensityPairInverseIso_hom_isHomogeneous :
    (postcomposeComparisonDensityPairInverseIso T hT G S hS h).hom.IsHomogeneous 0 0 := by
  intro a
  exact ⟨whiskerRight_mem _ (postcomposeInverseDensityFactorizationIso_hom_isHomogeneous S hS G a).1,
    GradedTwoSupercategory.whiskerRight_mem_degree _
      (postcomposeInverseDensityFactorizationIso_hom_isHomogeneous S hS G a).2⟩

theorem postcomposeComparisonDensityPairInverseIso_inv_isHomogeneous :
    (postcomposeComparisonDensityPairInverseIso T hT G S hS h).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _
    (postcomposeComparisonDensityPairInverseIso_hom_isHomogeneous T hT G S hS h)
end ComparisonConsumer

section CounitConsumer
variable {A : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : A ⟶ C)

/-- Consumer at exactly `S = mapQPi F ⋙ counit C`, `T = counit A ⋙ F`
and the actual `counit_naturality_restrict F`, with no invented equality. -/
def counitNaturalityPostcomposeInverseFactoredPair : TwoNatTrans
    (((mapQPi F.1).comp (counit C)).comp G.1) (((counit A).comp F.1).comp G.1) :=
  postcomposeComparisonInverseFactoredPair _ ((counit_isGraded A).comp F.2) G
    _ ((mapQPi_isGraded F.2).comp (counit_isGraded C)) (counit_naturality_restrict F)

/-- Factor the actual inverse-density leg of the actual counit density pair. -/
def counitNaturalityPostcomposeDensityPairInverseIso :
    counitNaturalityPostcomposeDensityPair G F ≅
      counitNaturalityPostcomposeInverseFactoredPair G F :=
  postcomposeComparisonDensityPairInverseIso _ ((counit_isGraded A).comp F.2) G
    _ ((mapQPi_isGraded F.2).comp (counit_isGraded C)) (counit_naturality_restrict F)

/-- The resulting isomorphism starts at the original postcomposed counit transformation. -/
def counitNaturalityPostcomposeInverseFactorizationIso :
    TwoNatTrans.postcompose G.1 (counitNaturality F) ≅
      counitNaturalityPostcomposeInverseFactoredPair G F :=
  counitNaturalityPostcomposeIso G F ≪≫ counitNaturalityPostcomposeDensityPairInverseIso G F

theorem counitNaturalityPostcomposeInverseFactorizationIso_hom_isHomogeneous :
    (counitNaturalityPostcomposeInverseFactorizationIso G F).hom.IsHomogeneous 0 0 := by
  intro a
  have h := postcomposeComparisonDensityPairInverseIso_hom_isHomogeneous
    _ ((counit_isGraded A).comp F.2) G
    _ ((mapQPi_isGraded F.2).comp (counit_isGraded C)) (counit_naturality_restrict F) a
  exact ⟨by simpa only [zero_add] using!
      comp_mem (counitNaturalityPostcomposeIso_hom_isHomogeneous G F a).1 h.1,
    by simpa only [zero_add] using!
      comp_mem_degree (counitNaturalityPostcomposeIso_hom_isHomogeneous G F a).2 h.2⟩

theorem counitNaturalityPostcomposeInverseFactorizationIso_inv_isHomogeneous :
    (counitNaturalityPostcomposeInverseFactorizationIso G F).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _
    (counitNaturalityPostcomposeInverseFactorizationIso_hom_isHomogeneous G F)
end CounitConsumer

end QPiTwoEnvelope
end StringDiagrams
