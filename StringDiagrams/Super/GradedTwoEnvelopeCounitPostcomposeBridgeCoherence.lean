import StringDiagrams.Super.GradedTwoEnvelopeCounitPostcomposeInverseDensity

/-!
# Both-endpoint coherence of the actual postcomposition bridge

The bridge is the existing normalized density followed by inverse density.
Its independence of an envelope functor with fixed restriction is proved using
naturality along every shift isomorphism, not inferred from restriction alone.
No strictness of the postcomposing functor is assumed.
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
local instance : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b
local instance : ∀ a b : D, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b

/-- Naturality along the actual shift isomorphism extends equality on `J`
to all shifted 1-cells, for arbitrary endpoint functors. -/
theorem twoNatTrans_ext_of_J_general
    {U V : TwoSuperfunctor R (QPiTwoEnvelope R B) D}
    (θ ψ : TwoNatTrans U V) (hX : θ.X = ψ.X)
    (hx : ∀ {a b : QPiTwoEnvelope R B} (f : a.as.as ⟶ b.as.as),
      HEq (θ.x (Jm f : a ⟶ b)) (ψ.x (Jm f))) : θ = ψ := by
  obtain ⟨X, x, xm, xn, xc, xi⟩ := θ
  obtain ⟨Y, y, ym, yn, yc, yi⟩ := ψ
  dsimp only at hX hx
  subst hX
  have hxy : @x = @y := by
    funext a b f
    have e : Epi (U.map₂ (shiftIso f).hom ▷ X b) :=
      inferInstanceAs (Epi (whiskerRightIso (R := R) (U.map₂Iso (shiftIso f)) (X b)).hom)
    exact TwoEnvelope.eq_of_conj_hom _ e _ (xn (shiftIso f).hom)
      (yn (shiftIso f).hom) (eq_of_heq (hx f.obj.obj))
  cases hxy
  rfl

/-- Heterogeneous version with both endpoint equalities supplied explicitly. -/
theorem twoNatTrans_hext_of_J_general
    {U V U' V' : TwoSuperfunctor R (QPiTwoEnvelope R B) D}
    (hu : U = U') (hv : V = V')
    (θ : TwoNatTrans U V) (ψ : TwoNatTrans U' V')
    (hX : HEq θ.X ψ.X)
    (hx : ∀ {a b : QPiTwoEnvelope R B} (f : a.as.as ⟶ b.as.as),
      HEq (θ.x (Jm f : a ⟶ b)) (ψ.x (Jm f))) : HEq θ ψ := by
  cases hu
  cases hv
  exact heq_of_eq (twoNatTrans_ext_of_J_general θ ψ (eq_of_heq hX) hx)

private theorem transportBoundary_heq
    {U V U' V' : TwoSuperfunctor R (QPiTwoEnvelope R B) D}
    (hu : U = U') (hv : V = V') (θ : TwoNatTrans U V) :
    HEq (TwoNatTrans.transportBoundary hu hv θ) θ := by
  cases hu
  cases hv
  rfl

variable (S T : TwoSuperfunctor R (QPiTwoEnvelope R B) C)
  (hS : S.IsGraded) (hT : T.IsGraded) (h : restrict S = restrict T) (G : C ⟶ D)

include h in
/-- The target alignment uses actual restriction/postcomposition coherence. -/
theorem postcompose_restrict_congr : restrict (S.comp G.1) = restrict (T.comp G.1) := by
  simpa only [restrict_eq_comp, TwoSuperfunctor.comp_assoc] using
    congrArg (fun H => H.comp G.1) h

include h in
/-- Source alignment of the two existing bridges. -/
theorem postcomposeBridge_source :
    (extend (restrict S)).comp G.1 = (extend (restrict T)).comp G.1 :=
  congrArg (fun H => (extend H).comp G.1) h

include h in
/-- Target alignment of the two existing bridges. -/
theorem postcomposeBridge_target :
    extend (restrict (S.comp G.1)) = extend (restrict (T.comp G.1)) :=
  congrArg extend (postcompose_restrict_congr S T h G)

private def bridgeUnitCell {a b : D} (f : a ⟶ b) :
    f ≫ (𝟙 b ≫ 𝟙 b) ⟶ (𝟙 a ≫ 𝟙 a) ≫ f :=
  (associator f (𝟙 b) (𝟙 b)).inv ≫
    ((rightUnitor f).hom ≫ (leftUnitor f).inv) ▷ 𝟙 b ≫
    (associator (𝟙 a) f (𝟙 b)).hom ≫
    𝟙 a ◁ ((rightUnitor f).hom ≫ (leftUnitor f).inv) ≫
    (associator (𝟙 a) (𝟙 a) f).inv

/-- Actual bridge cell on `J`; the mapped density and inverse density both
reduce here, with no assumption on `G.mapId` or `G.mapComp`. -/
theorem postcomposeDensityBridge_x_J {a b : QPiTwoEnvelope R B}
    (f : a.as.as ⟶ b.as.as) :
    (postcomposeDensityBridge T hT G).x (Jm f : a ⟶ b) =
      bridgeUnitCell (G.1.map ((restrict T).map f)) := by
  simp only [postcomposeDensityBridge, TwoNatTrans.vcomp_x,
    postcomposeDensity, postcomposeDensityX, extendRestrictNatTransInv,
    extendRestrictInvX, extendRestrictApp_J, extendRestrictAppInv_J,
    G.1.map₂_id, Category.id_comp]
  rfl

private theorem dependent_heq {α : Sort*} {β : α → Sort*}
    (f : (a : α) → β a) {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

include h in
/-- The existing bridges are heterogeneously equal after the two explicit
endpoint identifications. Shift-isomorphism naturality supplies the coherence. -/
theorem postcomposeDensityBridge_heq :
    HEq (postcomposeDensityBridge S hS G) (postcomposeDensityBridge T hT G) := by
  apply twoNatTrans_hext_of_J_general (postcomposeBridge_source S T h G)
    (postcomposeBridge_target S T h G)
  · exact dependent_heq
      (fun H : TwoSuperfunctor R B C =>
        fun a : QPiTwoEnvelope R B =>
          𝟙 (G.1.obj (H.obj a.as.as)) ≫ 𝟙 (G.1.obj (H.obj a.as.as))) h
  · intro a b f
    rw [postcomposeDensityBridge_x_J, postcomposeDensityBridge_x_J]
    exact dependent_heq
      (fun H : TwoSuperfunctor R B C => bridgeUnitCell (G.1.map (H.map f))) h

/-- Equality of the actual bridges after BOTH source and target transport. -/
theorem postcomposeDensityBridge_transportBoundary :
    TwoNatTrans.transportBoundary (postcomposeBridge_source S T h G)
      (postcomposeBridge_target S T h G) (postcomposeDensityBridge S hS G) =
        postcomposeDensityBridge T hT G := by
  have ht : HEq
      (TwoNatTrans.transportBoundary (postcomposeBridge_source S T h G)
        (postcomposeBridge_target S T h G) (postcomposeDensityBridge S hS G))
      (postcomposeDensityBridge S hS G) := by
    exact transportBoundary_heq _ _ _
  exact eq_of_heq (ht.trans (postcomposeDensityBridge_heq S T hS hT h G))

/-- The both-aligned bridge comparison as an even invertible modification. -/
def postcomposeDensityBridgeAlignmentIso :
    TwoNatTrans.transportBoundary (postcomposeBridge_source S T h G)
      (postcomposeBridge_target S T h G) (postcomposeDensityBridge S hS G) ≅
        postcomposeDensityBridge T hT G :=
  eqToIso (postcomposeDensityBridge_transportBoundary S T hS hT h G)

theorem postcomposeDensityBridgeAlignmentIso_hom_isHomogeneous :
    (postcomposeDensityBridgeAlignmentIso S T hS hT h G).hom.IsHomogeneous 0 0 :=
  TwoNatTrans.eqToIso_hom_isHomogeneous _

theorem postcomposeDensityBridgeAlignmentIso_inv_isHomogeneous :
    (postcomposeDensityBridgeAlignmentIso S T hS hT h G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _
    (postcomposeDensityBridgeAlignmentIso_hom_isHomogeneous S T hS hT h G)

end QPiTwoEnvelope
namespace TwoNatTrans
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R}
  {C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  {U U' V : TwoSuperfunctor R (QPiTwoEnvelope R B) C}
  (G : C ⟶ D)

/-- Actual postcomposition commutes with source transport, including its
unit and composition constraints. This is path induction, not strictness. -/
theorem postcompose_transportSource (p : U = U') (θ : TwoNatTrans U V) :
    postcompose G.1 (transportSource p θ) =
      transportSource (congrArg (fun H => H.comp G.1) p) (postcompose G.1 θ) := by
  cases p
  rfl

/-- Move retained source transport through an actual factorization isomorphism
and onto its first factor. The middle functor is not transported away. -/
def postcomposeTransportedFactorizationIso (p : U = U') (θ : TwoNatTrans U V)
    {W : TwoSuperfunctor R (QPiTwoEnvelope R B) D}
    (β : TwoNatTrans (U.comp G.1) W) (γ : TwoNatTrans W (V.comp G.1))
    (e : postcompose G.1 θ ≅ vcomp β γ) :
    postcompose G.1 (transportSource p θ) ≅
      vcomp (transportSource (congrArg (fun H => H.comp G.1) p) β) γ := by
  cases p
  exact e

theorem postcomposeTransportedFactorizationIso_hom_isHomogeneous
    (p : U = U') (θ : TwoNatTrans U V)
    {W : TwoSuperfunctor R (QPiTwoEnvelope R B) D}
    (β : TwoNatTrans (U.comp G.1) W) (γ : TwoNatTrans W (V.comp G.1))
    (e : postcompose G.1 θ ≅ vcomp β γ) (he : e.hom.IsHomogeneous 0 0) :
    (postcomposeTransportedFactorizationIso G p θ β γ e).hom.IsHomogeneous 0 0 := by
  cases p
  exact he

end TwoNatTrans
namespace QPiTwoEnvelope
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R}
  {C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  (S T : TwoSuperfunctor R (QPiTwoEnvelope R B) C)
  (hT : T.IsGraded) (h : restrict S = restrict T) (G : C ⟶ D)
local instance : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b
local instance : ∀ a b : D, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b

/-- Forward factorization of precisely the retained transported density in the
original postcomposed comparison. The old bridge and `G.mapId/mapComp` remain. -/
def postcomposeTransportedDensityFactorizationIso :
    TwoNatTrans.postcompose G.1
      (TwoNatTrans.transportSource (congrArg extend h.symm) (extendRestrictNatTrans T hT)) ≅
    TwoNatTrans.vcomp
      (TwoNatTrans.transportSource (postcomposeBridge_source S T h G).symm
        (postcomposeDensityBridge T hT G))
      (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2)) :=
  TwoNatTrans.postcomposeTransportedFactorizationIso G (congrArg extend h.symm)
    (extendRestrictNatTrans T hT) (postcomposeDensityBridge T hT G)
    (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2))
    (postcomposeDensityFactorizationIso T hT G)

theorem postcomposeTransportedDensityFactorizationIso_hom_isHomogeneous :
    (postcomposeTransportedDensityFactorizationIso S T hT h G).hom.IsHomogeneous 0 0 :=
  TwoNatTrans.postcomposeTransportedFactorizationIso_hom_isHomogeneous _ _ _ _ _ _
    (postcomposeDensityFactorizationIso_hom_isHomogeneous T hT G)

theorem postcomposeTransportedDensityFactorizationIso_inv_isHomogeneous :
    (postcomposeTransportedDensityFactorizationIso S T hT h G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _
    (postcomposeTransportedDensityFactorizationIso_hom_isHomogeneous S T hT h G)

section Counit
variable {A : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : A ⟶ C)

/-- The actual `S`, `T`, and restriction equality of the counit square. -/
def counitPostcomposeBridgeAlignmentIso :
    TwoNatTrans.transportBoundary
      (postcomposeBridge_source _ _ (counit_naturality_restrict F) G)
      (postcomposeBridge_target _ _ (counit_naturality_restrict F) G)
      (postcomposeDensityBridge ((mapQPi F.1).comp (counit C))
        ((mapQPi_isGraded F.2).comp (counit_isGraded C)) G) ≅
    postcomposeDensityBridge ((counit A).comp F.1) ((counit_isGraded A).comp F.2) G :=
  postcomposeDensityBridgeAlignmentIso _ _ _ _ (counit_naturality_restrict F) G

theorem counitPostcomposeBridgeAlignmentIso_hom_isHomogeneous :
    (counitPostcomposeBridgeAlignmentIso G F).hom.IsHomogeneous 0 0 :=
  postcomposeDensityBridgeAlignmentIso_hom_isHomogeneous _ _ _ _ _ _

theorem counitPostcomposeBridgeAlignmentIso_inv_isHomogeneous :
    (counitPostcomposeBridgeAlignmentIso G F).inv.IsHomogeneous 0 0 :=
  postcomposeDensityBridgeAlignmentIso_inv_isHomogeneous _ _ _ _ _ _

/-- The forward factor of the actual counit density pair, with its original
source equality transported through the actual forward factorization. -/
def counitPostcomposeTransportedDensityFactorizationIso :=
  postcomposeTransportedDensityFactorizationIso
    ((mapQPi F.1).comp (counit C)) ((counit A).comp F.1)
    ((counit_isGraded A).comp F.2) (counit_naturality_restrict F) G

end Counit

/-!
This module proves bridge identification and retained forward transport.
It does not assert the full right-leg or composite counit-paste isomorphism:
pasting the two factorizations, cancelling the middle bridges through the
remaining target transport, and normalizing the external boundaries are
separate obligations.
-/

end QPiTwoEnvelope
end StringDiagrams
