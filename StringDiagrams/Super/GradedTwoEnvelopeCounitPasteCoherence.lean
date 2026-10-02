import StringDiagrams.Super.GradedTwoEnvelopeCounitPaste

/-!
# Density compatibility for the left-whiskered counit leg

Precomposition by the actual `mapQPi F` commutes with the density component
`extendRestrictApp`, its inverse, and the corresponding naturality cells
including their unitors. These identities hold for arbitrary graded `F` and
arbitrary graded envelope functor `T`; neither must be strict.

This supplies a necessary whiskering-density identification. It does not yet
construct the modification from `counitNaturalityPaste F G` to
`counitNaturality (F ≫ G)`: the postcomposition comparison, its compositor
factors, and the assembly through transported boundaries remain open.
-/

noncomputable section
namespace StringDiagrams
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe w w₁ v₁ u₁
variable {R : Type w} [CommRing R]
namespace QPiTwoEnvelope
set_option backward.isDefEq.respectTransparency false
variable {B C : GTwoSCat.{w, w₁, v₁, u₁} R} {D : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  (F : TwoSuperfunctor R B C) (hF : F.IsGraded)
  (T : TwoSuperfunctor R (QPiTwoEnvelope R C) D) (hT : T.IsGraded)
local instance : ∀ a b : D, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b

/-- The chosen density component commutes with actual envelope precomposition.
No restriction on the integer shift or parity label of `f` is imposed. -/
theorem extendRestrictApp_precompose {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictApp ((mapQPi F).comp T) ((mapQPi_isGraded hF).comp hT) f =
      extendRestrictApp T hT ((mapQPi F).map f) := by
  simp only [extendRestrictApp, QPiEnvelope.extendRestrictIso, Iso.trans_hom,
    NatTrans.comp_app, Envelope.extendIso_hom_app,
    QEnvelope.extendRestrictIso, Envelope.extendRestrictIso,
    NatIso.ofComponents_hom_app, Envelope.extendNat,
    Functor.mapIso_hom, Functor.comp_map, Functor.comp_obj]
  dsimp [homFunctor, TwoSuperfunctor.mapFunctor, TwoSuperfunctor.comp,
    mapQPi, TwoEnvelope.mapPi, TwoEnvelope.mapPiMap, TwoEnvelope.mapPiMap₂,
    QTwoEnvelope.mapQ, Envelope.shiftIso, QEnvelope.shiftIso,
    Envelope.isoOfIso, QEnvelope.isoOfIso, Envelope.J, QEnvelope.J,
    QEnvelope.extend, Envelope.toHom, QEnvelope.toHom, Envelope.ofHom, QEnvelope.ofHom]
  simp! only [F.map₂_id]
  congr 1
  congr 1
  exact congrArg (fun η : F.map f.obj.obj ⟶ F.map f.obj.obj =>
    T.map₂ (a := (mapQPi F).obj a) (b := (mapQPi F).obj b)
      (f := ⟨0, ⟨f.obj.shift, F.map f.obj.obj⟩⟩) (g := (mapQPi F).map f)
      (QPiEnvelope.ofHom
      (X := ⟨0, ⟨f.obj.shift, F.map f.obj.obj⟩⟩)
      (Y := (mapQPi F).map f) η)) (F.map₂_id f.obj.obj)
/-- The inverse density component has the same precomposition compatibility. -/
theorem extendRestrictAppInv_precompose {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictAppInv ((mapQPi F).comp T) ((mapQPi_isGraded hF).comp hT) f =
      extendRestrictAppInv T hT ((mapQPi F).map f) := by
  let U := (mapQPi F).comp T
  let hU := (mapQPi_isGraded hF).comp hT
  calc
    extendRestrictAppInv U hU f = extendRestrictAppInv U hU f ≫
        (extendRestrictApp T hT ((mapQPi F).map f) ≫
          extendRestrictAppInv T hT ((mapQPi F).map f)) := by
      rw [extendRestrictApp_comp_inv]
      exact (Category.comp_id _).symm
    _ = (extendRestrictAppInv U hU f ≫ extendRestrictApp U hU f) ≫
        extendRestrictAppInv T hT ((mapQPi F).map f) := by
      rw [extendRestrictApp_precompose F hF T hT, Category.assoc]
    _ = extendRestrictAppInv T hT ((mapQPi F).map f) := by
      rw [extendRestrictAppInv_comp, Category.id_comp]

/-- Precomposition preserves the full density naturality cell, including unitors. -/
theorem extendRestrictX_precompose {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictX ((mapQPi F).comp T) ((mapQPi_isGraded hF).comp hT) f =
      extendRestrictX T hT ((mapQPi F).map f) := by
  simp only [extendRestrictX, extendRestrictApp_precompose F hF T hT]
  rfl

/-- The inverse density naturality cell is likewise compatible with precomposition. -/
theorem extendRestrictInvX_precompose {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictInvX ((mapQPi F).comp T) ((mapQPi_isGraded hF).comp hT) f =
      extendRestrictInvX T hT ((mapQPi F).map f) := by
  simp only [extendRestrictInvX, extendRestrictAppInv_precompose F hF T hT]
  rfl

/-- The actual prewhiskered density transformation has the computed density cell. -/
theorem precompose_extendRestrictNatTrans_x {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (TwoNatTrans.precompose (mapQPi F) (extendRestrictNatTrans T hT)).x f =
      (extendRestrictNatTrans ((mapQPi F).comp T)
        ((mapQPi_isGraded hF).comp hT)).x f :=
  (extendRestrictX_precompose F hF T hT f).symm

/-- The actual prewhiskered inverse density transformation has the inverse density cell. -/
theorem precompose_extendRestrictNatTransInv_x {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (TwoNatTrans.precompose (mapQPi F) (extendRestrictNatTransInv T hT)).x f =
      (extendRestrictNatTransInv ((mapQPi F).comp T)
        ((mapQPi_isGraded hF).comp hT)).x f :=
  (extendRestrictInvX_precompose F hF T hT f).symm

end QPiTwoEnvelope
end StringDiagrams
