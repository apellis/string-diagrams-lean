import StringDiagrams.Super.PiSOpInverse

/-!
# `PiSOp.twoFunctor` and its inverse compose to identities

Both composites of `PiSOp.twoFunctor` and `PiSOp.inverseTwoFunctor` are equal to identity
2-superfunctors (`PiSOp.twoFunctor_comp_inverseTwoFunctor`,
`PiSOp.inverseTwoFunctor_comp_twoFunctor`): on 2-morphisms the two correction signs cancel, and
so do the composition comparisons `(-1)^{ab}`. This identifies `(𝔅^{sop})_π` and
`(𝔅_π)^{sop}` (arXiv:1701.04133v2, §9, before Lemma 9.1) strictly.
-/
noncomputable section
namespace StringDiagrams.PiSOp
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe r u v w
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- The source composite is literally the identity on arbitrary 2-morphisms. -/
theorem twoFunctor_comp_inverse_map₂ {a b : TwoEnvelope R (TwoSOp R B)}
    {f g : a ⟶ b} (η : f ⟶ g) :
    inverseTwoFunctor.map₂ (twoFunctor.map₂ η) = η := reverseBridgeMap_bridge η

/-- The target composite is literally the identity on arbitrary 2-morphisms. -/
theorem inverse_comp_twoFunctor_map₂ {a b : TwoSOp R (TwoEnvelope R B)}
    {f g : a ⟶ b} (η : f ⟶ g) :
    twoFunctor.map₂ (inverseTwoFunctor.map₂ η) = η := bridge_reverseBridgeMap η

/-- The two nontrivial signs cancel in the source composite's comparison. -/
theorem twoFunctor_comp_inverse_comparison {a b c : TwoEnvelope R (TwoSOp R B)}
    (f : a ⟶ b) (g : b ⟶ c) :
    (((twoFunctor (R := R) (B := B)).comp inverseTwoFunctor).mapComp f g).hom = 𝟙 (f ≫ g) := by
  change (sign R (f.par * g.par) • 𝟙 _) ≫
    reverseBridge.map (sign R (f.par * g.par) • 𝟙 (bridge.obj (f ≫ g))) = _
  rw [Functor.map_smul, reverseBridge.map_id]
  erw [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    smul_smul, sign_mul_self, one_smul]
  rfl

/-- The two nontrivial signs cancel in the target composite's comparison. -/
theorem inverse_comp_twoFunctor_comparison {a b c : TwoSOp R (TwoEnvelope R B)}
    (f : a ⟶ b) (g : b ⟶ c) :
    (((inverseTwoFunctor (R := R) (B := B)).comp twoFunctor).mapComp f g).hom = 𝟙 (f ≫ g) := by
  change (sign R ((SOp.unop f).par * (SOp.unop g).par) • 𝟙 _) ≫
    bridge.map (sign R ((SOp.unop f).par * (SOp.unop g).par) •
      𝟙 (reverseBridge.obj (f ≫ g))) = _
  rw [Functor.map_smul, bridge.map_id]
  change (sign R ((SOp.unop f).par * (SOp.unop g).par) • 𝟙 (f ≫ g)) ≫
    (sign R ((SOp.unop f).par * (SOp.unop g).par) • 𝟙 (f ≫ g)) = _
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    smul_smul, sign_mul_self, one_smul]

/-- Identity comparisons also cancel literally on the source. -/
theorem twoFunctor_comp_inverse_identity (a : TwoEnvelope R (TwoSOp R B)) :
    (((twoFunctor (R := R) (B := B)).comp inverseTwoFunctor).mapId a).hom = 𝟙 (𝟙 a) := by
  change 𝟙 _ ≫ reverseBridge.map (𝟙 _) = _
  erw [reverseBridge.map_id, Category.id_comp]
  rfl

/-- Identity comparisons also cancel literally on the target. -/
theorem inverse_comp_twoFunctor_identity (a : TwoSOp R (TwoEnvelope R B)) :
    (((inverseTwoFunctor (R := R) (B := B)).comp twoFunctor).mapId a).hom = 𝟙 (𝟙 a) := by
  change 𝟙 _ ≫ bridge.map (𝟙 _) = _
  erw [bridge.map_id, Category.id_comp]
  rfl

/-- The source global composite equals the identity 2-superfunctor. -/
theorem twoFunctor_comp_inverseTwoFunctor :
    (twoFunctor (R := R) (B := B)).comp inverseTwoFunctor = TwoSuperfunctor.id R _ := by
  unfold TwoSuperfunctor.comp
  congr 1
  · funext a b f g η
    exact twoFunctor_comp_inverse_map₂ η
  · funext a b c f g
    exact Iso.ext (twoFunctor_comp_inverse_comparison f g)
  · funext a
    exact Iso.ext (twoFunctor_comp_inverse_identity a)

/-- The target global composite equals the identity 2-superfunctor. -/
theorem inverseTwoFunctor_comp_twoFunctor :
    (inverseTwoFunctor (R := R) (B := B)).comp twoFunctor = TwoSuperfunctor.id R _ := by
  unfold TwoSuperfunctor.comp
  congr 1
  · funext a b f g η
    exact inverse_comp_twoFunctor_map₂ η
  · funext a b c f g
    exact Iso.ext (inverse_comp_twoFunctor_comparison f g)
  · funext a
    exact Iso.ext (inverse_comp_twoFunctor_identity a)
end StringDiagrams.PiSOp
