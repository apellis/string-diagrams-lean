import StringDiagrams.Super.PiSOpInverseBridge

/-!
# Comparison data for the inverse of the parity bridge 2-superfunctor

The objects, hom functors (`PiSOp.reverseHom`, given by `PiSOp.reverseBridge`), composition
comparison and identity comparison of the inverse of the 2-superfunctor
`PiSOp.twoFunctor : (𝔅^{sop})_π → (𝔅_π)^{sop}` of arXiv:1701.04133v2, §9 (before Lemma 9.1).
The composition comparison carries the same sign `(-1)^{ab}` as that of `PiSOp.twoFunctor`;
its naturality is reflected from that of `PiSOp.twoFunctor`.
-/
noncomputable section
namespace StringDiagrams.PiSOp
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe r u v w
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- The inverse on objects: `Πᵃ X` in `(𝔅_π)^{sop}` goes to `Πᵃ X` in `(𝔅^{sop})_π`. -/
def reverseObj (a : TwoSOp R (TwoEnvelope R B)) : TwoEnvelope R (TwoSOp R B) :=
  ⟨⟨a.unop.as⟩⟩

/-- The reverse hom functor on the global objects. -/
def reverseHom (a b : TwoSOp R (TwoEnvelope R B)) :
    (a ⟶ b) ⥤ (reverseObj a ⟶ reverseObj b) := reverseBridge

/-- The reverse has the same self-inverse product-of-tags comparison sign. -/
def reverseComparison {a b c : TwoSOp R (TwoEnvelope R B)} (f : a ⟶ b) (g : b ⟶ c) :
    (reverseHom a b).obj f ≫ (reverseHom b c).obj g ≅ (reverseHom a c).obj (f ≫ g) :=
  signIso (R := R) ((SOp.unop f).par * (SOp.unop g).par) _

/-- The reverse identity comparison is the literal identity. -/
def reverseIdentityComparison (a : TwoSOp R (TwoEnvelope R B)) :
    𝟙 (reverseObj a) ≅ (reverseHom a a).obj (𝟙 a) := Iso.refl _

/-- The inverse sign equation used to reflect the two naturality squares. -/
theorem reverse_sign_equation {M : Type*} [AddCommGroup M] [Module R M]
    (p q : ZMod 2) {x y : M} (h : sign R q • y = sign R p • x) :
    sign R q • x = sign R p • y := by
  have e := congrArg (fun z => sign R p • z) h
  rw [sign_smul_sign_smul] at e
  rw [← e, smul_comm (sign R q) (sign R p), sign_smul_sign_smul]

/-- Reverse naturality in the first variable, reflected through the forward bridge. -/
theorem reverseComparison_naturality_left {a b c : TwoSOp R (TwoEnvelope R B)}
    {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (reverseHom a b).map η ▷ (reverseHom b c).obj h ≫ (reverseComparison g h).hom =
      (reverseComparison f h).hom ≫ (reverseHom a c).map (η ▷ h) := by
  apply (bridge (R := R) (C := a.unop.as ⟶ c.unop.as)).map_injective
  change bridge.map (_ ≫ (sign R ((SOp.unop g).par * (SOp.unop h).par) • 𝟙 _)) =
    bridge.map ((sign R ((SOp.unop f).par * (SOp.unop h).par) • 𝟙 _) ≫ reverseBridgeMap (η ▷ h))
  erw [Linear.comp_smul, Category.comp_id, Linear.smul_comp, Category.id_comp,
    Functor.map_smul, Functor.map_smul]
  erw [bridge_reverseBridgeMap (R := R) (C := a.unop.as ⟶ c.unop.as) (η ▷ h)]
  have e := comparison_naturality_left (R := R) (B := B)
    (a := reverseObj a) (b := reverseObj b) (c := reverseObj c)
    ((reverseHom a b).map η) ((reverseHom b c).obj h)
  change bridge.map (reverseBridgeMap η) ▷ h ≫
      (sign R ((SOp.unop g).par * (SOp.unop h).par) • 𝟙 _) =
    (sign R ((SOp.unop f).par * (SOp.unop h).par) • 𝟙 _) ≫
      bridge.map ((reverseHom a b).map η ▷ (reverseHom b c).obj h) at e
  erw [bridge_reverseBridgeMap (R := R) (C := a.unop.as ⟶ b.unop.as) η,
    Linear.comp_smul, Category.comp_id,
    Linear.smul_comp, Category.id_comp] at e
  exact reverse_sign_equation _ _ e

/-- Reverse naturality in the second variable, on arbitrary 2-morphisms. -/
theorem reverseComparison_naturality_right {a b c : TwoSOp R (TwoEnvelope R B)}
    (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (reverseHom a b).obj f ◁ (reverseHom b c).map η ≫ (reverseComparison f h).hom =
      (reverseComparison f g).hom ≫ (reverseHom a c).map (f ◁ η) := by
  apply (bridge (R := R) (C := a.unop.as ⟶ c.unop.as)).map_injective
  change bridge.map (_ ≫ (sign R ((SOp.unop f).par * (SOp.unop h).par) • 𝟙 _)) =
    bridge.map ((sign R ((SOp.unop f).par * (SOp.unop g).par) • 𝟙 _) ≫ reverseBridgeMap (f ◁ η))
  erw [Linear.comp_smul, Category.comp_id, Linear.smul_comp, Category.id_comp,
    Functor.map_smul, Functor.map_smul]
  erw [bridge_reverseBridgeMap (R := R) (C := a.unop.as ⟶ c.unop.as) (f ◁ η)]
  have e := comparison_naturality_right (R := R) (B := B)
    (a := reverseObj a) (b := reverseObj b) (c := reverseObj c)
    ((reverseHom a b).obj f) ((reverseHom b c).map η)
  change f ◁ bridge.map (reverseBridgeMap η) ≫
      (sign R ((SOp.unop f).par * (SOp.unop h).par) • 𝟙 _) =
    (sign R ((SOp.unop f).par * (SOp.unop g).par) • 𝟙 _) ≫
      bridge.map ((reverseHom a b).obj f ◁ (reverseHom b c).map η) at e
  erw [bridge_reverseBridgeMap (R := R) (C := b.unop.as ⟶ c.unop.as) η,
    Linear.comp_smul, Category.comp_id,
    Linear.smul_comp, Category.id_comp] at e
  exact reverse_sign_equation _ _ e
end StringDiagrams.PiSOp
