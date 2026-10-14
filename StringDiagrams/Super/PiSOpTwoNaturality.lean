import StringDiagrams.Super.PiSOpTwoData

/-!
# The Π-envelope of a 2-super-opposite: naturality

Naturality of the composition comparison `(-1)^{ab}` of the 2-superfunctor
`(𝔅^{sop})_π → (𝔅_π)^{sop}` (J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, §9) in both variables.
-/
noncomputable section
namespace StringDiagrams.PiSOp
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe r u v w
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- Naturality in the second factor, without a homogeneity restriction. -/
theorem comparison_naturality_right {a b c : TwoEnvelope R (TwoSOp R B)}
    (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (hom a b).obj f ◁ (hom b c).map η ≫ (comparison f h).hom =
      (comparison f g).hom ≫ (hom a c).map (f ◁ η) := by
  change _ ≫ (sign R (f.par * h.par) • 𝟙 _) =
    (sign R (f.par * g.par) • 𝟙 _) ≫ _
  erw [Linear.comp_smul, Category.comp_id, Linear.smul_comp, Category.id_comp]
  apply SOp.hom_ext
  apply Envelope.hom_ext
  change sign R (f.par * h.par) •
      (SOp.unop f.obj ◁ twist R f.par
        (correction (R := R) g.par h.par
          (SOp.unsop (Envelope.toHom (C := SOp R (b.as.unop ⟶ c.as.unop)) η)))) =
    sign R (f.par * g.par) • correction (R := R) (f.par + g.par) (f.par + h.par)
      (SOp.unsop (f.obj ◁ twist R f.par
        (Envelope.toHom (C := SOp R (b.as.unop ⟶ c.as.unop)) η)))
  rw [TwoSOp.unsop_whiskerLeft, unsop_twist, correction_whiskerLeft,
    smul_smul, ← sign_add]
  have e : f.par * g.par + f.par * (g.par + h.par) = f.par * h.par := by
    calc
      _ = (f.par * g.par + f.par * g.par) + f.par * h.par := by ring
      _ = _ := by rw [zmod2_add_self, zero_add]
  rw [e]

/-- Naturality in the first factor, including shifted right-whisker signs. -/
theorem comparison_naturality_left {a b c : TwoEnvelope R (TwoSOp R B)}
    {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (hom a b).map η ▷ (hom b c).obj h ≫ (comparison g h).hom =
      (comparison f h).hom ≫ (hom a c).map (η ▷ h) := by
  change _ ≫ (sign R (g.par * h.par) • 𝟙 _) =
    (sign R (f.par * h.par) • 𝟙 _) ≫ _
  erw [Linear.comp_smul, Category.comp_id, Linear.smul_comp, Category.id_comp]
  apply SOp.hom_ext
  apply Envelope.hom_ext
  change sign R (g.par * h.par) •
      (Envelope.toHom (twist R h.par
        (Envelope.ofHom (correction (R := R) f.par g.par
          (SOp.unsop (Envelope.toHom (C := SOp R (a.as.unop ⟶ b.as.unop)) η))) :
            (⟨g.par, SOp.unop g.obj⟩ : Envelope R (a.as.unop ⟶ b.as.unop)) ⟶
            ⟨f.par, SOp.unop f.obj⟩)) ▷ SOp.unop h.obj) =
    sign R (f.par * h.par) • correction (R := R) (f.par + h.par) (g.par + h.par)
      (SOp.unsop (Envelope.toHom (C := SOp R (a.as.unop ⟶ b.as.unop))
        (twist R h.par η) ▷ h.obj))
  rw [Envelope.toHom_twist, Envelope.toHom_twist, TwoSOp.unsop_whiskerRight,
    SOp.unsop_smul, unsop_twist, smul_whiskerRight, smul_whiskerRight,
    map_smul, correction_whiskerRight]
  change sign R (g.par * h.par) •
      (sign R (h.par * (g.par + f.par)) •
        (twist R h.par (correction (R := R) f.par g.par
          (SOp.unsop (Envelope.toHom (C := SOp R (a.as.unop ⟶ b.as.unop)) η))) ▷
          SOp.unop h.obj)) =
    sign R (f.par * h.par) • (sign R (h.par * (f.par + g.par)) •
      (sign R (h.par * (f.par + g.par)) •
        (twist R h.par (correction (R := R) f.par g.par
          (SOp.unsop (Envelope.toHom (C := SOp R (a.as.unop ⟶ b.as.unop)) η))) ▷
          SOp.unop h.obj)))
  rw [sign_smul_sign_smul, smul_smul, ← sign_add]
  have e : g.par * h.par + h.par * (g.par + f.par) = f.par * h.par := by
    calc
      _ = (g.par * h.par + g.par * h.par) + f.par * h.par := by ring
      _ = _ := by rw [zmod2_add_self, zero_add]
  rw [e]
end StringDiagrams.PiSOp
