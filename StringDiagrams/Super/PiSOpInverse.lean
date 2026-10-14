import StringDiagrams.Super.PiSOpInverseData

/-!
# The inverse of the parity bridge 2-superfunctor

`PiSOp.inverseTwoFunctor : (𝔅_π)^{sop} → (𝔅^{sop})_π` is a graded 2-superfunctor
(`PiSOp.inverseTwoFunctor_isGraded`). Its associativity and unit axioms are checked directly from
the comparison data. It is a strict inverse of `PiSOp.twoFunctor` of arXiv:1701.04133v2, §9
(before Lemma 9.1); see `StringDiagrams.Super.PiSOpInverseRoundtrip`.
-/
noncomputable section
namespace StringDiagrams.PiSOp
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe r u v w
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- Equal total endpoint tags make the associator correction trivial. -/
theorem reverseHom_associator_inv {a b c d : TwoSOp R (TwoEnvelope R B)}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (reverseHom a d).map (associator f g h).inv =
      (associator ((reverseHom a b).obj f) ((reverseHom b c).obj g)
        ((reverseHom c d).obj h)).inv := by
  apply Envelope.hom_ext
  apply SOp.hom_ext
  change correction (R := R)
    ((SOp.unop f).par + ((SOp.unop g).par + (SOp.unop h).par))
    (((SOp.unop f).par + (SOp.unop g).par) + (SOp.unop h).par)
    (associator (SOp.unop f).obj (SOp.unop g).obj (SOp.unop h).obj).hom = _
  rw [add_assoc]
  simp only [correction, zmod2_add_self, mul_zero, sign_zero, twist_zero, one_smul]
  rfl

/-- The reverse preserves the left unitor. -/
theorem reverseHom_leftUnitor {a b : TwoSOp R (TwoEnvelope R B)} (f : a ⟶ b) :
    (reverseHom a b).map (leftUnitor f).hom =
      (leftUnitor ((reverseHom a b).obj f)).hom := by
  apply Envelope.hom_ext
  apply SOp.hom_ext
  change correction (R := R) (0 + (SOp.unop f).par) (SOp.unop f).par
    (leftUnitor (SOp.unop f).obj).inv = _
  simp only [zero_add, correction, zmod2_add_self, mul_zero, sign_zero, twist_zero, one_smul]
  rfl

/-- The reverse preserves the right unitor. -/
theorem reverseHom_rightUnitor {a b : TwoSOp R (TwoEnvelope R B)} (f : a ⟶ b) :
    (reverseHom a b).map (rightUnitor f).hom =
      (rightUnitor ((reverseHom a b).obj f)).hom := by
  apply Envelope.hom_ext
  apply SOp.hom_ext
  change correction (R := R) ((SOp.unop f).par + 0) (SOp.unop f).par
    (rightUnitor (SOp.unop f).obj).inv = _
  simp only [add_zero, correction, zmod2_add_self, mul_zero, sign_zero, twist_zero, one_smul]
  rfl

/-- The associativity axiom for the inverse, with both signed comparison factors. -/
theorem reverseComparison_associator {a b c d : TwoSOp R (TwoEnvelope R B)}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (reverseHom a b).obj f ◁ (reverseComparison g h).hom ≫
        (reverseComparison f (g ≫ h)).hom ≫ (reverseHom a d).map (associator f g h).inv =
      (associator ((reverseHom a b).obj f) ((reverseHom b c).obj g)
        ((reverseHom c d).obj h)).inv ≫
        (reverseComparison f g).hom ▷ (reverseHom c d).obj h ≫
          (reverseComparison (f ≫ g) h).hom := by
  change (reverseHom a b).obj f ◁ (sign R ((SOp.unop g).par * (SOp.unop h).par) • 𝟙 _) ≫
      (sign R ((SOp.unop f).par * ((SOp.unop g).par + (SOp.unop h).par)) • 𝟙 _) ≫ _ =
    _ ≫ (sign R ((SOp.unop f).par * (SOp.unop g).par) • 𝟙 _) ▷ (reverseHom c d).obj h ≫
      (sign R (((SOp.unop f).par + (SOp.unop g).par) * (SOp.unop h).par) • 𝟙 _)
  erw [whiskerLeft_smul, whiskerLeft_id (R := R), smul_whiskerRight, id_whiskerRight (R := R),
    Linear.smul_comp, Category.id_comp, Linear.smul_comp, Category.id_comp,
    Linear.comp_smul, Category.comp_id, Linear.comp_smul, Linear.comp_smul, Category.comp_id]
  erw [reverseHom_associator_inv, smul_smul, smul_smul, comparison_cocycle, mul_comm]

/-- The left unit axiom for the inverse. -/
theorem reverseComparison_leftUnitor {a b : TwoSOp R (TwoEnvelope R B)} (f : a ⟶ b) :
    (reverseIdentityComparison a).hom ▷ (reverseHom a b).obj f ≫
        (reverseComparison (𝟙 a) f).hom ≫ (reverseHom a b).map (leftUnitor f).hom =
      (leftUnitor ((reverseHom a b).obj f)).hom := by
  change 𝟙 _ ▷ (reverseHom a b).obj f ≫ (sign R (0 * (SOp.unop f).par) • 𝟙 _) ≫ _ = _
  erw [zero_mul, sign_zero, one_smul, id_whiskerRight (R := R),
    Category.id_comp, Category.id_comp]
  exact reverseHom_leftUnitor f

/-- The right unit axiom for the inverse. -/
theorem reverseComparison_rightUnitor {a b : TwoSOp R (TwoEnvelope R B)} (f : a ⟶ b) :
    (reverseHom a b).obj f ◁ (reverseIdentityComparison b).hom ≫
        (reverseComparison f (𝟙 b)).hom ≫ (reverseHom a b).map (rightUnitor f).hom =
      (rightUnitor ((reverseHom a b).obj f)).hom := by
  change (reverseHom a b).obj f ◁ 𝟙 _ ≫ (sign R ((SOp.unop f).par * 0) • 𝟙 _) ≫ _ = _
  erw [mul_zero, sign_zero, one_smul, whiskerLeft_id (R := R),
    Category.id_comp, Category.id_comp]
  exact reverseHom_rightUnitor f

/-- The inverse of `PiSOp.twoFunctor`, as a 2-superfunctor `(𝔅_π)^{sop} → (𝔅^{sop})_π`. -/
def inverseTwoFunctor :
    TwoSuperfunctor R (TwoSOp R (TwoEnvelope R B)) (TwoEnvelope R (TwoSOp R B)) where
  obj := reverseObj
  map {a b} := (reverseHom a b).obj
  map₂ {a b} := (reverseHom a b).map
  map₂_id f := reverseBridge.map_id f
  map₂_comp η θ := reverseBridge.map_comp η θ
  map₂_add _ _ := reverseBridge.map_add
  map₂_smul r η := reverseBridge.map_smul r η
  map₂_mem hη := (reverseBridge_super (R := R)).map_mem hη
  mapComp := reverseComparison
  mapId := reverseIdentityComparison
  mapComp_hom_mem _ _ := Submodule.smul_mem _ _ (id_mem _)
  mapId_hom_mem _ := id_mem _
  mapComp_naturality_left := reverseComparison_naturality_left
  mapComp_naturality_right := reverseComparison_naturality_right
  map₂_associator := reverseComparison_associator
  map₂_leftUnitor := reverseComparison_leftUnitor
  map₂_rightUnitor := reverseComparison_rightUnitor

variable [∀ a b : B, GradedSupercategory R (a ⟶ b)]

/-- The inverse is graded: it preserves degrees and its comparisons have degree zero. -/
theorem inverseTwoFunctor_isGraded : (inverseTwoFunctor (R := R) (B := B)).IsGraded where
  map₂_mem_degree {a b _ _ _ _} hη :=
    (reverseBridge_graded (R := R) (C := a.unop.as ⟶ b.unop.as)).map_mem_degree hη
  mapComp_hom_mem_degree _ _ := Submodule.smul_mem _ _ (id_mem_degree _)
  mapId_hom_mem_degree _ := id_mem_degree _
end StringDiagrams.PiSOp
