import StringDiagrams.Super.PiSOpTwoCoherence
import StringDiagrams.Super.TwoHom

/-!
# The Π-envelope of a 2-super-opposite

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §9 (before Lemma
9.1): the 2-superfunctor `PiSOp.twoFunctor : (𝔅^{sop})_π → (𝔅_π)^{sop}`, the identity on
objects, `PiSOp.bridge` on hom categories, with composition comparison `(-1)^{ab}`. It is graded
(`PiSOp.twoFunctor_isGraded`) and a local 2-superequivalence
(`PiSOp.twoFunctor_isLocalTwoSuperequivalence`). Composing the Π-envelope of a 2-superfunctor
`𝔄_q → (𝔅_q)^{sop}` with it gives the 2-superfunctor `𝔄_{q,π} → (𝔅_{q,π})^{sop}` of Lemma 9.1.
-/
noncomputable section
namespace StringDiagrams.PiSOp
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory
universe r u v w
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- The 2-superfunctor `(𝔅^{sop})_π → (𝔅_π)^{sop}`, with sign-corrected maps and
comparison `(-1)^{ab}`. -/
def twoFunctor : TwoSuperfunctor R (TwoEnvelope R (TwoSOp R B)) (TwoSOp R (TwoEnvelope R B)) where
  obj := obj
  map {a b} := (hom a b).obj
  map₂ {a b} := (hom a b).map
  map₂_id f := bridge.map_id f
  map₂_comp η θ := bridge.map_comp η θ
  map₂_add _ _ := bridge.map_add
  map₂_smul r η := bridge.map_smul r η
  map₂_mem hη := (bridge_super (R := R)).map_mem hη
  mapComp := comparison
  mapId := identityComparison
  mapComp_hom_mem := comparison_even
  mapId_hom_mem _ := id_mem _
  mapComp_naturality_left := comparison_naturality_left
  mapComp_naturality_right := comparison_naturality_right
  map₂_associator := comparison_associator
  map₂_leftUnitor := comparison_leftUnitor
  map₂_rightUnitor := comparison_rightUnitor

/-- The hom functors are `PiSOp.bridge`. -/
theorem twoFunctor_mapFunctor (a b : TwoEnvelope R (TwoSOp R B)) :
    (twoFunctor (R := R) (B := B)).mapFunctor a b = hom a b := rfl

/-- The 2-superfunctor is surjective on objects. -/
theorem twoFunctor_obj_surjective : Function.Surjective (twoFunctor (R := R) (B := B)).obj := by
  intro a
  exact ⟨⟨⟨a.unop.as⟩⟩, rfl⟩

variable [∀ a b : B, GradedSupercategory R (a ⟶ b)]

/-- The 2-superfunctor preserves integer degree and has degree-zero comparisons. -/
theorem twoFunctor_isGraded : (twoFunctor (R := R) (B := B)).IsGraded where
  map₂_mem_degree {a b _ _ _ _} hη :=
    (bridge_graded (R := R) (C := a.as.unop ⟶ b.as.unop)).map_mem_degree hη
  mapComp_hom_mem_degree := comparison_degree
  mapId_hom_mem_degree _ := id_mem_degree _

/-- Every hom functor is a graded superequivalence. -/
def twoFunctor_homGradedEquivalence (a b : TwoEnvelope R (TwoSOp R B)) :
    GradedSuperequivalence R ((twoFunctor (R := R) (B := B)).mapFunctor a b) :=
  bridgeGradedEquivalence

/-- The 2-superfunctor is a local 2-superequivalence. -/
theorem twoFunctor_isLocalTwoSuperequivalence :
    (twoFunctor (R := R) (B := B)).IsLocalTwoSuperequivalence where
  hom a b := ⟨(twoFunctor_homGradedEquivalence a b).toSuperequivalence⟩
  essSurj a := by
    obtain ⟨b, hb⟩ := twoFunctor_obj_surjective a
    exact ⟨b, hb.symm ▸ Superequivalent.refl a⟩
end StringDiagrams.PiSOp
