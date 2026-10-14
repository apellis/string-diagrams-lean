import StringDiagrams.Super.PiSOpCorrection

/-!
# The Π-envelope of a super-opposite

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §9 (before
Lemma 9.1): the superfunctor `(𝒜^{sop})_π → (𝒜_π)^{sop}` which is the identity on objects
`Πᵃ X` and multiplies morphisms by the sign of `PiSOp.correction` (`PiSOp.bridge`). It is
fully faithful, surjective on objects and graded, hence a graded superequivalence
(`PiSOp.bridgeGradedEquivalence`).
-/
noncomputable section
namespace StringDiagrams.PiSOp
open CategoryTheory Supercategory GradedSupercategory
universe r u v
variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear R C] [Supercategory R C]

/-- Parity tags are unchanged; morphisms receive the endpoint-dependent Koszul correction. -/
def bridge : Envelope R (SOp R C) ⥤ SOp R (Envelope R C) where
  obj X := ⟨⟨X.par, X.obj.unop⟩⟩
  map {X Y} f := SOp.mk' (Envelope.ofHom
    (correction (R := R) X.par Y.par (SOp.unsop (Envelope.toHom f))))
  map_id X := by
    apply SOp.hom_ext
    change correction (R := R) X.par X.par (𝟙 X.obj.unop) = 𝟙 X.obj.unop
    simp [correction, zmod2_add_self]
  map_comp {X Y Z} f g := by
    apply SOp.hom_ext
    exact correction_comp X.par Y.par Z.par (SOp.unsop (Envelope.toHom f))
      (SOp.unsop (Envelope.toHom g))

instance bridge_additive : (bridge (R := R) (C := C)).Additive where
  map_add {X Y} f g := by
    apply SOp.hom_ext
    change correction (R := R) X.par Y.par (SOp.unsop (Envelope.toHom (f + g))) =
      correction (R := R) X.par Y.par (SOp.unsop (Envelope.toHom f)) +
      correction (R := R) X.par Y.par (SOp.unsop (Envelope.toHom g))
    rw [Envelope.toHom_add, SOp.unsop_add, map_add]

instance bridge_linear : (bridge (R := R) (C := C)).Linear R where
  map_smul {X Y} f r := by
    apply SOp.hom_ext
    change correction (R := R) X.par Y.par (SOp.unsop (Envelope.toHom (r • f))) =
      r • correction (R := R) X.par Y.par (SOp.unsop (Envelope.toHom f))
    rw [Envelope.toHom_smul, SOp.unsop_smul, map_smul]

instance bridge_super : IsSuperfunctor R (bridge (R := R) (C := C)) where
  map_mem {X Y p f} hf := by
    change correction (R := R) X.par Y.par (SOp.unsop (Envelope.toHom f)) ∈
      parity (R := R) Y.obj.unop X.obj.unop (p + (Y.par + X.par))
    rw [add_comm Y.par X.par]
    exact correction_mem X.par Y.par hf

/-- The correction is an involution on each morphism module. -/
theorem correction_twice (a b : ZMod 2) {X Y : C} (f : X ⟶ Y) :
    correction (R := R) a b (correction (R := R) a b f) = f := by
  change sign R (a * (a + b)) • twist R (a + b)
    (sign R (a * (a + b)) • twist R (a + b) f) = f
  rw [map_smul, twist_twist, sign_smul_sign_smul]

instance bridge_faithful : (bridge (R := R) (C := C)).Faithful where
  map_injective {X Y} {f g} h := by
    apply Envelope.hom_ext
    apply SOp.hom_ext
    have e := congrArg (fun z => correction (R := R) X.par Y.par
      (Envelope.toHom (SOp.unsop z))) h
    change correction (R := R) X.par Y.par
        (correction (R := R) X.par Y.par (SOp.unsop (Envelope.toHom f))) =
      correction (R := R) X.par Y.par
        (correction (R := R) X.par Y.par (SOp.unsop (Envelope.toHom g))) at e
    simpa only [correction_twice] using e

instance bridge_full : (bridge (R := R) (C := C)).Full where
  map_surjective {X Y} f := by
    refine ⟨Envelope.ofHom (SOp.mk' (correction (R := R) X.par Y.par
      (Envelope.toHom (SOp.unsop f)))), ?_⟩
    apply SOp.hom_ext
    exact correction_twice X.par Y.par (Envelope.toHom (SOp.unsop f))

/-- The bridge is surjective on objects. -/
theorem bridge_obj_surjective : Function.Surjective (bridge (R := R) (C := C)).obj := by
  intro X
  exact ⟨⟨X.unop.par, ⟨X.unop.obj⟩⟩, rfl⟩

variable [GradedSupercategory R C]

instance bridge_graded : IsGradedSuperfunctor R (bridge (R := R) (C := C)) where
  map_mem_degree {X Y n f} hf := by
    change sign R (X.par * (X.par + Y.par)) •
        twist R (X.par + Y.par) (SOp.unsop (Envelope.toHom f)) ∈
      degree (R := R) Y.obj.unop X.obj.unop n
    have hf' : SOp.unsop (Envelope.toHom f) ∈
        degree (R := R) Y.obj.unop X.obj.unop n := hf
    exact Submodule.smul_mem _ _ (twist_mem_degree (X.par + Y.par) hf')

/-- The corrected bridge has even degree-zero object preimages. -/
theorem bridge_gradedEvenlyDense : GradedEvenlyDense R (bridge (R := R) (C := C)) := by
  intro Y
  obtain ⟨X, hX⟩ := bridge_obj_surjective Y
  subst Y
  exact ⟨X, Iso.refl _, id_mem _, id_mem_degree _⟩

/-- The bridge is a graded superequivalence. -/
def bridgeGradedEquivalence : GradedSuperequivalence R (bridge (R := R) (C := C)) :=
  GradedSuperequivalence.ofFullyFaithful bridge bridge_gradedEvenlyDense
end StringDiagrams.PiSOp
