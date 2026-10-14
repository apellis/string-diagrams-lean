import StringDiagrams.Super.SOpGraded
import StringDiagrams.Super.QEnvelope

/-!
# The parity sign relating the Π-envelope and the super-opposite

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §9 (before
Lemma 9.1): to view `(𝔅_π)^{sop}` as a Π-2-supercategory, a 2-morphism `x : Y → X` of parity
`p` between the parity shifts `Πᵃ` and `Πᵇ` is multiplied by `(-1)^{a(a+b) + (a+b)p}`
(`PiSOp.exponent`, `PiSOp.correction`). This sign intertwines the composition of
`Envelope(𝒜^{sop})` with that of `Envelope(𝒜)^{sop}` (`PiSOp.correction_comp`).
-/
noncomputable section
namespace StringDiagrams.PiSOp
open CategoryTheory Supercategory GradedSupercategory
universe r u v
variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear R C] [Supercategory R C]

/-- The exponent for a morphism of parity `p` between the parity shifts `Πᵃ` and `Πᵇ`. -/
def exponent (a b p : ZMod 2) : ZMod 2 := a * (a + b) + (a + b) * p

/-- The endpoint correction, defined on the entire morphism module. -/
def correction (a b : ZMod 2) {X Y : C} : (X ⟶ Y) →ₗ[R] (X ⟶ Y) :=
  sign R (a * (a + b)) • twist R (a + b)

/-- The correction on a homogeneous morphism has the required endpoint-dependent sign. -/
theorem correction_of_mem (a b : ZMod 2) {X Y : C} {p : ZMod 2} {f : X ⟶ Y}
    (hf : f ∈ parity (R := R) X Y p) :
    correction (R := R) a b f = sign R (exponent a b p) • f := by
  change sign R (a * (a + b)) • twist R (a + b) f = _
  rw [twist_of_mem _ hf, smul_smul, ← sign_add]
  rfl

/-- The correction does not change parity. -/
theorem correction_mem (a b : ZMod 2) {X Y : C} {p : ZMod 2} {f : X ⟶ Y}
    (hf : f ∈ parity (R := R) X Y p) :
    correction (R := R) a b f ∈ parity (R := R) X Y p :=
  Submodule.smul_mem _ _ (twist_mem _ hf)

/-- The sign identity compensates exactly for the shifted Koszul composition. -/
theorem exponent_comp (a b c p q : ZMod 2) :
    exponent a c (p + q) + p * q =
      (p + (a + b)) * (q + (b + c)) + exponent a b p + exponent b c q := by
  rcases parity_eq_zero_or_one a with rfl | rfl <;>
    rcases parity_eq_zero_or_one b with rfl | rfl <;>
    rcases parity_eq_zero_or_one c with rfl | rfl <;>
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;> decide

/-- Corrected compositions agree with composition in the super-opposite of the Π-envelope. -/
theorem correction_comp (a b c : ZMod 2) {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) :
    correction (R := R) a c (SOp.compC (R := R) f g) =
      Envelope.toHom (SOp.compC (R := R) (C := Envelope R C)
        (Envelope.ofHom (X := ⟨b, Y⟩) (Y := ⟨a, X⟩) (correction (R := R) a b f))
        (Envelope.ofHom (X := ⟨c, Z⟩) (Y := ⟨b, Y⟩) (correction (R := R) b c g))) := by
  refine induction_on (R := R) f ?_ (fun p f hf => ?_) ?_
  · simp only [map_zero, Envelope.ofHom, SOp.zero_compC, Envelope.toHom_zero]
  · refine induction_on (R := R) g ?_ (fun q g hg => ?_) ?_
    · simp only [map_zero, Envelope.ofHom, SOp.compC_zero, Envelope.toHom_zero]
    · rw [SOp.compC_of_mem hf hg, map_smul,
        correction_of_mem a c (comp_mem hg hf)]
      have hcf := Envelope.ofHom_mem (X := (⟨b, Y⟩ : Envelope R C))
        (Y := ⟨a, X⟩) (correction_mem a b hf)
      have hcg := Envelope.ofHom_mem (X := (⟨c, Z⟩ : Envelope R C))
        (Y := ⟨b, Y⟩) (correction_mem b c hg)
      rw [SOp.compC_of_mem hcf hcg]
      change sign R (p * q) • (sign R (exponent a c (q + p)) • (g ≫ f)) =
        sign R ((p + (b + a)) * (q + (c + b))) •
          (correction (R := R) b c g ≫ correction (R := R) a b f)
      rw [correction_of_mem b c hg, correction_of_mem a b hf,
        Linear.smul_comp, Linear.comp_smul, smul_smul, smul_smul, smul_smul]
      congr 1
      simp only [← sign_add]
      congr 1
      have e := exponent_comp a b c p q
      convert e using 1 <;> unfold exponent <;> ring
    · intro g h hg hh
      simp only [map_add, Envelope.ofHom, SOp.compC_add, Envelope.toHom_add, hg, hh]
  · intro f h hf hh
    simp only [map_add, Envelope.ofHom, SOp.add_compC, Envelope.toHom_add, hf, hh]
end StringDiagrams.PiSOp
