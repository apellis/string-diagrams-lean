import StringDiagrams.Examples.FreeDots
import StringDiagrams.LocalInterpretation
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The polynomial representation of free commuting dots

Every object of `FD R` is sent to the polynomial ring `MvPolynomial ℕ R`, and a dot with `i`
strands to its left acts by multiplication by `X i`. This is an interpretation by local
operators with a single module for all objects (`StringDiagrams.LocalInterpretation.uniform`);
there are no defining relations, and the interchange law holds because multiplication
operators commute (`LocalInterpretation.evalW_interchange_eq_zero_of_comm`).

## Main declarations

* `FreeDots.polyLocal R`, `FreeDots.polyRep R : FD R ⥤ ModuleCat R` (an `R`-linear functor),
  with `polyRep_map_x`: a dot on strand `i` acts by multiplication by `X i`.
* Non-vacuity over a nontrivial ring: dots are nonzero (`x_ne_zero`) and dots on distinct
  strands are distinct (`x_ne_x`).
-/

noncomputable section

namespace StringDiagrams.FreeDots

open CategoryTheory MvPolynomial LocalInterpretation

universe u

variable (R : Type u) [CommRing R]

/-- Multiplication by the variable `X i`. -/
def mulX (i : ℕ) : MvPolynomial ℕ R →ₗ[R] MvPolynomial ℕ R := LinearMap.mulLeft R (X i)

@[simp] theorem mulX_apply (i : ℕ) (f : MvPolynomial ℕ R) : mulX R i f = X i * f := rfl

/-- The operator of a layer: multiplication by the variable indexed by the number of strands
to the left of the dot. -/
def layerOp (L : Layer sig) : MvPolynomial ℕ R →ₗ[R] MvPolynomial ℕ R :=
  mulX R L.left.length

/-- The polynomial representation as an interpretation by local operators, with a single
module for all objects. -/
def polyLocal :
    LocalInterpretation sig R (MvPolynomial ℕ R) (fun _ : Unit => MvPolynomial ℕ R) :=
  uniform (layerOp R)

/-- Soundness: there are no relations, and the interchange law holds because multiplication
operators commute. -/
theorem polyLocal_respects : (pres R).Respects (polyLocal R).functor :=
  (polyLocal R).respects_of _ (fun r => r.elim) fun x hx u v _ =>
    (polyLocal R).evalW_interchange_eq_zero_of_comm (fun s l m r g g' => by
      have hs : (((⟨s, g, m, g'⟩ : InterchangeData sig).sign : ℤ) : R) = 1 := by
        simp [InterchangeData.sign, sig]
      have hc : (sig.cod g).length = (sig.dom g).length := rfl
      rw [hs, one_smul]
      refine LinearMap.ext fun f => ?_
      simp only [polyLocal, uniform_op, layerOp, LinearMap.comp_apply, mulX_apply,
        List.length_append, hc]
      ring) x hx u v

/-- The polynomial representation of free commuting dots. -/
def polyRep : FD R ⥤ ModuleCat.{u} R := (pres R).lift (polyLocal_respects R)

instance : (polyRep R).Additive := Presentation.lift_additive _

instance : (polyRep R).Linear R := Presentation.lift_linear _

@[simp] theorem polyRep_obj (n : ℕ) :
    (polyRep R).obj (FD.obj R n) = ModuleCat.of R (MvPolynomial ℕ R) := rfl

/-- The class of a diagram acts by the composite of the operators of its layers. -/
@[simp] theorem polyRep_map_diag {a b : Obj sig} (f : a ⟶ b) :
    (polyRep R).map ((pres R).diag f) = (polyLocal R).functor.map f :=
  Presentation.lift_diag _ f

/-- A dot on strand `i` acts by multiplication by `X i`. -/
theorem polyRep_map_x {n i : ℕ} (h : i < n) :
    (polyRep R).map (x R n i) = ModuleCat.ofHom (mulX R i) := by
  rw [x_def R h, polyRep_map_diag]
  apply ModuleCat.hom_ext
  rw [functor_map_hom]
  simp [polyLocal, layerOp, lay]

theorem polyRep_map_x_one {n i : ℕ} (h : i < n) :
    ((polyRep R).map (x R n i)).hom (1 : MvPolynomial ℕ R) = X i := by
  rw [polyRep_map_x R h, ModuleCat.hom_ofHom]
  exact mul_one (X i : MvPolynomial ℕ R)

/-- Over a nontrivial ring, a dot on any strand is nonzero. -/
theorem x_ne_zero [Nontrivial R] {n i : ℕ} (h : i < n) : x R n i ≠ 0 := by
  intro h0
  have h1 := polyRep_map_x_one R h
  rw [h0, CategoryTheory.Functor.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply] at h1
  exact MvPolynomial.X_ne_zero i h1.symm

/-- Over a nontrivial ring, dots on distinct strands are distinct. -/
theorem x_ne_x [Nontrivial R] {n i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    x R n i ≠ x R n j := by
  intro h0
  have h1 := polyRep_map_x_one R hi
  rw [h0, polyRep_map_x_one R hj] at h1
  exact hij (MvPolynomial.X_injective h1.symm)

end StringDiagrams.FreeDots

end
