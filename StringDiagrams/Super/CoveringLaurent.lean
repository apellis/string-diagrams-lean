/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.K0Ring
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coefficients of the covering Laurent ring

The coefficient algebra for the corrected BE2 §11 type-M/type-Q decomposition.
The covering Laurent ring has unique coordinates `a + bπ` over ℤ[q,q⁻¹].
-/

noncomputable section
namespace StringDiagrams.CoveringLaurent
open LaurentPolynomial
abbrev R := LaurentPolynomial ℤ
abbrev S := LaurentPolynomial Zπ

/-- The parity element in the covering Laurent ring. -/
def pi : S := C Zπ.π

/-- Extension of integral Laurent coefficients. -/
def inclusion : R →+* S := AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ)

@[simp] theorem pi_sq : pi * pi = 1 := by
  rw [pi, ← map_mul, Zπ.π_mul_π, map_one]

/-- Specialize the parity variable to a sign. -/
def eval (e : ℤ) (he : e * e = 1) : S →+* R :=
  AddMonoidAlgebra.mapRingHom ℤ (Zπ.eval e he)

@[simp] theorem eval_pi (e : ℤ) (he : e * e = 1) : eval e he pi = C e := by
  change AddMonoidAlgebra.mapRingHom ℤ (Zπ.eval e he)
    (AddMonoidAlgebra.single 0 Zπ.π) = AddMonoidAlgebra.single 0 e
  rw [AddMonoidAlgebra.mapRingHom_single, Zπ.eval_π]

@[simp] theorem eval_inclusion (e : ℤ) (he : e * e = 1) (a : R) :
    eval e he (inclusion a) = a := by
  ext n
  simp [eval, inclusion]

/-- Every covering Laurent polynomial has two integral Laurent coordinates. -/
theorem exists_pair (z : S) : ∃ a b : R, z = inclusion a + inclusion b * pi := by
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by simp only [map_add]; ring⟩
  | single n x =>
    obtain ⟨a, b, rfl⟩ := Zπ.exists_eq_add_mul_π x
    refine ⟨C a * T n, C b * T n, ?_⟩
    simp only [← single_eq_C_mul_T, inclusion, AddMonoidAlgebra.mapRingHom_single]
    change AddMonoidAlgebra.single n ((a : Zπ) + b * Zπ.π) =
      AddMonoidAlgebra.single n (a : Zπ) +
      AddMonoidAlgebra.single n (b : Zπ) * AddMonoidAlgebra.single 0 Zπ.π
    rw [AddMonoidAlgebra.single_mul_single, add_zero, ← AddMonoidAlgebra.single_add]

/-- The two coordinates are unique; no division by two is used. -/
theorem pair_injective {a b c d : R}
    (h : inclusion a + inclusion b * pi = inclusion c + inclusion d * pi) :
    a = c ∧ b = d := by
  have hp := congrArg (eval 1 (by norm_num)) h
  have hm := congrArg (eval (-1) (by norm_num)) h
  simp only [map_add, map_mul, eval_inclusion, eval_pi, map_one, mul_one] at hp
  simp only [map_add, map_mul, eval_inclusion, eval_pi, map_neg, map_one, mul_neg,
    mul_one] at hm
  constructor <;> ext n
  all_goals
    have h₁ := congrArg (fun z : R => z.coeff n) hp
    have h₂ := congrArg (fun z : R => z.coeff n) hm
    change a.coeff n + b.coeff n = c.coeff n + d.coeff n at h₁
    change a.coeff n + -(b.coeff n) = c.coeff n + -(d.coeff n) at h₂
    omega

/-- Specialization at π = 1. -/
abbrev augmentation : S →+* R := eval 1 (by norm_num)

/-- The parity-fixed coefficient module. -/
@[instance_reducible] def typeQModule : Module S R := Module.compHom R augmentation

/-- The only relation in the parity-fixed summand is π − 1. -/
theorem augmentation_ker : RingHom.ker augmentation = Ideal.span ({pi - 1} : Set S) := by
  apply le_antisymm
  · intro z hz
    change augmentation z = 0 at hz
    obtain ⟨a, b, rfl⟩ := exists_pair z
    have hab : a + b = 0 := by simpa only [map_add, map_mul, eval_inclusion,
      eval_pi, map_one, mul_one] using hz
    have ha : a = -b := eq_neg_of_add_eq_zero_left hab
    apply Ideal.mem_span_singleton'.2
    refine ⟨inclusion b, ?_⟩
    rw [ha, map_neg]
    ring
  · apply Ideal.span_le.2
    intro z hz
    obtain rfl : z = pi - 1 := hz
    change augmentation (pi - 1) = 0
    simp only [map_sub, eval_pi, map_one, sub_self]

/-- The parity relation generates a two-sided ideal. -/
instance parityIdeal_twoSided : (Ideal.span ({pi - 1} : Set S)).IsTwoSided where
  mul_mem_of_left := by
    intro z w hw
    rw [mul_comm z w]
    exact (Ideal.span ({pi - 1} : Set S)).mul_mem_left w hw

/-- Evaluate the parity-fixed quotient in integral Laurent polynomials. -/
def quotientEval : (S ⧸ Ideal.span ({pi - 1} : Set S)) →+* R :=
  Ideal.Quotient.lift _ augmentation (by
    intro z hz
    exact (show z ∈ RingHom.ker augmentation from by rwa [augmentation_ker]))

/-- The quotient evaluation is bijective. -/
theorem quotientEval_bijective : Function.Bijective quotientEval := by
  constructor
  · intro x y h
    apply sub_eq_zero.mp
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (x - y)
    rw [← hz]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    rw [← augmentation_ker]
    change augmentation z = 0
    change quotientEval (Ideal.Quotient.mk _ z) = 0
    rw [hz, map_sub, h, sub_self]
  · intro a
    refine ⟨Ideal.Quotient.mk _ (inclusion a), ?_⟩
    exact eval_inclusion 1 (by norm_num) a

/-- The parity-fixed summand is precisely ℒ/(π − 1), as an ℒ-module. -/
def typeQEquiv :
    letI := typeQModule
    (S ⧸ Ideal.span ({pi - 1} : Set S)) ≃ₗ[S] R := by
  letI := typeQModule
  refine { (RingEquiv.ofBijective quotientEval quotientEval_bijective).toAddEquiv with
    map_smul' := ?_ }
  intro z x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  change augmentation (z * w) = augmentation z * augmentation w
  exact map_mul _ _ _

end StringDiagrams.CoveringLaurent
