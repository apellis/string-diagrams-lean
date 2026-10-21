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

end StringDiagrams.CoveringLaurent
