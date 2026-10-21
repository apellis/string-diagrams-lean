/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Local finite-dimensional algebras

Fitting's lemma for a finite-dimensional algebra with no nontrivial idempotents.
This is the parity-independent algebraic input to the Krull–Schmidt argument in
Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §11
(first preliminary fact, used in Theorem 11.3). No algebraic closure assumption is needed.
-/

noncomputable section
namespace StringDiagrams.FiniteDimensionalAlgebra
open Function

section Fitting

variable (k : Type*) {E : Type*} [Field k] [Ring E] [Algebra k E] [FiniteDimensional k E]

include k

/-- In a finite-dimensional algebra, a left-invertible element is a unit. -/
theorem isUnit_of_mul_eq_one_left {g f : E} (h : g * f = 1) : IsUnit f := by
  have hinj : Injective (LinearMap.mulLeft k f) := fun x y hxy => by
    have := congrArg (g * ·) hxy
    simpa [← mul_assoc, h] using this
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
  have hy' : f * y = 1 := hy
  have hgy : g = y := by rw [← mul_one g, ← hy', ← mul_assoc, h, one_mul]
  exact ⟨⟨f, g, by rw [hgy, hy'], h⟩, rfl⟩

/-- **Fitting's lemma for algebras.** In a finite-dimensional `k`-algebra whose only idempotents
are `0` and `1`, every element is nilpotent or a unit. -/
theorem isNilpotent_or_isUnit_of_idempotent
    (h : ∀ e : E, IsIdempotentElem e → e = 0 ∨ e = 1) (f : E) : IsNilpotent f ∨ IsUnit f := by
  obtain ⟨n, hn, hn1⟩ := ((LinearMap.mulRight k f).eventually_isCompl_ker_pow_range_pow.and
    (Filter.eventually_ge_atTop 1)).exists
  rw [LinearMap.pow_mulRight] at hn
  set K := LinearMap.ker (LinearMap.mulRight k (f ^ n))
  set I := LinearMap.range (LinearMap.mulRight k (f ^ n))
  have hK : ∀ y x, x ∈ K → y * x ∈ K := by
    intro y x hx
    simp only [K, LinearMap.mem_ker, LinearMap.mulRight_apply] at hx ⊢
    rw [mul_assoc, hx, mul_zero]
  have hI : ∀ y x, x ∈ I → y * x ∈ I := by
    rintro y _ ⟨z, rfl⟩
    exact ⟨y * z, by simp [mul_assoc]⟩
  have h1 : (1 : E) ∈ K ⊔ I := by rw [hn.sup_eq_top]; trivial
  obtain ⟨e₁, he₁, e₂, he₂, hsum⟩ := Submodule.mem_sup.1 h1
  have hid : IsIdempotentElem e₁ := by
    have hdis := Submodule.disjoint_def.1 hn.disjoint
    have hK' : e₁ * e₁ - e₁ ∈ K := sub_mem (hK _ _ he₁) he₁
    have heq : e₁ * e₁ - e₁ = -(e₁ * e₂) := by
      have : e₁ * (e₁ + e₂) = e₁ := by rw [hsum, mul_one]
      rw [mul_add] at this
      rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, this, sub_self]
    have hI' : e₁ * e₁ - e₁ ∈ I := by rw [heq]; exact neg_mem (hI _ _ he₂)
    exact sub_eq_zero.1 (hdis _ hK' hI')
  rcases h e₁ hid with h0 | h1'
  · right
    rw [h0, zero_add] at hsum
    obtain ⟨z, hz⟩ : (1 : E) ∈ I := hsum ▸ he₂
    simp only [LinearMap.mulRight_apply] at hz
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn1
    refine isUnit_of_mul_eq_one_left k (g := z * f ^ m) ?_
    rw [mul_assoc, ← pow_succ, hz]
  · left
    refine ⟨n, ?_⟩
    have : (1 : E) ∈ K := h1' ▸ he₁
    simpa [K] using this

end Fitting

end StringDiagrams.FiniteDimensionalAlgebra
