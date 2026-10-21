/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Laurent bases from free integer-shift orbits

The linear-algebra input to the corrected first preliminary fact of
Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §11,
used in Theorems 11.3 and 11.7. Regrouping an integral basis into free
integer-shift orbits gives a basis over `ℤ[q,q⁻¹]`.
-/

noncomputable section
namespace StringDiagrams.LaurentBasis
open Module LaurentPolynomial

variable {ι M : Type*} [AddCommGroup M] [Module (LaurentPolynomial ℤ) M]

/-- Regroup the integral coordinates along the integer coordinate. -/
def regroup (b : Basis (ι × ℤ) ℤ M) :
    (ι →₀ LaurentPolynomial ℤ) ≃ₗ[ℤ] M :=
  (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv ℤ)).trans
    ((Finsupp.curryLinearEquiv ℤ).symm.trans b.repr.symm)

omit [Module (LaurentPolynomial ℤ) M] in
/-- The regrouping sends a single Laurent monomial to its integral basis vector. -/
theorem regroup_single (b : Basis (ι × ℤ) ℤ M) (i : ι) (n : ℤ) (a : ℤ) :
    regroup b (Finsupp.single i (AddMonoidAlgebra.single n a)) = a • b (i, n) := by
  classical
  have h : Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv ℤ)
      (Finsupp.single i (AddMonoidAlgebra.single n a)) =
      Finsupp.single i (Finsupp.single n a) :=
        Finsupp.mapRange_single (hf := map_zero _)
  change b.repr.symm (Finsupp.uncurry _) = _
  simp only [LinearEquiv.coe_coe]
  rw [h, Finsupp.uncurry_single, b.repr_symm_single]

/-- A product-indexed integral basis compatible with grading shift is a
Laurent basis on the degree-zero representatives. -/
def ofProduct (b : Basis (ι × ℤ) ℤ M)
    (hb : ∀ i n, (T n : LaurentPolynomial ℤ) • b (i, 0) = b (i, n)) :
    Basis ι (LaurentPolynomial ℤ) M := by
  let f := Finsupp.linearCombination (LaurentPolynomial ℤ) (fun i => b (i, 0))
  have hf : f.restrictScalars ℤ = (regroup b).toLinearMap := by
    apply Finsupp.lhom_ext
    intro i p
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp [f]
    | add p q hp hq => simpa only [Finsupp.single_add, map_add] using congrArg₂ (· + ·) hp hq
    | single n a =>
      simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, f,
        Finsupp.linearCombination_single, regroup_single]
      rw [← hb i n]
      rw [← smul_assoc]
      rw [T, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  exact Basis.ofRepr (LinearEquiv.ofBijective f (by
    change Function.Bijective (f.restrictScalars ℤ)
    rw [hf]
    exact (regroup b).bijective)).symm

@[simp] theorem ofProduct_apply (b : Basis (ι × ℤ) ℤ M)
    (hb : ∀ i n, (T n : LaurentPolynomial ℤ) • b (i, 0) = b (i, n)) (i : ι) :
    ofProduct b hb i = b (i, 0) := by
  simp [ofProduct, Basis.coe_ofRepr]

section Orbits
variable [AddAction ℤ ι]

/-- Integer-shift orbits, without identifying parity shifts. -/
abbrev Orbit := Quotient (AddAction.orbitRel ℤ ι)

/-- The chosen representative and its integer translates parameterize a free orbit. -/
def orbitEquiv (hfree : ∀ (i : ι) (n : ℤ), n +ᵥ i = i → n = 0) :
    Orbit (ι := ι) × ℤ ≃ ι :=
  Equiv.ofBijective (fun p => p.2 +ᵥ p.1.out) (by
    constructor
    · rintro ⟨o, m⟩ ⟨p, n⟩ h
      have hop : o = p := by
        have := congrArg (Quotient.mk (AddAction.orbitRel ℤ ι)) h
        simpa only [AddAction.orbitRel.Quotient.quotient_vadd_eq, Quotient.out_eq] using this
      subst p
      have hmn : m - n = 0 := hfree o.out (m - n) (by
        have := congrArg (fun i => (-n) +ᵥ i) h
        simpa only [← add_vadd, neg_add_cancel, zero_vadd, sub_eq_add_neg,
          add_comm m (-n)] using this)
      congr 1
      omega
    · intro i
      let o : Orbit (ι := ι) := Quotient.mk _ i
      have h : AddAction.orbitRel ℤ ι i o.out :=
        Quotient.exact (Quotient.out_eq o).symm
      obtain ⟨n, hn⟩ := h
      exact ⟨(o, n), hn⟩)

/-- A lower bound on the integers fixing each point forces a free action.
This is the group-action form of integer-shift rigidity. -/
theorem free_of_boundedBelow
    (h : ∀ i : ι, ∃ N : ℤ, ∀ n : ℤ, n +ᵥ i = i → N ≤ n) :
    ∀ (i : ι) (n : ℤ), n +ᵥ i = i → n = 0 := by
  intro i m hm
  obtain ⟨N, hN⟩ := h i
  have nonneg : ∀ n : ℤ, n ∈ AddAction.stabilizer ℤ i → 0 ≤ n := by
    intro n hn
    by_contra hneg
    have hn' : n ≤ -1 := by omega
    let a : ℕ := N.natAbs + 1
    have ha : -(a : ℤ) < N := by
      have := Int.le_natAbs (a := -N)
      rw [Int.natAbs_neg] at this
      dsimp [a]
      omega
    have hmem := (AddAction.stabilizer ℤ i).nsmul_mem hn a
    have hbound := hN ((a : ℤ) * n) (by
      simpa only [nsmul_eq_mul, AddAction.mem_stabilizer_iff] using hmem)
    have := mul_le_mul_of_nonneg_left hn' (Int.natCast_nonneg a)
    omega
  have hp := nonneg m hm
  have hn := nonneg (-m) ((AddAction.stabilizer ℤ i).neg_mem hm)
  omega

/-- The Laurent basis indexed by integer-shift orbits of an integral basis.
Freeness of the action is an explicit intermediate hypothesis, discharged in
categorical applications by bounded-below graded endomorphisms. -/
def ofOrbits (b : Basis ι ℤ M)
    (hb : ∀ n i, (T n : LaurentPolynomial ℤ) • b i = b (n +ᵥ i))
    (hfree : ∀ (i : ι) (n : ℤ), n +ᵥ i = i → n = 0) :
    Basis (Orbit (ι := ι)) (LaurentPolynomial ℤ) M :=
  ofProduct (b.reindex (orbitEquiv hfree).symm) (by
    intro o n
    simp only [Basis.reindex_apply, Equiv.symm_symm]
    change (T n : LaurentPolynomial ℤ) • b ((0 : ℤ) +ᵥ o.out) = b (n +ᵥ o.out)
    simpa only [zero_vadd] using hb n o.out)

@[simp] theorem ofOrbits_apply (b : Basis ι ℤ M)
    (hb : ∀ n i, (T n : LaurentPolynomial ℤ) • b i = b (n +ᵥ i))
    (hfree : ∀ (i : ι) (n : ℤ), n +ᵥ i = i → n = 0)
    (o : Orbit (ι := ι)) : ofOrbits b hb hfree o = b o.out := by
  rw [ofOrbits, ofProduct_apply]
  simp only [Basis.reindex_apply, Equiv.symm_symm]
  change b ((0 : ℤ) +ᵥ o.out) = b o.out
  rw [zero_vadd]

end Orbits
end StringDiagrams.LaurentBasis
