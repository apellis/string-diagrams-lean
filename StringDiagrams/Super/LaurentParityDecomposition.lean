/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.CoveringLaurent
import StringDiagrams.Super.ParityBasis
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Type-M and type-Q summands of a parity-permuted Laurent basis

This is the coefficient-module step in the corrected preliminary fact of BE2 §11.
A basis over R = ℤ[q,q⁻¹] permuted by parity gives free ℒ summands on paired
orbits and ℒ/(π − 1) summands on fixed orbits. No finite-rank hypothesis is used.
-/

noncomputable section
namespace StringDiagrams.CoveringLaurent
open Module
variable {M ι : Type*} [AddCommGroup M] [Module S M]
local instance : Module R M := Module.compHom M inclusion
local instance : Module S R := typeQModule
local instance : SMulCommClass S S M where
  smul_comm a c x := by rw [← mul_smul, mul_comm a c, mul_smul]
variable (b : Basis ι R M) (σ : ι → ι) (hσ : Function.Involutive σ)
  (hb : ∀ i, pi • b i = b (σ i)) [LinearOrder ι]

abbrev PairRep := {i : ι // i < σ i}
abbrev FixedRep := {i : ι // σ i = i}

include hσ in
private theorem pair_ne (i j : PairRep σ) : σ j.val ≠ i.val := by
  intro h
  have h' : σ i.val = j.val := by rw [← h, hσ]
  exact lt_asymm i.property (by simpa only [h', h] using j.property)

private theorem pair_ne_fixed (i : PairRep σ) (j : FixedRep σ) : i.val ≠ j.val := by
  intro h
  have hi := i.property
  rw [h, j.property] at hi
  exact lt_irrefl _ hi

include hσ in
private theorem pair_pi_ne_fixed (i : PairRep σ) (j : FixedRep σ) : σ i.val ≠ j.val := by
  intro h
  apply pair_ne_fixed σ i j
  have := congrArg σ h
  simpa only [hσ i.val, j.property] using this

include hσ hb in
/-- Coordinates at the first member of a paired orbit. -/
theorem repr_pair (z : S) (j : PairRep σ) (a d : R)
    (hz : z = inclusion a + inclusion d * pi) (i : PairRep σ) :
    b.repr (z • b j.val) i.val = if j = i then a else 0 := by
  classical
  rw [hz, add_smul, mul_smul, hb]
  change b.repr (a • b j.val + d • b (σ j.val)) i.val = _
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  simp [pair_ne σ hσ i j, Subtype.ext_iff]

include hσ hb in
/-- Coordinates at the second member of a paired orbit. -/
theorem repr_pair_pi (z : S) (j : PairRep σ) (a d : R)
    (hz : z = inclusion a + inclusion d * pi) (i : PairRep σ) :
    b.repr (z • b j.val) (σ i.val) = if j = i then d else 0 := by
  classical
  rw [hz, add_smul, mul_smul, hb]
  change b.repr (a • b j.val + d • b (σ j.val)) (σ i.val) = _
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  have hne : j.val ≠ σ i.val := (pair_ne σ hσ j i).symm
  simp [hne, hσ.injective.eq_iff, Subtype.ext_iff]

include hσ hb in
/-- Paired summands have no coordinates at fixed indices. -/
theorem repr_pair_fixed (z : S) (j : PairRep σ) (i : FixedRep σ) :
    b.repr (z • b j.val) i.val = 0 := by
  obtain ⟨a, d, rfl⟩ := exists_pair z
  rw [add_smul, mul_smul, hb]
  change b.repr (a • b j.val + d • b (σ j.val)) i.val = 0
  simp [pair_ne_fixed σ j i, pair_pi_ne_fixed σ hσ j i]

omit [LinearOrder ι] in
include hb in
/-- Parity-fixed basis vectors see specialization at π = 1. -/
theorem fixed_smul (z : S) (i : FixedRep σ) :
    z • b i.val = (augmentation z : R) • b i.val := by
  obtain ⟨a, d, rfl⟩ := exists_pair z
  rw [add_smul, mul_smul, hb, i.property]
  change a • b i.val + d • b i.val = augmentation (inclusion a + inclusion d * pi) • b i.val
  simp only [map_add, map_mul, eval_inclusion, eval_pi, map_one, mul_one, add_smul]

/-- Inclusion of a fixed-orbit coefficient module. -/
def fixedLift (i : FixedRep σ) : R →ₗ[S] M where
  toFun r := (r : R) • b i.val
  map_add' r s := add_smul r s _
  map_smul' z r := by
    change (augmentation z * r) • b i.val = z • (inclusion r • b i.val)
    rw [← mul_smul, fixed_smul b σ hb (z * inclusion r) i, map_mul, eval_inclusion]

/-- The sum of the paired and fixed coefficient maps. -/
def decompositionMap : ((PairRep σ →₀ S) × (FixedRep σ →₀ R)) →ₗ[S] M :=
  (Finsupp.linearCombination S (fun i : PairRep σ => b i.val)).coprod
    (Finsupp.lsum S (fixedLift b σ hb))

@[simp] theorem decompositionMap_pair_single (i : PairRep σ) (z : S) :
    decompositionMap b σ hb (Finsupp.single i z, 0) = z • b i.val := by
  simp [decompositionMap]

@[simp] theorem decompositionMap_fixed_single (i : FixedRep σ) (r : R) :
    decompositionMap b σ hb (0, Finsupp.single i r) = (r : R) • b i.val := by
  simp [decompositionMap, Finsupp.lsum_single, fixedLift]

/-- Explicit finite sum underlying the decomposition map. -/
theorem decompositionMap_apply (p : PairRep σ →₀ S) (q : FixedRep σ →₀ R) :
    decompositionMap b σ hb (p, q) =
      p.sum (fun i z => z • b i.val) + q.sum (fun i r => (r : R) • b i.val) := rfl

private theorem repr_fixed_pair (r : R) (j : FixedRep σ) (i : PairRep σ) :
    b.repr (r • b j.val) i.val = 0 := by
  simp [(pair_ne_fixed σ i j).symm]

include hσ in
private theorem repr_fixed_pair_pi (r : R) (j : FixedRep σ) (i : PairRep σ) :
    b.repr (r • b j.val) (σ i.val) = 0 := by
  simp [(pair_pi_ne_fixed σ hσ i j).symm]

private theorem repr_fixed_fixed (r : R) (j i : FixedRep σ) :
    b.repr (r • b j.val) i.val = if j = i then r else 0 := by
  classical
  simp [Subtype.ext_iff, Finsupp.single_apply]

include hσ in
/-- The paired and fixed coefficient maps have independent images. -/
theorem decompositionMap_ker (p : PairRep σ →₀ S) (q : FixedRep σ →₀ R)
    (h : decompositionMap b σ hb (p, q) = 0) : p = 0 ∧ q = 0 := by
  classical
  choose a d hd using fun j => exists_pair (p j)
  constructor
  · apply Finsupp.ext
    intro i
    by_cases hi : i ∈ p.support
    · have h₁ := congrArg (fun x => b.repr x i.val) h
      have h₂ := congrArg (fun x => b.repr x (σ i.val)) h
      simp only [decompositionMap_apply, Finsupp.sum, map_add, map_sum,
        Finsupp.add_apply, Finsupp.finsetSum_apply, map_zero, Finsupp.zero_apply,
        repr_pair b σ hσ hb _ _ _ _ (hd _) i, repr_fixed_pair b σ] at h₁
      simp only [decompositionMap_apply, Finsupp.sum, map_add, map_sum,
        Finsupp.add_apply, Finsupp.finsetSum_apply, map_zero, Finsupp.zero_apply,
        repr_pair_pi b σ hσ hb _ _ _ _ (hd _) i, repr_fixed_pair_pi b σ hσ] at h₂
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_ite_eq', hi, ite_true] at h₁ h₂
      rw [hd, h₁, h₂]
      simp
    · simpa only [Finsupp.zero_apply] using Finsupp.notMem_support_iff.1 hi
  · apply Finsupp.ext
    intro i
    by_cases hi : i ∈ q.support
    · have hq := congrArg (fun x => b.repr x i.val) h
      simp only [decompositionMap_apply, Finsupp.sum, map_add, map_sum,
        Finsupp.add_apply, Finsupp.finsetSum_apply, map_zero, Finsupp.zero_apply,
        repr_pair_fixed b σ hσ hb, repr_fixed_fixed b σ] at hq
      simpa only [Finset.sum_const_zero, zero_add, Finset.sum_ite_eq', hi, ite_true,
        Finsupp.zero_apply] using hq
    · simpa only [Finsupp.zero_apply] using Finsupp.notMem_support_iff.1 hi

include hσ in
/-- Every basis vector belongs to a paired or fixed coefficient summand. -/
theorem decompositionMap_surjective : Function.Surjective (decompositionMap b σ hb) := by
  classical
  let L := decompositionMap b σ hb
  have hi (i : ι) : b i ∈ LinearMap.range L := by
    rcases lt_trichotomy i (σ i) with h | h | h
    · refine ⟨(Finsupp.single ⟨i, h⟩ 1, 0), ?_⟩
      simp [L]
    · refine ⟨(0, Finsupp.single ⟨i, h.symm⟩ 1), ?_⟩
      simp [L]
    · refine ⟨(Finsupp.single ⟨σ i, by simpa only [hσ i] using h⟩ pi, 0), ?_⟩
      simp only [L, decompositionMap_pair_single, hb, hσ i]
  intro x
  change x ∈ LinearMap.range L
  rw [← b.linearCombination_repr x]
  change (b.repr x).sum (fun i r => (r : R) • b i) ∈ LinearMap.range L
  exact Submodule.sum_mem _ (fun i _ =>
    (LinearMap.range L).smul_mem (inclusion (b.repr x i)) (hi i))

/-- Mixed M/Q decomposition, with the fixed coefficient module written as R
with π specialized to 1. -/
def decomposition : ((PairRep σ →₀ S) × (FixedRep σ →₀ R)) ≃ₗ[S] M :=
  LinearEquiv.ofBijective (decompositionMap b σ hb) ⟨by
    intro x y h
    apply sub_eq_zero.mp
    have hz : decompositionMap b σ hb (x - y) = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨hp, hq⟩ := decompositionMap_ker b σ hσ hb (x - y).1 (x - y).2 hz
    exact Prod.ext hp hq,
    decompositionMap_surjective b σ hσ hb⟩

/-- The corrected covering-Laurent decomposition into ℒ and ℒ/(π − 1) summands. -/
def quotientDecomposition :
    ((PairRep σ →₀ S) × (FixedRep σ →₀ (S ⧸ Ideal.span ({pi - 1} : Set S)))) ≃ₗ[S] M :=
  (LinearEquiv.prodCongr (LinearEquiv.refl S (PairRep σ →₀ S))
    (Finsupp.mapRange.linearEquiv typeQEquiv)).trans (decomposition b σ hσ hb)

end StringDiagrams.CoveringLaurent
