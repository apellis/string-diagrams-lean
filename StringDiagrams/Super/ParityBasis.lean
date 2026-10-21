/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.K0
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.SetTheory.Cardinal.Order

/-!
# Parity-permuted integral bases

The algebraic parity-orbit step in the corrected first preliminary fact of
Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §11,
used in Theorem 11.3. The index set need not be finite. A parity-fixed basis
vector obstructs freeness by fixed points modulo norms, not by comparing ranks.
The basis in this module is an intermediate algebraic input; the categorical
application constructs it by Krull–Schmidt.
-/

noncomputable section
namespace StringDiagrams.ParityBasis
open Module

universe u v
variable {M : Type u} [AddCommGroup M] [Module Zπ M]

/-- The parity action, viewed as an integral linear map. -/
def piLinear : M →ₗ[ℤ] M where
  toFun x := Zπ.π • x
  map_add' := smul_add _
  map_smul' n x := by simp [smul_comm n Zπ.π]

/-- The integral submodule of parity-fixed vectors. -/
def fixedSubmodule : Submodule ℤ M where
  carrier := {x | Zπ.π • x = x}
  zero_mem' := smul_zero _
  add_mem' hx hy := by simp only [Set.mem_ofPred_eq] at *; rw [smul_add, hx, hy]
  smul_mem' n x hx := by
    change Zπ.π • (n • x) = n • x
    rw [smul_comm, hx]

/-- The norm takes values in the fixed submodule. -/
def norm : M →ₗ[ℤ] fixedSubmodule (M := M) where
  toFun x := ⟨x + Zπ.π • x, by
    change Zπ.π • (x + Zπ.π • x) = x + Zπ.π • x
    rw [smul_add, smul_smul, Zπ.π_mul_π, one_smul, add_comm]⟩
  map_add' x y := by apply Subtype.ext; simp [smul_add, add_add_add_comm]
  map_smul' n x := by apply Subtype.ext; simp [smul_add, smul_comm Zπ.π n]

/-- Degree-zero Tate group: fixed vectors modulo norms. -/
abbrev TateZero := fixedSubmodule (M := M) ⧸ LinearMap.range (norm (M := M))

/-- A fixed vector represents zero in the Tate group exactly when it is a norm. -/
theorem tate_eq_zero_iff (x : M) (hx : Zπ.π • x = x) :
    Submodule.Quotient.mk (⟨x, hx⟩ : fixedSubmodule (M := M)) =
      (0 : TateZero (M := M)) ↔ ∃ y : M, y + Zπ.π • y = x := by
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

variable {ι : Type v} (b : Basis ι ℤ M) (σ : ι → ι)
    (hσ : Function.Involutive σ) (hb : ∀ i, Zπ.π • b i = b (σ i))
include hσ hb

/-- Parity permutes the integral coordinates by the same involution. -/
theorem repr_pi (x : M) (i : ι) : b.repr (Zπ.π • x) i = b.repr x (σ i) := by
  classical
  have h : (b.coord i).comp piLinear = b.coord (σ i) := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, piLinear, LinearMap.coe_mk, AddHom.coe_mk,
      hb, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    have he : σ j = i ↔ j = σ i := ⟨fun h => by rw [← h, hσ], fun h => by rw [h, hσ]⟩
    simp only [he]
  exact congrArg (fun f : M →ₗ[ℤ] ℤ => f x) h

/-- A parity-fixed integral basis vector is not a norm. -/
theorem fixed_not_norm (i : ι) (hi : σ i = i) :
    ¬ ∃ x : M, x + Zπ.π • x = b i := by
  rintro ⟨x, hx⟩
  have h := congrArg (fun y => b.repr y i) hx
  simp only [map_add, Finsupp.add_apply, repr_pi b σ hσ hb, hi,
    Basis.repr_self, Finsupp.single_eq_same] at h
  omega

/-- Each parity-fixed basis index supplies a nonzero Tate class. -/
theorem fixed_tate_ne_zero (i : ι) (hi : σ i = i) :
    Submodule.Quotient.mk
      (⟨b i, by change Zπ.π • b i = b i; rw [hb, hi]⟩ : fixedSubmodule (M := M)) ≠
        (0 : TateZero (M := M)) := by
  intro h
  exact fixed_not_norm b σ hσ hb i hi
    ((tate_eq_zero_iff (b i) (by rw [hb, hi])).1 h)

omit hσ hb in
/-- Every fixed point in a free parity module is a norm, even in infinite rank. -/
theorem norm_surjective_of_free [Module.Free Zπ M] (x : M) (hx : Zπ.π • x = x) :
    ∃ y : M, y + Zπ.π • y = x := by
  classical
  let c := Module.Free.chooseBasis Zπ M
  have hz (i) : ∃ a : ℤ, c.repr x i = (a : Zπ) + a * Zπ.π := by
    obtain ⟨a, d, hd⟩ := Zπ.exists_eq_add_mul_π (c.repr x i)
    have h := congrArg (fun y => c.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, hd] at h
    have he : (d : Zπ) + a * Zπ.π = a + d * Zπ.π := by
      calc
        (d : Zπ) + a * Zπ.π = Zπ.π * (a + d * Zπ.π) := by
          rw [mul_add, ← mul_assoc Zπ.π, mul_comm Zπ.π (d : Zπ), mul_assoc,
            Zπ.π_mul_π, mul_one, mul_comm Zπ.π (a : Zπ), add_comm]
        _ = _ := h
    have had := (Zπ.add_mul_π_injective he).1
    exact ⟨a, by simpa only [had] using hd⟩
  choose a ha using hz
  refine ⟨∑ i ∈ (c.repr x).support, (a i : Zπ) • c i, ?_⟩
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i ∈ (c.repr x).support, c.repr x i • c i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, mul_comm Zπ.π, ← add_smul, ← ha]
    _ = x := c.linearCombination_repr x

/-- Freeness excludes parity-fixed integral basis indices. This uses the norm
obstruction and makes no finiteness or cardinal-rank assumption. -/
theorem no_fixed_of_free [Module.Free Zπ M] : ∀ i, σ i ≠ i := by
  intro i hi
  exact fixed_not_norm b σ hσ hb i hi
    (norm_surjective_of_free (b i) (by rw [hb, hi]))

section Ordered
variable [LinearOrder ι]

/-- One representative of each two-element parity orbit. -/
abbrev PairRep := {i : ι // i < σ i}

omit hb in
private theorem pair_ne (i j : PairRep σ) : σ j.val ≠ i.val := by
  intro h
  have h' : σ i.val = j.val := by rw [← h, hσ]
  exact lt_asymm i.property (by simpa only [h', h] using j.property)

/-- Coordinates of a scalar times a chosen orbit representative. -/
theorem repr_scalar_pair (z : Zπ) (j : PairRep σ) (a d : ℤ)
    (hz : z = (a : Zπ) + d * Zπ.π) (i : PairRep σ) :
    b.repr (z • b j.val) i.val = if j = i then a else 0 := by
  classical
  rw [hz, add_smul, mul_smul, hb]
  simp only [Int.cast_smul_eq_zsmul, map_add, map_smul, Finsupp.add_apply,
    Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  simp [pair_ne σ hσ i j, Subtype.ext_iff]

/-- Coordinates at the other member of a chosen orbit. -/
theorem repr_scalar_pair_pi (z : Zπ) (j : PairRep σ) (a d : ℤ)
    (hz : z = (a : Zπ) + d * Zπ.π) (i : PairRep σ) :
    b.repr (z • b j.val) (σ i.val) = if j = i then d else 0 := by
  classical
  rw [hz, add_smul, mul_smul, hb]
  simp only [Int.cast_smul_eq_zsmul, map_add, map_smul, Finsupp.add_apply,
    Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  have hne : j.val ≠ σ i.val := (pair_ne σ hσ j i).symm
  simp [hne, hσ.injective.eq_iff, Subtype.ext_iff]

/-- The two-element orbit representatives are independent over the parity ring. -/
theorem paired_independent : LinearIndependent Zπ (fun i : PairRep σ => b i.val) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose a d hd using fun j => Zπ.exists_eq_add_mul_π (g j)
  have h₁ := congrArg (fun x => b.repr x i.val) hg
  have h₂ := congrArg (fun x => b.repr x (σ i.val)) hg
  simp only [map_sum, Finsupp.finsetSum_apply, map_zero, Finsupp.zero_apply,
    repr_scalar_pair b σ hσ hb _ _ _ _ (hd _) i] at h₁
  simp only [map_sum, Finsupp.finsetSum_apply, map_zero, Finsupp.zero_apply,
    repr_scalar_pair_pi b σ hσ hb _ _ _ _ (hd _) i] at h₂
  simp only [Finset.sum_ite_eq', hi, ite_true] at h₁ h₂
  rw [hd, h₁, h₂]
  simp

/-- In the absence of parity-fixed indices, the paired representatives form a
basis over `Zπ`. The basis is constructed from the integral basis, not assumed. -/
def pairedBasis (hn : ∀ i, σ i ≠ i) : Basis (PairRep σ) Zπ M :=
  Basis.mk (paired_independent b σ hσ hb) (by
    intro x _
    let S := Submodule.span Zπ (Set.range fun i : PairRep σ => b i.val)
    have hi (i : ι) : b i ∈ S := by
      rcases lt_or_gt_of_ne (hn i) with h | h
      · have hmem : b (σ i) ∈ S := Submodule.subset_span
          ⟨⟨σ i, by simpa only [hσ i] using h⟩, rfl⟩
        simpa only [hb, hσ i] using S.smul_mem Zπ.π hmem
      · exact Submodule.subset_span ⟨⟨i, h⟩, rfl⟩
    rw [← b.linearCombination_repr x]
    change (b.repr x).sum (fun i n => n • b i) ∈ S
    exact Submodule.sum_mem S (fun i _ => by
      simpa only [Int.cast_smul_eq_zsmul] using S.smul_mem ((b.repr x i : ℤ) : Zπ) (hi i)))

@[simp] theorem pairedBasis_apply (hn : ∀ i, σ i ≠ i) (i : PairRep σ) :
    pairedBasis b σ hσ hb hn i = b i.val :=
  Basis.mk_apply _ _ _

end Ordered

/-- The corrected freeness criterion for a parity-permuted integral basis,
valid for an arbitrary, possibly infinite, set of indices. -/
theorem free_iff : Module.Free Zπ M ↔ ∀ i, σ i ≠ i := by
  classical
  constructor
  · intro h
    let := h
    exact no_fixed_of_free b σ hσ hb
  · intro h
    let := linearOrderOfSTO (WellOrderingRel : ι → ι → Prop)
    exact Module.Free.of_basis (pairedBasis b σ hσ hb h)

/-- In this permutation-basis setting, vanishing of the fixed-point-modulo-norm
obstruction is equivalent to parity-ring freeness, in arbitrary rank. -/
theorem free_iff_norm_surjective : Module.Free Zπ M ↔
    ∀ x : M, Zπ.π • x = x → ∃ y : M, y + Zπ.π • y = x := by
  constructor
  · intro h
    let := h
    exact norm_surjective_of_free
  · intro h
    apply (free_iff b σ hσ hb).2
    intro i hi
    exact fixed_not_norm b σ hσ hb i hi (h (b i) (by rw [hb, hi]))

end StringDiagrams.ParityBasis
