import StringDiagrams.Examples.OddTemperleyLieb.KZeroRing
import Mathlib.Algebra.Polynomial.Laurent

/-!
# `K₀(SKar(STL(δ)))` as a subring of `Zπ[x, x⁻¹]` (Theorem A.3 = Theorem 1.18)

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Theorem 1.18 and
Theorem A.3 (the ring structure).

In `Zπ[x, x⁻¹]` (`LZ`), `[n + 1]_{x,π} = x^n + π x^{n-2} + ⋯ + π^n x^{-n}` (`brk`). The elements
`π^b [n + 1]_{x,π}` (`genL (n, b)`, `n ∈ ℕ`, `b ∈ ℤ/2`) are linearly independent over `ℤ`
(`linearIndependent_genL`).

**Theorem A.3 (the Grothendieck ring).** `K₀ToLZ : K₀(SKar(STL(δ))) →+* Zπ[x, x⁻¹]` sends the class
of `P n b = (f_n)^b_b` to `π^b [n + 1]_{x,π}` (`K₀ToLZ_classJw`); it is injective
(`K₀ToLZ_injective`) with image the `ℤ`-span of these elements, giving the ring isomorphism
`K₀Equiv : K₀(SKar(STL(δ))) ≃+* (K₀ToLZ q hq).range` (a subring whose underlying set is the
`ℤ`-span of the elements `π^b [n + 1]_{x,π}`, `range_K₀ToLZ`) which maps the basis of classes of the indecomposable
objects `P n b` (`basisK₀`) to the basis `{[n+1]_{x,π}, π [n+1]_{x,π}}`, i.e. an isomorphism of
based rings.
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory Limits Idempotents MonoidalCategory
open Rep (delta)
open LaurentPolynomial

/-! ## `Zπ` and `Zπ[x, x⁻¹]` -/

/-- `1` and `π` are linearly independent over `ℤ`. -/
theorem Zπ.eq_zero_of_add_mul_π {a b : ℤ} (h : (a : Zπ) + (b : Zπ) * Zπ.π = 0) : a = 0 ∧ b = 0 :=
  Zπ.add_mul_π_injective (c := 0) (d := 0) (by rw [h]; simp)

/-- The ring `Zπ[x, x⁻¹]`. -/
abbrev LZ : Type := LaurentPolynomial Zπ

/-- The unit `x ∈ Zπ[x, x⁻¹]`. -/
def xU : LZˣ where
  val := T 1
  inv := T (-1)
  val_inv := by rw [← T_add]; simp
  inv_val := by rw [← T_add]; simp

theorem xz_xU (k : ℤ) : xz xU k = T k := by
  rw [xz]
  induction k using Int.induction_on with
  | hz => simp
  | hp n ih => rw [zpow_add_one, Units.val_mul, ih, T_add]; rfl
  | hn n ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    show T (-(n : ℤ)) * T (-1) = T (-(n : ℤ) - 1)
    rw [← T_add]
    congr 1

/-- `π` as a constant Laurent polynomial. -/
abbrev πL : LZ := C Zπ.π

theorem πL_mul_πL : πL * πL = 1 := by rw [← map_mul, Zπ.π_mul_π, map_one]

/-- `[n]_{x,π}` in `Zπ[x, x⁻¹]`. -/
abbrev brk (n : ℕ) : LZ := qbracket xU πL n

theorem brk_succ (n : ℕ) :
    brk (n + 1) = ∑ r ∈ Finset.range (n + 1), C (Zπ.π ^ r) * T ((n : ℤ) - 2 * r) := by
  rw [brk, qbracket_succ_eq]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [xz_xU, map_pow]

/-- The basis elements `π^b [n + 1]_{x,π}`. -/
def genL (x : ℕ × ZMod 2) : LZ := πL ^ x.2.val * brk (x.1 + 1)

theorem genL_coeff (n : ℕ) (b : ZMod 2) (k : ℤ) :
    genL (n, b) k = ∑ r ∈ Finset.range (n + 1),
      if (n : ℤ) - 2 * r = k then Zπ.π ^ (b.val + r) else 0 := by
  rw [genL, brk_succ, Finset.mul_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← map_pow, ← mul_assoc, ← map_mul, ← pow_add, ← single_eq_C_mul_T, Finsupp.single_apply]

theorem genL_coeff_self (n : ℕ) (b : ZMod 2) : genL (n, b) n = Zπ.π ^ b.val := by
  rw [genL_coeff, Finset.sum_eq_single 0]
  · simp
  · intro r _ hr; rw [if_neg]; omega
  · simp

theorem genL_coeff_of_lt {n : ℕ} (b : ZMod 2) {k : ℤ} (hk : (n : ℤ) < k) : genL (n, b) k = 0 := by
  rw [genL_coeff]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [if_neg]; omega

/-- **The elements `[n+1]_{x,π}`, `π [n+1]_{x,π}` are linearly independent over `ℤ`.** -/
theorem linearIndependent_genL : LinearIndependent ℤ genL := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  set s' := s.filter fun j => g j ≠ 0
  have hne : s'.Nonempty := ⟨i, by simp [s', hi, hgi]⟩
  obtain ⟨i₀, hi₀, hmax⟩ := s'.exists_max_image (fun j => j.1) hne
  set N := i₀.1
  have hc := congrArg (fun p : LZ => p (N : ℤ)) hsum
  simp only at hc
  rw [Finsupp.finset_sum_apply] at hc
  simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply] at hc
  -- only the terms of degree `N` contribute
  have hterm : ∀ j ∈ s, (g j • genL j) (N : ℤ) =
      if j.1 = N then g j • Zπ.π ^ j.2.val else 0 := by
    intro j hj
    change g j • genL j (N : ℤ) = _
    by_cases hgj : g j = 0
    · simp [hgj]
    · have hjN : j.1 ≤ N := hmax j (by simp [s', hj, hgj])
      obtain ⟨n, b⟩ := j
      split_ifs with h
      · simp only at h; subst h; rw [genL_coeff_self]
      · rw [genL_coeff_of_lt b (by simp only at hjN h; omega), smul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter] at hc
  -- the degree-`N` terms are `g (N, 0) + g (N, 1) π`
  set A := ∑ j ∈ s.filter (fun j => j.1 = N ∧ j.2 = 0), g j
  set B := ∑ j ∈ s.filter (fun j => j.1 = N ∧ j.2 = 1), g j
  have hAB : (A : Zπ) + (B : Zπ) * Zπ.π = 0 := by
    rw [← hc]
    have : s.filter (fun j => j.1 = N) = s.filter (fun j => j.1 = N ∧ j.2 = 0) ∪
        s.filter (fun j => j.1 = N ∧ j.2 = 1) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Supercategory.parity_eq_zero_or_one j.2 with h | h
        · exact Or.inl ⟨h1, h2, h⟩
        · exact Or.inr ⟨h1, h2, h⟩
      · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩
    rw [this, Finset.sum_union]
    · simp only [A, B, Int.cast_sum, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_filter] at hj
        rw [hj.2.2]; simp
      · refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_filter] at hj
        rw [hj.2.2]; simp [zsmul_eq_mul, ZMod.val_one]
    · rw [Finset.disjoint_filter]
      rintro j - ⟨-, h0⟩ ⟨-, h1⟩
      rw [h0] at h1; exact absurd h1 (by decide)
  obtain ⟨hA, hB⟩ := Zπ.eq_zero_of_add_mul_π hAB
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.mp hi₀).1
  have hgi₀ : g i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2
  rcases Supercategory.parity_eq_zero_or_one i₀.2 with h | h
  · have : A = g i₀ := by
      show ∑ j ∈ s.filter (fun j => j.1 = N ∧ j.2 = 0), g j = g i₀
      rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_filter.mpr ⟨hi₀s, rfl, h⟩)]
      intro j hj hji
      simp only [Finset.mem_filter] at hj
      exact absurd (Prod.ext hj.2.1 (hj.2.2.trans h.symm)) hji
    exact hgi₀ (this ▸ hA)
  · have : B = g i₀ := by
      show ∑ j ∈ s.filter (fun j => j.1 = N ∧ j.2 = 1), g j = g i₀
      rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_filter.mpr ⟨hi₀s, rfl, h⟩)]
      intro j hj hji
      simp only [Finset.mem_filter] at hj
      exact absurd (Prod.ext hj.2.1 (hj.2.2.trans h.symm)) hji
    exact hgi₀ (this ▸ hB)

theorem genL_zero_zero : genL (0, 0) = 1 := by simp [genL, brk]

theorem genL_one (n : ℕ) : genL (n, 1) = πL * genL (n, 0) := by
  simp [genL, ZMod.val_one]

/-! ## The ring homomorphism `K₀ → Zπ[x, x⁻¹]` -/

variable {k : Type*} [Field k] (q : kˣ)

local notation "δq" => delta q

variable (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq

/-- The additive map `K₀(SKar(STL(δ))) → Zπ[x, x⁻¹]`, `[P n b] ↦ π^b [n+1]_{x,π}`. -/
def K₀ToLZlin : K₀ (SKar k (STL k δq)) →ₗ[ℤ] LZ := (basisK₀ q hq).constr ℤ genL

theorem basisK₀_eq_classJw (x : ℕ × ZMod 2) : basisK₀ q hq x = classJw q hq x :=
  basisK₀_apply q hq x

theorem K₀ToLZlin_classJw (x : ℕ × ZMod 2) : K₀ToLZlin q hq (classJw q hq x) = genL x := by
  rw [K₀ToLZlin, ← basisK₀_eq_classJw, Basis.constr_basis]

omit hq in
theorem πsmul_πsmul (x : K₀ (SKar k (STL k δq))) : Zπ.π • Zπ.π • x = x := by
  rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, Zπ.π_mul_π, map_one, one_mul]

theorem K₀ToLZlin_π_smul (x : K₀ (SKar k (STL k δq))) :
    K₀ToLZlin q hq (Zπ.π • x) = πL * K₀ToLZlin q hq x := by
  have : (K₀ToLZlin q hq).comp (DistribMulAction.toLinearMap ℤ _ Zπ.π) =
      (LinearMap.mulLeft ℤ πL).comp (K₀ToLZlin q hq) := by
    refine (basisK₀ q hq).ext fun ⟨n, b⟩ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, DistribMulAction.toLinearMap_apply,
      LinearMap.mulLeft_apply, basisK₀_eq_classJw]
    rcases Supercategory.parity_eq_zero_or_one b with rfl | rfl
    · rw [← classJw_one, K₀ToLZlin_classJw, K₀ToLZlin_classJw, genL_one]
    · rw [K₀ToLZlin_classJw q hq (n, 1), classJw_one, πsmul_πsmul, K₀ToLZlin_classJw, genL_one,
        ← mul_assoc, πL_mul_πL, one_mul]
  exact LinearMap.congr_fun this x

theorem K₀ToLZlin_classJw_mul_gen (n : ℕ) :
    K₀ToLZlin q hq (classJw q hq (n, 0) * classJw q hq (1, 0)) = genL (n, 0) * brk 2 := by
  rcases n with _ | N
  · rw [← one_eq_classJw, one_mul, K₀ToLZlin_classJw, genL_zero_zero, one_mul]
    simp [genL]
  · rw [classJw_mul_one, map_add, K₀ToLZlin_π_smul, K₀ToLZlin_classJw, K₀ToLZlin_classJw]
    simp only [genL, ZMod.val_zero, pow_zero, one_mul]
    rw [qbracket_succ_mul_two]

theorem K₀ToLZlin_mul_gen (x : K₀ (SKar k (STL k δq))) :
    K₀ToLZlin q hq (x * classJw q hq (1, 0)) = K₀ToLZlin q hq x * brk 2 := by
  have : (K₀ToLZlin q hq).comp (LinearMap.mulRight ℤ (classJw q hq (1, 0))) =
      (LinearMap.mulRight ℤ (brk 2)).comp (K₀ToLZlin q hq) := by
    refine (basisK₀ q hq).ext fun ⟨n, b⟩ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply, basisK₀_eq_classJw]
    rcases Supercategory.parity_eq_zero_or_one b with rfl | rfl
    · rw [K₀ToLZlin_classJw, K₀ToLZlin_classJw_mul_gen]
    · rw [K₀ToLZlin_classJw q hq (n, 1), classJw_one, smul_mul_assoc, K₀ToLZlin_π_smul,
        K₀ToLZlin_classJw_mul_gen, genL_one, mul_assoc]
  exact LinearMap.congr_fun this x

theorem K₀ToLZlin_mul_classJw (n : ℕ) : ∀ x : K₀ (SKar k (STL k δq)),
    K₀ToLZlin q hq (x * classJw q hq (n, 0)) = K₀ToLZlin q hq x * genL (n, 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x
  match n, ih with
  | 0, _ => rw [← one_eq_classJw, mul_one, genL_zero_zero, mul_one]
  | 1, _ => rw [K₀ToLZlin_mul_gen]; simp [genL]
  | n + 2, ih =>
    have e : classJw q hq (n + 2, 0) =
        classJw q hq (n + 1, 0) * classJw q hq (1, 0) - Zπ.π • classJw q hq (n, 0) := by
      rw [classJw_mul_one]; abel
    rw [e, mul_sub, ← mul_assoc, mul_smul_comm, map_sub, K₀ToLZlin_mul_gen, K₀ToLZlin_π_smul,
      ih (n + 1) (by omega), ih n (by omega)]
    simp only [genL, ZMod.val_zero, pow_zero, one_mul]
    have := qbracket_succ_mul_two xU πL (n + 1)
    rw [show n + 2 + 1 = n + 1 + 2 by omega, show n + 1 + 1 = n + 2 by omega] at *
    linear_combination (K₀ToLZlin q hq x) * this

theorem K₀ToLZlin_mul (x y : K₀ (SKar k (STL k δq))) :
    K₀ToLZlin q hq (x * y) = K₀ToLZlin q hq x * K₀ToLZlin q hq y := by
  have : (K₀ToLZlin q hq).comp (LinearMap.mulLeft ℤ x) =
      (LinearMap.mulLeft ℤ (K₀ToLZlin q hq x)).comp (K₀ToLZlin q hq) := by
    refine (basisK₀ q hq).ext fun ⟨n, b⟩ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, basisK₀_eq_classJw]
    rcases Supercategory.parity_eq_zero_or_one b with rfl | rfl
    · rw [K₀ToLZlin_mul_classJw, K₀ToLZlin_classJw]
    · rw [classJw_one, mul_smul_comm, K₀ToLZlin_π_smul, K₀ToLZlin_π_smul,
        K₀ToLZlin_mul_classJw, K₀ToLZlin_classJw]
      ring
  exact LinearMap.congr_fun this y

/-- **Theorem A.3**: the ring homomorphism `K₀(SKar(STL(δ))) → Zπ[x, x⁻¹]` with
`[(f_n)^b_b] ↦ π^b [n+1]_{x,π}`. -/
def K₀ToLZ : K₀ (SKar k (STL k δq)) →+* LZ where
  toFun := K₀ToLZlin q hq
  map_one' := by rw [one_eq_classJw, K₀ToLZlin_classJw, genL_zero_zero]
  map_mul' := K₀ToLZlin_mul q hq
  map_zero' := map_zero _
  map_add' := map_add _

@[simp] theorem K₀ToLZ_classJw (x : ℕ × ZMod 2) : K₀ToLZ q hq (classJw q hq x) = genL x :=
  K₀ToLZlin_classJw q hq x

theorem K₀ToLZ_injective : Function.Injective (K₀ToLZ q hq) := by
  intro x y h
  have hx : K₀ToLZ q hq x = Finsupp.linearCombination ℤ genL ((basisK₀ q hq).repr x) := by
    rw [K₀ToLZ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, K₀ToLZlin, Basis.constr_apply,
      Finsupp.linearCombination_apply]
  have hy : K₀ToLZ q hq y = Finsupp.linearCombination ℤ genL ((basisK₀ q hq).repr y) := by
    rw [K₀ToLZ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, K₀ToLZlin, Basis.constr_apply,
      Finsupp.linearCombination_apply]
  rw [hx, hy] at h
  exact (basisK₀ q hq).repr.injective (linearIndependent_genL h)

/-- The image of `K₀(SKar(STL(δ)))` is the `ℤ`-span of the elements `π^b [n+1]_{x,π}`. -/
theorem range_K₀ToLZ :
    ((K₀ToLZ q hq).range : Set LZ) = Submodule.span ℤ (Set.range genL) := by
  have : (Set.range (K₀ToLZ q hq)) = Set.range (K₀ToLZlin q hq) := rfl
  rw [RingHom.coe_range, this, ← LinearMap.range_coe, K₀ToLZlin, Basis.constr_range]

/-- **Theorem A.3 = Theorem 1.18 (the Grothendieck ring).** `K₀(SKar(STL(δ)))` is isomorphic, as
a ring, to the subring of `Zπ[x, x⁻¹]` spanned over `ℤ` by `[n+1]_{x,π}` and `π [n+1]_{x,π}`
(`range_K₀ToLZ`), by an isomorphism sending the class of `(f_n)^b_b` to `π^b [n+1]_{x,π}`. -/
def K₀Equiv : K₀ (SKar k (STL k δq)) ≃+* (K₀ToLZ q hq).range :=
  RingEquiv.ofBijective (K₀ToLZ q hq).rangeRestrict
    ⟨fun _ _ h => K₀ToLZ_injective q hq (congrArg Subtype.val h),
      (K₀ToLZ q hq).rangeRestrict_surjective⟩

theorem K₀Equiv_classJw (x : ℕ × ZMod 2) :
    (K₀Equiv q hq (classJw q hq x) : LZ) = genL x := K₀ToLZ_classJw q hq x

end StringDiagrams.OddTemperleyLieb

end
