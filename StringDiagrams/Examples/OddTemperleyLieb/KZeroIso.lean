import StringDiagrams.Examples.OddTemperleyLieb.KZeroRing
import Mathlib.Algebra.Polynomial.Laurent

/-!
# `K₀(SKar(STL(δ)))` as a subring of `Zπ[x, x⁻¹]` (Theorem A.3 = Theorem 1.18)

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Theorem 1.18 and
Theorem A.3 (the ring structure).

In `Zπ[x, x⁻¹]` (`LZ`), `[n + 1]_{x,π} = x^n + π x^{n-2} + ⋯ + π^n x^{-n}` (`brk`). The elements
`π^b [n + 1]_{x,π}` (`genL (n, b)`, `n ∈ ℕ`, `b ∈ ℤ/2`) are linearly independent over `ℤ`
(`linearIndependent_genL`), and their `ℤ`-span is a subring (`spanSubring`), by (1.11).

**Theorem A.3 (the Grothendieck ring).** `K₀ToLZ : K₀(SKar(STL(δ))) →+* Zπ[x, x⁻¹]` sends the class
of `P n b = (f_n)^b_b` to `π^b [n + 1]_{x,π}` (`K₀ToLZ_classJw`); it is injective
(`K₀ToLZ_injective`) with image the `ℤ`-span of these elements, giving the ring isomorphism
`K₀Equiv : K₀(SKar(STL(δ))) ≃+* spanSubring` which maps the basis of classes of the indecomposable
objects `P n b` (`basisK₀`) to the basis `{[n+1]_{x,π}, π [n+1]_{x,π}}`, i.e. an isomorphism of
based rings.
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory Limits Idempotents MonoidalCategory
open Rep (delta)
open LaurentPolynomial

/-! ## `Zπ` and `Zπ[x, x⁻¹]` -/

/-- The evaluations `Zπ → ℤ`, `π ↦ ±1`. -/
def evalZπ (s : ℤ) (hs : s ^ 2 = 1) : Zπ →+* ℤ :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom s) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [hs])

theorem evalZπ_π (s : ℤ) (hs : s ^ 2 = 1) : evalZπ s hs Zπ.π = s := by
  simp [evalZπ, Zπ.π]

/-- `1` and `π` are linearly independent over `ℤ`. -/
theorem Zπ.eq_zero_of_add_mul_π {a b : ℤ} (h : (a : Zπ) + (b : Zπ) * Zπ.π = 0) : a = 0 ∧ b = 0 := by
  have h1 := congrArg (evalZπ 1 (by norm_num)) h
  have h2 := congrArg (evalZπ (-1) (by norm_num)) h
  rw [map_add, map_mul, map_intCast, map_intCast, evalZπ_π, map_zero] at h1 h2
  simp only [Int.cast_id, mul_one, mul_neg] at h1 h2
  omega

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

end StringDiagrams.OddTemperleyLieb

end
