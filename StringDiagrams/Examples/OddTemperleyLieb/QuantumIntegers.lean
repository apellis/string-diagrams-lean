import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# `π`-deformed quantum integers

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (1.10)–(1.12) and
Appendix A.

For a commutative ring `A`, a unit `x` and an element `π` of `A`,
`[n + 1]_{x,π} := x^n + π x^{n-2} + ⋯ + π^n x^{-n}` (1.10) is `qbracket x π (n + 1)`; in
general `qbracket x π n = Σ_{r < n} π^r x^{n-1-2r}`, so `qbracket x π 0 = 0`.

* `qbracket_succ_mul_two`: `[n + 1][2] = [n + 2] + π [n]`, the case `m = 1` of (1.11);
* `qbracket_mul` (**(1.11)**): `[n + 1][m + 1] = Σ_{r = 0}^{min(m,n)} π^r [n + m - 2r + 1]`
  (no hypothesis on `π` is needed);
* `qbracket_genFun_mul` (**(1.12)**, corrected): in `A⟦t⟧`,
  `(Σ_{n ≥ 0} [n + 1] tⁿ) · (1 - [2] t + π t²) = 1`.

**Correction to (1.12).** The paper prints `Σ_{n=0}^∞ [n]_{x,π} tⁿ = 1/(1 - [2]_{x,π} t + π t²)`.
Since `[0] = 0` (with the convention of Appendix A; (1.10) only defines `[n + 1]`) and
`[1] = 1`, the left side has constant term `0` while the right side has constant term `1`; the
correct statement is `Σ_{n=0}^∞ [n + 1]_{x,π} tⁿ = 1/(1 - [2]_{x,π} t + π t²)`, i.e.
`Σ_{n=0}^∞ [n]_{x,π} tⁿ = t/(1 - [2]_{x,π} t + π t²)` (`qbracket_genFun_mul'`). This is the
π-deformed generating function of the Chebyshev polynomials of the second kind, as the paper
says.

## The quantum integers of Appendix A

Appendix A fixes `ε := -1` and `q` in a field, and sets `[n] := (qⁿ - (εq)⁻ⁿ)/(q - εq⁻¹)`,
which is `[n]_{q,ε}` (`qint`, `qint_mul_eq`). The recurrence `[n][2] = [n + 1] + ε [n - 1]`
used in the proof of Theorem A.3 is `qint_mul_two`. If `q` is not a root of unity then
`[n] ≠ 0` for `n ≥ 1` (`qint_ne_zero`).
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open Finset

variable {A : Type*} [CommRing A]

/-- The integer powers of a unit, as elements of the ring. -/
abbrev xz (x : Aˣ) (k : ℤ) : A := ((x ^ k : Aˣ) : A)

theorem xz_mul_xz (x : Aˣ) (a b : ℤ) : xz x a * xz x b = xz x (a + b) := by
  rw [xz, xz, xz, ← Units.val_mul, ← zpow_add]

theorem xz_congr (x : Aˣ) {a b : ℤ} (h : a = b) : xz x a = xz x b := by rw [h]

/-- The `π`-deformed quantum integer `[n]_{x,π} = Σ_{r < n} π^r x^{n-1-2r}`; for `n + 1` this is
`x^n + π x^{n-2} + ⋯ + π^n x^{-n}`, (1.10). -/
def qbracket (x : Aˣ) (π : A) (n : ℕ) : A :=
  ∑ r ∈ range n, π ^ r * xz x ((n : ℤ) - 1 - 2 * r)

variable (x : Aˣ) (π : A)

@[simp] theorem qbracket_zero : qbracket x π 0 = 0 := by simp [qbracket]

@[simp] theorem qbracket_one : qbracket x π 1 = 1 := by simp [qbracket]

theorem qbracket_two : qbracket x π 2 = xz x 1 + π * xz x (-1) := by
  simp only [qbracket, sum_range_succ, range_zero, sum_empty, pow_zero, one_mul, zero_add,
    pow_one, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  congr 2

/-- (1.10): `[n + 1]_{x,π} = x^n + π x^{n-2} + ⋯ + π^n x^{-n}`. -/
theorem qbracket_succ_eq (n : ℕ) :
    qbracket x π (n + 1) = ∑ r ∈ range (n + 1), π ^ r * xz x ((n : ℤ) - 2 * r) := by
  refine sum_congr rfl fun r _ => ?_
  congr 2; push_cast; ring

/-- The recurrence `[n + 1][2] = [n + 2] + π [n]`: the case `m = 1` of (1.11). -/
theorem qbracket_succ_mul_two (n : ℕ) :
    qbracket x π (n + 1) * qbracket x π 2 = qbracket x π (n + 2) + π * qbracket x π n := by
  have ha : ∑ r ∈ range (n + 1), π ^ r * xz x (((n + 1 : ℕ) : ℤ) - 1 - 2 * r) * xz x 1 =
      ∑ r ∈ range (n + 1), π ^ r * xz x (((n + 2 : ℕ) : ℤ) - 1 - 2 * r) := by
    refine sum_congr rfl fun r _ => ?_
    rw [mul_assoc, xz_mul_xz]; congr 2; push_cast; ring
  have hb : ∑ r ∈ range (n + 1), π ^ r * xz x (((n + 1 : ℕ) : ℤ) - 1 - 2 * r) *
      (π * xz x (-1)) = π * ∑ r ∈ range n, π ^ r * xz x ((n : ℤ) - 1 - 2 * r) +
        π ^ (n + 1) * xz x (((n + 2 : ℕ) : ℤ) - 1 - 2 * ((n + 1 : ℕ) : ℤ)) := by
    rw [sum_range_succ, mul_sum]
    congr 1
    · refine sum_congr rfl fun r _ => ?_
      rw [show π ^ r * xz x (((n + 1 : ℕ) : ℤ) - 1 - 2 * r) * (π * xz x (-1)) =
        π * π ^ r * (xz x (((n + 1 : ℕ) : ℤ) - 1 - 2 * r) * xz x (-1)) by ring, xz_mul_xz]
      rw [mul_assoc]; congr 3; push_cast; ring
    · rw [show π ^ n * xz x (((n + 1 : ℕ) : ℤ) - 1 - 2 * (n : ℕ)) * (π * xz x (-1)) =
        π ^ n * π * (xz x (((n + 1 : ℕ) : ℤ) - 1 - 2 * (n : ℕ)) * xz x (-1)) by ring,
        xz_mul_xz, ← pow_succ]
      congr 2; push_cast; ring
  rw [qbracket_two, mul_add, qbracket, sum_mul, sum_mul, ha]
  rw [hb, qbracket, qbracket, sum_range_succ (n := n + 1)]
  ring

/-- (1.11): `[n + 1][m + 1] = Σ_{r=0}^{m} π^r [n + m - 2r + 1]` for `m ≤ n`. -/
theorem qbracket_mul_of_le (m n : ℕ) (h : m ≤ n) :
    qbracket x π (n + 1) * qbracket x π (m + 1) =
      ∑ r ∈ range (m + 1), π ^ r * qbracket x π (n + m - 2 * r + 1) := by
  induction m using Nat.strong_induction_on generalizing n with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp
    | 1, _ =>
      rw [qbracket_succ_mul_two, sum_range_succ, sum_range_one]
      simp only [pow_zero, one_mul, mul_zero, Nat.sub_zero, pow_one]
      rw [show n + 1 - 2 * 1 + 1 = n by omega]
    | m + 2, ih =>
      -- `[m + 3] = [m + 2][2] - π [m + 1]`
      have hrec : qbracket x π (m + 3) = qbracket x π (m + 2) * qbracket x π 2 -
          π * qbracket x π (m + 1) := by
        rw [qbracket_succ_mul_two]; ring
      rw [hrec, mul_sub, ← mul_assoc, ih (m + 1) (by omega) n (by omega),
        mul_left_comm, ih m (by omega) n (by omega), sum_mul, mul_sum]
      have hk : ∀ r ∈ range (m + 2), π ^ r * qbracket x π (n + (m + 1) - 2 * r + 1) *
          qbracket x π 2 = π ^ r * qbracket x π (n + (m + 1) - 2 * r + 2) +
            π ^ (r + 1) * qbracket x π (n + (m + 1) - 2 * r) := by
        intro r _
        rw [mul_assoc, qbracket_succ_mul_two, pow_succ]; ring
      rw [sum_congr rfl hk, sum_add_distrib]
      rw [sum_range_succ (fun r => π ^ (r + 1) * qbracket x π (n + (m + 1) - 2 * r)) (m + 1)]
      rw [sum_range_succ' (fun r => π ^ r * qbracket x π (n + (m + 2) - 2 * r + 1)) (m + 2)]
      rw [sum_range_succ (fun r => π ^ (r + 1) * qbracket x π (n + (m + 2) - 2 * (r + 1) + 1))
        (m + 1)]
      have e1 : ∀ r ∈ range (m + 2), π ^ r * qbracket x π (n + (m + 1) - 2 * r + 2) =
          π ^ r * qbracket x π (n + (m + 2) - 2 * r + 1) := by
        intro r hr; rw [mem_range] at hr
        congr 2; omega
      have e2 : ∀ r ∈ range (m + 1), π ^ (r + 1) * qbracket x π (n + (m + 1) - 2 * r) -
          π * (π ^ r * qbracket x π (n + m - 2 * r + 1)) = 0 := by
        intro r hr; rw [mem_range] at hr
        rw [show n + (m + 1) - 2 * r = n + m - 2 * r + 1 by omega, pow_succ]; ring
      rw [sum_congr rfl e1]
      have e3 : ∑ r ∈ range (m + 1), π ^ (r + 1) * qbracket x π (n + (m + 1) - 2 * r) =
          π * ∑ r ∈ range (m + 1), π ^ r * qbracket x π (n + m - 2 * r + 1) := by
        rw [mul_sum]; refine sum_congr rfl fun r hr => ?_
        have := e2 r hr; linear_combination this
      rw [e3, show n + (m + 1) - 2 * (m + 1) = n + (m + 2) - 2 * (m + 1 + 1) + 1 by omega,
        sum_range_succ' (fun r => π ^ r * qbracket x π (n + (m + 2) - 2 * r + 1)) (m + 1)]
      simp only [pow_zero, one_mul, mul_zero, Nat.sub_zero, mul_sum]
      ring_nf

/-- **(1.11)** (Clebsch–Gordan for `U_q(osp(1|2))`):
`[n + 1][m + 1] = Σ_{r=0}^{min(m,n)} π^r [n + m - 2r + 1]`. -/
theorem qbracket_mul (m n : ℕ) :
    qbracket x π (n + 1) * qbracket x π (m + 1) =
      ∑ r ∈ range (min m n + 1), π ^ r * qbracket x π (n + m - 2 * r + 1) := by
  rcases le_total m n with h | h
  · rw [min_eq_left h, qbracket_mul_of_le x π m n h]
  · rw [min_eq_right h, mul_comm, qbracket_mul_of_le x π n m h, add_comm n m]

/-- **(1.12)**, corrected: `(Σ_{n ≥ 0} [n + 1]_{x,π} tⁿ) · (1 - [2]_{x,π} t + π t²) = 1` in
`A⟦t⟧`. -/
theorem qbracket_genFun_mul :
    PowerSeries.mk (fun n => qbracket x π (n + 1)) *
      (1 - PowerSeries.C A (qbracket x π 2) * PowerSeries.X +
        PowerSeries.C A π * PowerSeries.X ^ 2) = 1 := by
  ext k
  rw [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_one]
  rw [show PowerSeries.C A (qbracket x π 2) * PowerSeries.X =
    PowerSeries.X * PowerSeries.C A (qbracket x π 2) from mul_comm _ _,
    show PowerSeries.C A π * PowerSeries.X ^ 2 = PowerSeries.X ^ 2 * PowerSeries.C A π from
      mul_comm _ _, ← mul_assoc, ← mul_assoc]
  rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_C]
  match k with
  | 0 => simp
  | 1 => simp [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_X_pow']
  | k + 2 =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      show PowerSeries.X ^ 2 = PowerSeries.X * PowerSeries.X from sq _, ← mul_assoc,
      PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
    simp only [show k + 2 ≠ 0 by omega, if_false]
    have := qbracket_succ_mul_two x π (k + 1)
    linear_combination -this

/-- (1.12), in the form with `[n]`: `(Σ_{n ≥ 0} [n]_{x,π} tⁿ) · (1 - [2]_{x,π} t + π t²) = t`. -/
theorem qbracket_genFun_mul' :
    PowerSeries.mk (fun n => qbracket x π n) *
      (1 - PowerSeries.C A (qbracket x π 2) * PowerSeries.X +
        PowerSeries.C A π * PowerSeries.X ^ 2) = PowerSeries.X := by
  have : PowerSeries.mk (fun n => qbracket x π n) =
      PowerSeries.X * PowerSeries.mk (fun n => qbracket x π (n + 1)) := by
    ext k
    cases k with
    | zero => simp
    | succ k => rw [mul_comm, PowerSeries.coeff_succ_mul_X]; simp
  rw [this, mul_assoc, qbracket_genFun_mul, mul_one]

/-- The closed form: `(x - π x⁻¹) [n]_{x,π} = xⁿ - πⁿ x⁻ⁿ`. -/
theorem qbracket_mul_eq (n : ℕ) :
    (xz x 1 - π * xz x (-1)) * qbracket x π n = xz x n - π ^ n * xz x (-(n : ℤ)) := by
  have := sum_range_sub (fun r => -(π ^ r * xz x ((n : ℤ) - 2 * r))) n
  simp only [pow_zero, one_mul, CharP.cast_eq_zero, mul_zero, sub_zero, sub_neg_eq_add] at this
  rw [show xz x n - π ^ n * xz x (-(n : ℤ)) =
    -(π ^ n * xz x ((n : ℤ) - 2 * n)) + xz x n by
      rw [show (n : ℤ) - 2 * n = -n by ring]; ring, ← this, qbracket, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [sub_mul, mul_left_comm, xz_mul_xz, pow_succ]
  rw [show π * xz x (-1) * (π ^ r * xz x ((n : ℤ) - 1 - 2 * r)) =
    π ^ r * π * (xz x (-1) * xz x ((n : ℤ) - 1 - 2 * r)) by ring, xz_mul_xz]
  rw [show (1 : ℤ) + (n - 1 - 2 * r) = n - 2 * r by ring,
    show (-1 : ℤ) + (n - 1 - 2 * r) = n - 2 * ((r + 1 : ℕ) : ℤ) by push_cast; ring]
  ring

/-! ## The quantum integers of Appendix A (`ε = -1`) -/

/-- `[n] = [n]_{q,ε}` with `ε = -1`, for a unit `q`; this equals `(qⁿ - (εq)⁻ⁿ)/(q - εq⁻¹)`
(`qint_mul_eq`). -/
abbrev qint (q : Aˣ) (n : ℕ) : A := qbracket q (-1) n

/-- `(q - ε q⁻¹) [n] = qⁿ - (εq)⁻ⁿ` with `ε = -1`. -/
theorem qint_mul_eq (q : Aˣ) (n : ℕ) :
    ((q : A) + ((q⁻¹ : Aˣ) : A)) * qint q n = xz q n - (-1) ^ n * xz q (-(n : ℤ)) := by
  have := qbracket_mul_eq q (-1) n
  simp only [xz, zpow_one, zpow_neg, zpow_one, neg_one_mul, sub_neg_eq_add] at this ⊢
  exact this

/-- `[2] = q - q⁻¹`, so that `δ = -[2] = -(q + ε q⁻¹)`. -/
theorem qint_two (q : Aˣ) : qint q 2 = (q : A) - ((q⁻¹ : Aˣ) : A) := by
  rw [qint, qbracket_two]; simp [xz]; ring

/-- The recurrence `[n][2] = [n + 1] + ε [n - 1]` (`ε = -1`) for `n ≥ 1`, used in the proof of
Theorem A.3. -/
theorem qint_mul_two (q : Aˣ) (n : ℕ) :
    qint q (n + 1) * qint q 2 = qint q (n + 2) - qint q n := by
  rw [qint, qbracket_succ_mul_two]; ring

/-- If `q` is not a root of unity, then `[n] ≠ 0` for every `n ≥ 1`. -/
theorem qint_ne_zero {q : Aˣ} (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) {n : ℕ} (hn : 0 < n) :
    qint q n ≠ 0 := by
  intro h
  have e := qint_mul_eq q n
  rw [h, mul_zero] at e
  -- `qⁿ = (-1)ⁿ q⁻ⁿ`, hence `q^{4n} = 1`
  have e' : ((q ^ (2 * n) : Aˣ) : A) = (-1) ^ n := by
    have : xz q n * xz q n = (-1) ^ n * (xz q (-(n : ℤ)) * xz q n) := by
      rw [← mul_assoc, ← sub_eq_zero.mp e.symm]
    rw [xz_mul_xz, xz_mul_xz, neg_add_cancel] at this
    simp only [xz, zpow_zero, Units.val_one, mul_one] at this
    rw [← this, two_mul, pow_add, zpow_add, zpow_natCast, Units.val_mul]
  apply hq (4 * n) (by omega)
  ext
  rw [show 4 * n = 2 * n + 2 * n by ring, pow_add, Units.val_mul, e', ← pow_add, ← two_mul,
    pow_mul]
  simp

end StringDiagrams.OddTemperleyLieb

end
