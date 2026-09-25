import StringDiagrams.Examples.NilHecke.Relations
import StringDiagrams.Examples.NilHecke.DividedDifference
import StringDiagrams.Examples.NilHecke.Dots

/-!
# The longest element of the nilHecke algebra

Source: M. Khovanov, A. D. Lauda, *A diagrammatic approach to categorification of quantum
groups I*, arXiv:0803.4121v2, §2.2, Example 3 (pp. 10–11): for a reduced word `a₁ ⋯ a_r` of
`w ∈ S_m` the element `∂_w = ∂_{a₁} ⋯ ∂_{a_r}` does not depend on the reduced word, and for the
longest element `w₀` the element `x₁^{m-1} x₂^{m-2} ⋯ x_{m-1} ∂_{w₀}` is an idempotent.

## Conventions

Indices are `0`-based (the paper's `∂_a`, `x_a` are `ψ R n (a - 1)`, `x R n (a - 1)`), and
products in `End (NH.obj R n)` are composition of operators, as in the paper.

## The reduced word

For a family `s : ℕ → A` in a monoid with zero we set (see `NilCoxeter.down`, `NilCoxeter.up`,
`NilCoxeter.longest`)

* `down s k = s (k-1) * s (k-2) * ⋯ * s 0`,
* `up s k = s 0 * s 1 * ⋯ * s (k-1)`,
* `longest s m = down s 0 * down s 1 * ⋯ * down s (m-1)`
  `= (s 0) (s 1 s 0) (s 2 s 1 s 0) ⋯ (s (m-2) ⋯ s 0)`.

Thus `ψw₀ R n m = longest (ψ R n) m` is the product of crossings along the reduced word
`(0)(1 0)(2 1 0) ⋯ (m-2 ⋯ 1 0)` of the longest element of `S_m` (`0`-based), i.e. the paper's
`∂_1 (∂_2 ∂_1) (∂_3 ∂_2 ∂_1) ⋯ (∂_{m-1} ⋯ ∂_1)`, of length `m(m-1)/2`.

Whenever `s` satisfies the nil-Coxeter relations (`NilCoxeter.Rels`: `s i * s i = 0`, the braid
relation and far commutativity, at every index) we prove, by braid moves:

* `NilCoxeter.longest_succ`: `longest s (m+1) = up s m * longest s m`, and hence
  `NilCoxeter.longest_eq_longestRev`: `longest s m` equals the product along the reversed word
  `(0 1 ⋯ m-2) ⋯ (0 1)(0)`;
* `NilCoxeter.longest_mul_eq_zero`, `NilCoxeter.mul_longest_eq_zero`: for `i + 1 < m`,
  `longest s m * s i = 0` and `s i * longest s m = 0`.

These apply both to the crossings `ψ R n` (`ψw₀`) and to the divided difference operators
`divDiff` in `Module.End R (MvPolynomial ℕ R)` (`divDiffW₀`).

## Main results

* `ψw₀_mul_ψ`, `ψ_mul_ψw₀`: `ψw₀ R n m * ψ R n i = 0 = ψ R n i * ψw₀ R n m` for `i + 1 < m`
  (for all `n`).
* `ψw₀_succ`, `ψw₀_eq_rev`: the second factorization and the reversed word.
* `ψw₀_succ_eq_mul_shift`, `ψw₀_succ_eq_shift_mul`: the mirror factorizations
  `ψw₀ (m+1) = (ψ_{m-1} ⋯ ψ_0) * shift (ψw₀ m) = shift (ψw₀ m) * (ψ_0 ⋯ ψ_{m-1})`, where `shift`
  moves the longest crossing to the strands `1, …, m`.
* `divDiffW₀_xδ`: `∂_{w₀} (X 0 ^ (m-1) * X 1 ^ (m-2) * ⋯ * X (m-2)) = 1`.
* `ψw₀_mul_mul_ψw₀_of_slide`: if `d : MvPolynomial ℕ R → End (NH.obj R n)` satisfies the
  polynomial slide `ψ i * d f = d (swapVars i f) * ψ i + d (divDiff i f)` for `i + 1 < m`, then
  `ψw₀ * d f * ψw₀ = d (∂_{w₀} f) * ψw₀`, where `∂_{w₀} = divDiffW₀ R m` is the composite of
  divided differences along the same reduced word.
* `idempotent_of_slide`: under the same hypothesis and `d 1 = 1`,
  `e_m = d (x^δ) * ψw₀ R n m` satisfies `e_m * e_m = e_m`.
* `ψw₀_mul_dots_mul_ψw₀`: the case `d = dots R n` (the polynomial slide `ψ_mul_dots`):
  `ψw₀ * dots f * ψw₀ = dots (∂_{w₀} f) * ψw₀`, for all `n`, `m`, `f`.
* `klIdempotent R n m = dots R n (x^δ) * ψw₀ R n m` and `klIdempotent_mul_self`:
  the paper's `x_1^{m-1} x_2^{m-2} ⋯ x_{m-1} ∂_{w₀}` (dots on the first `m` of `n` strands,
  above the crossings) is an idempotent, over any commutative ring `R`, for all `m ≤ n`.

Independence of the reduced word is proved only for the two words above (which is what the
idempotence argument uses), not for arbitrary reduced words. Only idempotence is proved here; that `e_m ≠ 0` for `m ≤ n` (which needs a faithful
representation) is not addressed. For `m > n`, `m ≥ 2`, `ψw₀ R n m = 0`.
-/

noncomputable section

namespace StringDiagrams.NilHecke

open CategoryTheory MvPolynomial

/-! ## Words in a nil-Coxeter family -/

namespace NilCoxeter

variable {A : Type*} [MonoidWithZero A]

/-- The nil-Coxeter relations of type `A`, at every index: `s i ^ 2 = 0`, the braid relation,
and far commutativity. -/
structure Rels (s : ℕ → A) : Prop where
  sq : ∀ i, s i * s i = 0
  braid : ∀ i, s i * s (i + 1) * s i = s (i + 1) * s i * s (i + 1)
  comm : ∀ i j, i + 1 < j → s i * s j = s j * s i

/-- `down s k = s (k-1) * ⋯ * s 1 * s 0`. -/
def down (s : ℕ → A) : ℕ → A
  | 0 => 1
  | k + 1 => s k * down s k

/-- `up s k = s 0 * s 1 * ⋯ * s (k-1)`. -/
def up (s : ℕ → A) : ℕ → A
  | 0 => 1
  | k + 1 => up s k * s k

/-- The longest element along the word `(0)(1 0)(2 1 0) ⋯ (m-2 ⋯ 0)`:
`longest s m = down s 0 * down s 1 * ⋯ * down s (m-1)`. -/
def longest (s : ℕ → A) : ℕ → A
  | 0 => 1
  | m + 1 => longest s m * down s m

/-- The longest element along the reversed word:
`longestRev s m = up s (m-1) * ⋯ * up s 1 * up s 0`. -/
def longestRev (s : ℕ → A) : ℕ → A
  | 0 => 1
  | m + 1 => up s m * longestRev s m

@[simp] theorem down_zero (s : ℕ → A) : down s 0 = 1 := rfl
theorem down_succ (s : ℕ → A) (k : ℕ) : down s (k + 1) = s k * down s k := rfl
@[simp] theorem up_zero (s : ℕ → A) : up s 0 = 1 := rfl
theorem up_succ (s : ℕ → A) (k : ℕ) : up s (k + 1) = up s k * s k := rfl
@[simp] theorem longest_zero (s : ℕ → A) : longest s 0 = 1 := rfl
theorem longest_succ' (s : ℕ → A) (m : ℕ) : longest s (m + 1) = longest s m * down s m := rfl
@[simp] theorem longestRev_zero (s : ℕ → A) : longestRev s 0 = 1 := rfl
theorem longestRev_succ (s : ℕ → A) (m : ℕ) :
    longestRev s (m + 1) = up s m * longestRev s m := rfl

/-! ### Transport along a multiplicative relation -/

section Transport

variable {B : Type*} [MonoidWithZero B] (s : ℕ → A) (t : ℕ → B) (P : A → B → Prop)

theorem down_rel (h1 : P 1 1) (hmul : ∀ a b a' b', P a a' → P b b' → P (a * b) (a' * b'))
    {k : ℕ} (hs : ∀ i, i < k → P (s i) (t i)) : P (down s k) (down t k) := by
  induction k with
  | zero => exact h1
  | succ k ih => exact hmul _ _ _ _ (hs k (by omega)) (ih fun i hi => hs i (by omega))

theorem up_rel (h1 : P 1 1) (hmul : ∀ a b a' b', P a a' → P b b' → P (a * b) (a' * b'))
    {k : ℕ} (hs : ∀ i, i < k → P (s i) (t i)) : P (up s k) (up t k) := by
  induction k with
  | zero => exact h1
  | succ k ih => exact hmul _ _ _ _ (ih fun i hi => hs i (by omega)) (hs k (by omega))

/-- A relation `P` which contains `(1, 1)`, is closed under products and contains
`(s i, t i)` for `i + 1 < m` contains `(longest s m, longest t m)`. -/
theorem longest_rel (h1 : P 1 1) (hmul : ∀ a b a' b', P a a' → P b b' → P (a * b) (a' * b'))
    {m : ℕ} (hs : ∀ i, i + 1 < m → P (s i) (t i)) : P (longest s m) (longest t m) := by
  induction m with
  | zero => exact h1
  | succ m ih =>
    exact hmul _ _ _ _ (ih fun i hi => hs i (by omega))
      (down_rel s t P h1 hmul fun i hi => hs i (by omega))

end Transport

/-! ### Braid moves -/

variable {s : ℕ → A} (hs : Rels s)
include hs

theorem comm_assoc {i j : ℕ} (h : i + 1 < j) (x : A) : s i * (s j * x) = s j * (s i * x) := by
  rw [← mul_assoc, hs.comm i j h, mul_assoc]

theorem braid_assoc (i : ℕ) (x : A) :
    s i * (s (i + 1) * (s i * x)) = s (i + 1) * (s i * (s (i + 1) * x)) := by
  simp only [← mul_assoc, hs.braid i]

theorem down_comm {j k : ℕ} (h : j < k) : s k * down s j = down s j * s k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [down_succ, ← comm_assoc hs (by omega), ih (by omega), mul_assoc]

theorem up_comm {j k : ℕ} (h : j < k) : s k * up s j = up s j * s k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [up_succ, ← mul_assoc, ih (by omega), mul_assoc, ← hs.comm j k (by omega), mul_assoc]

theorem longest_comm {m k : ℕ} (h : m ≤ k) : s k * longest s m = longest s m * s k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [longest_succ', ← mul_assoc, ih (by omega), mul_assoc, down_comm hs (by omega),
      mul_assoc]

theorem down_succ_mul_zero (k : ℕ) : down s (k + 1) * s 0 = 0 := by
  induction k with
  | zero => simp [down_succ, hs.sq]
  | succ k ih => rw [down_succ, mul_assoc, ih, mul_zero]

theorem zero_mul_up_succ (k : ℕ) : s 0 * up s (k + 1) = 0 := by
  induction k with
  | zero => simp [up_succ, hs.sq]
  | succ k ih => rw [up_succ, ← mul_assoc, ih, zero_mul]

/-- `(s (m-1) ⋯ s 0) * s (j+1) = s j * (s (m-1) ⋯ s 0)` for `j + 2 ≤ m`. -/
theorem down_mul_succ {j m : ℕ} (h : j + 2 ≤ m) : down s m * s (j + 1) = s j * down s m := by
  induction m, h using Nat.le_induction with
  | base =>
    calc down s (j + 2) * s (j + 1)
        = s (j + 1) * (s j * (down s j * s (j + 1))) := by simp only [down_succ, mul_assoc]
      _ = s (j + 1) * (s j * (s (j + 1) * down s j)) := by rw [down_comm hs (by omega)]
      _ = s j * (s (j + 1) * (s j * down s j)) := by rw [braid_assoc hs]
      _ = s j * down s (j + 2) := by simp only [down_succ]
  | succ m hm ih =>
    rw [down_succ, mul_assoc, ih, ← comm_assoc hs (i := j) (j := m) (by omega)]

/-- `s (j+1) * (s 0 ⋯ s (m-1)) = (s 0 ⋯ s (m-1)) * s j` for `j + 2 ≤ m`. -/
theorem succ_mul_up {j m : ℕ} (h : j + 2 ≤ m) : s (j + 1) * up s m = up s m * s j := by
  induction m, h using Nat.le_induction with
  | base =>
    calc s (j + 1) * up s (j + 2)
        = (s (j + 1) * up s j) * (s j * s (j + 1)) := by simp only [up_succ, mul_assoc]
      _ = up s j * (s (j + 1) * (s j * (s (j + 1) * 1))) := by
          rw [up_comm hs (show j < j + 1 by omega)]; simp only [mul_assoc, mul_one]
      _ = up s j * (s j * (s (j + 1) * (s j * 1))) := by rw [braid_assoc hs]
      _ = up s (j + 2) * s j := by simp only [up_succ, mul_assoc, mul_one]
  | succ m hm ih =>
    rw [up_succ, ← mul_assoc, ih, mul_assoc, hs.comm j m (by omega), mul_assoc]

/-- The second factorization: `longest s (m+1) = up s m * longest s m`. -/
theorem longest_succ (m : ℕ) : longest s (m + 1) = up s m * longest s m := by
  induction m with
  | zero => simp [longest_succ']
  | succ m ih =>
    calc longest s (m + 2) = longest s (m + 1) * (s m * down s m) := rfl
      _ = up s m * ((s m * longest s m) * down s m) := by
          rw [ih, longest_comm hs le_rfl]; simp only [mul_assoc]
      _ = up s (m + 1) * longest s (m + 1) := by simp only [up_succ, longest_succ', mul_assoc]

/-- Independence of the reduced word: the words `(0)(1 0) ⋯ (m-2 ⋯ 0)` and
`(0 1 ⋯ m-2) ⋯ (0 1)(0)` give the same element. -/
theorem longest_eq_longestRev (m : ℕ) : longest s m = longestRev s m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [longest_succ hs, longestRev_succ, ih]

/-- The shifted family `i ↦ s (i + 1)` (the same generators on the strands `1, 2, …`) also
satisfies the nil-Coxeter relations. -/
theorem Rels.shift : Rels (fun i => s (i + 1)) where
  sq i := hs.sq (i + 1)
  braid i := hs.braid (i + 1)
  comm i j h := hs.comm (i + 1) (j + 1) (by omega)

omit hs in
theorem down_succ_eq_shift (k : ℕ) : down s (k + 1) = down (fun i => s (i + 1)) k * s 0 := by
  induction k with
  | zero => simp [down_succ]
  | succ k ih => rw [down_succ, ih, down_succ, mul_assoc]

omit hs in
theorem up_succ_eq_shift (k : ℕ) : up s (k + 1) = s 0 * up (fun i => s (i + 1)) k := by
  induction k with
  | zero => simp [up_succ]
  | succ k ih => rw [up_succ, ih, up_succ, mul_assoc]

theorem down_shift_mul_up {k M : ℕ} (h : k + 1 ≤ M) :
    down (fun i => s (i + 1)) k * up s M = up s M * down s k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [down_succ, mul_assoc, ih (by omega), ← mul_assoc, succ_mul_up hs (by omega), mul_assoc,
      down_succ]

/-- Mirror factorization: `longest s (m+1) = shift (longest s m) * (s 0 ⋯ s (m-1))`, where
`shift` raises every index by one. -/
theorem longest_succ_eq_shift_mul (m : ℕ) :
    longest s (m + 1) = longest (fun i => s (i + 1)) m * up s m := by
  induction m with
  | zero => simp [longest_succ']
  | succ m ih =>
    calc longest s (m + 2) = longest s (m + 1) * (s m * down s m) := rfl
      _ = longest (fun i => s (i + 1)) m * (up s (m + 1) * down s m) := by
          rw [ih, up_succ]; simp only [mul_assoc]
      _ = longest (fun i => s (i + 1)) (m + 1) * up s (m + 1) := by
          rw [← down_shift_mul_up hs le_rfl, longest_succ', mul_assoc]

/-- Mirror factorization: `longest s (m+1) = (s (m-1) ⋯ s 0) * shift (longest s m)`. -/
theorem longest_succ_eq_mul_shift (m : ℕ) :
    longest s (m + 1) = down s m * longest (fun i => s (i + 1)) m := by
  induction m with
  | zero => simp [longest_succ']
  | succ m ih =>
    rw [longest_succ hs, ih, ← mul_assoc, ← down_shift_mul_up hs le_rfl, up_succ_eq_shift,
      ← mul_assoc, ← down_succ_eq_shift, longest_succ hs.shift, mul_assoc]

theorem longest_mul_eq_zero {m i : ℕ} (h : i + 1 < m) : longest s m * s i = 0 := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [longest_succ', mul_assoc]
    rcases i with _ | j
    · rw [down_succ_mul_zero hs, mul_zero]
    · rw [down_mul_succ hs (by omega), ← mul_assoc, ih (by omega), zero_mul]

theorem mul_longest_eq_zero {m i : ℕ} (h : i + 1 < m) : s i * longest s m = 0 := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [longest_succ hs, ← mul_assoc]
    rcases i with _ | j
    · rw [zero_mul_up_succ hs, zero_mul]
    · rw [succ_mul_up hs (by omega), mul_assoc, ih (by omega), mul_zero]

end NilCoxeter

open NilCoxeter

/-! ## The longest crossing in `NH R` -/

variable (R : Type*) [CommRing R]

theorem ψ_rels (n : ℕ) : Rels (ψ R n) where
  sq := ψ_mul_ψ R n
  braid := ψ_braid R n
  comm _ _ h := ψ_mul_ψ_comm R h

/-- The crossing `ψ_{w₀}` of the longest element of `S_m`, on the first `m` of `n` strands, along
the reduced word `(0)(1 0)(2 1 0) ⋯ (m-2 ⋯ 1 0)` (`0`-based), i.e. the paper's
`∂_1 (∂_2 ∂_1) ⋯ (∂_{m-1} ⋯ ∂_1)`. It is meaningful for `m ≤ n`; for `m > n` it is `0` as soon
as `m ≥ 2` (`ψw₀_of_lt`). -/
def ψw₀ (n m : ℕ) : End (NH.obj R n) := longest (ψ R n) m

theorem ψw₀_zero (n : ℕ) : ψw₀ R n 0 = 1 := rfl

/-- `ψ_{w₀}` for `m + 1` strands is `ψ_{w₀}` for `m` strands followed (in operator order) by
`ψ_{m-1} ⋯ ψ_1 ψ_0`. -/
theorem ψw₀_succ' (n m : ℕ) : ψw₀ R n (m + 1) = ψw₀ R n m * down (ψ R n) m := rfl

/-- The second factorization: `ψ_{w₀}` for `m + 1` strands is `ψ_0 ψ_1 ⋯ ψ_{m-1}` times
`ψ_{w₀}` for `m` strands. -/
theorem ψw₀_succ (n m : ℕ) : ψw₀ R n (m + 1) = up (ψ R n) m * ψw₀ R n m :=
  longest_succ (ψ_rels R n) m

/-- `ψ_{w₀}` equals the product along the reversed reduced word
`(0 1 ⋯ m-2) ⋯ (0 1)(0)`. -/
theorem ψw₀_eq_rev (n m : ℕ) : ψw₀ R n m = longestRev (ψ R n) m :=
  longest_eq_longestRev (ψ_rels R n) m

/-- Mirror factorization: `ψ_{w₀}` for `m + 1` strands is `ψ_{m-1} ⋯ ψ_1 ψ_0` times `ψ_{w₀}` for
the `m` strands `1, …, m`. -/
theorem ψw₀_succ_eq_mul_shift (n m : ℕ) :
    ψw₀ R n (m + 1) = down (ψ R n) m * longest (fun i => ψ R n (i + 1)) m :=
  longest_succ_eq_mul_shift (ψ_rels R n) m

/-- Mirror factorization: `ψ_{w₀}` for `m + 1` strands is `ψ_{w₀}` for the `m` strands
`1, …, m` times `ψ_0 ψ_1 ⋯ ψ_{m-1}`. -/
theorem ψw₀_succ_eq_shift_mul (n m : ℕ) :
    ψw₀ R n (m + 1) = longest (fun i => ψ R n (i + 1)) m * up (ψ R n) m :=
  longest_succ_eq_shift_mul (ψ_rels R n) m

theorem ψw₀_mul_ψ {n m i : ℕ} (h : i + 1 < m) : ψw₀ R n m * ψ R n i = 0 :=
  longest_mul_eq_zero (ψ_rels R n) h

theorem ψ_mul_ψw₀ {n m i : ℕ} (h : i + 1 < m) : ψ R n i * ψw₀ R n m = 0 :=
  mul_longest_eq_zero (ψ_rels R n) h

theorem ψw₀_of_lt {n m : ℕ} (h : n < m) (h' : 1 < m) : ψw₀ R n m = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [ψw₀_succ', down_succ, ψ_of_le R (by omega), zero_mul, mul_zero]

/-! ## The divided difference operator of the longest element -/

variable {R}

theorem divDiff_rels : Rels (fun i => (divDiff (R := R) i : Module.End R (MvPolynomial ℕ R))) where
  sq i := LinearMap.ext (divDiff_divDiff_apply i)
  braid i := LinearMap.ext (divDiff_braid_apply i)
  comm _ _ h := LinearMap.ext (divDiff_comm_apply (Or.inl h))

variable (R) in
/-- `∂_{w₀} = ∂_0 (∂_1 ∂_0) ⋯ (∂_{m-2} ⋯ ∂_0)` (the paper's `∂_1 (∂_2 ∂_1) ⋯ (∂_{m-1} ⋯ ∂_1)`),
the divided difference operator of the longest element of `S_m`, along the same reduced word
as `ψw₀`. -/
def divDiffW₀ (m : ℕ) : Module.End R (MvPolynomial ℕ R) := longest (fun i => divDiff i) m

/-- The second factorization `∂_{w₀}^{(m+1)} = (∂_0 ∂_1 ⋯ ∂_{m-1}) ∂_{w₀}^{(m)}`. -/
theorem divDiffW₀_succ (m : ℕ) :
    divDiffW₀ R (m + 1) = up (fun i => divDiff i) m * divDiffW₀ R m :=
  longest_succ divDiff_rels m

theorem divDiffW₀_eq_rev (m : ℕ) : divDiffW₀ R m = longestRev (fun i => divDiff i) m :=
  longest_eq_longestRev divDiff_rels m

theorem divDiffW₀_mul_divDiff {m i : ℕ} (h : i + 1 < m) : divDiffW₀ R m * divDiff i = 0 :=
  longest_mul_eq_zero divDiff_rels (s := fun i => divDiff i) h

theorem divDiff_mul_divDiffW₀ {m i : ℕ} (h : i + 1 < m) : divDiff i * divDiffW₀ R m = 0 :=
  mul_longest_eq_zero divDiff_rels (s := fun i => divDiff i) h

/-- `∂_{w₀}` is linear over polynomials symmetric under `s_0, …, s_{m-2}`. -/
theorem divDiffW₀_mul_of_swap_eq {m : ℕ} {g : MvPolynomial ℕ R}
    (hg : ∀ i, i + 1 < m → swapVars i g = g) (f : MvPolynomial ℕ R) :
    divDiffW₀ R m (g * f) = g * divDiffW₀ R m f :=
  longest_rel (fun i => divDiff i) (fun i => divDiff (R := R) i)
    (fun a _ => ∀ f, a (g * f) = g * a f) (fun _ => rfl)
    (fun a b _ _ ha hb f => by rw [Module.End.mul_apply, Module.End.mul_apply, hb, ha])
    (fun i hi f => divDiff_mul_of_swap_eq (hg i hi) f) f

/-- The product `X 0 * X 1 * ⋯ * X (m-1)`. -/
def xProd (m : ℕ) : MvPolynomial ℕ R := ∏ j ∈ Finset.range m, X j

variable (R) in
/-- The monomial `x^δ = X 0 ^ (m-1) * X 1 ^ (m-2) * ⋯ * X (m-2) ^ 1`, the paper's
`x_1^{m-1} x_2^{m-2} ⋯ x_{m-1}`. -/
def xδ (m : ℕ) : MvPolynomial ℕ R := ∏ j ∈ Finset.range m, X j ^ (m - 1 - j)

theorem xδ_succ (m : ℕ) : xδ R (m + 1) = xProd m * xδ R m := by
  rw [xδ, xδ, xProd, Finset.prod_range_succ, show m + 1 - 1 - m = 0 by omega, pow_zero, mul_one,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [← pow_succ']
  congr 1
  omega

theorem swapVars_xProd {i m : ℕ} (h : i + 1 < m ∨ m ≤ i) :
    swapVars i (xProd (R := R) m) = xProd m := by
  rw [xProd, map_prod]
  simp only [swapVars_X]
  rcases h with h | h
  · refine Equiv.Perm.prod_comp (Equiv.swap i (i + 1)) _ X fun a ha => ?_
    simp only [Set.mem_setOf_eq] at ha
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h'
    exact ha (Equiv.swap_apply_of_ne_of_ne (by omega) (by omega))
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

theorem up_divDiff_xProd (k : ℕ) : up (fun i => divDiff (R := R) i) k (xProd k) = 1 := by
  induction k with
  | zero => simp [xProd]
  | succ k ih =>
    rw [up_succ, Module.End.mul_apply, xProd, Finset.prod_range_succ, ← xProd,
      divDiff_mul_of_swap_eq (swapVars_xProd (Or.inr le_rfl)), divDiff_X_self, mul_one, ih]

/-- `∂_{w₀} (x^δ) = 1` (KL I, §2.2 Example 3, p. 11). -/
theorem divDiffW₀_xδ (m : ℕ) : divDiffW₀ R m (xδ R m) = 1 := by
  induction m with
  | zero => simp [divDiffW₀, xδ]
  | succ m ih =>
    rw [divDiffW₀_succ, Module.End.mul_apply, xδ_succ,
      divDiffW₀_mul_of_swap_eq (fun i hi => swapVars_xProd (Or.inl hi)), ih, mul_one,
      up_divDiff_xProd]

/-! ## Sliding polynomials through `ψ_{w₀}` -/

section Slide

variable {n : ℕ} (d : MvPolynomial ℕ R → End (NH.obj R n))

/-- If `d` satisfies the polynomial slide `ψ_i d(f) = d(s_i f) ψ_i + d(∂_i f)` for `i + 1 < m`
and `Z` is killed on the left by `ψ_i` for `i + 1 < m`, then `ψ_{w₀} d(f) Z = d(∂_{w₀} f) Z`. -/
theorem ψw₀_mul_mul_of_slide {m : ℕ} {Z : End (NH.obj R n)}
    (hZ : ∀ i, i + 1 < m → ψ R n i * Z = 0)
    (hd : ∀ i f, i + 1 < m → ψ R n i * d f = d (swapVars i f) * ψ R n i + d (divDiff i f))
    (f : MvPolynomial ℕ R) :
    ψw₀ R n m * d f * Z = d (divDiffW₀ R m f) * Z := by
  have key := longest_rel (ψ R n) (fun i => divDiff (R := R) i)
    (fun a A => ∀ f, (a * d f - d (A f)) * Z = 0) (fun f => by simp)
    (fun a b A B ha hb f => by
      calc (a * b * d f - d ((A * B) f)) * Z
          = a * ((b * d f - d (B f)) * Z) + (a * d (B f) - d (A (B f))) * Z := by
            rw [Module.End.mul_apply]; simp only [mul_sub, sub_mul, mul_assoc]; abel
        _ = 0 := by rw [hb f, ha (B f), mul_zero, add_zero])
    (fun i hi f => by
      rw [hd i f hi, add_sub_cancel_right, mul_assoc, hZ i hi, mul_zero]) (m := m) f
  rw [sub_mul, sub_eq_zero] at key
  exact key

/-- `ψ_{w₀} d(f) ψ_{w₀} = d(∂_{w₀} f) ψ_{w₀}` for any `d` satisfying the polynomial slide. -/
theorem ψw₀_mul_mul_ψw₀_of_slide {m : ℕ}
    (hd : ∀ i f, i + 1 < m → ψ R n i * d f = d (swapVars i f) * ψ R n i + d (divDiff i f))
    (f : MvPolynomial ℕ R) :
    ψw₀ R n m * d f * ψw₀ R n m = d (divDiffW₀ R m f) * ψw₀ R n m :=
  ψw₀_mul_mul_of_slide d (fun _ hi => ψ_mul_ψw₀ R hi) hd f

/-- `e_m = d(x^δ) ψ_{w₀}` is an idempotent for any unital `d` satisfying the polynomial slide. -/
theorem idempotent_of_slide {m : ℕ}
    (hd : ∀ i f, i + 1 < m → ψ R n i * d f = d (swapVars i f) * ψ R n i + d (divDiff i f))
    (h1 : d 1 = 1) :
    d (xδ R m) * ψw₀ R n m * (d (xδ R m) * ψw₀ R n m) = d (xδ R m) * ψw₀ R n m := by
  calc d (xδ R m) * ψw₀ R n m * (d (xδ R m) * ψw₀ R n m)
      = d (xδ R m) * (ψw₀ R n m * d (xδ R m) * ψw₀ R n m) := by simp only [mul_assoc]
    _ = d (xδ R m) * ψw₀ R n m := by
      rw [ψw₀_mul_mul_ψw₀_of_slide d hd, divDiffW₀_xδ, h1, one_mul]

end Slide

/-! ## The idempotent `e_m` -/

section Dots

/-- `ψ_{w₀} f ψ_{w₀} = (∂_{w₀} f) ψ_{w₀}` for every polynomial `f` in the dots, where `ψ_{w₀}`
and `∂_{w₀}` are taken along the same reduced word. It holds for all `n` and `m`; it has content
for `m ≤ n` (for `m > n`, `m ≥ 2`, both sides vanish). -/
theorem ψw₀_mul_dots_mul_ψw₀ (n m : ℕ) (f : MvPolynomial ℕ R) :
    ψw₀ R n m * dots R n f * ψw₀ R n m = dots R n (divDiffW₀ R m f) * ψw₀ R n m := by
  by_cases h : m ≤ n ∨ m ≤ 1
  · exact ψw₀_mul_mul_ψw₀_of_slide (dots R n)
      (fun i f hi => ψ_mul_dots R (by omega) f) f
  · rw [ψw₀_of_lt R (by omega) (by omega), mul_zero, mul_zero]

variable (R) in
/-- The element `e_m = x^δ ψ_{w₀} = x_0^{m-1} x_1^{m-2} ⋯ x_{m-2} ψ_{w₀}` of `End (NH.obj R n)`,
the dots acting on the first `m` of the `n` strands. In the paper's `1`-based notation this is
`x_1^{m-1} x_2^{m-2} ⋯ x_{m-1} ∂_{w₀}` (KL I, §2.2 Example 3, p. 11), with the dots above
(applied after) the crossings. -/
def klIdempotent (n m : ℕ) : End (NH.obj R n) := dots R n (xδ R m) * ψw₀ R n m

/-- KL I, §2.2 Example 3, p. 11: `e_m = x_1^{m-1} ⋯ x_{m-1} ∂_{w₀}` is an idempotent. Here in
`End (NH.obj R n)` over any commutative ring `R`, for all `m ≤ n` (the statement is stated, and
true, for all `m`; for `m > n` with `m ≥ 2` the element is `0`). Non-vanishing of `e_m` is not
proved here. -/
theorem klIdempotent_mul_self (n m : ℕ) :
    klIdempotent R n m * klIdempotent R n m = klIdempotent R n m := by
  calc klIdempotent R n m * klIdempotent R n m
      = dots R n (xδ R m) * (ψw₀ R n m * dots R n (xδ R m) * ψw₀ R n m) := by
        simp only [klIdempotent, mul_assoc]
    _ = klIdempotent R n m := by
      rw [ψw₀_mul_dots_mul_ψw₀, divDiffW₀_xδ, map_one, one_mul, klIdempotent]

theorem klIdempotent_isIdempotentElem (n m : ℕ) : IsIdempotentElem (klIdempotent R n m) :=
  klIdempotent_mul_self n m

end Dots

end StringDiagrams.NilHecke

end
