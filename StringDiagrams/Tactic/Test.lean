import StringDiagrams.Tactic.WordRw
import StringDiagrams.Examples.NilHecke.Relations

/-!
# Tests for the word rewriting tactics

Examples for `word_rw`, `word_norm`, `word_comm` and `word_comm_nf`, over an arbitrary ring and
in the nilHecke endomorphism rings `End (NH.obj R n)` at symbolic width.
-/

namespace StringDiagrams.WordRw.Test

section Generic

variable {A : Type*} [Ring A]

/-! ### `word_rw` -/

example (a b c d e : A) (h : b * c = e) : a * b * c * d = a * e * d := by
  word_rw [h]

example (a b c e : A) (h : b * c = e) : a * (b * c) = a * e := by
  word_rw [h]

example (a b c d e : A) (h : e = b * c) : a * b * c * d = a * e * d := by
  word_rw [← h]

example (a b c d : A) (h : b * c = 1) : a * b * c * d = a * d := by
  word_rw [h]

example (a b c d : A) (h : b * c = c * b + 1) : a * b * c * d = a * c * b * d + a * d := by
  word_rw [h]

example (a b : A) (h : a * b = 0) : a * (b + a) * b = a * a * b := by
  word_rw [h]

/-- Quantified rules: the variables are determined by matching. -/
example (f : ℕ → A) (h : ∀ i, f i * f (i + 1) = 0) (a : A) : a * f 3 * f 4 * a = 0 := by
  word_rw [h]

/-- Side conditions are discharged by `omega` using the context. -/
example (f : ℕ → A) (h : ∀ i j, i + 1 < j → f i * f j = f j * f i) (a : A) (k m : ℕ)
    (hkm : k + 1 < m) : a * f k * f m * a = a * f m * f k * a := by
  word_rw [h]

/-- The first match whose side conditions are discharged is used. -/
example (f : ℕ → A) (h : ∀ i j, i + 1 < j → f i * f j = f j * f i) (k : ℕ) :
    f k * f (k + 1) * f (k + 3) = f k * f (k + 3) * f (k + 1) := by
  word_rw [h]

/-- Side conditions that cannot be discharged remain as goals. -/
example (f : ℕ → A) (h : ∀ i j, i + 1 < j → f i * f j = f j * f i) (a : A) (k m : ℕ)
    (hkm : k + 5 < m) : a * f k * f m = a * f m * f k := by
  word_rw (disch := skip) [h]
  omega

example (a b c : A) (h : a * b = c) (x : A) (hx : x = b * a * b * a) : x = b * c * a := by
  word_rw [h] at hx
  word_norm
  exact hx

example (a b c : A) (h : a * b = c) (r : ℤ) : (r • a) * (b * a) = r • (c * a) := by
  word_rw [h]

example (a b c : A) (h : a * b = c) : -(a * (-b)) * a = c * a := by
  word_rw [h]

set_option linter.unusedVariables false in
/-- A rule whose left-hand side does not occur fails. -/
example (a b : A) (h : a * b = 0) : True := by
  fail_if_success
    have : b * a = 0 := by word_rw [h]
  trivial

/-! ### `word_comm` and `word_comm_nf` -/

example (f : ℕ → A) (h : ∀ i j, i + 1 < j → f i * f j = f j * f i) (a : A) (k : ℕ) :
    a * f k * f (k + 2) * a = a * f (k + 2) * f k * a := by
  word_comm [h]

example (f : ℕ → A) (h : ∀ i j, i + 1 < j → f i * f j = f j * f i) (k : ℕ) :
    f k * f (k + 2) * f (k + 4) + f 0 = f 0 + f (k + 4) * f k * f (k + 2) := by
  word_comm [h]

set_option linter.unusedVariables false in
/-- Adjacent indices do not commute. -/
example (f : ℕ → A) (h : ∀ i j, i + 1 < j → f i * f j = f j * f i) (k : ℕ) :
    True := by
  fail_if_success
    have : f k * f (k + 1) = f (k + 1) * f k := by word_comm [h]
  trivial

example (f : ℕ → A) (h : ∀ i j, i + 1 < j → f i * f j = f j * f i) (k : ℕ)
    (H : f (k + 2) * f (k + 3) * f k = 0) :
    f k * f (k + 2) * f (k + 3) = 0 := by
  word_comm_nf [h] at H ⊢
  exact H

/-- Commuting a letter out of the way, then rewriting. -/
example (f : ℕ → A) (h : ∀ i j, i + 1 < j → f i * f j = f j * f i)
    (hsq : ∀ i, f i * f i = 0) (k : ℕ) :
    f k * f (k + 2) * f k = 0 := by
  word_rw [(show f k * f (k + 2) * f k = f (k + 2) * f k * f k by word_comm [h]), hsq]

end Generic

section NilHecke

open CategoryTheory NilHecke

variable (R : Type*) [CommRing R]

/-- `ψ_i x_i ψ_i = ψ_i`. -/
example {n i : ℕ} (h : i + 1 < n) : ψ R n i * x R n i * ψ R n i = ψ R n i := by
  have hs : ψ R n i * x R n i = x R n (i + 1) * ψ R n i + 1 :=
    sub_eq_iff_eq_add'.mp (ψ_mul_x_sub_x_mul_ψ R h)
  word_rw [hs, ψ_mul_ψ]

/-- A braid move followed by a double crossing. -/
example (n i : ℕ) (a : End (NH.obj R n)) :
    a * ψ R n i * ψ R n (i + 1) * ψ R n i * ψ R n (i + 1) = 0 := by
  word_rw [ψ_braid, ψ_mul_ψ]

/-- Far commutativity, with side conditions discharged by `omega`. -/
example {n i : ℕ} :
    x R n (i + 3) * ψ R n i * x R n i * ψ R n (i + 2) =
      ψ R n i * x R n i * x R n (i + 3) * ψ R n (i + 2) := by
  word_comm [x_mul_ψ_comm R, ψ_mul_ψ_comm R, x_mul_x_comm R]

set_option linter.unusedVariables false in
/-- `x_{i+3}` and `ψ_{i+2}` do not commute. -/
example {n i : ℕ} : True := by
  fail_if_success
    have : x R n (i + 3) * ψ R n (i + 2) = ψ R n (i + 2) * x R n (i + 3) := by
      word_comm [x_mul_ψ_comm R, ψ_mul_ψ_comm R, x_mul_x_comm R]
  trivial

/-- Commutation followed by a rewrite: `ψ_i ψ_{i+2} ψ_i = 0`. -/
example (n i : ℕ) : ψ R n i * ψ R n (i + 2) * ψ R n i = 0 := by
  word_rw [(show ψ R n i * ψ R n (i + 2) * ψ R n i = ψ R n (i + 2) * ψ R n i * ψ R n i by
    word_comm [ψ_mul_ψ_comm R]), ψ_mul_ψ]

end NilHecke

end StringDiagrams.WordRw.Test
