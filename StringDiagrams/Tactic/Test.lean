import StringDiagrams.Tactic.WordRw
import StringDiagrams.Examples.TemperleyLieb.FarCommutativity
import StringDiagrams.Examples.FreeDots
import StringDiagrams.Examples.Exterior

/-!
# Tests for the word rewriting tactics

Examples for `word_rw`, `word_norm`, `word_comm` and `word_comm_nf`, over an arbitrary ring and
in endomorphism rings of example categories at symbolic width and position: the
Temperley–Lieb generators `e δ m i`, free commuting dots `FreeDots.x R n i`, and anticommuting
odd dots `Exterior.x R n i`.
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

section TemperleyLieb

open CategoryTheory TemperleyLieb

variable {R : Type*} [CommRing R] (δ : R)

/-- `e_i e_{i+1} e_i e_i = δ e_i`; the side condition `i + 1 ≤ m` is discharged by `omega`. -/
example {m i : ℕ} (h : i + 2 ≤ m) :
    e δ m i * e δ m (i + 1) * e δ m i * e δ m i = δ • e δ m i := by
  word_rw [e_mul_e_succ_mul_e δ, e_mul_self]

/-- A rewrite in the middle of a word, inside a linear combination. -/
example {m i : ℕ} (h : i + 1 ≤ m) (a b : End ((pres R δ).obj (strands (m + 2)))) :
    a * e δ m (i + 1) * e δ m i * e δ m (i + 1) * b + a =
      a * e δ m (i + 1) * b + a := by
  word_rw [e_succ_mul_e_mul_e_succ δ]

/-- Far commutativity, with the side conditions `i + 2 ≤ j` discharged by `omega`. -/
example {m i : ℕ} :
    e δ m i * e δ m (i + 3) * e δ m (i + 1) * e δ m (i + 5) =
      e δ m (i + 3) * e δ m (i + 5) * e δ m i * e δ m (i + 1) := by
  word_comm [e_mul_e_comm δ]

/-- Far commutativity at symbolic distance, using a hypothesis from the context. -/
example {m i j : ℕ} (hij : i + 2 ≤ j) :
    e δ m j * e δ m i + e δ m i = e δ m i + e δ m i * e δ m j := by
  word_comm [e_mul_e_comm δ]

set_option linter.unusedVariables false in
/-- Neighbouring generators do not commute. -/
example {m i : ℕ} : True := by
  fail_if_success
    have : e δ m i * e δ m (i + 1) = e δ m (i + 1) * e δ m i := by
      word_comm [e_mul_e_comm δ]
  trivial

/-- Commutation followed by a rewrite: `e_i e_{i+2} e_i = δ e_{i+2} e_i`. -/
example (m i : ℕ) :
    e δ m i * e δ m (i + 2) * e δ m i = δ • (e δ m (i + 2) * e δ m i) := by
  word_rw [(show e δ m i * e δ m (i + 2) * e δ m i = e δ m (i + 2) * e δ m i * e δ m i by
    word_comm [e_mul_e_comm δ]), e_mul_self]

/-- Rewriting a hypothesis. -/
example {m i : ℕ} (h : i + 1 ≤ m) (a : End ((pres R δ).obj (strands (m + 2))))
    (ha : a = e δ m i * e δ m (i + 1) * e δ m i * e δ m (i + 1)) :
    a = e δ m i * e δ m (i + 1) := by
  word_rw [e_mul_e_succ_mul_e δ] at ha
  exact ha

end TemperleyLieb

section FreeDots

open CategoryTheory FreeDots

variable (R : Type*) [CommRing R]

/-- Commuting dots are sorted, with the side conditions `i ≠ j` discharged by `omega`. -/
example (n k : ℕ) :
    x R n k * x R n (k + 2) * x R n (k + 1) = x R n (k + 1) * x R n (k + 2) * x R n k := by
  word_comm [x_mul_x_comm R]

/-- Symbolic positions, using a hypothesis from the context. -/
example {n k l : ℕ} (hkl : k < l) (a : End (FD.obj R n)) :
    x R n k * x R n l * x R n k * a = x R n k * x R n k * x R n l * a := by
  word_comm [x_mul_x_comm R]

set_option linter.unusedVariables false in
/-- Without a hypothesis, dots at unrelated symbolic positions do not commute. -/
example {n k l : ℕ} : True := by
  fail_if_success
    have : x R n k * x R n l = x R n l * x R n k := by word_comm [x_mul_x_comm R]
  trivial

example {n k : ℕ} (H : x R n (k + 1) * x R n k * x R n (k + 1) = 0) :
    x R n k * x R n (k + 1) * x R n (k + 1) = 0 := by
  word_comm_nf [x_mul_x_comm R] at H ⊢
  exact H

end FreeDots

section Exterior

open CategoryTheory Exterior

variable (R : Type*) [CommRing R]

/-- Anticommutation (side condition `k < k + 1` by `omega`) followed by `x² = 0`. -/
example (n k : ℕ) : x R n k * x R n (k + 1) * x R n k = 0 := by
  word_rw [x_mul_x_anticomm R, x_mul_x_self]

/-- A signed rewrite inside a linear combination. -/
example (n k : ℕ) (a : End ((pres R).obj (strands n))) :
    a * x R n k * x R n (k + 3) + a = 2 • a - a * x R n (k + 3) * x R n k - a := by
  word_rw [x_mul_x_anticomm R]
  abel

end Exterior

end StringDiagrams.WordRw.Test
