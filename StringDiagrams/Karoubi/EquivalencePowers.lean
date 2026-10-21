/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Integer powers of an autoequivalence

The integer-shift core used by the orbit construction (Brundan–Ellis,
*Monoidal supercategories*, arXiv:1603.05928v3, §6) and by Laurent
Krull–Schmidt bases (Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, §11).
-/

namespace StringDiagrams.EquivalencePowers
open CategoryTheory
variable {C : Type*} [Category C] (e : C ≌ C)

/-- Positive powers, with the equivalence applied last. -/
def powNat : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => powNat n ⋙ e.functor

/-- Negative powers, with the inverse equivalence applied last. -/
def powNeg : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => powNeg n ⋙ e.inverse

/-- Integer powers of an autoequivalence. -/
def pow : ℤ → C ⥤ C
  | Int.ofNat n => powNat e n
  | Int.negSucc n => powNeg e (n + 1)

@[simp] theorem pow_zero : pow e 0 = 𝟭 C := rfl
@[simp] theorem powNat_zero : powNat e 0 = 𝟭 C := rfl
@[simp] theorem powNat_succ (n : ℕ) : powNat e (n + 1) = powNat e n ⋙ e.functor := rfl
@[simp] theorem powNeg_zero : powNeg e 0 = 𝟭 C := rfl
@[simp] theorem powNeg_succ (n : ℕ) : powNeg e (n + 1) = powNeg e n ⋙ e.inverse := rfl

/-- Composing an integer power with the equivalence increments the exponent. -/
def succ : ∀ i : ℤ, pow e i ⋙ e.functor ≅ pow e (i + 1)
  | Int.ofNat _ => Iso.refl _
  | Int.negSucc 0 => e.counitIso
  | Int.negSucc (n + 1) => Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (powNeg e (n + 1)) e.counitIso ≪≫ Functor.rightUnitor _

variable [Preadditive C] [e.functor.Additive] [e.inverse.Additive]
instance powNat_additive : ∀ n, (powNat e n).Additive
  | 0 => inferInstanceAs (𝟭 C).Additive
  | n + 1 => by have := powNat_additive n; exact inferInstanceAs (powNat e n ⋙ e.functor).Additive
instance powNeg_additive : ∀ n, (powNeg e n).Additive
  | 0 => inferInstanceAs (𝟭 C).Additive
  | n + 1 => by have := powNeg_additive n; exact inferInstanceAs (powNeg e n ⋙ e.inverse).Additive
instance pow_additive : ∀ n, (pow e n).Additive
  | Int.ofNat n => powNat_additive e n
  | Int.negSucc n => powNeg_additive e (n + 1)

end StringDiagrams.EquivalencePowers
