import StringDiagrams.Examples.OddTemperleyLieb.SKar
import StringDiagrams.Super.Semisimple

/-!
# `SKar(STL(δ))` is a semisimple abelian category (Theorem A.3 = Theorem 1.18)

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Theorem 1.18 and
Theorem A.3, first assertion: for `q ∈ k^×` not a root of unity and `δ = -(q - q⁻¹)`,
`SKar(STL(δ))` is a semisimple Abelian category.

The objects `P n a = (f_n)^a_a` (`jwObj`) form a family of orthogonal Schur generators
(`orthogonalSchurGenerators_jwObj`: `End(P n a) = k`, `Hom(P m a, P n b) = 0` for
`(m, a) ≠ (n, b)`, and every object is a finite direct sum of them, from the module `SKar`).
Hence, by `StringDiagrams.Super.Semisimple`:

* `abelian`: `SKar(STL(δ))` is an abelian category;
* `simple_jwObj`: each `P n a` is a simple object;
* `exists_iso_bsum_simple`: every object is isomorphic to a finite biproduct of simple objects;
* `exists_iso_jwObj_of_simple`, `isEmpty_iso_jwObj`: the `P n a` (`n ∈ ℕ`, `a ∈ ℤ/2`) form a
  complete set of pairwise non-isomorphic simple objects.

Together with `KZeroRing`/`KZeroIso` (the based ring `K₀`), this completes Theorem A.3.
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory Limits Idempotents
open Rep (delta)

variable {k : Type*} [Field k] (q : kˣ)

local notation "δq" => delta q

variable (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq

/-- The objects `P n a = (f_n)^a_a`, indexed by `(n, a) ∈ ℕ × ℤ/2`. -/
def jwFamily : ℕ × ZMod 2 → SKar k (STL k δq) := fun x => jwObj q hq x.1 x.2

@[simp] theorem jwFamily_apply (n : ℕ) (a : ZMod 2) : jwFamily q hq (n, a) = jwObj q hq n a := rfl

/-- **The `P n a` are orthogonal Schur generators of `SKar(STL(δ))`.** -/
theorem orthogonalSchurGenerators_jwObj : OrthogonalSchurGenerators k (jwFamily q hq) where
  schur x := jwObj_isSchur q hq x.1 x.2
  id_ne_zero x := id_jwObj_ne_zero q hq x.1 x.2
  hom_eq_zero {x y} hxy f :=
    hom_jwObj_eq_zero q hq (by
      by_contra h
      push_neg at h
      exact hxy (Prod.ext h.1 h.2)) f
  exists_iso_bsum Z := by
    obtain ⟨L, hL, e⟩ := exists_iso_bsum_jwObj q hq Z
    exact ⟨L, fun P hP => by
      obtain ⟨n, a, rfl⟩ := hL P hP
      exact ⟨(n, a), rfl⟩, e⟩

/-- **Brundan–Ellis, Theorem 1.18 = Theorem A.3.** `SKar(STL(δ))` is an abelian category. -/
def abelian : Abelian (SKar k (STL k δq)) := (orthogonalSchurGenerators_jwObj q hq).abelian

/-- **Theorem A.3.** The objects `P n a = (f_n)^a_a` are simple. -/
theorem simple_jwObj (n : ℕ) (a : ZMod 2) : Simple (jwObj q hq n a) :=
  (orthogonalSchurGenerators_jwObj q hq).simple (n, a)

/-- **Theorem A.3 (semisimplicity).** Every object of `SKar(STL(δ))` is isomorphic to a finite
biproduct of simple objects. -/
theorem exists_iso_bsum_simple (Z : SKar k (STL k δq)) :
    ∃ L : List (SKar k (STL k δq)), (∀ P ∈ L, Simple P) ∧ Nonempty (Z ≅ bsum L) :=
  (orthogonalSchurGenerators_jwObj q hq).exists_iso_bsum_simple Z

/-- **Theorem A.3.** Every simple object of `SKar(STL(δ))` is isomorphic to some `P n a`. -/
theorem exists_iso_jwObj_of_simple (Z : SKar k (STL k δq)) [Simple Z] :
    ∃ n a, Nonempty (Z ≅ jwObj q hq n a) := by
  obtain ⟨⟨n, a⟩, e⟩ := (orthogonalSchurGenerators_jwObj q hq).exists_iso_of_simple Z
  exact ⟨n, a, e⟩

/-- **Theorem A.3.** The `P n a` are pairwise non-isomorphic. -/
theorem isEmpty_iso_jwObj {m n : ℕ} {a b : ZMod 2} (h : m ≠ n ∨ a ≠ b) :
    IsEmpty (jwObj q hq m a ≅ jwObj q hq n b) :=
  (orthogonalSchurGenerators_jwObj q hq).isEmpty_iso_of_ne (i := (m, a)) (j := (n, b))
    (fun e => by
      rcases h with h | h
      · exact h (congrArg Prod.fst e)
      · exact h (congrArg Prod.snd e))

end StringDiagrams.OddTemperleyLieb

end
