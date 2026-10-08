import StringDiagrams.Super.TwoStrictification
import StringDiagrams.Super.TwoSuperequivalenceWhitehead

/-!
# The coherence theorem for 2-supercategories, first formulation

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, after
Definition 2.2: every 2-supercategory is 2-superequivalent to a strict 2-supercategory, in the
first formulation of 2-superequivalence of Definition 2.2 (2-superfunctors in both directions
whose composites are superequivalent to the identities in `𝔥𝔬𝔪`). This combines the
strictification `TwoStrictification` (second formulation,
`TwoSupercategory.exists_strict_localTwoSuperequivalent`) with the Whitehead theorem
`TwoSuperfunctor.LocalTwoSuperequivalent.twoSuperequivalent`.
-/

namespace StringDiagrams

open CategoryTheory

universe w₁ w v u₁

namespace TwoSupercategory

variable (R : Type w₁) [CommRing R] (B : Type u₁) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- **Brundan–Ellis, the coherence theorem for 2-supercategories (after Definition 2.2).** Every
2-supercategory is 2-superequivalent to a strict 2-supercategory (first formulation of
Definition 2.2). -/
theorem exists_strict_twoSuperequivalent :
    ∃ (C : Type u₁) (_ : BicategoryStruct.{max u₁ v w, max u₁ v w} C)
      (_ : ∀ a b : C, Preadditive (a ⟶ b)) (_ : ∀ a b : C, Linear R (a ⟶ b))
      (_ : ∀ a b : C, Supercategory R (a ⟶ b)) (_ : TwoSupercategory R C),
      BicategoryStruct.Strict C ∧ TwoSuperfunctor.TwoSuperequivalent R B C := by
  obtain ⟨C, i₁, i₂, i₃, i₄, i₅, hs, h⟩ := exists_strict_localTwoSuperequivalent R B
  exact ⟨C, i₁, i₂, i₃, i₄, i₅, hs, h.twoSuperequivalent⟩

end TwoSupercategory

end StringDiagrams
