import StringDiagrams.Super.AssociatedTwoLocal
import StringDiagrams.Super.TwoSuperequivalenceWhitehead

/-!
# `𝕋 : D₂(E₂ 𝔄) → 𝔄` is a 2-superequivalence (first formulation)

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Lemma 5.4
and Theorem 5.5.

`Associated2.T_isLocalTwoSuperequivalence` shows that `𝕋_𝔄 : D₂(E₂ 𝔄) → 𝔄` is a
2-superequivalence in the second formulation of Definition 2.2. By the super bicategorical
Whitehead theorem (`TwoSuperfunctor.IsLocalTwoSuperequivalence.isTwoSuperequivalence`) it is a
2-superequivalence in the first formulation: it has a quasi-inverse 2-superfunctor `𝕊` such
that `𝕊 ∘ 𝕋` and `𝕋 ∘ 𝕊` are superequivalent to the identities
(`Associated2.T_isTwoSuperequivalence`). Hence `D₂(E₂ 𝔄)` and `𝔄` are 2-superequivalent
(`Associated2.twoSuperequivalent_associated2_underlying2`), which is Theorem 5.5 on objects.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁

namespace Associated2

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A] [PiTwoSupercategory R A]

/-- **Lemma 5.4 / Theorem 5.5.** `𝕋_𝔄 : D₂(E₂ 𝔄) → 𝔄` is a 2-superequivalence (first
formulation of Definition 2.2). -/
theorem T_isTwoSuperequivalence : (T R A).IsTwoSuperequivalence :=
  T_isLocalTwoSuperequivalence.isTwoSuperequivalence

variable (R A) in
/-- **Theorem 5.5** (on objects). `D₂(E₂ 𝔄)` and `𝔄` are 2-superequivalent. -/
theorem twoSuperequivalent_associated2_underlying2 :
    TwoSuperfunctor.TwoSuperequivalent R (Associated2 R (Underlying2 R A)) A :=
  ⟨T R A, T_isTwoSuperequivalence⟩

end Associated2

end StringDiagrams

end
