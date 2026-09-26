import StringDiagrams.Super.AssociatedTwoT
import StringDiagrams.Super.TwoHom

/-!
# `𝕋 : D₂(E₂ 𝔄) → 𝔄` is a 2-superequivalence

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Lemma 5.4,
Theorem 5.5 and Corollary 5.6.

The 2-superfunctor `𝕋_𝔄 : (E₂ 𝔄)^ → 𝔄` of Lemma 5.4 (`Associated2.T`, an isomorphism of
2-supercategories: the identity on objects and 1-morphisms and bijective on 2-morphisms) is a
2-superequivalence in the second formulation of Definition 2.2
(`Associated2.T_isLocalTwoSuperequivalence`): it is a superequivalence (indeed an isomorphism)
on each morphism supercategory and surjective on objects. This is the first step of the proof
of Corollary 5.6 in the paper (`Π-2-SCat ≅ D₂(E₂(Π-2-SCat))`, then `D₂` of the
Π-2-equivalence `E₁ : E₂(Π-SCat) → Π-Cat` of Theorem 5.3). Corollary 5.6 itself
(`Π-2-SCat` and `Π-2-𝔠𝔞𝔱̂ = D₂(Π-Cat)` are 2-superequivalent) is not formalized: the
Π-2-category `Π-Cat` of Π-categories, Π-functors and Π-natural transformations is not bundled
as a Lean bicategory, so `D₂(Π-Cat)` and the composite `D₂(E₁) ∘ 𝕋⁻¹` are not available.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁

namespace Associated2

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A] [PiTwoSupercategory R A]

instance (a b : Associated2 R (Underlying2 R A)) : ((T R A).mapFunctor a b).Full where
  map_surjective x := ⟨Tinv₂ R A x, T_map₂_Tinv₂ x⟩

instance (a b : Associated2 R (Underlying2 R A)) : ((T R A).mapFunctor a b).Faithful where
  map_injective h := T_map₂_injective h

/-- `𝕋_𝔄` is surjective on 1-morphisms (it is the identity on them). -/
theorem T_mapFunctor_evenlyDense (a b : Associated2 R (Underlying2 R A)) :
    EvenlyDense R ((T R A).mapFunctor a b) := fun g =>
  ⟨(⟨⟨g⟩⟩ : a ⟶ b), Iso.refl _, id_mem _⟩

/-- **Lemma 5.4 / Theorem 5.5.** `𝕋_𝔄 : D₂(E₂ 𝔄) → 𝔄` is a 2-superequivalence (second
formulation of Definition 2.2): a superequivalence on every morphism supercategory and
surjective on objects. -/
theorem T_isLocalTwoSuperequivalence : (T R A).IsLocalTwoSuperequivalence where
  hom a b := ⟨Superequivalence.ofFullyFaithful _ (T_mapFunctor_evenlyDense a b)⟩
  essSurj c := ⟨⟨⟨c⟩⟩, Superequivalent.refl _⟩

variable (R A) in
/-- `D₂(E₂ 𝔄)` and `𝔄` are 2-superequivalent (second formulation of Definition 2.2). -/
theorem localTwoSuperequivalent_associated2_underlying2 :
    TwoSuperfunctor.LocalTwoSuperequivalent R (Associated2 R (Underlying2 R A)) A :=
  ⟨T R A, T_isLocalTwoSuperequivalence⟩

end Associated2

end StringDiagrams

end
