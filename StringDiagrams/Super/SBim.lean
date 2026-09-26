import StringDiagrams.Super.BalancedTensor
import StringDiagrams.Super.PiTwo

/-!
# The 2-supercategory `𝔖𝔅𝔦𝔪` of superbimodules

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Section 2 (after Definition 2.2) and Section 3 (before Lemma 3.2).

`SuperAlg k` is the type of superalgebras over the commutative ground ring `k` (a `k`-algebra
with a `ℤ/2`-grading making it a graded algebra). It is a 2-supercategory `𝔖𝔅𝔦𝔪`:

* the morphism supercategory `Hom(A, B)` is `B-SMod-A`, the supercategory of
  `(B, A)`-superbimodules (`SuperBimodule B.grading A.grading`, Example 1.2(iii));
* horizontal composition is the balanced tensor product: for `M : A → B` and `N : B → C`
  (a `(B, A)`- and a `(C, B)`-superbimodule), `M ≫ N := N ⊗_B M`
  (`StringDiagrams.Super.BalancedTensor`); the identity 1-morphism of `A` is the regular
  superbimodule `A`;
* the coherence maps are the associators and unitors of the balanced tensor product; they are
  not identities, so `𝔖𝔅𝔦𝔪` is a basic example of a 2-supercategory which is not strict
  (`SuperAlg.instTwoSupercategory`).

`𝔖𝔅𝔦𝔪` is a Π-2-supercategory with `π_A := Π A` (the parity-switching functor applied to the
regular superbimodule) and `ζ_A : π_A ⇒ 1_A` the identity function
(`SuperAlg.instPiTwoSupercategory`, Section 3).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe u

variable (k : Type u) [CommRing k]

/-- A superalgebra over `k` (Brundan–Ellis, Example 1.2(ii)), bundled: a `k`-algebra with a
`ℤ/2`-grading making it a graded algebra. These are the objects of `𝔖𝔅𝔦𝔪`. -/
structure SuperAlg where
  /-- The underlying algebra. -/
  carrier : Type u
  [ring : Ring carrier]
  [algebra : Algebra k carrier]
  /-- The `ℤ/2`-grading. -/
  grading : ZMod 2 → Submodule k carrier
  [gradedAlgebra : GradedAlgebra grading]

namespace SuperAlg

attribute [instance] ring algebra gradedAlgebra

variable {k}

instance : CoeSort (SuperAlg k) (Type u) := ⟨SuperAlg.carrier⟩

open BicategoryStruct SuperBimodule

/-- The horizontal composition data of `𝔖𝔅𝔦𝔪`: `Hom(A, B) := B-SMod-A`, composition the
balanced tensor product (`M ≫ N := N ⊗_B M`), identities the regular superbimodules, and the
associators and unitors of the balanced tensor product. -/
instance instBicategoryStruct : BicategoryStruct.{u, u + 1} (SuperAlg k) where
  Hom A B := SuperBimodule B.grading A.grading
  id A := regular A.grading
  comp M N := tensor N M
  homCategory _ _ := inferInstance
  whiskerLeft M _ _ η := SuperBimodule.whiskerRight η M
  whiskerRight η N := SuperBimodule.whiskerLeft N η
  associator M N P := (assoc P N M).symm
  leftUnitor M := SuperBimodule.rightUnitor M
  rightUnitor M := SuperBimodule.leftUnitor M

instance (A B : SuperAlg k) : Preadditive (A ⟶ B) :=
  inferInstanceAs (Preadditive (SuperBimodule B.grading A.grading))

instance (A B : SuperAlg k) : Linear k (A ⟶ B) :=
  inferInstanceAs (Linear k (SuperBimodule B.grading A.grading))

instance (A B : SuperAlg k) : Supercategory k (A ⟶ B) :=
  inferInstanceAs (Supercategory k (SuperBimodule B.grading A.grading))

theorem hom_def (A B : SuperAlg k) : (A ⟶ B) = SuperBimodule B.grading A.grading := rfl

theorem id_def (A : SuperAlg k) : 𝟙 A = regular A.grading := rfl

theorem comp_def {A B C : SuperAlg k} (M : A ⟶ B) (N : B ⟶ C) : M ≫ N = tensor N M := rfl

theorem whiskerLeft_def {A B C : SuperAlg k} (M : A ⟶ B) {N N' : B ⟶ C} (η : N ⟶ N') :
    M ◁ η = SuperBimodule.whiskerRight η M := rfl

theorem whiskerRight_def {A B C : SuperAlg k} {M M' : A ⟶ B} (η : M ⟶ M') (N : B ⟶ C) :
    η ▷ N = SuperBimodule.whiskerLeft N η := rfl

theorem associator_def {A B C D : SuperAlg k} (M : A ⟶ B) (N : B ⟶ C) (P : C ⟶ D) :
    associator M N P = (assoc P N M).symm := rfl

theorem leftUnitor_def {A B : SuperAlg k} (M : A ⟶ B) :
    BicategoryStruct.leftUnitor M = SuperBimodule.rightUnitor M := rfl

theorem rightUnitor_def {A B : SuperAlg k} (M : A ⟶ B) :
    BicategoryStruct.rightUnitor M = SuperBimodule.leftUnitor M := rfl

/-- **Brundan–Ellis, Section 2 (after Definition 2.2).** Superalgebras, superbimodules and
superbimodule homomorphisms form a 2-supercategory `𝔖𝔅𝔦𝔪`, with horizontal composition the
balanced tensor product. Its coherence maps are not identities. -/
instance instTwoSupercategory : TwoSupercategory k (SuperAlg k) where
  whiskerLeft_id M N := id_whiskerRight N M
  whiskerLeft_comp M _ _ _ η θ := comp_whiskerRight η M θ
  id_whiskerLeft {A B M M'} η := by
    change SuperBimodule.whiskerRight η (regular A.grading) =
      (SuperBimodule.rightUnitor M).hom ≫ η ≫ (SuperBimodule.rightUnitor M').inv
    rw [← Category.assoc, Iso.eq_comp_inv, rightUnitor_naturality]
  comp_whiskerLeft {A B C D} M N {P P'} η := by
    change SuperBimodule.whiskerRight η (tensor N M) =
      (assoc P N M).inv ≫ SuperBimodule.whiskerRight (SuperBimodule.whiskerRight η N) M ≫
        (assoc P' N M).hom
    rw [assoc_naturality_left, Iso.inv_hom_id_assoc]
  id_whiskerRight M N := whiskerLeft_id N M
  comp_whiskerRight η θ N := whiskerLeft_comp N η θ
  whiskerRight_id {A B M M'} η := by
    change SuperBimodule.whiskerLeft (regular B.grading) η =
      (SuperBimodule.leftUnitor M).hom ≫ η ≫ (SuperBimodule.leftUnitor M').inv
    rw [← Category.assoc, Iso.eq_comp_inv, leftUnitor_naturality]
  whiskerRight_comp {A B C D M M'} η N P := by
    change SuperBimodule.whiskerLeft (tensor P N) η =
      (assoc P N M).hom ≫ SuperBimodule.whiskerLeft P (SuperBimodule.whiskerLeft N η) ≫
        (assoc P N M').inv
    rw [← Category.assoc, Iso.eq_comp_inv, assoc_naturality_right]
  whisker_assoc {A B C D} M {N N'} η P := by
    change SuperBimodule.whiskerLeft P (SuperBimodule.whiskerRight η M) =
      (assoc P N M).inv ≫ SuperBimodule.whiskerRight (SuperBimodule.whiskerLeft P η) M ≫
        (assoc P N' M).hom
    rw [assoc_naturality_middle, Iso.inv_hom_id_assoc]
  pentagon M N P Q := by
    change SuperBimodule.whiskerLeft Q (assoc P N M).inv ≫ (assoc Q (tensor P N) M).inv ≫
        SuperBimodule.whiskerRight (assoc Q P N).inv M =
      (assoc Q P (tensor N M)).inv ≫ (assoc (tensor Q P) N M).inv
    exact pentagon_inv Q P N M
  triangle M N := by
    change (assoc N (regular _) M).inv ≫ SuperBimodule.whiskerRight (SuperBimodule.rightUnitor N).hom M =
      SuperBimodule.whiskerLeft N (SuperBimodule.leftUnitor M).hom
    rw [Iso.inv_comp_eq, SuperBimodule.triangle]
  whiskerLeft_add M _ _ η θ := add_whiskerRight η M θ
  add_whiskerRight η θ N := whiskerLeft_add N η θ
  whiskerLeft_smul M _ _ r η := smul_whiskerRight η M r
  smul_whiskerRight r η N := whiskerLeft_smul N η r
  whiskerLeft_mem M _ _ _ _ hη := whiskerRight_mem _ hη M
  whiskerRight_mem N hη := whiskerLeft_mem N _ hη
  super_interchange {A B C M M' N N' p q η θ} hη hθ := by
    change SuperBimodule.whiskerLeft N η ≫ SuperBimodule.whiskerRight θ M' =
      koszulSign p q • (SuperBimodule.whiskerRight θ M ≫ SuperBimodule.whiskerLeft N' η)
    rw [SuperBimodule.super_interchange _ _ hθ hη, koszulSign_comm, koszulSign_smul_smul]
  associator_hom_mem M N P := assoc_inv_mem P N M
  leftUnitor_hom_mem M := rightUnitor_hom_mem M
  rightUnitor_hom_mem M := leftUnitor_hom_mem M

/-- **Brundan–Ellis, Section 3.** `𝔖𝔅𝔦𝔪` is a Π-2-supercategory (not strict), with
`π_A := Π A` the parity-switching functor applied to the regular superbimodule and
`ζ_A : Π A ⇒ A` the identity function. -/
instance instPiTwoSupercategory : PiTwoSupercategory k (SuperAlg k) where
  pi A := piObj (regular A.grading)
  ζ A := ζIso (regular A.grading)
  ζ_hom_mem A := ζIso_hom_mem (regular A.grading)

theorem pi_def (A : SuperAlg k) :
    PiTwoSupercategory.pi (R := k) A = piObj (regular A.grading) := rfl

theorem ζ_def (A : SuperAlg k) :
    PiTwoSupercategory.ζ (R := k) A = ζIso (regular A.grading) := rfl

end SuperAlg

end StringDiagrams

end
