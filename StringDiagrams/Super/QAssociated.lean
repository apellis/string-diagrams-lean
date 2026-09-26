import StringDiagrams.Super.Orbit
import StringDiagrams.Super.QPiCategory
import StringDiagrams.Super.Associated

/-!
# The graded (Q, Π)-supercategory associated to a (Q, Π)-category

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6, the
construction `𝔻` in the proof of Theorem 6.13.

For a `(Q, Π)`-category `A`, the paper's associated graded `(Q, Π)`-supercategory `Â` has the
objects of `A` and `Hom_Â(λ, μ)_{m,a} := Hom_A(λ, Q^m Π^a μ)`, with composition using
`β_{Qⁿ}`, `ξ` and the coherence isomorphisms `c_{m,n} : QᵐQⁿ ≅ Qᵐ⁺ⁿ`. We build it in two steps:

1. the associated Π-supercategory `Associated R A` of (5.2) (Lemma 5.1), with the sign
   correction of `StringDiagrams.Super.Associated`; `Q` induces a superfunctor `Q̂` of it
   (`Associated.map` of the Π-functor `(Q, β_Q)`), which is full, faithful and evenly dense;
2. the orbit supercategory `Orbit` of `Q̂` (`StringDiagrams.Super.Orbit`), in which a morphism of
   degree `m` is a family `(f_{i,j} : Q̂ⁱ λ → Q̂ʲ μ)_{i-j=m}` compatible with `Q̂`, determined by
   `f_{0,-m} : λ → Q̂⁻ᵐ μ`.

Thus `QAssociated R A := Orbit (QAssociated.shiftData R A)`, a graded `(Q, Π)`-supercategory.

## A convention correction

With the degree conventions of Definition 6.4 (`σ : Q ⇒ I` has degree `-1`, as for the grading
shift `(QV)ₙ = Vₙ₋₁`), the morphisms `λ → μ` of degree `m` must correspond to
`Hom_A(λ, Q⁻ᵐ Π^a μ)`, not to `Hom_A(λ, Q^m Π^a μ)` as printed: the isomorphism
`σ_λ : Qλ → λ` of the associated supercategory comes from `1_{Qλ} ∈ Hom_A(Qλ, Q¹ λ)`, which
must have degree `-1`. (With the printed convention there is no degree `-1` isomorphism
`Qλ → λ` in general.) Our orbit supercategory uses the corrected convention.

## Main definitions and statements

* `QAssociated.shiftData`, `QAssociated R A` (the object part of `𝔻`), a graded
  `(Q, Π)`-supercategory (instances from `StringDiagrams.Super.Orbit`).
* `QAssociated.unit`, `QAssociated.counit`: mutually inverse functors between `A` and the
  underlying category of `QAssociated R A` (`unit_comp_counit`, `counit_comp_unit`), which
  commute strictly with `Π`, `Q` and `ξ`; `QAssociated.unitQPiFunctor` is the resulting
  `(Q, Π)`-functor with `β = 1` and `γ = 1` (`𝔼 ∘ 𝔻 = I` on objects).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe w w₁ w₂ w₃ w₄

namespace QAssociated

variable (R : Type w) [CommRing R] (A : Type w₁) [Category.{w₂} A] [Preadditive A] [Linear R A]
  [QPiCategory R A]

open Associated

/-- The superfunctor `Q̂` of the associated Π-supercategory. -/
abbrev Qhat : Associated R A ⥤ Associated R A :=
  Associated.map (QPiCategory.Q_pi (R := R) (C := A))

instance : (QPiCategory.Q (R := R) (C := A)).Full :=
  inferInstanceAs (QPiCategory.qEquivalence R A).functor.Full

instance : (QPiCategory.Q (R := R) (C := A)).Faithful :=
  inferInstanceAs (QPiCategory.qEquivalence R A).functor.Faithful

instance : (Qhat R A).Faithful where
  map_injective {X Y f g} h := by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Associated.map_map, homMk_fst, homMk_snd] at h1 h2
    exact hom_ext ((QPiCategory.Q (R := R)).map_injective h1)
      ((QPiCategory.Q (R := R)).map_injective ((cancel_mono _).1 h2))

instance : (Qhat R A).Full where
  map_surjective {X Y} f :=
    ⟨homMk ((QPiCategory.Q (R := R)).preimage f.1)
      ((QPiCategory.Q (R := R)).preimage
        (f.2 ≫ (QPiCategory.Q_pi (R := R) (C := A)).β.hom.app Y.obj)), by
      apply hom_ext
      · simp
      · simp⟩

/-- `Q̂` is evenly dense: `jj_λ : Q Q⁻¹ λ ≅ λ` is even. -/
theorem Qhat_evenlyDense : EvenlyDense R (Qhat R A) := fun Y =>
  ⟨⟨(QPiCategory.Qinv (R := R)).obj Y.obj⟩,
    (Underlying.ι R (Associated R A)).mapIso ((Associated.unit R A).mapIso
      ((QPiCategory.jj (R := R) (C := A)).app Y.obj)),
    ((Associated.unit R A).map ((QPiCategory.jj (R := R) (C := A)).hom.app Y.obj)).2⟩

/-- The superequivalence `Q̂`. -/
def Qhat_superequivalence : Superequivalence R (Qhat R A) :=
  Superequivalence.ofFullyFaithful (Qhat R A) (Qhat_evenlyDense R A)

omit [Preadditive A] [Linear R A] [QPiCategory R A] in
theorem equivalence_mk_unit_app {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (G : D ⥤ C)
    (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) (X : C) :
    (CategoryTheory.Equivalence.mk F G η ε).unitIso.hom.app X =
      η.hom.app X ≫ G.map (ε.inv.app (F.obj X)) ≫ G.map (F.map (η.inv.app X)) := by
  simp [CategoryTheory.Equivalence.mk, CategoryTheory.Equivalence.adjointifyη]

/-- The shift data of the associated Π-supercategory: the adjoint equivalence obtained from
the superequivalence `Q̂`. -/
def shiftData : ShiftData R (Associated R A) where
  e := CategoryTheory.Equivalence.mk (Qhat R A) (Qhat_superequivalence R A).inverse
    (Qhat_superequivalence R A).unitIso (Qhat_superequivalence R A).counitIso
  functor_additive := inferInstanceAs (Qhat R A).Additive
  functor_linear := inferInstanceAs ((Qhat R A).Linear R)
  functor_isSuperfunctor := inferInstanceAs (IsSuperfunctor R (Qhat R A))
  inverse_additive := inferInstanceAs (Qhat_superequivalence R A).inverse.Additive
  inverse_linear := inferInstanceAs ((Qhat_superequivalence R A).inverse.Linear R)
  inverse_isSuperfunctor := inferInstanceAs (IsSuperfunctor R (Qhat_superequivalence R A).inverse)
  unit_mem X := by
    rw [equivalence_mk_unit_app]
    have h1 := (Qhat_superequivalence R A).unitIso_mem X
    have h2 := inv_mem _ ((Qhat_superequivalence R A).counitIso_mem ((Qhat R A).obj X))
    have h3 := inv_mem _ ((Qhat_superequivalence R A).unitIso_mem X)
    have := comp_mem h1 (comp_mem (map_mem (Qhat_superequivalence R A).inverse h2)
      (map_mem (Qhat_superequivalence R A).inverse (map_mem (Qhat R A) h3)))
    simpa using this
  counit_mem X := Superequivalence.counitIso_mem (Qhat_superequivalence R A) X

end QAssociated

end StringDiagrams

end
