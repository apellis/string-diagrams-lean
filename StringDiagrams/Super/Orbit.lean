import StringDiagrams.Super.QPi

/-!
# The orbit supercategory of an auto-equivalence

This file provides the construction behind the associated graded `(Q, Π)`-supercategory of a
`(Q, Π)`-category (J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
§6, proof of Theorem 6.13).

Let `S` be a supercategory with an adjoint auto-equivalence `(Q, Q⁻¹)` by superfunctors with
even unit and counit (`StringDiagrams.ShiftData`). Its powers `Qⁱ`, `i ∈ ℤ`
(`ShiftData.pow`), come with even isomorphisms `Q Qⁱ ≅ Qⁱ⁺¹` (`ShiftData.succ`) and
`Qⁱ Q ≅ Qⁱ⁺¹` (`ShiftData.comm`). The *orbit supercategory* `Orbit d` has the objects of `S`,
and its morphisms `λ → μ` of degree `m` are the families
`(f_{i,j} : Qⁱ λ → Qʲ μ)_{i - j = m}` compatible with `Q`, i.e.
`f_{i+1,j+1} = Q f_{i,j}` up to the isomorphisms `Q Qⁱ ≅ Qⁱ⁺¹` (`ShiftData.Fam`). Such a
family is determined by any one of its entries (as `Q` is faithful), e.g. by
`f_{0,-m} : λ → Q⁻ᵐ μ`; thus the morphisms of degree `m` are `Hom_S(λ, Q⁻ᵐ μ)`, and
composition is `g ∘ f = (g_{j,k} ∘ f_{i,j})`. Using compatible families rather than
`Hom_S(λ, Q⁻ᵐ μ)` itself makes composition strictly associative without the coherence
isomorphisms `Qᵐ Qⁿ ≅ Qᵐ⁺ⁿ`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w v u

variable (R : Type w) [CommRing R]

/-- An adjoint auto-equivalence of a supercategory by superfunctors, with even unit and
counit. -/
structure ShiftData (S : Type u) [Category.{v} S] [Preadditive S] [Linear R S]
    [Supercategory R S] where
  /-- The adjoint equivalence `(Q, Q⁻¹)`. -/
  e : S ≌ S
  [functor_additive : e.functor.Additive]
  [functor_linear : e.functor.Linear R]
  [functor_isSuperfunctor : IsSuperfunctor R e.functor]
  [inverse_additive : e.inverse.Additive]
  [inverse_linear : e.inverse.Linear R]
  [inverse_isSuperfunctor : IsSuperfunctor R e.inverse]
  unit_mem : ∀ X : S, e.unitIso.hom.app X ∈ parity (R := R) X (e.inverse.obj (e.functor.obj X)) 0
  counit_mem : ∀ X : S, e.counitIso.hom.app X ∈ parity (R := R) (e.functor.obj (e.inverse.obj X)) X 0

attribute [instance] ShiftData.functor_additive ShiftData.functor_linear
  ShiftData.functor_isSuperfunctor ShiftData.inverse_additive ShiftData.inverse_linear
  ShiftData.inverse_isSuperfunctor

namespace ShiftData

variable {R} {S : Type u} [Category.{v} S] [Preadditive S] [Linear R S] [Supercategory R S]
  (d : ShiftData R S)

/-- `Q`. -/
abbrev Q : S ⥤ S := d.e.functor

/-- `Q⁻¹`. -/
abbrev Qi : S ⥤ S := d.e.inverse

theorem unit_inv_mem (X : S) :
    d.e.unitIso.inv.app X ∈ parity (R := R) (d.Qi.obj (d.Q.obj X)) X 0 :=
  inv_mem (d.e.unitIso.app X) (d.unit_mem X)

theorem counit_inv_mem (X : S) :
    d.e.counitIso.inv.app X ∈ parity (R := R) X (d.Q.obj (d.Qi.obj X)) 0 :=
  inv_mem (d.e.counitIso.app X) (d.counit_mem X)

/-! ## Powers of `Q` -/

/-- `Qⁿ`, `n ∈ ℕ` (with `Qⁿ⁺¹ = Qⁿ ⋙ Q`, i.e. `Q` applied last). -/
def powNat : ℕ → S ⥤ S
  | 0 => 𝟭 S
  | n + 1 => powNat n ⋙ d.Q

/-- `Q⁻ⁿ`, `n ∈ ℕ` (with `Q⁻ⁿ⁻¹ = Q⁻ⁿ ⋙ Q⁻¹`). -/
def powNeg : ℕ → S ⥤ S
  | 0 => 𝟭 S
  | n + 1 => powNeg n ⋙ d.Qi

/-- `Qⁱ`, `i ∈ ℤ`. -/
def pow : ℤ → S ⥤ S
  | Int.ofNat n => d.powNat n
  | Int.negSucc n => d.powNeg (n + 1)

instance powNat_additive : ∀ n, (d.powNat n).Additive
  | 0 => inferInstanceAs (𝟭 S).Additive
  | n + 1 => by haveI := powNat_additive n; exact inferInstanceAs (d.powNat n ⋙ d.Q).Additive

instance powNat_linear : ∀ n, (d.powNat n).Linear R
  | 0 => inferInstanceAs ((𝟭 S).Linear R)
  | n + 1 => by haveI := powNat_linear n; exact inferInstanceAs ((d.powNat n ⋙ d.Q).Linear R)

instance powNat_isSuperfunctor : ∀ n, IsSuperfunctor R (d.powNat n)
  | 0 => inferInstanceAs (IsSuperfunctor R (𝟭 S))
  | n + 1 => by
    haveI := powNat_isSuperfunctor n; exact inferInstanceAs (IsSuperfunctor R (d.powNat n ⋙ d.Q))

instance powNeg_additive : ∀ n, (d.powNeg n).Additive
  | 0 => inferInstanceAs (𝟭 S).Additive
  | n + 1 => by haveI := powNeg_additive n; exact inferInstanceAs (d.powNeg n ⋙ d.Qi).Additive

instance powNeg_linear : ∀ n, (d.powNeg n).Linear R
  | 0 => inferInstanceAs ((𝟭 S).Linear R)
  | n + 1 => by haveI := powNeg_linear n; exact inferInstanceAs ((d.powNeg n ⋙ d.Qi).Linear R)

instance powNeg_isSuperfunctor : ∀ n, IsSuperfunctor R (d.powNeg n)
  | 0 => inferInstanceAs (IsSuperfunctor R (𝟭 S))
  | n + 1 => by
    haveI := powNeg_isSuperfunctor n
    exact inferInstanceAs (IsSuperfunctor R (d.powNeg n ⋙ d.Qi))

instance pow_additive : ∀ i, (d.pow i).Additive
  | Int.ofNat n => d.powNat_additive n
  | Int.negSucc n => d.powNeg_additive (n + 1)

instance pow_linear : ∀ i, (d.pow i).Linear R
  | Int.ofNat n => d.powNat_linear n
  | Int.negSucc n => d.powNeg_linear (n + 1)

instance pow_isSuperfunctor : ∀ i, IsSuperfunctor R (d.pow i)
  | Int.ofNat n => d.powNat_isSuperfunctor n
  | Int.negSucc n => d.powNeg_isSuperfunctor (n + 1)

@[simp] theorem pow_zero : d.pow 0 = 𝟭 S := rfl

/-! ## The isomorphisms `Q Qⁱ ≅ Qⁱ⁺¹` -/

/-- `Q Qⁱ ≅ Qⁱ⁺¹` (in diagrammatic order `Qⁱ ⋙ Q ≅ Qⁱ⁺¹`): the identity for `i ≥ 0`, the
counit for `i < 0`. -/
def succ : ∀ i : ℤ, d.pow i ⋙ d.Q ≅ d.pow (i + 1)
  | Int.ofNat _ => Iso.refl _
  | Int.negSucc 0 => d.e.counitIso
  | Int.negSucc (n + 1) => Functor.associator _ _ _ ≪≫ isoWhiskerLeft (d.powNeg (n + 1)) d.e.counitIso ≪≫
      Functor.rightUnitor _

theorem succ_hom_mem (i : ℤ) (X : S) :
    (d.succ i).hom.app X ∈ parity (R := R) (d.Q.obj ((d.pow i).obj X)) ((d.pow (i + 1)).obj X) 0 := by
  rcases i with n | (_ | n)
  · exact id_mem _
  · exact d.counit_mem X
  · convert d.counit_mem ((d.powNeg (n + 1)).obj X) using 1
    show 𝟙 _ ≫ _ ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]; rfl

theorem succ_inv_mem (i : ℤ) (X : S) :
    (d.succ i).inv.app X ∈ parity (R := R) ((d.pow (i + 1)).obj X) (d.Q.obj ((d.pow i).obj X)) 0 :=
  inv_mem ((d.succ i).app X) (d.succ_hom_mem i X)

/-! ## The isomorphisms `Qⁱ Q ≅ Qⁱ⁺¹` -/

/-- `Qⁿ Q ≅ Qⁿ⁺¹` for `n ∈ ℕ`. -/
def commNat : ∀ n : ℕ, d.Q ⋙ d.powNat n ≅ d.powNat (n + 1)
  | 0 => Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm
  | n + 1 => (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (commNat n) d.Q

/-- `Q⁻ⁿ⁻¹ Q ≅ Q⁻ⁿ` for `n ∈ ℕ`. -/
def commNeg : ∀ n : ℕ, d.Q ⋙ d.powNeg (n + 1) ≅ d.powNeg n
  | 0 => isoWhiskerLeft d.Q (Functor.leftUnitor _) ≪≫ d.e.unitIso.symm
  | n + 1 => (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (commNeg n) d.Qi

/-- `Qⁱ Q ≅ Qⁱ⁺¹` (in diagrammatic order `Q ⋙ Qⁱ ≅ Qⁱ⁺¹`): built from identities for
`i ≥ 0` and from the unit for `i < 0`. -/
def comm : ∀ i : ℤ, d.Q ⋙ d.pow i ≅ d.pow (i + 1)
  | Int.ofNat n => d.commNat n
  | Int.negSucc 0 => d.commNeg 0
  | Int.negSucc (n + 1) => d.commNeg (n + 1)

theorem commNat_hom_mem (n : ℕ) (X : S) :
    (d.commNat n).hom.app X ∈ parity (R := R) ((d.powNat n).obj (d.Q.obj X)) ((d.powNat (n + 1)).obj X) 0 := by
  induction n with
  | zero => simpa [commNat] using id_mem (R := R) (d.Q.obj X)
  | succ n ih =>
    convert map_mem d.Q ih using 1
    exact Category.id_comp _

theorem commNeg_hom_mem (n : ℕ) (X : S) :
    (d.commNeg n).hom.app X ∈ parity (R := R) ((d.powNeg (n + 1)).obj (d.Q.obj X)) ((d.powNeg n).obj X) 0 := by
  induction n with
  | zero =>
    convert d.unit_inv_mem X using 1
    exact Category.id_comp _
  | succ n ih =>
    convert map_mem d.Qi ih using 1
    exact Category.id_comp _

theorem comm_hom_mem (i : ℤ) (X : S) :
    (d.comm i).hom.app X ∈ parity (R := R) ((d.pow i).obj (d.Q.obj X)) ((d.pow (i + 1)).obj X) 0 := by
  rcases i with n | (_ | n)
  · exact d.commNat_hom_mem n X
  · exact d.commNeg_hom_mem 0 X
  · exact d.commNeg_hom_mem (n + 1) X

theorem comm_inv_mem (i : ℤ) (X : S) :
    (d.comm i).inv.app X ∈ parity (R := R) ((d.pow (i + 1)).obj X) ((d.pow i).obj (d.Q.obj X)) 0 :=
  inv_mem ((d.comm i).app X) (d.comm_hom_mem i X)

theorem succ_negSucc_succ_hom_app (n : ℕ) (X : S) :
    (d.succ (Int.negSucc (n + 1))).hom.app X = d.e.counitIso.hom.app ((d.powNeg (n + 1)).obj X) := by
  show 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]; rfl

theorem succ_negSucc_succ_inv_app (n : ℕ) (X : S) :
    (d.succ (Int.negSucc (n + 1))).inv.app X = d.e.counitIso.inv.app ((d.powNeg (n + 1)).obj X) := by
  rw [← cancel_mono ((d.succ (Int.negSucc (n + 1))).hom.app X), Iso.inv_hom_id_app,
    succ_negSucc_succ_hom_app]
  exact (Iso.inv_hom_id_app d.e.counitIso _).symm

theorem commNeg_succ_hom_app (n : ℕ) (X : S) :
    (d.commNeg (n + 1)).hom.app X = d.Qi.map ((d.commNeg n).hom.app X) := by
  show 𝟙 _ ≫ _ = _
  rw [Category.id_comp]; rfl

/-- The compatibility of `comm` with `succ`: `Qⁱ⁺¹ Q ≅ Qⁱ⁺²` is obtained from `Qⁱ Q ≅ Qⁱ⁺¹` by
applying `Q` and the isomorphisms `succ`. For `i = -1` this is the triangle identity of the
adjoint equivalence. -/
theorem comm_succ (i : ℤ) (X : S) :
    (d.comm (i + 1)).hom.app X =
      (d.succ i).inv.app (d.Q.obj X) ≫ d.Q.map ((d.comm i).hom.app X) ≫ (d.succ (i + 1)).hom.app X := by
  rcases i with n | (_ | n)
  · show (d.commNat (n + 1)).hom.app X = 𝟙 _ ≫ d.Q.map ((d.commNat n).hom.app X) ≫ 𝟙 _
    rw [Category.comp_id]; rfl
  · show 𝟙 _ ≫ 𝟙 _ = (d.e.counitIso.inv.app (d.Q.obj X)) ≫
      d.Q.map (𝟙 _ ≫ d.e.unitIso.inv.app X) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact (d.e.counitInv_functor_comp X).symm
  · rcases n with _ | n
    · show (d.commNeg 0).hom.app X = (d.succ (Int.negSucc 1)).inv.app (d.Q.obj X) ≫
        d.Q.map ((d.commNeg 1).hom.app X) ≫ d.e.counitIso.hom.app X
      rw [succ_negSucc_succ_inv_app, commNeg_succ_hom_app]
      symm
      exact (Iso.inv_comp_eq (d.e.counitIso.app _)).2 (d.e.counitIso.hom.naturality _)
    · show (d.commNeg (n + 1)).hom.app X = (d.succ (Int.negSucc (n + 2))).inv.app (d.Q.obj X) ≫
        d.Q.map ((d.commNeg (n + 2)).hom.app X) ≫ (d.succ (Int.negSucc (n + 1))).hom.app X
      rw [succ_negSucc_succ_inv_app, succ_negSucc_succ_hom_app, commNeg_succ_hom_app d (n + 1)]
      symm
      exact (Iso.inv_comp_eq (d.e.counitIso.app _)).2 (d.e.counitIso.hom.naturality _)

end ShiftData

end StringDiagrams

end
