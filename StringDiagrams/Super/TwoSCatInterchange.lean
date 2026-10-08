import StringDiagrams.Super.TwoFunctorPostcomposition

/-!
# 2-natural transformations do not form a 2-category: failure of the interchange law

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 2.2(iii). After defining 2-natural transformations (oplax natural transformations), the
paper asserts that 2-supercategories, 2-superfunctors and 2-natural transformations form a
2-category `2-𝔖ℭ𝔄𝔗`; Theorem 5.5 likewise speaks of the strict 2-categories `Π-2-ℭ𝔄𝔗` and
`Π-2-𝔖ℭ𝔄𝔗`, and Remarks 4.10 and 5.7 of strict 3-(super)categories one level higher.

With the whiskerings of 2-natural transformations by 2-superfunctors (`TwoNatTrans.precompose`,
`TwoNatTrans.postcompose`), this fails: for `(X, x) : ℝ ⇒ 𝕊` and `(Y, y) : ℝ' ⇒ 𝕊'`, a
horizontal composition satisfying the interchange law would have to agree with both composites
`(ℝ'X)·(Y𝕊)` and `(Yℝ)·(𝕊'X)` of whiskerings, but these have different components
`Y_{𝕊λ} ∘ ℝ'X_λ` and `𝕊'X_λ ∘ Y_{ℝλ}` (they are related only by the 2-morphism `y_{X_λ}`, as in
a Gray-category). We give a counterexample in which all 2-superfunctors are identities and the
transformations are strong, even and of degree zero: the strict 2-supercategory `Codisc M` with
one object, the elements of a monoid `M` as 1-morphisms (composition the multiplication of `M`)
and a unique (zero) 2-morphism between any two 1-morphisms. Every element `m` of `M` is the
component of a strong 2-natural transformation `𝕀 ⇒ 𝕀` (`Codisc.trans`), and the two composites
of the whiskerings of `Codisc.trans m` and `Codisc.trans n` have components `m n` and `n m`
(`Codisc.whisker_composites_ne`). For `M = Equiv.Perm (Fin 3)` they differ
(`Codisc.interchange_fails`).

Hence `2-𝔖ℭ𝔄𝔗` (and `Π-2-ℭ𝔄𝔗`, `Π-2-𝔖ℭ𝔄𝔗`) is a sesquicategory — 1-truncation, categories of
2-morphisms and whiskerings — but not a 2-category, also when restricted to strong
transformations, to strict 2-supercategories and strict 2-superfunctors, or to the purely even
case. See the README (errata to §2 and §5).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct

/-- The single object of `Codisc M`. -/
inductive Codisc (M : Type) : Type
  | pt

namespace Codisc

variable {M : Type} [Monoid M]

/-- The 1-morphisms of `Codisc M`: the elements of `M`. -/
structure Hom1 (M : Type) where
  /-- The element of `M`. -/
  val : M

/-- The 2-morphisms: a unique one between any two 1-morphisms (a codiscrete category). -/
instance (M : Type) : Category (Hom1 M) where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

instance (M : Type) (f g : Hom1 M) : Subsingleton (f ⟶ g) := inferInstanceAs (Subsingleton PUnit)

instance (M : Type) : Preadditive (Hom1 M) where
  homGroup _ _ := inferInstanceAs (AddCommGroup PUnit)
  add_comp _ _ _ _ _ _ := Subsingleton.elim _ _
  comp_add _ _ _ _ _ _ := Subsingleton.elim _ _

variable (R : Type) [CommRing R]

instance (M : Type) : Linear R (Hom1 M) where
  homModule _ _ := inferInstanceAs (Module R PUnit)
  smul_comp _ _ _ _ _ _ := Subsingleton.elim _ _
  comp_smul _ _ _ _ _ _ := Subsingleton.elim _ _

instance (M : Type) : Supercategory R (Hom1 M) where
  parity _ _ _ := ⊤
  isInternal X Y := by
    have : Subsingleton (DirectSum (ZMod 2) fun p : ZMod 2 => (⊤ : Submodule R (X ⟶ Y))) :=
      ⟨fun a b => DFinsupp.ext fun i => Subsingleton.elim _ _⟩
    exact ⟨fun a b _ => Subsingleton.elim a b, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  id_mem _ := Submodule.mem_top
  comp_mem _ _ := Submodule.mem_top

/-- The one-object 2-category of a monoid with codiscrete morphism categories. -/
instance : BicategoryStruct.{0, 0} (Codisc M) where
  Hom _ _ := Hom1 M
  id _ := ⟨1⟩
  comp f g := ⟨f.val * g.val⟩
  homCategory _ _ := inferInstance
  whiskerLeft _ _ _ _ := PUnit.unit
  whiskerRight _ _ := PUnit.unit
  associator _ _ _ := ⟨PUnit.unit, PUnit.unit, rfl, rfl⟩
  leftUnitor _ := ⟨PUnit.unit, PUnit.unit, rfl, rfl⟩
  rightUnitor _ := ⟨PUnit.unit, PUnit.unit, rfl, rfl⟩

instance (a b : Codisc M) (f g : a ⟶ b) : Subsingleton (f ⟶ g) :=
  inferInstanceAs (Subsingleton PUnit)

instance (a b : Codisc M) : Preadditive (a ⟶ b) := inferInstanceAs (Preadditive (Hom1 M))

instance (a b : Codisc M) : Linear R (a ⟶ b) := inferInstanceAs (Linear R (Hom1 M))

instance (a b : Codisc M) : Supercategory R (a ⟶ b) := inferInstanceAs (Supercategory R (Hom1 M))

/-- `Codisc M` is a 2-supercategory (all 2-morphisms are zero and even). -/
instance : TwoSupercategory R (Codisc M) where
  whiskerLeft_id := by intros; exact Subsingleton.elim _ _
  whiskerLeft_comp := by intros; exact Subsingleton.elim _ _
  id_whiskerLeft := by intros; exact Subsingleton.elim _ _
  comp_whiskerLeft := by intros; exact Subsingleton.elim _ _
  id_whiskerRight := by intros; exact Subsingleton.elim _ _
  comp_whiskerRight := by intros; exact Subsingleton.elim _ _
  whiskerRight_id := by intros; exact Subsingleton.elim _ _
  whiskerRight_comp := by intros; exact Subsingleton.elim _ _
  whisker_assoc := by intros; exact Subsingleton.elim _ _
  pentagon := by intros; exact Subsingleton.elim _ _
  triangle := by intros; exact Subsingleton.elim _ _
  whiskerLeft_add := by intros; exact Subsingleton.elim _ _
  add_whiskerRight := by intros; exact Subsingleton.elim _ _
  whiskerLeft_smul := by intros; exact Subsingleton.elim _ _
  smul_whiskerRight := by intros; exact Subsingleton.elim _ _
  whiskerLeft_mem := by intros; exact Submodule.mem_top
  whiskerRight_mem := by intros; exact Submodule.mem_top
  super_interchange := by intros; exact Subsingleton.elim _ _
  associator_hom_mem := by intros; exact Submodule.mem_top
  leftUnitor_hom_mem := by intros; exact Submodule.mem_top
  rightUnitor_hom_mem := by intros; exact Submodule.mem_top

variable {R}

/-- An element `m` of `M` as a (strong) 2-natural transformation `𝕀 ⇒ 𝕀` with component `m`. -/
def trans (m : M) :
    TwoNatTrans (TwoSuperfunctor.id R (Codisc M)) (TwoSuperfunctor.id R (Codisc M)) where
  X _ := ⟨m⟩
  x _ := PUnit.unit
  x_mem _ := Submodule.mem_top
  naturality _ := Subsingleton.elim _ _
  x_comp _ _ := Subsingleton.elim _ _
  x_id _ := Subsingleton.elim _ _

@[simp] theorem trans_X (m : M) (a : Codisc M) : ((trans (R := R) m).X a).val = m := rfl

/-- `Codisc.trans m` is strong (all its 2-morphisms are invertible). -/
theorem trans_isStrong (m : M) : (trans (R := R) m).IsStrong := fun _ =>
  ⟨⟨PUnit.unit, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

/-- `Codisc.trans m` is even (all its 2-morphisms are even). -/
theorem trans_x_mem (m : M) {a b : Codisc M} (f : a ⟶ b) :
    (trans (R := R) m).x f ∈ parity (R := R) _ _ 0 := Submodule.mem_top

/-- The two composites of whiskerings of `Codisc.trans m` and `Codisc.trans n` have the
components `m n` and `n m`. -/
theorem whisker_composites_X (m n : M) (a : Codisc M) :
    (((TwoNatTrans.postcompose (TwoSuperfunctor.id R (Codisc M)) (trans (R := R) m)).vcomp
        (TwoNatTrans.precompose (TwoSuperfunctor.id R (Codisc M)) (trans (R := R) n))).X a).val =
        m * n ∧
      (((TwoNatTrans.precompose (TwoSuperfunctor.id R (Codisc M)) (trans (R := R) n)).vcomp
        (TwoNatTrans.postcompose (TwoSuperfunctor.id R (Codisc M)) (trans (R := R) m))).X a).val =
        n * m :=
  ⟨rfl, rfl⟩

/-- **Failure of the interchange law (Definition 2.2(iii), Theorem 5.5).** If `m n ≠ n m`, the two
composites `(ℝ'X)·(Y𝕊)` and `(Yℝ)·(𝕊'X)` of whiskerings of `X = Codisc.trans m` and
`Y = Codisc.trans n` (all 2-superfunctors identities) are different 2-natural transformations,
so no horizontal composition of 2-natural transformations restricting to these whiskerings
satisfies the interchange law. -/
theorem whisker_composites_ne {m n : M} (h : m * n ≠ n * m) :
    (TwoNatTrans.postcompose (TwoSuperfunctor.id R (Codisc M)) (trans (R := R) m)).vcomp
        (TwoNatTrans.precompose (TwoSuperfunctor.id R (Codisc M)) (trans (R := R) n)) ≠
      (TwoNatTrans.precompose (TwoSuperfunctor.id R (Codisc M)) (trans (R := R) n)).vcomp
        (TwoNatTrans.postcompose (TwoSuperfunctor.id R (Codisc M)) (trans (R := R) m)) := by
  intro e
  have h' := congrArg (fun θ => (θ.X Codisc.pt).val) e
  rw [(whisker_composites_X m n Codisc.pt).1, (whisker_composites_X m n Codisc.pt).2] at h'
  exact h h'

variable (R) in
/-- **The 2-natural transformations of Definition 2.2(iii) do not form a 2-category.** In the
2-supercategory `Codisc (Equiv.Perm (Fin 3))` there are strong, even 2-natural transformations
`X, Y : 𝕀 ⇒ 𝕀` whose two composites of whiskerings differ. -/
theorem interchange_fails :
    ∃ X Y : TwoNatTrans (TwoSuperfunctor.id R (Codisc (Equiv.Perm (Fin 3))))
        (TwoSuperfunctor.id R (Codisc (Equiv.Perm (Fin 3)))),
      X.IsStrong ∧ Y.IsStrong ∧
        (TwoNatTrans.postcompose (TwoSuperfunctor.id R _) X).vcomp
            (TwoNatTrans.precompose (TwoSuperfunctor.id R _) Y) ≠
          (TwoNatTrans.precompose (TwoSuperfunctor.id R _) Y).vcomp
            (TwoNatTrans.postcompose (TwoSuperfunctor.id R _) X) :=
  ⟨trans (Equiv.swap 0 1), trans (Equiv.swap 1 2), trans_isStrong _, trans_isStrong _,
    whisker_composites_ne (by decide)⟩

end Codisc

end StringDiagrams

end
