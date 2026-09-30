import StringDiagrams.Super.TwoFunctorComp
import StringDiagrams.Super.TwoFunctorStrict
import StringDiagrams.Super.Supernatural

/-!
# The 2-supercategory `𝔥𝔬𝔪(𝔄, 𝔅)` and 2-superequivalences

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 2.2(iv) and the end of Definition 2.2.

For 2-supercategories `𝔄` and `𝔅`, the 2-superfunctors `𝔄 → 𝔅`, the 2-natural transformations
and the supermodifications form a 2-supercategory `𝔥𝔬𝔪(𝔄, 𝔅)`: here this is the instance
`TwoSupercategory R (TwoSuperfunctor R B C)`, whose morphism supercategories are the
supercategories `ℋom(ℝ, 𝕊)` of `StringDiagrams.Super.TwoFunctor`, whose horizontal composition
of 1-morphisms is the vertical composite `TwoNatTrans.vcomp` of 2-natural transformations
(`(Y, y) ∘ (X, x)` has components `X_λ ≫ Y_λ`, the paper's `Y_λ X_λ`), whose whiskerings of
supermodifications are `X_λ ◁ α_λ` and `α_λ ▷ Y_λ`, and whose coherence maps are the
associators and unitors of `𝔅` componentwise. Since `(X, x) ↦ (X, x)` identifies 2-natural
transformations with the oplax transformations of the underlying bicategories that are natural
with respect to odd 2-morphisms (`TwoNatTrans.toOplaxTrans`, `TwoNatTrans.ofOplaxTrans`), the
coherence maps and their supermodification conditions are taken from Mathlib's bicategory of
oplax functors, exactly as for the Drinfeld center (`StringDiagrams.Super.DrinfeldCenter`, which
is the endomorphism monoidal supercategory of `𝕀` in `𝔥𝔬𝔪(𝔄, 𝔄)` restricted to strong
2-natural transformations).

As the paper notes at the end of Definition 2.2, `𝔥𝔬𝔪(𝔄, 𝔅)` is strict if `𝔅` is strict
(`TwoSuperfunctor.instStrict`, for arbitrary 2-superfunctors `𝔄 → 𝔅`): the components of
`((X, x)(Y, y))(Z, z)` and `(X, x)((Y, y)(Z, z))` agree by the strictness of `𝔅`, and so do their
2-morphisms `x`, which differ only by associators and unitors of `𝔅`.

## 2-superequivalences

Two objects `λ, μ` of a 2-supercategory are *superequivalent* if there is a 1-morphism
`λ → μ` which is a superequivalence (`TwoSupercategory.Superequivalent`, a symmetric relation).
Definition 2.2 gives two formulations of a 2-superequivalence `ℝ : 𝔄 → 𝔅`:

* `TwoSuperfunctor.IsTwoSuperequivalence`: there is a 2-superfunctor `𝕊 : 𝔅 → 𝔄` such that
  `𝕊 ∘ ℝ` and `ℝ ∘ 𝕊` are superequivalent to the identities in `𝔥𝔬𝔪(𝔄, 𝔄)` and `𝔥𝔬𝔪(𝔅, 𝔅)`;
* `TwoSuperfunctor.IsLocalTwoSuperequivalence`: `ℝ` induces superequivalences
  `ℋom_𝔄(λ, μ) → ℋom_𝔅(ℝλ, ℝμ)` on all morphism supercategories, and every object of `𝔅` is
  superequivalent to an object of the form `ℝλ`.

The paper states that the two formulations are equivalent; here the implication from the first
to the second is proved (`TwoSuperfunctor.IsTwoSuperequivalence.isLocalTwoSuperequivalence`,
`TwoSuperfunctor.TwoSuperequivalent.localTwoSuperequivalent`). Along the way: whiskering by a
superequivalence 1-morphism is bijective on 2-morphisms
(`TwoSupercategory.IsSuperequivalence.whiskerLeft_injective` etc.), and a superequivalence
`(X, x)` in `𝔥𝔬𝔪(𝔄, 𝔅)` is strong, i.e. all `x_F` are invertible
(`TwoSuperfunctor.IsSuperequivalence.isIso_x`). If `(X, x) : 𝕊ℝ ⇒ 𝕀` is a superequivalence,
then `η X_λ = x_G ∘ X_μ (𝕊ℝη) ∘ x_F⁻¹` shows that `ℝ` is faithful on 2-morphisms; with the
same for `ℝ𝕊` this gives fullness, and `K ≅ ℝ(X_μ (𝕊K) X'_λ)` gives even density.
`TwoSuperequivalent R B C` (resp. `LocalTwoSuperequivalent R B C`) is the existence of a
2-superequivalence in the first (resp. second) sense.

## Not formalized

The converse implication (a 2-superfunctor which is a local superequivalence and essentially
surjective up to superequivalence has a quasi-inverse 2-superfunctor), which needs the choice of
a quasi-inverse on objects and 1-morphisms together with its coherence data; and the
3-supercategory of 2-supercategories.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory
open scoped Oplax.OplaxTrans Oplax.OplaxTrans.OplaxFunctor

universe w₁ v₁ u₁ w₂ v₂ u₂ w

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

namespace TwoNatTrans

variable {F G H I : TwoSuperfunctor R B C}

omit [TwoSupercategory R B] in
/-- The components of an `eqToHom` between 2-natural transformations are `eqToHom`s. -/
theorem eqToHom_app {θ θ' : TwoNatTrans F G} (h : θ = θ') (a : B) :
    (eqToHom h).app a = eqToHom (congrArg (fun ψ => TwoNatTrans.X ψ a) h) := by
  subst h; rfl

theorem toOplaxTrans_vcomp (θ : TwoNatTrans F G) (ψ : TwoNatTrans G H) :
    toOplaxTrans (vcomp θ ψ) = toOplaxTrans θ ≫ toOplaxTrans ψ := rfl

theorem toOplaxTrans_id : toOplaxTrans (id F) = 𝟙 F.toOplax := rfl

/-- A modification of the associated oplax transformations (whose components are even) as a
supermodification. -/
@[simps]
def homOfOplaxModification {θ θ' : TwoNatTrans F G}
    (Γ : Oplax.OplaxTrans.Modification θ.toOplaxTrans θ'.toOplaxTrans) : θ ⟶ θ' where
  app a := (Γ.app ⟨a⟩).1
  naturality f := (congrArg Subtype.val (Γ.naturality (Underlying2.hom1 f))).symm

/-- An isomorphism of the associated oplax transformations as an (even) isomorphism of
2-natural transformations. -/
@[simps]
def isoOfOplaxModificationIso {θ θ' : TwoNatTrans F G} (e : θ.toOplaxTrans ≅ θ'.toOplaxTrans) :
    θ ≅ θ' where
  hom := homOfOplaxModification e.hom.as
  inv := homOfOplaxModification e.inv.as
  hom_inv_id := hom_ext fun a =>
    congrArg (fun Γ => Subtype.val
      (Oplax.OplaxTrans.Modification.app (Oplax.OplaxTrans.Hom.as Γ) ⟨a⟩)) e.hom_inv_id
  inv_hom_id := hom_ext fun a =>
    congrArg (fun Γ => Subtype.val
      (Oplax.OplaxTrans.Modification.app (Oplax.OplaxTrans.Hom.as Γ) ⟨a⟩)) e.inv_hom_id

/-! ### Whiskerings of supermodifications -/

/-- `(X, x) ◁ α`: the component at `λ` is `X_λ ◁ α_λ`. -/
def whiskerLeft (θ : TwoNatTrans F G) {ψ ψ' : TwoNatTrans G H} (α : ψ ⟶ ψ') :
    vcomp θ ψ ⟶ vcomp θ ψ' where
  app a := θ.X a ◁ α.app a
  naturality {a b} f := by
    change ((associator (F.map f) (θ.X b) (ψ.X b)).inv ≫ θ.x f ▷ ψ.X b ≫
        (associator (θ.X a) (G.map f) (ψ.X b)).hom ≫ θ.X a ◁ ψ.x f ≫
          (associator (θ.X a) (ψ.X a) (H.map f)).inv) ≫ (θ.X a ◁ α.app a) ▷ H.map f =
      F.map f ◁ (θ.X b ◁ α.app b) ≫ (associator (F.map f) (θ.X b) (ψ'.X b)).inv ≫
        θ.x f ▷ ψ'.X b ≫ (associator (θ.X a) (G.map f) (ψ'.X b)).hom ≫ θ.X a ◁ ψ'.x f ≫
          (associator (θ.X a) (ψ'.X a) (H.map f)).inv
    have hα := α.naturality f
    simp only [Category.assoc]
    rw [← associator_inv_naturality_middle R, ← whiskerLeft_comp'_assoc R, hα,
      whiskerLeft_comp'_assoc R, ← associator_naturality_right_assoc R,
      whisker_exchange_of_even_left_assoc (θ.x_mem f),
      ← associator_inv_naturality_right_assoc R]

/-- `α ▷ (Y, y)`: the component at `λ` is `α_λ ▷ Y_λ`. -/
def whiskerRight {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') (ψ : TwoNatTrans G H) :
    vcomp θ ψ ⟶ vcomp θ' ψ where
  app a := α.app a ▷ ψ.X a
  naturality {a b} f := by
    change ((associator (F.map f) (θ.X b) (ψ.X b)).inv ≫ θ.x f ▷ ψ.X b ≫
        (associator (θ.X a) (G.map f) (ψ.X b)).hom ≫ θ.X a ◁ ψ.x f ≫
          (associator (θ.X a) (ψ.X a) (H.map f)).inv) ≫ (α.app a ▷ ψ.X a) ▷ H.map f =
      F.map f ◁ (α.app b ▷ ψ.X b) ≫ (associator (F.map f) (θ'.X b) (ψ.X b)).inv ≫
        θ'.x f ▷ ψ.X b ≫ (associator (θ'.X a) (G.map f) (ψ.X b)).hom ≫ θ'.X a ◁ ψ.x f ≫
          (associator (θ'.X a) (ψ.X a) (H.map f)).inv
    have hα := α.naturality f
    simp only [Category.assoc]
    rw [← associator_inv_naturality_left R,
      ← whisker_exchange_of_even_right_assoc (α.app a) (ψ.x_mem f),
      ← associator_naturality_left_assoc R, ← comp_whiskerRight'_assoc R, hα,
      comp_whiskerRight'_assoc R, ← associator_inv_naturality_middle_assoc R]

@[simp] theorem whiskerLeft_app (θ : TwoNatTrans F G) {ψ ψ' : TwoNatTrans G H} (α : ψ ⟶ ψ')
    (a : B) : (whiskerLeft θ α).app a = θ.X a ◁ α.app a := rfl

@[simp] theorem whiskerRight_app {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') (ψ : TwoNatTrans G H)
    (a : B) : (whiskerRight α ψ).app a = α.app a ▷ ψ.X a := rfl

/-! ### Coherence maps -/

/-- The associator of `𝔥𝔬𝔪(𝔄, 𝔅)`, with components the associators of `𝔅`. -/
def associator (θ : TwoNatTrans F G) (ψ : TwoNatTrans G H) (φ : TwoNatTrans H I) :
    vcomp (vcomp θ ψ) φ ≅ vcomp θ (vcomp ψ φ) :=
  isoOfOplaxModificationIso (θ := vcomp (vcomp θ ψ) φ) (θ' := vcomp θ (vcomp ψ φ))
    (Bicategory.associator θ.toOplaxTrans ψ.toOplaxTrans φ.toOplaxTrans)

/-- The left unitor of `𝔥𝔬𝔪(𝔄, 𝔅)`, with components the left unitors of `𝔅`. -/
def leftUnitor (θ : TwoNatTrans F G) : vcomp (id F) θ ≅ θ :=
  isoOfOplaxModificationIso (θ := vcomp (id F) θ) (θ' := θ) (Bicategory.leftUnitor θ.toOplaxTrans)

/-- The right unitor of `𝔥𝔬𝔪(𝔄, 𝔅)`, with components the right unitors of `𝔅`. -/
def rightUnitor (θ : TwoNatTrans F G) : vcomp θ (id G) ≅ θ :=
  isoOfOplaxModificationIso (θ := vcomp θ (id G)) (θ' := θ) (Bicategory.rightUnitor θ.toOplaxTrans)

@[simp] theorem associator_hom_app (θ : TwoNatTrans F G) (ψ : TwoNatTrans G H)
    (φ : TwoNatTrans H I) (a : B) :
    (associator θ ψ φ).hom.app a = (BicategoryStruct.associator (θ.X a) (ψ.X a) (φ.X a)).hom :=
  rfl

@[simp] theorem associator_inv_app (θ : TwoNatTrans F G) (ψ : TwoNatTrans G H)
    (φ : TwoNatTrans H I) (a : B) :
    (associator θ ψ φ).inv.app a = (BicategoryStruct.associator (θ.X a) (ψ.X a) (φ.X a)).inv :=
  rfl

@[simp] theorem leftUnitor_hom_app (θ : TwoNatTrans F G) (a : B) :
    (leftUnitor θ).hom.app a = (BicategoryStruct.leftUnitor (θ.X a)).hom := rfl

@[simp] theorem leftUnitor_inv_app (θ : TwoNatTrans F G) (a : B) :
    (leftUnitor θ).inv.app a = (BicategoryStruct.leftUnitor (θ.X a)).inv := rfl

@[simp] theorem rightUnitor_hom_app (θ : TwoNatTrans F G) (a : B) :
    (rightUnitor θ).hom.app a = (BicategoryStruct.rightUnitor (θ.X a)).hom := rfl

@[simp] theorem rightUnitor_inv_app (θ : TwoNatTrans F G) (a : B) :
    (rightUnitor θ).inv.app a = (BicategoryStruct.rightUnitor (θ.X a)).inv := rfl

end TwoNatTrans

/-! ## The 2-supercategory `𝔥𝔬𝔪(𝔄, 𝔅)` -/

namespace TwoSuperfunctor

/-- The bicategory data of `𝔥𝔬𝔪(𝔄, 𝔅)`: 2-natural transformations, supermodifications, the
vertical composite of 2-natural transformations, the whiskerings of supermodifications and the
componentwise coherence maps. -/
instance instBicategoryStruct : BicategoryStruct (TwoSuperfunctor R B C) where
  Hom F G := TwoNatTrans F G
  id F := TwoNatTrans.id F
  comp θ ψ := TwoNatTrans.vcomp θ ψ
  homCategory _ _ := inferInstance
  whiskerLeft θ _ _ α := TwoNatTrans.whiskerLeft θ α
  whiskerRight α ψ := TwoNatTrans.whiskerRight α ψ
  associator := TwoNatTrans.associator
  leftUnitor := TwoNatTrans.leftUnitor
  rightUnitor := TwoNatTrans.rightUnitor

instance (F G : TwoSuperfunctor R B C) : Preadditive (F ⟶ G) :=
  inferInstanceAs (Preadditive (TwoNatTrans F G))

instance (F G : TwoSuperfunctor R B C) : Linear R (F ⟶ G) :=
  inferInstanceAs (Linear R (TwoNatTrans F G))

instance (F G : TwoSuperfunctor R B C) : Supercategory R (F ⟶ G) :=
  inferInstanceAs (Supercategory R (TwoNatTrans F G))

variable {F G H I : TwoSuperfunctor R B C}

theorem hom_def (F G : TwoSuperfunctor R B C) : (F ⟶ G) = TwoNatTrans F G := rfl

theorem id_def (F : TwoSuperfunctor R B C) : 𝟙 F = TwoNatTrans.id F := rfl

theorem comp_def (θ : F ⟶ G) (ψ : G ⟶ H) : θ ≫ ψ = TwoNatTrans.vcomp θ ψ := rfl

@[simp] theorem comp_X (θ : F ⟶ G) (ψ : G ⟶ H) (a : B) :
    TwoNatTrans.X (θ ≫ ψ) a = θ.X a ≫ ψ.X a := rfl

@[simp] theorem id_X (F : TwoSuperfunctor R B C) (a : B) :
    TwoNatTrans.X (𝟙 F) a = 𝟙 (F.obj a) := rfl

@[simp] theorem whiskerLeft_app (θ : F ⟶ G) {ψ ψ' : G ⟶ H} (α : ψ ⟶ ψ') (a : B) :
    (θ ◁ α).app a = θ.X a ◁ α.app a := rfl

@[simp] theorem whiskerRight_app {θ θ' : F ⟶ G} (α : θ ⟶ θ') (ψ : G ⟶ H) (a : B) :
    (α ▷ ψ).app a = α.app a ▷ ψ.X a := rfl

@[simp] theorem associator_hom_app (θ : F ⟶ G) (ψ : G ⟶ H) (φ : H ⟶ I) (a : B) :
    (associator θ ψ φ).hom.app a = (associator (θ.X a) (ψ.X a) (φ.X a)).hom := rfl

@[simp] theorem associator_inv_app (θ : F ⟶ G) (ψ : G ⟶ H) (φ : H ⟶ I) (a : B) :
    (associator θ ψ φ).inv.app a = (associator (θ.X a) (ψ.X a) (φ.X a)).inv := rfl

@[simp] theorem leftUnitor_hom_app (θ : F ⟶ G) (a : B) :
    (leftUnitor θ).hom.app a = (leftUnitor (θ.X a)).hom := rfl

@[simp] theorem leftUnitor_inv_app (θ : F ⟶ G) (a : B) :
    (leftUnitor θ).inv.app a = (leftUnitor (θ.X a)).inv := rfl

@[simp] theorem rightUnitor_hom_app (θ : F ⟶ G) (a : B) :
    (rightUnitor θ).hom.app a = (rightUnitor (θ.X a)).hom := rfl

@[simp] theorem rightUnitor_inv_app (θ : F ⟶ G) (a : B) :
    (rightUnitor θ).inv.app a = (rightUnitor (θ.X a)).inv := rfl

theorem mem_parity_iff {θ θ' : F ⟶ G} {p : ZMod 2} {α : θ ⟶ θ'} :
    α ∈ parity (R := R) θ θ' p ↔ ∀ a, α.app a ∈ parity (R := R) (θ.X a) (θ'.X a) p :=
  Iff.rfl

/-- **Brundan–Ellis, Definition 2.2(iv).** 2-superfunctors `𝔄 → 𝔅`, 2-natural transformations
and supermodifications form a 2-supercategory `𝔥𝔬𝔪(𝔄, 𝔅)`. -/
instance instTwoSupercategory : TwoSupercategory R (TwoSuperfunctor R B C) where
  whiskerLeft_id _ _ := TwoNatTrans.hom_ext fun _ => whiskerLeft_id (R := R) _ _
  whiskerLeft_comp _ _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => whiskerLeft_comp (R := R) _ _ _
  id_whiskerLeft _ := TwoNatTrans.hom_ext fun _ => id_whiskerLeft (R := R) _
  comp_whiskerLeft _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => comp_whiskerLeft (R := R) _ _ _
  id_whiskerRight _ _ := TwoNatTrans.hom_ext fun _ => id_whiskerRight (R := R) _ _
  comp_whiskerRight _ _ _ := TwoNatTrans.hom_ext fun _ => comp_whiskerRight (R := R) _ _ _
  whiskerRight_id _ := TwoNatTrans.hom_ext fun _ => whiskerRight_id (R := R) _
  whiskerRight_comp _ _ _ := TwoNatTrans.hom_ext fun _ => whiskerRight_comp (R := R) _ _ _
  whisker_assoc _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => whisker_assoc (R := R) _ _ _
  pentagon _ _ _ _ := TwoNatTrans.hom_ext fun _ => pentagon (R := R) _ _ _ _
  triangle _ _ := TwoNatTrans.hom_ext fun _ => triangle (R := R) _ _
  whiskerLeft_add _ _ _ _ _ := TwoNatTrans.hom_ext fun _ => whiskerLeft_add (R := R) _ _ _
  add_whiskerRight _ _ _ := TwoNatTrans.hom_ext fun _ => add_whiskerRight (R := R) _ _ _
  whiskerLeft_smul _ _ _ r _ := TwoNatTrans.hom_ext fun _ => whiskerLeft_smul (R := R) _ r _
  smul_whiskerRight r _ _ := TwoNatTrans.hom_ext fun _ => smul_whiskerRight (R := R) r _ _
  whiskerLeft_mem _ _ _ _ _ hα a := whiskerLeft_mem _ (hα a)
  whiskerRight_mem _ hα a := whiskerRight_mem _ (hα a)
  super_interchange hα hβ := TwoNatTrans.hom_ext fun a => super_interchange (hα a) (hβ a)
  associator_hom_mem _ _ _ _ := associator_hom_mem (R := R) _ _ _
  leftUnitor_hom_mem _ _ := leftUnitor_hom_mem (R := R) _
  rightUnitor_hom_mem _ _ := rightUnitor_hom_mem (R := R) _

/-! ### Strictness -/

section Strict

variable [BicategoryStruct.Strict C]

open BicategoryStruct.Strict in
/-- For strict `𝔅`, the identity 2-natural transformation is a strict left unit. -/
theorem id_comp_of_strict (θ : F ⟶ G) : 𝟙 F ≫ θ = θ := by
  change TwoNatTrans.vcomp (TwoNatTrans.id F) θ = θ
  refine TwoNatTrans.ext_of_eq (funext fun a => by
    rw [TwoNatTrans.vcomp_X, TwoNatTrans.id_X]; exact id_comp (θ.X a)) fun f => ?_
  simp only [TwoNatTrans.vcomp_x, TwoNatTrans.vcomp_X, TwoNatTrans.id_x, TwoNatTrans.id_X,
    associator_eqToIso, leftUnitor_eqToIso, rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
    id_whiskerLeft (R := R), eqToHom_whiskerRight R, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]

open BicategoryStruct.Strict in
/-- For strict `𝔅`, the identity 2-natural transformation is a strict right unit. -/
theorem comp_id_of_strict (θ : F ⟶ G) : θ ≫ 𝟙 G = θ := by
  change TwoNatTrans.vcomp θ (TwoNatTrans.id G) = θ
  refine TwoNatTrans.ext_of_eq (funext fun a => by
    rw [TwoNatTrans.vcomp_X, TwoNatTrans.id_X]; exact comp_id (θ.X a)) fun f => ?_
  simp only [TwoNatTrans.vcomp_x, TwoNatTrans.vcomp_X, TwoNatTrans.id_x, TwoNatTrans.id_X,
    associator_eqToIso, leftUnitor_eqToIso, rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
    whiskerRight_id (R := R), whiskerLeft_eqToHom R, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]

open BicategoryStruct.Strict in
/-- For strict `𝔅`, the composition of 2-natural transformations is strictly associative. -/
theorem assoc_of_strict (θ : F ⟶ G) (ψ : G ⟶ H) (φ : H ⟶ I) :
    (θ ≫ ψ) ≫ φ = θ ≫ ψ ≫ φ := by
  change TwoNatTrans.vcomp (TwoNatTrans.vcomp θ ψ) φ = TwoNatTrans.vcomp θ (TwoNatTrans.vcomp ψ φ)
  refine TwoNatTrans.ext_of_eq (funext fun a => by
    rw [TwoNatTrans.vcomp_X, TwoNatTrans.vcomp_X, TwoNatTrans.vcomp_X, TwoNatTrans.vcomp_X]
    exact assoc (θ.X a) (ψ.X a) (φ.X a)) fun f => ?_
  simp only [TwoNatTrans.vcomp_x, TwoNatTrans.vcomp_X, associator_eqToIso, eqToIso.hom,
    eqToIso.inv, whiskerLeft_comp (R := R), comp_whiskerRight (R := R),
    whiskerRight_comp (R := R), comp_whiskerLeft (R := R), whisker_assoc (R := R),
    eqToHom_whiskerRight R, whiskerLeft_eqToHom R, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]
  erw [eqToHom_trans_assoc, eqToHom_trans]

/-- **Brundan–Ellis, Definition 2.2.** If `𝔅` is a strict 2-supercategory, so is
`𝔥𝔬𝔪(𝔄, 𝔅)` (for arbitrary, not necessarily strict, 2-superfunctors `𝔄 → 𝔅`): composition of
2-natural transformations is strictly associative and unital, and the associators and unitors,
whose components are those of `𝔅`, are identities. -/
instance instStrict : BicategoryStruct.Strict (TwoSuperfunctor R B C) where
  id_comp := id_comp_of_strict
  comp_id := comp_id_of_strict
  assoc := assoc_of_strict
  leftUnitor_eqToIso θ := Iso.ext (TwoNatTrans.hom_ext fun a => by
    rw [leftUnitor_hom_app, eqToIso.hom, TwoNatTrans.eqToHom_app,
      BicategoryStruct.Strict.leftUnitor_eqToIso, eqToIso.hom]
    rfl)
  rightUnitor_eqToIso θ := Iso.ext (TwoNatTrans.hom_ext fun a => by
    rw [rightUnitor_hom_app, eqToIso.hom, TwoNatTrans.eqToHom_app,
      BicategoryStruct.Strict.rightUnitor_eqToIso, eqToIso.hom]
    rfl)
  associator_eqToIso θ ψ φ := Iso.ext (TwoNatTrans.hom_ext fun a => by
    rw [associator_hom_app, eqToIso.hom, TwoNatTrans.eqToHom_app,
      BicategoryStruct.Strict.associator_eqToIso, eqToIso.hom]
    rfl)

end Strict

end TwoSuperfunctor

/-! ## Superequivalent objects -/

namespace TwoSupercategory

variable (R) in
/-- Two objects of a 2-supercategory are superequivalent if there is a superequivalence
1-morphism between them (Brundan–Ellis, Definition 2.2). -/
def Superequivalent (a b : B) : Prop := ∃ f : a ⟶ b, IsSuperequivalence R f

theorem Superequivalent.refl (a : B) : Superequivalent R a a :=
  ⟨𝟙 a, 𝟙 a, leftUnitor (𝟙 a), leftUnitor (𝟙 a), leftUnitor_hom_mem (R := R) _,
    leftUnitor_hom_mem (R := R) _⟩

omit [TwoSupercategory R B] in
theorem Superequivalent.symm {a b : B} (h : Superequivalent R a b) : Superequivalent R b a := by
  obtain ⟨f, g, e₁, e₂, h₁, h₂⟩ := h
  exact ⟨g, f, e₂, e₁, h₂, h₁⟩

end TwoSupercategory

/-! ## 2-superequivalences -/

namespace TwoSuperfunctor

variable {F G : TwoSuperfunctor R B C}

set_option backward.isDefEq.respectTransparency false in
/-- The components of a superequivalence in `𝔥𝔬𝔪(𝔄, 𝔅)` are superequivalences in `𝔅`. -/
theorem IsSuperequivalence.app {θ : F ⟶ G} (h : IsSuperequivalence R θ) (a : B) :
    IsSuperequivalence R (θ.X a) := by
  obtain ⟨ψ, e₁, e₂, h₁, h₂⟩ := h
  refine ⟨ψ.X a, ⟨e₁.hom.app a, e₁.inv.app a, ?_, ?_⟩, ⟨e₂.hom.app a, e₂.inv.app a, ?_, ?_⟩,
    h₁ a, h₂ a⟩
  · rw [← TwoNatTrans.comp_app, e₁.hom_inv_id]; rfl
  · rw [← TwoNatTrans.comp_app, e₁.inv_hom_id]; rfl
  · rw [← TwoNatTrans.comp_app, e₂.hom_inv_id]; rfl
  · rw [← TwoNatTrans.comp_app, e₂.inv_hom_id]; rfl

/-- **Brundan–Ellis, Definition 2.2.** A 2-superfunctor `ℝ : 𝔄 → 𝔅` is a 2-superequivalence if
there is a 2-superfunctor `𝕊 : 𝔅 → 𝔄` such that `𝕊 ∘ ℝ` and `ℝ ∘ 𝕊` are superequivalent to the
identities in `𝔥𝔬𝔪(𝔄, 𝔄)` and `𝔥𝔬𝔪(𝔅, 𝔅)`. -/
def IsTwoSuperequivalence (F : TwoSuperfunctor R B C) : Prop :=
  ∃ G : TwoSuperfunctor R C B,
    Superequivalent R (F.comp G) (TwoSuperfunctor.id R B) ∧
      Superequivalent R (G.comp F) (TwoSuperfunctor.id R C)

/-- **Brundan–Ellis, Definition 2.2**, second formulation: `ℝ` induces superequivalences
`ℋom_𝔄(λ, μ) → ℋom_𝔅(ℝλ, ℝμ)`, and every object of `𝔅` is superequivalent to an object of the
form `ℝλ`. The paper asserts that this is equivalent to `IsTwoSuperequivalence`; only the
implication `IsTwoSuperequivalence.isLocalTwoSuperequivalence` is proved here. -/
structure IsLocalTwoSuperequivalence (F : TwoSuperfunctor R B C) : Prop where
  /-- `ℝ` is a superequivalence on each morphism supercategory. -/
  hom (a b : B) : Nonempty (Superequivalence R (F.mapFunctor a b))
  /-- Every object of `𝔅` is superequivalent to some `ℝλ`. -/
  essSurj (c : C) : ∃ a : B, Superequivalent R (F.obj a) c

/-- A 2-superequivalence is essentially surjective up to superequivalence: if `ℝ ∘ 𝕊 ⇒ 𝕀` is a
superequivalence in `𝔥𝔬𝔪(𝔅, 𝔅)`, its component at `ν` is a superequivalence `ℝ(𝕊ν) → ν`. -/
theorem IsTwoSuperequivalence.essSurj {F : TwoSuperfunctor R B C} (h : F.IsTwoSuperequivalence)
    (c : C) : ∃ a : B, Superequivalent R (F.obj a) c := by
  obtain ⟨G, -, θ, hθ⟩ := h
  exact ⟨G.obj c, θ.X c, IsSuperequivalence.app hθ c⟩

variable (R B C) in
/-- Two 2-supercategories are 2-superequivalent if there is a 2-superequivalence between them
(Brundan–Ellis, Definition 2.2). -/
def TwoSuperequivalent : Prop := ∃ F : TwoSuperfunctor R B C, F.IsTwoSuperequivalence

variable (R B C) in
/-- Two 2-supercategories are 2-superequivalent in the second formulation of Definition 2.2 if
there is a 2-superfunctor between them which is a superequivalence on morphism supercategories
and essentially surjective up to superequivalence. -/
def LocalTwoSuperequivalent : Prop := ∃ F : TwoSuperfunctor R B C, F.IsLocalTwoSuperequivalence

end TwoSuperfunctor

/-! ## From the first to the second formulation of a 2-superequivalence

### Whiskering by superequivalences -/

namespace TwoSupercategory

variable {a b c : B}

/-- If `g f ≅ 1` via an even 2-isomorphism, a 2-morphism `η` is recovered from `f ◁ η`
(`η` is `g ◁ f ◁ η` conjugated by `h ≅ 1 h ≅ (g f) h ≅ g (f h)`). -/
theorem eq_of_whiskerLeft {f : a ⟶ b} {g : b ⟶ a} (e : g ≫ f ≅ 𝟙 b)
    (he : e.hom ∈ parity (R := R) (g ≫ f) (𝟙 b) 0) {h h' : b ⟶ c} (η : h ⟶ h') :
    η = (leftUnitor h).inv ≫ e.inv ▷ h ≫ (associator g f h).hom ≫ g ◁ f ◁ η ≫
      (associator g f h').inv ≫ e.hom ▷ h' ≫ (leftUnitor h').hom := by
  rw [associator_inv_naturality_right_assoc R, Iso.hom_inv_id_assoc,
    ← whisker_exchange_of_even_left_assoc he, inv_hom_whiskerRight_assoc R,
    leftUnitor_naturality R, Iso.inv_hom_id_assoc]

/-- If `f g ≅ 1` via an even 2-isomorphism, a 2-morphism `η` is recovered from `η ▷ f`. -/
theorem eq_of_whiskerRight {f : a ⟶ b} {g : b ⟶ a} (e : f ≫ g ≅ 𝟙 a)
    (he : e.hom ∈ parity (R := R) (f ≫ g) (𝟙 a) 0) {h h' : c ⟶ a} (η : h ⟶ h') :
    η = (rightUnitor h).inv ≫ h ◁ e.inv ≫ (associator h f g).inv ≫ η ▷ f ▷ g ≫
      (associator h' f g).hom ≫ h' ◁ e.hom ≫ (rightUnitor h').hom := by
  rw [associator_naturality_left_assoc R, Iso.inv_hom_id_assoc,
    whisker_exchange_of_even_right_assoc η he, whiskerLeft_inv_hom_assoc R,
    rightUnitor_naturality R, Iso.inv_hom_id_assoc]

/-- If `g f ≅ 1` via an even 2-isomorphism, `η ↦ f ◁ η` is injective. -/
theorem whiskerLeft_injective_of_iso {f : a ⟶ b} {g : b ⟶ a} (e : g ≫ f ≅ 𝟙 b)
    (he : e.hom ∈ parity (R := R) (g ≫ f) (𝟙 b) 0) {h h' : b ⟶ c} :
    Function.Injective (fun η : h ⟶ h' => f ◁ η) := fun η η' hη => by
  have hη : f ◁ η = f ◁ η' := hη
  rw [eq_of_whiskerLeft e he η, eq_of_whiskerLeft e he η', hη]

/-- If `f g ≅ 1` via an even 2-isomorphism, `η ↦ η ▷ f` is injective. -/
theorem whiskerRight_injective_of_iso {f : a ⟶ b} {g : b ⟶ a} (e : f ≫ g ≅ 𝟙 a)
    (he : e.hom ∈ parity (R := R) (f ≫ g) (𝟙 a) 0) {h h' : c ⟶ a} :
    Function.Injective (fun η : h ⟶ h' => η ▷ f) := fun η η' hη => by
  have hη : η ▷ f = η' ▷ f := hη
  rw [eq_of_whiskerRight e he η, eq_of_whiskerRight e he η', hη]

/-- Left whiskering by a superequivalence is injective on 2-morphisms. -/
theorem IsSuperequivalence.whiskerLeft_injective {f : a ⟶ b} (hf : IsSuperequivalence R f)
    {h h' : b ⟶ c} : Function.Injective (fun η : h ⟶ h' => f ◁ η) := by
  obtain ⟨g, -, e₂, -, h₂⟩ := hf
  exact whiskerLeft_injective_of_iso e₂ h₂

/-- Right whiskering by a superequivalence is injective on 2-morphisms. -/
theorem IsSuperequivalence.whiskerRight_injective {f : a ⟶ b} (hf : IsSuperequivalence R f)
    {h h' : c ⟶ a} : Function.Injective (fun η : h ⟶ h' => η ▷ f) := by
  obtain ⟨g, e₁, -, h₁, -⟩ := hf
  exact whiskerRight_injective_of_iso e₁ h₁

/-- Left whiskering by a superequivalence is surjective on 2-morphisms. -/
theorem IsSuperequivalence.whiskerLeft_surjective {f : a ⟶ b} (hf : IsSuperequivalence R f)
    {h h' : b ⟶ c} : Function.Surjective (fun η : h ⟶ h' => f ◁ η) := by
  obtain ⟨g, e₁, e₂, h₁, h₂⟩ := hf
  intro ζ
  set η := (leftUnitor h).inv ≫ e₂.inv ▷ h ≫ (associator g f h).hom ≫ g ◁ ζ ≫
    (associator g f h').inv ≫ e₂.hom ▷ h' ≫ (leftUnitor h').hom with hη
  refine ⟨η, whiskerLeft_injective_of_iso (f := g) e₁ h₁ ?_⟩
  have key := (eq_of_whiskerLeft e₂ h₂ η).symm.trans hη
  have key' := congrArg (fun t => (associator g f h).inv ≫ e₂.hom ▷ h ≫ (leftUnitor h).hom ≫ t ≫
    (leftUnitor h').inv ≫ e₂.inv ▷ h' ≫ (associator g f h').hom) key
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, hom_inv_whiskerRight_assoc R] at key'
  exact key'

/-- Right whiskering by a superequivalence is surjective on 2-morphisms. -/
theorem IsSuperequivalence.whiskerRight_surjective {f : a ⟶ b} (hf : IsSuperequivalence R f)
    {h h' : c ⟶ a} : Function.Surjective (fun η : h ⟶ h' => η ▷ f) := by
  obtain ⟨g, e₁, e₂, h₁, h₂⟩ := hf
  intro ζ
  set η := (rightUnitor h).inv ≫ h ◁ e₁.inv ≫ (associator h f g).inv ≫ ζ ▷ g ≫
    (associator h' f g).hom ≫ h' ◁ e₁.hom ≫ (rightUnitor h').hom with hη
  refine ⟨η, whiskerRight_injective_of_iso (f := g) e₂ h₂ ?_⟩
  have key := (eq_of_whiskerRight e₁ h₁ η).symm.trans hη
  have key' := congrArg (fun t => (associator h f g).hom ≫ h ◁ e₁.hom ≫ (rightUnitor h).hom ≫
    t ≫ (rightUnitor h').inv ≫ h' ◁ e₁.inv ≫ (associator h' f g).inv) key
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id,
    whiskerLeft_hom_inv_assoc R] at key'
  exact key'

/-! ### Even isomorphisms of 1-morphisms (auxiliary) -/

variable {d : B}

variable (R) in
/-- Two 1-morphisms are isomorphic via an even 2-isomorphism. -/
private def EvenIso (f g : a ⟶ b) : Prop := ∃ e : f ≅ g, e.hom ∈ parity (R := R) f g 0

omit [TwoSupercategory R B] in
private theorem EvenIso.trans {f g h : a ⟶ b} (h₁ : EvenIso R f g) (h₂ : EvenIso R g h) :
    EvenIso R f h := by
  obtain ⟨e, he⟩ := h₁
  obtain ⟨e', he'⟩ := h₂
  exact ⟨e ≪≫ e', by simpa using comp_mem he he'⟩

omit [TwoSupercategory R B] in
private theorem EvenIso.symm {f g : a ⟶ b} (h : EvenIso R f g) : EvenIso R g f := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, inv_mem e he⟩

private theorem EvenIso.whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (hgh : EvenIso R g h) :
    EvenIso R (f ≫ g) (f ≫ h) := by
  obtain ⟨e, he⟩ := hgh
  exact ⟨whiskerLeftIso (R := R) f e, whiskerLeft_mem f he⟩

private theorem EvenIso.whiskerRight {f g : a ⟶ b} (hfg : EvenIso R f g) (h : b ⟶ c) :
    EvenIso R (f ≫ h) (g ≫ h) := by
  obtain ⟨e, he⟩ := hfg
  exact ⟨whiskerRightIso (R := R) e h, whiskerRight_mem h he⟩

variable (R) in
private theorem EvenIso.associator (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    EvenIso R ((f ≫ g) ≫ h) (f ≫ g ≫ h) :=
  ⟨BicategoryStruct.associator f g h, associator_hom_mem (R := R) f g h⟩

variable (R) in
private theorem EvenIso.leftUnitor (f : a ⟶ b) : EvenIso R (𝟙 a ≫ f) f :=
  ⟨BicategoryStruct.leftUnitor f, leftUnitor_hom_mem (R := R) f⟩

variable (R) in
private theorem EvenIso.rightUnitor (f : a ⟶ b) : EvenIso R (f ≫ 𝟙 b) f :=
  ⟨BicategoryStruct.rightUnitor f, rightUnitor_hom_mem (R := R) f⟩

end TwoSupercategory

/-! ### Superequivalences in `𝔥𝔬𝔪(𝔄, 𝔅)` are strong -/

namespace TwoSuperfunctor

variable {F' G' : TwoSuperfunctor R B C}

/-- An isomorphism `θ₁ ≅ θ₂` in `ℋom(ℝ, 𝕊)` conjugates the 2-morphisms `x` of `θ₁` and `θ₂`. -/
theorem x_eq_of_iso {θ₁ θ₂ : F' ⟶ G'} (e : θ₁ ≅ θ₂) {a b : B} (f : a ⟶ b) :
    θ₁.x f = F'.map f ◁ e.hom.app b ≫ θ₂.x f ≫ e.inv.app a ▷ G'.map f := by
  have h : e.hom.app a ≫ e.inv.app a = 𝟙 _ := by
    rw [← TwoNatTrans.comp_app, e.hom_inv_id]; rfl
  rw [← Category.assoc, ← e.hom.naturality f, Category.assoc, ← comp_whiskerRight' R, h,
    id_whiskerRight (R := R), Category.comp_id]

/-- The components of an isomorphism in `ℋom(ℝ, 𝕊)`. -/
private def appIso {θ₁ θ₂ : F' ⟶ G'} (e : θ₁ ≅ θ₂) (a : B) : θ₁.X a ≅ θ₂.X a where
  hom := e.hom.app a
  inv := e.inv.app a
  hom_inv_id := by rw [← TwoNatTrans.comp_app, e.hom_inv_id]; rfl
  inv_hom_id := by rw [← TwoNatTrans.comp_app, e.inv_hom_id]; rfl

/-- The 2-morphism `x_F` of a 2-natural transformation isomorphic in `ℋom(ℝ, 𝕊)` to one with
invertible `x_F` is invertible. -/
theorem isIso_x_of_iso {θ₁ θ₂ : F' ⟶ G'} (e : θ₁ ≅ θ₂) {a b : B} (f : a ⟶ b)
    [IsIso (θ₂.x f)] : IsIso (θ₁.x f) := by
  rw [x_eq_of_iso e f]
  have : IsIso (F'.map f ◁ e.hom.app b) :=
    (whiskerLeftIso (R := R) (F'.map f) (appIso e b)).isIso_hom
  have : IsIso (e.inv.app a ▷ G'.map f) :=
    (whiskerRightIso (R := R) (appIso e a).symm (G'.map f)).isIso_hom
  infer_instance

/-- The 2-morphisms `x_F = λ_F⁻¹ ∘ ρ_F` of the identity 2-natural transformation are invertible. -/
theorem isIso_id_x (F' : TwoSuperfunctor R B C) {a b : B} (f : a ⟶ b) :
    IsIso (TwoNatTrans.x (𝟙 F') f) := by
  rw [id_def, TwoNatTrans.id_x]
  exact (rightUnitor (F'.map f) ≪≫ (leftUnitor (F'.map f)).symm).isIso_hom

/-- The 2-morphisms `x_F` of a superequivalence `(X, x)` in `𝔥𝔬𝔪(𝔄, 𝔅)` are invertible, i.e. a
superequivalence in `𝔥𝔬𝔪(𝔄, 𝔅)` is a strong 2-natural transformation. -/
theorem IsSuperequivalence.isIso_x {θ : F' ⟶ G'} (hθ : IsSuperequivalence R θ) {a b : B}
    (f : a ⟶ b) : IsIso (θ.x f) := by
  obtain ⟨θ', e₁, e₂, h₁, h₂⟩ := hθ
  have hθ' : IsSuperequivalence R θ' := ⟨θ, e₂, e₁, h₂, h₁⟩
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : (θ.X a ≫ θ'.X a) ≫ F'.map f ⟶ F'.map f ≫ θ.X b ≫ θ'.X b,
      (θ ≫ θ').x f ≫ T₁ = 𝟙 _ := by
    obtain ⟨T, hT, -⟩ := (have := isIso_id_x F' f; isIso_x_of_iso e₁ f).out
    exact ⟨T, hT⟩
  obtain ⟨T₂, hT₂⟩ : ∃ T₂ : (θ'.X a ≫ θ.X a) ≫ G'.map f ⟶ G'.map f ≫ θ'.X b ≫ θ.X b,
      T₂ ≫ (θ' ≫ θ).x f = 𝟙 _ := by
    obtain ⟨T, -, hT⟩ := (have := isIso_id_x G' f; isIso_x_of_iso e₂ f).out
    exact ⟨T, hT⟩
  -- a right inverse of `θ.x f`, from `(θ ≫ θ').x f`
  obtain ⟨r, hr⟩ : ∃ r, θ.x f ≫ r = 𝟙 _ := by
    have h : ((associator (F'.map f) (θ.X b) (θ'.X b)).inv ≫ θ.x f ▷ θ'.X b ≫
        (associator (θ.X a) (G'.map f) (θ'.X b)).hom ≫ θ.X a ◁ θ'.x f ≫
          (associator (θ.X a) (θ'.X a) (F'.map f)).inv) ≫ T₁ = 𝟙 _ :=
      hT₁
    simp only [Category.assoc] at h
    obtain ⟨r', hr'⟩ := (IsSuperequivalence.app hθ' b).whiskerRight_surjective
      ((associator (θ.X a) (G'.map f) (θ'.X b)).hom ≫ θ.X a ◁ θ'.x f ≫
        (associator (θ.X a) (θ'.X a) (F'.map f)).inv ≫ T₁ ≫
          (associator (F'.map f) (θ.X b) (θ'.X b)).inv)
    refine ⟨r', (IsSuperequivalence.app hθ' b).whiskerRight_injective ?_⟩
    change (θ.x f ≫ r') ▷ θ'.X b = 𝟙 (F'.map f ≫ θ.X b) ▷ θ'.X b
    have hr' : r' ▷ θ'.X b = _ := hr'
    rw [comp_whiskerRight' R, hr', id_whiskerRight (R := R),
      ← cancel_epi (associator (F'.map f) (θ.X b) (θ'.X b)).inv, reassoc_of% h, Category.comp_id]
  -- a left inverse of `θ.x f`, from `(θ' ≫ θ).x f`
  obtain ⟨l, hl⟩ : ∃ l, l ≫ θ.x f = 𝟙 _ := by
    have h : T₂ ≫ (associator (G'.map f) (θ'.X b) (θ.X b)).inv ≫
        θ'.x f ▷ θ.X b ≫ (associator (θ'.X a) (F'.map f) (θ.X b)).hom ≫
          θ'.X a ◁ θ.x f ≫ (associator (θ'.X a) (θ.X a) (G'.map f)).inv = 𝟙 _ :=
      hT₂
    obtain ⟨l', hl'⟩ := (IsSuperequivalence.app hθ' a).whiskerLeft_surjective
      ((associator (θ'.X a) (θ.X a) (G'.map f)).inv ≫ T₂ ≫
        (associator (G'.map f) (θ'.X b) (θ.X b)).inv ≫ θ'.x f ▷ θ.X b ≫
          (associator (θ'.X a) (F'.map f) (θ.X b)).hom)
    refine ⟨l', (IsSuperequivalence.app hθ' a).whiskerLeft_injective ?_⟩
    change θ'.X a ◁ (l' ≫ θ.x f) = θ'.X a ◁ 𝟙 (θ.X a ≫ G'.map f)
    have hl' : θ'.X a ◁ l' = _ := hl'
    rw [whiskerLeft_comp' R, hl', whiskerLeft_id (R := R),
      ← cancel_mono (associator (θ'.X a) (θ.X a) (G'.map f)).inv]
    simp only [Category.assoc]
    rw [h, Category.comp_id, Category.id_comp]
  have hlr : l = r := calc
    l = l ≫ θ.x f ≫ r := by rw [hr, Category.comp_id]
    _ = r := by rw [reassoc_of% hl]
  exact ⟨r, hr, hlr ▸ hl⟩

/-- A superequivalence in `𝔥𝔬𝔪(𝔄, 𝔅)` is a strong 2-natural transformation. -/
theorem IsSuperequivalence.isStrong {θ : F' ⟶ G'} (hθ : IsSuperequivalence R θ) :
    TwoNatTrans.IsStrong θ :=
  fun f => IsSuperequivalence.isIso_x hθ f

/-! ### Local superequivalence -/

variable {F : TwoSuperfunctor R B C} {G : TwoSuperfunctor R C B}

omit [TwoSupercategory R C] in
/-- If `𝕊 ∘ ℝ` is superequivalent to `𝕀` in `𝔥𝔬𝔪(𝔄, 𝔄)`, then `ℝ` is faithful on 2-morphisms:
for a superequivalence `(X, x) : 𝕊ℝ ⇒ 𝕀`, `η X_λ = x_G ∘ X_μ (𝕊ℝη) ∘ x_F⁻¹`. -/
theorem map₂_injective_of_superequivalent
    (h : Superequivalent R (F.comp G) (TwoSuperfunctor.id R B)) {a b : B} {f g : a ⟶ b} :
    Function.Injective (F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)) := by
  intro η η' hη
  obtain ⟨θ, hθ⟩ := h
  have := IsSuperequivalence.isIso_x hθ f
  apply (IsSuperequivalence.app hθ a).whiskerLeft_injective
  change θ.X a ◁ η = θ.X a ◁ η'
  rw [← cancel_epi (θ.x f)]
  have n := θ.naturality η
  have n' := θ.naturality η'
  change G.map₂ (F.map₂ η) ▷ θ.X b ≫ θ.x g = θ.x f ≫ θ.X a ◁ η at n
  change G.map₂ (F.map₂ η') ▷ θ.X b ≫ θ.x g = θ.x f ≫ θ.X a ◁ η' at n'
  rw [← n, ← n', hη]

omit [TwoSupercategory R C] in
/-- If `𝕊 ∘ ℝ` is superequivalent to `𝕀` in `𝔥𝔬𝔪(𝔄, 𝔄)` and `𝕊` is faithful on 2-morphisms,
then `ℝ` is full on 2-morphisms. -/
theorem map₂_surjective_of_superequivalent
    (h : Superequivalent R (F.comp G) (TwoSuperfunctor.id R B)) {a b : B}
    (hG : ∀ {f g : F.obj a ⟶ F.obj b},
      Function.Injective (G.map₂ : (f ⟶ g) → (G.map f ⟶ G.map g)))
    {f g : a ⟶ b} : Function.Surjective (F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)) := by
  intro ζ
  obtain ⟨θ, hθ⟩ := h
  have := IsSuperequivalence.isIso_x hθ f
  obtain ⟨η, hη⟩ := (IsSuperequivalence.app hθ a).whiskerLeft_surjective
    (inv (θ.x f) ≫ G.map₂ ζ ▷ θ.X b ≫ θ.x g)
  have hη : θ.X a ◁ η = inv (θ.x f) ≫ G.map₂ ζ ▷ θ.X b ≫ θ.x g := hη
  have := IsSuperequivalence.isIso_x hθ g
  have key : (F.comp G).map₂ η ▷ θ.X b ≫ θ.x g = G.map₂ ζ ▷ θ.X b ≫ θ.x g := calc
    _ = θ.x f ≫ θ.X a ◁ η := θ.naturality η
    _ = _ := by rw [hη, IsIso.hom_inv_id_assoc]; rfl
  exact ⟨η, hG ((IsSuperequivalence.app hθ b).whiskerRight_injective
    ((cancel_mono (θ.x g)).1 key))⟩

omit [TwoSupercategory R C] in
/-- If `𝕊 ∘ ℝ` is superequivalent to `𝕀` in `𝔥𝔬𝔪(𝔄, 𝔄)` and `𝕊` is full and faithful on
2-morphisms, then every 1-morphism `K : ℝλ → ℝμ` is evenly isomorphic to one of the form `ℝF`:
for a superequivalence `(X, x) : 𝕊ℝ ⇒ 𝕀` with quasi-inverse `(X', x')`, take
`F = X_μ (𝕊K) X'_λ`; then `𝕊ℝF ≅ 𝕊K` since `x_F` is invertible, and `𝕊` reflects even
isomorphisms. -/
theorem evenlyDense_of_superequivalent
    (h : Superequivalent R (F.comp G) (TwoSuperfunctor.id R B)) (a b : B)
    [(G.mapFunctor (F.obj a) (F.obj b)).Full] [(G.mapFunctor (F.obj a) (F.obj b)).Faithful] :
    EvenlyDense R (F.mapFunctor a b) := by
  intro k
  obtain ⟨θ, hθ⟩ := h
  have hθ₀ := hθ
  obtain ⟨θ', e₁, -, h₁, -⟩ := hθ₀
  let f : a ⟶ b := θ'.X a ≫ G.map k ≫ θ.X b
  have := IsSuperequivalence.isIso_x hθ f
  have E : ∀ c : B, EvenIso R (θ.X c ≫ θ'.X c) (𝟙 (G.obj (F.obj c))) := fun c =>
    ⟨appIso e₁ c, h₁ c⟩
  have hx : EvenIso R (G.map (F.map f) ≫ θ.X b) (θ.X a ≫ f) :=
    ⟨@asIso _ _ _ _ (θ.x f) this, θ.x_mem f⟩
  have h6 : EvenIso R (f ≫ θ'.X b) (θ'.X a ≫ G.map k) :=
    (EvenIso.associator R _ _ _).trans (EvenIso.whiskerLeft _
      ((EvenIso.associator R _ _ _).trans
        ((EvenIso.whiskerLeft _ (E b)).trans (EvenIso.rightUnitor R _))))
  have hGk : EvenIso R (G.map (F.map f)) (G.map k) :=
    (EvenIso.rightUnitor R _).symm.trans <|
      (EvenIso.whiskerLeft _ (E b).symm).trans <|
        (EvenIso.associator R _ _ _).symm.trans <|
          (EvenIso.whiskerRight hx _).trans <|
            (EvenIso.associator R _ _ _).trans <|
              (EvenIso.whiskerLeft _ h6).trans <|
                (EvenIso.associator R _ _ _).symm.trans <|
                  (EvenIso.whiskerRight (E a) _).trans (EvenIso.leftUnitor R _)
  obtain ⟨e, he⟩ : EvenIso R ((G.mapFunctor (F.obj a) (F.obj b)).obj ((F.mapFunctor a b).obj f))
      ((G.mapFunctor (F.obj a) (F.obj b)).obj k) := hGk
  exact ⟨f, (G.mapFunctor (F.obj a) (F.obj b)).preimageIso e,
    mem_of_map_mem (G.mapFunctor (F.obj a) (F.obj b))
      (by rw [Functor.preimageIso_hom, Functor.map_preimage]; exact he)⟩

/-- **Brundan–Ellis, Definition 2.2**, one direction of the equivalence of the two formulations:
a 2-superequivalence `ℝ` (with `𝕊ℝ`, `ℝ𝕊` superequivalent to the identities) induces
superequivalences `ℋom_𝔄(λ, μ) → ℋom_𝔅(ℝλ, ℝμ)` and is essentially surjective up to
superequivalence. -/
theorem IsTwoSuperequivalence.isLocalTwoSuperequivalence {F : TwoSuperfunctor R B C}
    (h : F.IsTwoSuperequivalence) : F.IsLocalTwoSuperequivalence := by
  have h₀ := h
  obtain ⟨G, hFG, hGF⟩ := h₀
  have injF : ∀ {a b : B} {f g : a ⟶ b},
      Function.Injective (F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)) :=
    @fun _ _ _ _ => map₂_injective_of_superequivalent hFG
  have injG : ∀ {c d : C} {f g : c ⟶ d},
      Function.Injective (G.map₂ : (f ⟶ g) → (G.map f ⟶ G.map g)) :=
    @fun _ _ _ _ => map₂_injective_of_superequivalent hGF
  refine ⟨fun a b => ?_, h.essSurj⟩
  have : (F.mapFunctor a b).Faithful := ⟨fun h => injF h⟩
  have : (F.mapFunctor a b).Full :=
    ⟨map₂_surjective_of_superequivalent hFG fun h => injG h⟩
  have : (G.mapFunctor (F.obj a) (F.obj b)).Faithful := ⟨fun h => injG h⟩
  have : (G.mapFunctor (F.obj a) (F.obj b)).Full :=
    ⟨map₂_surjective_of_superequivalent hGF fun h => injF h⟩
  exact ⟨Superequivalence.ofFullyFaithful _ (evenlyDense_of_superequivalent hFG a b)⟩

/-- 2-superequivalent 2-supercategories (first formulation of Definition 2.2) are
2-superequivalent in the second formulation. -/
theorem TwoSuperequivalent.localTwoSuperequivalent (h : TwoSuperequivalent R B C) :
    LocalTwoSuperequivalent R B C := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, hF.isLocalTwoSuperequivalence⟩

end TwoSuperfunctor

end StringDiagrams

end
