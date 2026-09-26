import StringDiagrams.Super.TwoFunctorComp
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

## 2-superequivalences

Two objects `λ, μ` of a 2-supercategory are *superequivalent* if there is a 1-morphism
`λ → μ` which is a superequivalence (`TwoSupercategory.Superequivalent`, a symmetric relation).
Definition 2.2 gives two formulations of a 2-superequivalence `ℝ : 𝔄 → 𝔅`:

* `TwoSuperfunctor.IsTwoSuperequivalence`: there is a 2-superfunctor `𝕊 : 𝔅 → 𝔄` such that
  `𝕊 ∘ ℝ` and `ℝ ∘ 𝕊` are superequivalent to the identities in `𝔥𝔬𝔪(𝔄, 𝔄)` and `𝔥𝔬𝔪(𝔅, 𝔅)`;
* `TwoSuperfunctor.IsLocalTwoSuperequivalence`: `ℝ` induces superequivalences
  `ℋom_𝔄(λ, μ) → ℋom_𝔅(ℝλ, ℝμ)` on all morphism supercategories, and every object of `𝔅` is
  superequivalent to an object of the form `ℝλ`.

The paper states that the two formulations are equivalent; here only the implication from the
first to the essential surjectivity part of the second is proved
(`TwoSuperfunctor.IsTwoSuperequivalence.essSurj`). `TwoSuperequivalent R B C` (resp.
`LocalTwoSuperequivalent R B C`) is the existence of a 2-superequivalence in the first (resp.
second) sense.

## Not formalized

The equivalence of the two formulations of a 2-superequivalence, the strictness of
`𝔥𝔬𝔪(𝔄, 𝔅)` for strict `𝔅`, and the 3-supercategory of 2-supercategories.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

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

theorem toOplaxTrans_vcomp (θ : TwoNatTrans F G) (ψ : TwoNatTrans G H) :
    toOplaxTrans (vcomp θ ψ) = toOplaxTrans θ ≫ toOplaxTrans ψ := rfl

theorem toOplaxTrans_id : toOplaxTrans (id F) = 𝟙 F.toOplax := rfl

/-- A modification of the associated oplax transformations (whose components are even) as a
supermodification. -/
@[simps]
def homOfModification {θ θ' : TwoNatTrans F G}
    (Γ : Oplax.Modification θ.toOplaxTrans θ'.toOplaxTrans) : θ ⟶ θ' where
  app a := (Γ.app ⟨a⟩).1
  naturality f := (congrArg Subtype.val (Γ.naturality (Underlying2.hom1 f))).symm

/-- An isomorphism of the associated oplax transformations as an (even) isomorphism of
2-natural transformations. -/
@[simps]
def isoOfModificationIso {θ θ' : TwoNatTrans F G} (e : θ.toOplaxTrans ≅ θ'.toOplaxTrans) :
    θ ≅ θ' where
  hom := homOfModification e.hom
  inv := homOfModification e.inv
  hom_inv_id := hom_ext fun a =>
    congrArg (fun Γ => Subtype.val (Oplax.Modification.app Γ ⟨a⟩)) e.hom_inv_id
  inv_hom_id := hom_ext fun a =>
    congrArg (fun Γ => Subtype.val (Oplax.Modification.app Γ ⟨a⟩)) e.inv_hom_id

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
  isoOfModificationIso (θ := vcomp (vcomp θ ψ) φ) (θ' := vcomp θ (vcomp ψ φ))
    (Bicategory.associator θ.toOplaxTrans ψ.toOplaxTrans φ.toOplaxTrans)

/-- The left unitor of `𝔥𝔬𝔪(𝔄, 𝔅)`, with components the left unitors of `𝔅`. -/
def leftUnitor (θ : TwoNatTrans F G) : vcomp (id F) θ ≅ θ :=
  isoOfModificationIso (θ := vcomp (id F) θ) (θ' := θ) (Bicategory.leftUnitor θ.toOplaxTrans)

/-- The right unitor of `𝔥𝔬𝔪(𝔄, 𝔅)`, with components the right unitors of `𝔅`. -/
def rightUnitor (θ : TwoNatTrans F G) : vcomp θ (id G) ≅ θ :=
  isoOfModificationIso (θ := vcomp θ (id G)) (θ' := θ) (Bicategory.rightUnitor θ.toOplaxTrans)

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
form `ℝλ`. The paper asserts that this is equivalent to `IsTwoSuperequivalence`; only
`IsTwoSuperequivalence.essSurj` is proved here. -/
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

end StringDiagrams

end
