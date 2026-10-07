import StringDiagrams.Super.GradedTwoEnvelopeTwoHom
import StringDiagrams.Super.GradedTwoEnvelopeCoherence

/-!
# The `(Q, Π)`-envelope as a biuniversal arrow

Brundan–Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6: the assertion after
Lemma 6.11 that `-_{q,π}` is left 2-adjoint to the forgetful functor `ν` (the analogue of
Theorem 4.9).

The 2-natural transformations of Definition 2.2(iii) are oplax, so graded 2-supercategories,
graded 2-superfunctors and graded 2-natural transformations do not form a 2-category (see the
README). We formalize the 2-adjunction as a family of biuniversal arrows: for every graded
2-supercategory `𝔄`, the canonical strict graded 2-superfunctor `𝕁 : 𝔄 → ν(𝔄_{q,π})` (the
components of the natural transformation `GTwoSCat.envelopeUnit : 𝟭 ⟶ -_{q,π} ⋙ ν` of
1-truncations) is such that, for every graded 2-supercategory `𝔅` whose morphism
supercategories are graded `(Q, Π)`-supercategories (for instance a graded
`(Q, Π)`-2-supercategory), **precomposition with `𝕁`**
`ℋom(𝔄_{q,π}, 𝔅) → ℋom(𝔄, ν𝔅)` is a 2-superequivalence of hom 2-supercategories
(`QPiTwoEnvelope.restrictGradedTwoHom_isTwoSuperequivalence`). The extension
`ℝ ↦ ℝ̃` of Lemma 6.11 is a strict section of it (the triangle identity `ℝ̃𝕁 = ℝ` on objects,
1-morphisms and 2-morphisms of the hom 2-supercategories:
`QPiTwoEnvelope.restrictGradedTwoHom_obj_extendGradedTwoHom_obj`,
`QPiTwoEnvelope.restrictGradedTwoHom_map_extendGradedTwoHom_map`,
`QPiTwoEnvelope.restrictGradedTwoHom_map₂_extendGradedTwoHom_map₂`), and is itself a
2-superequivalence (`QPiTwoEnvelope.extendGradedTwoHom_isTwoSuperequivalence`).

On the bundled 1-truncations (`GTwoSCat`, `QPiTwoGSCat`), the restriction is precomposition
with the component of the unit `GTwoSCat.envelopeUnit` (`GTwoSCat.envelopeUnit_app_comp_val`),
the triangle identity reads `𝕁_𝔄 ≫ ν(ℝ̃) = ℝ` (`GTwoSCat.envelopeUnit_app_comp_extend`), and
`GTwoSCat.envelopeUnit_isBiuniversal` states the biuniversal property for every graded
`(Q, Π)`-2-supercategory `𝔅`.

The hom 2-supercategories `GradedTwoHom` have all graded (oplax) 2-natural transformations as
1-morphisms and all supermodifications as 2-morphisms.

Along the way: a 2-natural transformation between *arbitrary* 2-superfunctors
`𝕋, 𝕋' : 𝔄_{q,π} → 𝔅` is determined by its restriction along `𝕁`, and every 2-natural
transformation `𝕋𝕁 ⇒ 𝕋'𝕁` is such a restriction (`QPiTwoEnvelope.liftNatTrans`,
`QPiTwoEnvelope.restrictNatTransEquiv`); likewise for supermodifications. This needs no
structure on `𝔅`: it uses only the shift isomorphisms `Q⁰Π⁰F ≅ Q^mΠ^aF` of the envelope.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace QPiTwoEnvelope

/-! ### The shift isomorphisms -/

section Shift

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]
  {a b : QPiTwoEnvelope R B}

/-- The shift isomorphism `Q⁰Π⁰F ≅ Q^mΠ^aF` has parity `a`. -/
theorem shiftIso_hom_mem (f : a ⟶ b) :
    (shiftIso (R := R) f).hom ∈ parity (R := R) (Jm f.obj.obj : a ⟶ b) f f.par := by
  show 𝟙 f.obj.obj ∈ parity (R := R) f.obj.obj f.obj.obj (f.par + (0 + f.par))
  rw [zero_add, zmod2_add_self]
  exact id_mem _

theorem shiftIso_inv_mem (f : a ⟶ b) :
    (shiftIso (R := R) f).inv ∈ parity (R := R) f (Jm f.obj.obj : a ⟶ b) f.par :=
  inv_mem _ (shiftIso_hom_mem f)

/-- The shift isomorphism `Q⁰Π⁰F ≅ Q^mΠ^aF` has degree `m`. -/
theorem shiftIso_hom_mem_degree [∀ a b : B, GradedSupercategory R (a ⟶ b)] (f : a ⟶ b) :
    (shiftIso (R := R) f).hom ∈ degree (R := R) (Jm f.obj.obj : a ⟶ b) f f.obj.shift := by
  have h : (Envelope.ofHom (QEnvelope.ofHom (𝟙 f.obj.obj)) : (Jm f.obj.obj : a ⟶ b) ⟶ f) ∈
      degree (R := R) _ _ (0 + f.obj.shift - 0) :=
    ofHom_mem_degree (R := R) (id_mem_degree (R := R) f.obj.obj)
  rw [zero_add, sub_zero] at h
  exact h

theorem shiftIso_inv_mem_degree [∀ a b : B, GradedSupercategory R (a ⟶ b)] (f : a ⟶ b) :
    (shiftIso (R := R) f).inv ∈ degree (R := R) f (Jm f.obj.obj : a ⟶ b) (-f.obj.shift) :=
  inv_mem_degree _ (shiftIso_hom_mem_degree f)

/-- The shift isomorphism of `Q⁰Π⁰F` is the identity. -/
theorem shiftIso_Jm (f : a.as.as ⟶ b.as.as) :
    shiftIso (R := R) (Jm f : a ⟶ b) = Iso.refl _ := rfl

/-- Conjugating a 2-morphism `x^{n,b}_{m,a}` by the shift isomorphisms gives `x^{0,0}_{0,0}`. -/
theorem shiftIso_conj {f g : a ⟶ b} (η : f ⟶ g) :
    (shiftIso (R := R) f).hom ≫ η ≫ (shiftIso g).inv = J2 (toHom η) := by
  apply Envelope.hom_ext
  apply QEnvelope.hom_ext
  show 𝟙 _ ≫ toHom η ≫ 𝟙 _ = toHom η
  rw [Category.id_comp, Category.comp_id]

end Shift

/-! ### Restriction of transformations between arbitrary functors out of the envelope -/

section Restrict

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  {T T' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}

/-- The restriction `(X𝕁, x𝕁) : 𝕋𝕁 ⇒ 𝕋'𝕁` of a 2-natural transformation `(X, x) : 𝕋 ⇒ 𝕋'`
between arbitrary 2-superfunctors `𝔄_{q,π} → 𝔅`. -/
def restrictNatTrans (θ : TwoNatTrans T T') : TwoNatTrans (restrict T) (restrict T') where
  X a := θ.X ⟨⟨a⟩⟩
  x f := θ.x (Jm f)
  x_mem f := θ.x_mem (Jm f)
  naturality η := θ.naturality (J2 η)
  x_comp f g := θ.x_comp (Jm f) (Jm g)
  x_id a := θ.x_id ⟨⟨a⟩⟩

omit [TwoSupercategory R C] in
@[simp] theorem restrictNatTrans_X (θ : TwoNatTrans T T') (a : B) :
    (restrictNatTrans θ).X a = θ.X ⟨⟨a⟩⟩ := rfl

omit [TwoSupercategory R C] in
theorem restrictNatTrans_x (θ : TwoNatTrans T T') {a b : B} (f : a ⟶ b) :
    (restrictNatTrans θ).x f = θ.x (Jm f) := rfl

/-- The restriction `α𝕁` of a supermodification: `(α𝕁)_λ = α_λ`. -/
def restrictSupermodification {θ θ' : TwoNatTrans T T'} (α : θ ⟶ θ') :
    restrictNatTrans θ ⟶ restrictNatTrans θ' where
  app a := α.app ⟨⟨a⟩⟩
  naturality f := α.naturality (Jm f)

@[simp] theorem restrictSupermodification_app {θ θ' : TwoNatTrans T T'} (α : θ ⟶ θ') (a : B) :
    (restrictSupermodification α).app a = α.app ⟨⟨a⟩⟩ := rfl

/-- The components of a 2-natural transformation out of the envelope are determined by their
values on `Q⁰Π⁰F`: `x_{Q^mΠ^aF} = 𝕋(ι⁻¹) X ∘ x_F ∘ X 𝕋'(ι)` for the shift isomorphism `ι`. -/
theorem x_eq_shift (θ : TwoNatTrans T T') {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    θ.x f = T.map₂ (shiftIso f).inv ▷ θ.X b ≫ θ.x (Jm f.obj.obj) ≫
      θ.X a ◁ T'.map₂ (shiftIso f).hom := by
  rw [← θ.naturality (shiftIso f).hom, ← Category.assoc, ← comp_whiskerRight (R := R),
    ← T.map₂_comp, Iso.inv_hom_id, T.map₂_id, id_whiskerRight (R := R), Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The supermodification condition at `Q^mΠ^aF` follows from the condition at `Q⁰Π⁰F`, for a
family of homogeneous 2-morphisms. -/
theorem naturality_of_Jm_of_mem {θ θ' : TwoNatTrans T T'} {p : ZMod 2}
    (α : ∀ a, θ.X a ⟶ θ'.X a) (hα : ∀ a, α a ∈ parity (R := R) _ _ p)
    {a b : QPiTwoEnvelope R B} (f : a ⟶ b)
    (h : θ.x (Jm f.obj.obj : a ⟶ b) ≫ α a ▷ T'.map (Jm f.obj.obj) =
      T.map (Jm f.obj.obj) ◁ α b ≫ θ'.x (Jm f.obj.obj)) :
    θ.x f ≫ α a ▷ T'.map f = T.map f ◁ α b ≫ θ'.x f := by
  rw [x_eq_shift θ f, x_eq_shift θ' f]
  have h₁ := super_interchange (R := R) (hα a) (T'.map₂_mem (shiftIso_hom_mem (R := R) f))
  have h₂ := super_interchange (R := R) (T.map₂_mem (shiftIso_inv_mem (R := R) f)) (hα b)
  simp only [Category.assoc]
  rw [← koszulSign_smul_smul p f.par (θ.X a ◁ _ ≫ _), ← h₁, Linear.comp_smul,
    Linear.comp_smul, reassoc_of% h, ← Category.assoc (T.map₂ (shiftIso f).inv ▷ _),
    h₂, Linear.smul_comp, smul_smul, koszulSign_comm, koszulSign_mul_self, one_smul]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The supermodification condition at all 1-morphisms of the envelope follows from the
condition at the 1-morphisms `Q⁰Π⁰F`. -/
theorem naturality_of_Jm {θ θ' : TwoNatTrans T T'} (β : restrictNatTrans θ ⟶ restrictNatTrans θ')
    {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    θ.x f ≫ β.app a.as.as ▷ T'.map f = T.map f ◁ β.app b.as.as ≫ θ'.x f := by
  have h := fun p => naturality_of_Jm_of_mem (fun a => (TwoNatTrans.projHom p β).app a.as.as)
    (fun a => proj_mem (R := R) p (β.app a.as.as)) f
    ((TwoNatTrans.projHom p β).naturality f.obj.obj)
  have e : ∀ a : B, β.app a = (TwoNatTrans.projHom 0 β).app a + (TwoNatTrans.projHom 1 β).app a :=
    fun a => (proj_add_proj (R := R) (β.app a)).symm
  rw [e, e, add_whiskerRight (R := R), whiskerLeft_add (R := R), Preadditive.comp_add,
    Preadditive.add_comp, h 0, h 1]

/-- Every supermodification `θ𝕁 ⇛ θ'𝕁` is the restriction of a unique supermodification
`θ ⇛ θ'`, with the same components. -/
def liftSupermodification {θ θ' : TwoNatTrans T T'}
    (β : restrictNatTrans θ ⟶ restrictNatTrans θ') : θ ⟶ θ' where
  app a := β.app a.as.as
  naturality f := naturality_of_Jm β f

@[simp] theorem liftSupermodification_app {θ θ' : TwoNatTrans T T'}
    (β : restrictNatTrans θ ⟶ restrictNatTrans θ') (a : QPiTwoEnvelope R B) :
    (liftSupermodification β).app a = β.app a.as.as := rfl

theorem restrictSupermodification_liftSupermodification {θ θ' : TwoNatTrans T T'}
    (β : restrictNatTrans θ ⟶ restrictNatTrans θ') :
    restrictSupermodification (liftSupermodification β) = β :=
  TwoNatTrans.hom_ext fun _ => rfl

theorem liftSupermodification_restrictSupermodification {θ θ' : TwoNatTrans T T'}
    (α : θ ⟶ θ') : liftSupermodification (restrictSupermodification α) = α :=
  TwoNatTrans.hom_ext fun _ => rfl

/-! ### Lifting transformations along the restriction -/

section Lift

variable (ψ : TwoNatTrans (restrict T) (restrict T'))

/-- The 1-morphisms `Y_λ : 𝕋λ → 𝕋'λ` of the lift of `(Y, y) : 𝕋𝕁 ⇒ 𝕋'𝕁`. -/
def liftObj (a : QPiTwoEnvelope R B) : T.obj a ⟶ T'.obj a := ψ.X a.as.as

/-- The 2-morphism `y_F` at `Q⁰Π⁰F`. -/
def liftXJ {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    T.map (Jm f.obj.obj : a ⟶ b) ≫ liftObj ψ b ⟶ liftObj ψ a ≫ T'.map (Jm f.obj.obj) :=
  ψ.x f.obj.obj

/-- The components `𝕋(ι⁻¹) Y ∘ y_F ∘ Y 𝕋'(ι)` of the lift of `(Y, y) : 𝕋𝕁 ⇒ 𝕋'𝕁`. -/
def liftX {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    T.map f ≫ liftObj ψ b ⟶ liftObj ψ a ≫ T'.map f :=
  T.map₂ (shiftIso f).inv ▷ liftObj ψ b ≫ liftXJ ψ f ≫ liftObj ψ a ◁ T'.map₂ (shiftIso f).hom

theorem liftX_Jm {a b : QPiTwoEnvelope R B} (f : a.as.as ⟶ b.as.as) :
    liftX ψ (Jm f : a ⟶ b) = liftXJ ψ (Jm f : a ⟶ b) := by
  have h₁ : T.map₂ (shiftIso (R := R) (Jm f : a ⟶ b)).inv = 𝟙 _ := T.map₂_id _
  have h₂ : T'.map₂ (shiftIso (R := R) (Jm f : a ⟶ b)).hom = 𝟙 _ := T'.map₂_id _
  rw [liftX, h₁, h₂]
  erw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp, Category.comp_id]

theorem liftX_mem {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    liftX ψ f ∈ parity (R := R) _ _ 0 := by
  have := comp_mem (whiskerRight_mem (R := R) (liftObj ψ b)
    (T.map₂_mem (shiftIso_inv_mem (R := R) f)))
    (comp_mem (ψ.x_mem f.obj.obj) (whiskerLeft_mem (R := R) (liftObj ψ a)
      (T'.map₂_mem (shiftIso_hom_mem (R := R) f))))
  rwa [zero_add, zmod2_add_self] at this

theorem liftX_naturality {a b : QPiTwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    T.map₂ η ▷ liftObj ψ b ≫ liftX ψ g = liftX ψ f ≫ liftObj ψ a ◁ T'.map₂ η := by
  have k₁ : η ≫ (shiftIso g).inv = (shiftIso f).inv ≫ J2 (toHom η) := by
    rw [← shiftIso_conj, Iso.inv_hom_id_assoc]
  have k₂ : J2 (toHom η) ≫ (shiftIso g).hom = (shiftIso f).hom ≫ η := by
    rw [← shiftIso_conj]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn : T.map₂ (J2 (toHom η)) ▷ liftObj ψ b ≫ liftXJ ψ g =
      liftXJ ψ f ≫ liftObj ψ a ◁ T'.map₂ (J2 (toHom η)) :=
    ψ.naturality (toHom η)
  simp only [liftX]
  rw [← Category.assoc (T.map₂ η ▷ _), ← comp_whiskerRight (R := R), ← T.map₂_comp, k₁,
    T.map₂_comp, comp_whiskerRight (R := R), Category.assoc, reassoc_of% hn,
    ← whiskerLeft_comp (R := R), ← T'.map₂_comp, k₂, T'.map₂_comp, whiskerLeft_comp (R := R)]
  simp only [Category.assoc]

/-- The lift `(Y, ŷ) : 𝕋 ⇒ 𝕋'` of a 2-natural transformation `(Y, y) : 𝕋𝕁 ⇒ 𝕋'𝕁`, with
`ŷ_{Q^mΠ^aF} = 𝕋(ι⁻¹) Y ∘ y_F ∘ Y 𝕋'(ι)`. -/
def liftNatTrans : TwoNatTrans T T' where
  X := liftObj ψ
  x f := liftX ψ f
  x_mem f := liftX_mem ψ f
  naturality η := liftX_naturality ψ η
  x_comp f g := xcomp_of_J (F' := T) (G' := T') (liftObj ψ)
    (fun f => liftX ψ f) (fun f => liftX_mem ψ f) (fun η => liftX_naturality ψ η)
    (fun {a b c} f g => by
      have h₁ := liftX_Jm ψ (a := ⟨⟨a⟩⟩) (b := ⟨⟨c⟩⟩) (f ≫ g)
      have h₂ := liftX_Jm ψ (a := ⟨⟨a⟩⟩) (b := ⟨⟨b⟩⟩) f
      have h₃ := liftX_Jm ψ (a := ⟨⟨b⟩⟩) (b := ⟨⟨c⟩⟩) g
      simp only [xcompL, xcompR]
      erw [h₁, h₂, h₃]
      exact ψ.x_comp f g) f g
  x_id a := by
    have h : liftX ψ (𝟙 a) = liftXJ ψ (𝟙 a) := liftX_Jm ψ (a := a) (b := a) (𝟙 a.as.as)
    rw [h]
    exact ψ.x_id a.as.as

@[simp] theorem liftNatTrans_X (a : QPiTwoEnvelope R B) : (liftNatTrans ψ).X a = ψ.X a.as.as :=
  rfl

theorem liftNatTrans_x {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (liftNatTrans ψ).x f = liftX ψ f := rfl

/-- `(Y, ŷ)𝕁 = (Y, y)`. -/
theorem restrictNatTrans_liftNatTrans : restrictNatTrans (liftNatTrans ψ) = ψ :=
  TwoEnvelope.twoNatTrans_ext rfl fun f =>
    heq_of_eq (liftX_Jm ψ (a := ⟨⟨_⟩⟩) (b := ⟨⟨_⟩⟩) f)

end Lift

/-- A 2-natural transformation out of the envelope is the lift of its restriction. -/
theorem liftNatTrans_restrictNatTrans (θ : TwoNatTrans T T') :
    liftNatTrans (restrictNatTrans θ) = θ :=
  TwoEnvelope.twoNatTrans_ext rfl fun f => heq_of_eq (x_eq_shift θ f).symm

/-- **Lemma 6.11(ii), for arbitrary functors out of the envelope.** Restriction along `𝕁` is a
bijection from 2-natural transformations `𝕋 ⇒ 𝕋'` to 2-natural transformations `𝕋𝕁 ⇒ 𝕋'𝕁`, for
all 2-superfunctors `𝕋, 𝕋' : 𝔄_{q,π} → 𝔅` (not only extensions). -/
def restrictNatTransEquiv : TwoNatTrans T T' ≃ TwoNatTrans (restrict T) (restrict T') where
  toFun := restrictNatTrans
  invFun := liftNatTrans
  left_inv := liftNatTrans_restrictNatTrans
  right_inv := restrictNatTrans_liftNatTrans

/-- Restriction commutes with vertical composition. -/
theorem restrictNatTrans_vcomp [TwoSupercategory R B] {T'' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}
    (θ : TwoNatTrans T T') (θ' : TwoNatTrans T' T'') :
    restrictNatTrans (TwoNatTrans.vcomp θ θ') =
      TwoNatTrans.vcomp (restrictNatTrans θ) (restrictNatTrans θ') := rfl

/-- Restriction preserves identities. -/
theorem restrictNatTrans_id [TwoSupercategory R B] : restrictNatTrans (TwoNatTrans.id T) = TwoNatTrans.id (restrict T) :=
  rfl

/-! ### Grading -/

variable [∀ a b : B, GradedSupercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]

omit [∀ a b : B, GradedSupercategory R (a ⟶ b)] [TwoSupercategory R C] in
theorem restrictNatTrans_isGraded {θ : TwoNatTrans T T'} (hθ : θ.IsGraded) :
    (restrictNatTrans θ).IsGraded := fun f => hθ (Jm f)

theorem liftNatTrans_isGraded [GradedTwoSupercategory R C] (hT : T.IsGraded) (hT' : T'.IsGraded)
    {ψ : TwoNatTrans (restrict T) (restrict T')} (hψ : ψ.IsGraded) :
    (liftNatTrans ψ).IsGraded := fun {a b} f => by
  have := comp_mem_degree
    (GradedTwoSupercategory.whiskerRight_mem_degree (R := R) (liftObj ψ b)
      (hT.map₂_mem_degree (shiftIso_inv_mem_degree (R := R) f)))
    (comp_mem_degree (hψ f.obj.obj) (GradedTwoSupercategory.whiskerLeft_mem_degree (R := R)
      (liftObj ψ a) (hT'.map₂_mem_degree (shiftIso_hom_mem_degree (R := R) f))))
  rw [zero_add, neg_add_cancel] at this
  exact this

end Restrict

/-! ### Precomposition with `𝕁` on the hom 2-supercategories -/

section TwoHom

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R C] [GradedTwoSupercategory R C]

/-- Restriction of a graded transformation between bundled graded functors on the envelope. -/
def restrictGradedNatTrans {T T' : GradedTwoHom R (QPiTwoEnvelope R B) C} (θ : T ⟶ T') :
    restrictGraded T ⟶ restrictGraded T' :=
  ⟨restrictNatTrans θ.val, restrictNatTrans_isGraded θ.property⟩

variable (R B C) in
/-- Strict data of precomposition with `𝕁` on the hom 2-supercategories. -/
def restrictGradedCore :
    TwoSuperfunctor.StrictCore R (GradedTwoHom R (QPiTwoEnvelope R B) C) (GradedTwoHom R B C) where
  obj := restrictGraded
  map := restrictGradedNatTrans
  map₂ := restrictSupermodification
  map₂_id _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_comp _ _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_add _ _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_smul _ _ := TwoNatTrans.hom_ext fun _ => rfl
  map₂_mem hα a := hα ⟨⟨a⟩⟩
  map_comp _ _ := rfl
  map_id _ := rfl
  map₂_whiskerLeft _ _ _ _ := HEq.rfl
  map₂_whiskerRight _ _ := HEq.rfl
  map₂_associator _ _ _ := HEq.rfl
  map₂_leftUnitor _ := HEq.rfl
  map₂_rightUnitor _ := HEq.rfl

variable (R B C) in
/-- **Precomposition with `𝕁`**, `ℋom(𝔄_{q,π}, 𝔅) → ℋom(𝔄, ν𝔅)`, `𝕋 ↦ 𝕋𝕁`, as a strict
2-superfunctor of hom 2-supercategories of graded 2-superfunctors, all graded 2-natural
transformations and all supermodifications. -/
def restrictGradedTwoHom :
    TwoSuperfunctor R (GradedTwoHom R (QPiTwoEnvelope R B) C) (GradedTwoHom R B C) :=
  (restrictGradedCore R B C).toTwoSuperfunctor

@[simp] theorem restrictGradedTwoHom_obj (T : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    (restrictGradedTwoHom R B C).obj T = restrictGraded T := rfl

@[simp] theorem restrictGradedTwoHom_map {T T' : GradedTwoHom R (QPiTwoEnvelope R B) C}
    (θ : T ⟶ T') : (restrictGradedTwoHom R B C).map θ = restrictGradedNatTrans θ := rfl

@[simp] theorem restrictGradedTwoHom_map₂ {T T' : GradedTwoHom R (QPiTwoEnvelope R B) C}
    {θ ψ : T ⟶ T'} (α : θ ⟶ ψ) :
    (restrictGradedTwoHom R B C).map₂ α = restrictSupermodification α := rfl

theorem restrictGradedTwoHom_isStrict : (restrictGradedTwoHom R B C).IsStrict :=
  (restrictGradedCore R B C).isStrict

/-- Restriction preserves and reflects the parity and degree of supermodifications. -/
theorem restrictGradedTwoHom_map₂_isHomogeneous_iff
    {T T' : GradedTwoHom R (QPiTwoEnvelope R B) C} {θ ψ : T ⟶ T'} (α : θ ⟶ ψ) (p : ZMod 2)
    (n : ℤ) : ((restrictGradedTwoHom R B C).map₂ α).IsHomogeneous p n ↔ α.IsHomogeneous p n :=
  ⟨fun h a => h a.as.as, fun h a => h ⟨⟨a⟩⟩⟩

instance (T T' : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    ((restrictGradedTwoHom R B C).mapFunctor T T').Faithful where
  map_injective {θ ψ} α β h := TwoNatTrans.hom_ext fun a => by
    have := congrArg (fun γ : restrictNatTrans θ.val ⟶ restrictNatTrans ψ.val => γ.app a.as.as) h
    exact this

instance (T T' : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    ((restrictGradedTwoHom R B C).mapFunctor T T').Full where
  map_surjective {θ ψ} β := ⟨liftSupermodification (T := T.toTwoSuperfunctor)
    (T' := T'.toTwoSuperfunctor) (θ := θ.val) (θ' := ψ.val) β, TwoNatTrans.hom_ext fun _ => rfl⟩

omit [GradedTwoSupercategory R B] in
theorem eqToIso_hom_mem {T T' : GradedTwoHom R B C} {θ θ' : T ⟶ T'} (h : θ = θ') :
    (eqToIso h).hom ∈ parity (R := R) θ θ' 0 := by
  subst h; exact id_mem _

/-- Lifting graded transformations witnesses density of the local functor. -/
theorem restrictGradedTwoHom_evenlyDense (T T' : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    EvenlyDense R ((restrictGradedTwoHom R B C).mapFunctor T T') := fun ψ =>
  ⟨⟨liftNatTrans ψ.val, liftNatTrans_isGraded T.isGraded T'.isGraded ψ.property⟩,
    eqToIso (Subtype.ext (restrictNatTrans_liftNatTrans ψ.val)),
    eqToIso_hom_mem (Subtype.ext (restrictNatTrans_liftNatTrans ψ.val))⟩

/-- Precomposition with `𝕁` is a superequivalence on every transformation supercategory: this
is Lemma 6.11(ii) (with Remark 4.10 for supermodifications) for arbitrary graded
2-superfunctors out of the envelope. -/
def restrictGradedHomSuperequivalence (T T' : GradedTwoHom R (QPiTwoEnvelope R B) C) :
    Superequivalence R ((restrictGradedTwoHom R B C).mapFunctor T T') :=
  Superequivalence.ofFullyFaithful _ (restrictGradedTwoHom_evenlyDense T T')

variable [∀ a b : C, QPiSupercategory R (a ⟶ b)]

/-- `restrictGraded (extendGraded ℝ) = ℝ`. -/
theorem restrictGraded_extendGraded (F : GradedTwoHom R B C) :
    restrictGraded (extendGraded F) = F := by
  obtain ⟨F, hF⟩ := F
  simp only [restrictGraded, extendGraded, restrict_extend]

/-- **The triangle identity** `ℝ̃𝕁 = ℝ`: the extension is a strict section of precomposition
with `𝕁`, on objects of the hom 2-supercategories. -/
theorem restrictGradedTwoHom_obj_extendGradedTwoHom_obj (F : GradedTwoHom R B C) :
    (restrictGradedTwoHom R B C).obj ((extendGradedTwoHom R B C).obj F) = F :=
  restrictGraded_extendGraded F

omit [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B]
  [∀ a b : C, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R C]
  [∀ a b : C, QPiSupercategory R (a ⟶ b)] in
/-- On transformations between extensions, the restriction along `𝕁` of this file agrees with
the restriction `restrictTwoNatTrans` of Lemma 6.11(ii). -/
theorem restrictNatTrans_heq_restrictTwoNatTrans
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] [∀ a b : C, QPiSupercategory R (a ⟶ b)]
    {F G : TwoSuperfunctor R B C} (ψ : TwoNatTrans (extend F) (extend G)) :
    HEq (restrictNatTrans ψ) (restrictTwoNatTrans ψ) :=
  TwoNatTrans.hext_of_eq (restrict_extend F) (restrict_extend G) HEq.rfl fun _ => HEq.rfl

omit [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B]
  [∀ a b : C, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R C]
  [∀ a b : C, QPiSupercategory R (a ⟶ b)] in
/-- **The triangle identity on 2-natural transformations**: `(X̃, x̃)𝕁 = (X, x)`. -/
theorem restrictNatTrans_extendTwoNatTrans
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] [∀ a b : C, QPiSupercategory R (a ⟶ b)]
    {F G : TwoSuperfunctor R B C} (θ : TwoNatTrans F G) :
    HEq (restrictNatTrans (extendTwoNatTrans θ)) θ :=
  (restrictNatTrans_heq_restrictTwoNatTrans _).trans
    (heq_of_eq (restrictTwoNatTrans_extendTwoNatTrans θ))

omit [GradedTwoSupercategory R B] [∀ a b : C, QPiSupercategory R (a ⟶ b)] in
theorem _root_.StringDiagrams.GradedTwoHom.hom_heq_of_val {F F' G G' : GradedTwoHom R B C}
    (hF : F = F') (hG : G = G') {θ : F ⟶ G} {θ' : F' ⟶ G'} (h : HEq θ.val θ'.val) :
    HEq θ θ' := by
  subst hF
  subst hG
  exact heq_of_eq (Subtype.ext (eq_of_heq h))

/-- **The triangle identity** on the 1-morphisms of the hom 2-supercategories: restricting the
extension of a graded 2-natural transformation gives it back. -/
theorem restrictGradedTwoHom_map_extendGradedTwoHom_map {F G : GradedTwoHom R B C} (θ : F ⟶ G) :
    HEq ((restrictGradedTwoHom R B C).map ((extendGradedTwoHom R B C).map θ)) θ :=
  GradedTwoHom.hom_heq_of_val (restrictGraded_extendGraded F) (restrictGraded_extendGraded G)
    (restrictNatTrans_extendTwoNatTrans θ.val)

/-- **The triangle identity** on supermodifications: `α̃𝕁 = α` componentwise. -/
theorem restrictGradedTwoHom_map₂_extendGradedTwoHom_map₂ {F G : GradedTwoHom R B C}
    {θ ψ : F ⟶ G} (α : θ ⟶ ψ) (a : B) :
    ((restrictGradedTwoHom R B C).map₂ ((extendGradedTwoHom R B C).map₂ α)).app a = α.app a :=
  rfl

/-- **The analogue of Theorem 4.9, as a biuniversal arrow.** Precomposition with `𝕁`
is locally a superequivalence, and every graded 2-superfunctor `𝔄 → 𝔅` is (equal to) the
restriction of a graded 2-superfunctor `𝔄_{q,π} → 𝔅`, namely its extension. -/
theorem restrictGradedTwoHom_isLocalTwoSuperequivalence :
    (restrictGradedTwoHom R B C).IsLocalTwoSuperequivalence where
  hom T T' := ⟨restrictGradedHomSuperequivalence T T'⟩
  essSurj F := ⟨extendGraded F, by
    rw [restrictGradedTwoHom_obj, restrictGraded_extendGraded]
    exact Superequivalent.refl (R := R) F⟩

/-- **Brundan–Ellis, after Lemma 6.11 (`-_{q,π}` is left 2-adjoint to `ν`), as a
biuniversal arrow.** For a graded 2-supercategory `𝔄` and a graded 2-supercategory `𝔅`
whose morphism supercategories are graded `(Q, Π)`-supercategories, precomposition with
`𝕁 : 𝔄 → 𝔄_{q,π}` is a 2-superequivalence `ℋom(𝔄_{q,π}, 𝔅) → ℋom(𝔄, ν𝔅)` of hom
2-supercategories (all graded oplax transformations, all supermodifications). -/
theorem restrictGradedTwoHom_isTwoSuperequivalence :
    (restrictGradedTwoHom R B C).IsTwoSuperequivalence :=
  restrictGradedTwoHom_isLocalTwoSuperequivalence.isTwoSuperequivalence

end TwoHom

end QPiTwoEnvelope

/-! ### The biuniversal arrows on the 1-truncations -/

namespace GTwoSCat

variable {R : Type w} [CommRing R]

/-- Precomposition with the component `𝕁_𝔄` of the unit `𝟭 ⟶ -_{q,π} ⋙ ν` is the restriction
along `𝕁`. -/
theorem envelopeUnit_app_comp_val (A : GTwoSCat.{w, w₁, v₁, u₁} R)
    {B : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (T : envelope.obj A ⟶ B) :
    (envelopeUnit.app A ≫ QPiTwoGSCat.forget.map T).1 = QPiTwoEnvelope.restrict T.1 :=
  (QPiTwoEnvelope.restrict_eq_comp T.1).symm

/-- The extension `ℝ̃ : 𝔄_{q,π} → 𝔅` of a graded 2-superfunctor `ℝ : 𝔄 → ν𝔅` (Lemma 6.11(i)),
as a morphism of `(Q, Π)-2-GSCat`. -/
def extend {A : GTwoSCat.{w, w₁, v₁, u₁} R} {B : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
    (F : A ⟶ B.toGTwoSCat) : envelope.obj A ⟶ B :=
  ⟨QPiTwoEnvelope.extendQPi F.1, QPiTwoEnvelope.extendQPi_isGraded F.1 F.2⟩

/-- **The triangle identity** `𝕁_𝔄 ≫ ν(ℝ̃) = ℝ` (Lemma 6.11(i)). -/
theorem envelopeUnit_app_comp_extend {A : GTwoSCat.{w, w₁, v₁, u₁} R}
    {B : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : A ⟶ B.toGTwoSCat) :
    envelopeUnit.app A ≫ QPiTwoGSCat.forget.map (extend F) = F :=
  Subtype.ext (QPiTwoEnvelope.twoJ_comp_extendQPi F.1)

/-- **Brundan–Ellis, after Lemma 6.11: `-_{q,π}` is left 2-adjoint to `ν`, as biuniversal
arrows.** For every graded 2-supercategory `𝔄` and graded `(Q, Π)`-2-supercategory `𝔅`,
precomposition with the component `𝕁_𝔄 : 𝔄 → ν(𝔄_{q,π})` of the unit `GTwoSCat.envelopeUnit`
(`envelopeUnit_app_comp_val`) is a 2-superequivalence `ℋom(𝔄_{q,π}, 𝔅) → ℋom(𝔄, ν𝔅)` of hom
2-supercategories of graded 2-superfunctors, all graded 2-natural transformations and all
supermodifications; the morphism supercategories of `𝔅` carry the `(Q, Π)` structures
`Q = q_μ -`, `Π = π_μ -` of Lemma 6.11. -/
theorem envelopeUnit_isBiuniversal (A : GTwoSCat.{w, w₁, v₁, u₁} R)
    (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    letI : ∀ a b : B, QPiSupercategory R (a ⟶ b) := fun a b =>
      QPiTwoSupercategory.homQPiLeft a b
    (QPiTwoEnvelope.restrictGradedTwoHom R A B).IsTwoSuperequivalence :=
  letI : ∀ a b : B, QPiSupercategory R (a ⟶ b) := fun a b =>
    QPiTwoSupercategory.homQPiLeft a b
  QPiTwoEnvelope.restrictGradedTwoHom_isTwoSuperequivalence

end GTwoSCat

end StringDiagrams
