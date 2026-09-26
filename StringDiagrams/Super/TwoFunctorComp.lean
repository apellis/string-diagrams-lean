import StringDiagrams.Super.TwoFunctor
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Oplax

/-!
# Composition of 2-superfunctors and of 2-natural transformations

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 2.2(ii)–(iii): 2-superfunctors compose (`TwoSuperfunctor.comp`, with
`c_{G∘F} = G(c_F) ∘ c_G` and `i_{G∘F} = G(i_F) ∘ i_G`), and 2-natural transformations have
identities and vertical composites (`TwoNatTrans.id`, `TwoNatTrans.vcomp`).

## Implementation

The coherence data of 2-superfunctors and 2-natural transformations consists of even
2-morphisms, so a 2-superfunctor `ℝ : 𝔄 → 𝔅` induces an oplax functor of the underlying
bicategories (`TwoSuperfunctor.toOplax`, with Mathlib's oplax conventions
`mapComp := c⁻¹`, `mapId := i⁻¹`), and a 2-natural transformation induces an oplax
transformation (`TwoNatTrans.toOplaxTrans`). Conversely an oplax transformation which is also
natural with respect to odd 2-morphisms is a 2-natural transformation
(`TwoNatTrans.ofOplaxTrans`). We obtain the identity and the vertical composite of
2-natural transformations from Mathlib's.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃ w

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  {D : Type u₃} [BicategoryStruct.{w₃, v₃} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)]
  [∀ a b : D, Supercategory R (a ⟶ b)] [TwoSupercategory R D]

namespace TwoSuperfunctor

/-- The composite `𝕊 ∘ ℝ` of 2-superfunctors (Definition 2.2(ii)): `c_{𝕊ℝ} := 𝕊(c_ℝ) ∘ c_𝕊` and
`i_{𝕊ℝ} := 𝕊(i_ℝ) ∘ i_𝕊`. -/
@[simps]
def comp (F : TwoSuperfunctor R B C) (G : TwoSuperfunctor R C D) : TwoSuperfunctor R B D where
  obj a := G.obj (F.obj a)
  map f := G.map (F.map f)
  map₂ η := G.map₂ (F.map₂ η)
  map₂_id f := by rw [F.map₂_id, G.map₂_id]
  map₂_comp η θ := by rw [F.map₂_comp, G.map₂_comp]
  map₂_add η θ := by rw [F.map₂_add, G.map₂_add]
  map₂_smul r η := by rw [F.map₂_smul, G.map₂_smul]
  map₂_mem h := G.map₂_mem (F.map₂_mem h)
  mapComp f g := G.mapComp (F.map f) (F.map g) ≪≫ G.map₂Iso (F.mapComp f g)
  mapId a := G.mapId (F.obj a) ≪≫ G.map₂Iso (F.mapId a)
  mapComp_hom_mem f g := by
    simpa using comp_mem (G.mapComp_hom_mem (F.map f) (F.map g))
      (G.map₂_mem (F.mapComp_hom_mem f g))
  mapId_hom_mem a := by
    simpa using comp_mem (G.mapId_hom_mem (F.obj a)) (G.map₂_mem (F.mapId_hom_mem a))
  mapComp_naturality_left η g := by
    simp only [Iso.trans_hom, map₂Iso_hom]
    rw [← Category.assoc, G.mapComp_naturality_left, Category.assoc, ← G.map₂_comp,
      F.mapComp_naturality_left, G.map₂_comp, ← Category.assoc]
  mapComp_naturality_right f _ _ η := by
    simp only [Iso.trans_hom, map₂Iso_hom]
    rw [← Category.assoc, G.mapComp_naturality_right, Category.assoc, ← G.map₂_comp,
      F.mapComp_naturality_right, G.map₂_comp, ← Category.assoc]
  map₂_associator f g h := by
    simp only [Iso.trans_hom, map₂Iso_hom, whiskerLeft_comp' R, comp_whiskerRight' R,
      Category.assoc]
    rw [G.mapComp_naturality_right_assoc, ← G.map₂_comp, ← G.map₂_comp, F.map₂_associator,
      G.map₂_comp, G.map₂_comp, G.map₂_associator_assoc, ← G.mapComp_naturality_left_assoc]
  map₂_leftUnitor f := by
    simp only [Iso.trans_hom, map₂Iso_hom, comp_whiskerRight' R, Category.assoc]
    rw [G.mapComp_naturality_left_assoc, ← G.map₂_comp, ← G.map₂_comp, F.map₂_leftUnitor,
      G.map₂_leftUnitor]
  map₂_rightUnitor f := by
    simp only [Iso.trans_hom, map₂Iso_hom, whiskerLeft_comp' R, Category.assoc]
    rw [G.mapComp_naturality_right_assoc, ← G.map₂_comp, ← G.map₂_comp, F.map₂_rightUnitor,
      G.map₂_rightUnitor]

/-- The oplax functor of underlying bicategories (even 2-morphisms) induced by a
2-superfunctor, with Mathlib's oplax conventions `mapComp f g := c⁻¹`, `mapId a := i⁻¹`. -/
def toOplax (F : TwoSuperfunctor R B C) : OplaxFunctor (Underlying2 R B) (Underlying2 R C) where
  obj a := ⟨F.obj a.obj⟩
  map f := ⟨F.map f.obj⟩
  map₂ η := ⟨F.map₂ η.1, F.map₂_mem η.2⟩
  map₂_id f := Subtype.ext (F.map₂_id f.obj)
  map₂_comp η θ := Subtype.ext (F.map₂_comp η.1 θ.1)
  mapId a := ⟨(F.mapId a.obj).inv, inv_mem _ (F.mapId_hom_mem a.obj)⟩
  mapComp f g := ⟨(F.mapComp f.obj g.obj).inv, inv_mem _ (F.mapComp_hom_mem _ _)⟩
  mapComp_naturality_left η g := Subtype.ext (by
    change F.map₂ (η.1 ▷ g.obj) ≫ (F.mapComp _ g.obj).inv =
      (F.mapComp _ g.obj).inv ≫ F.map₂ η.1 ▷ F.map g.obj
    rw [Iso.comp_inv_eq, Category.assoc, F.mapComp_naturality_left, Iso.inv_hom_id_assoc])
  mapComp_naturality_right f _ _ η := Subtype.ext (by
    change F.map₂ (f.obj ◁ η.1) ≫ (F.mapComp f.obj _).inv =
      (F.mapComp f.obj _).inv ≫ F.map f.obj ◁ F.map₂ η.1
    rw [Iso.comp_inv_eq, Category.assoc, F.mapComp_naturality_right, Iso.inv_hom_id_assoc])
  map₂_associator f g h := Subtype.ext (by
    change F.map₂ (associator f.obj g.obj h.obj).hom ≫ (F.mapComp f.obj (g.obj ≫ h.obj)).inv ≫
        F.map f.obj ◁ (F.mapComp g.obj h.obj).inv =
      (F.mapComp (f.obj ≫ g.obj) h.obj).inv ≫ (F.mapComp f.obj g.obj).inv ▷ F.map h.obj ≫
        (associator (F.map f.obj) (F.map g.obj) (F.map h.obj)).hom
    have e : whiskerLeftIso (R := R) (F.map f.obj) (F.mapComp g.obj h.obj) ≪≫
        F.mapComp f.obj (g.obj ≫ h.obj) ≪≫ F.map₂Iso (associator f.obj g.obj h.obj).symm =
      (associator (F.map f.obj) (F.map g.obj) (F.map h.obj)).symm ≪≫
        whiskerRightIso (R := R) (F.mapComp f.obj g.obj) (F.map h.obj) ≪≫
          F.mapComp (f.obj ≫ g.obj) h.obj := Iso.ext (by simpa using F.map₂_associator _ _ _)
    simpa using congrArg Iso.inv e)
  map₂_leftUnitor f := Subtype.ext (by
    change F.map₂ (leftUnitor f.obj).hom = (F.mapComp (𝟙 _) f.obj).inv ≫
      (F.mapId _).inv ▷ F.map f.obj ≫ (leftUnitor (F.map f.obj)).hom
    rw [← F.map₂_leftUnitor]
    simp only [inv_hom_whiskerRight_assoc R, Iso.inv_hom_id_assoc])
  map₂_rightUnitor f := Subtype.ext (by
    change F.map₂ (rightUnitor f.obj).hom = (F.mapComp f.obj (𝟙 _)).inv ≫
      F.map f.obj ◁ (F.mapId _).inv ≫ (rightUnitor (F.map f.obj)).hom
    rw [← F.map₂_rightUnitor]
    simp only [whiskerLeft_inv_hom_assoc R, Iso.inv_hom_id_assoc])

end TwoSuperfunctor

namespace TwoNatTrans

variable {F G H : TwoSuperfunctor R B C}

omit [TwoSupercategory R B] in
/-- The first coherence condition of a 2-natural transformation, solved for `x_{GF}`. -/
theorem x_comp_eq (θ : TwoNatTrans F G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    θ.x (f ≫ g) = (F.mapComp f g).inv ▷ θ.X c ≫ (associator (F.map f) (F.map g) (θ.X c)).hom ≫
      F.map f ◁ θ.x g ≫ (associator (F.map f) (θ.X b) (G.map g)).inv ≫ θ.x f ▷ G.map g ≫
        (associator (θ.X a) (G.map f) (G.map g)).hom ≫ θ.X a ◁ (G.mapComp f g).hom := by
  rw [← θ.x_comp, inv_hom_whiskerRight_assoc R]

omit [TwoSupercategory R B] in
/-- The second coherence condition of a 2-natural transformation, solved for `x_{1_λ}`. -/
theorem x_id_eq (θ : TwoNatTrans F G) (a : B) :
    θ.x (𝟙 a) = (F.mapId a).inv ▷ θ.X a ≫ (leftUnitor (θ.X a)).hom ≫
      (rightUnitor (θ.X a)).inv ≫ θ.X a ◁ (G.mapId a).hom := by
  rw [← θ.x_id]
  simp only [Iso.inv_hom_id_assoc, inv_hom_whiskerRight_assoc R, Iso.hom_inv_id_assoc]

/-- A 2-natural transformation as an oplax transformation of the induced oplax functors of the
underlying bicategories. -/
def toOplaxTrans (θ : TwoNatTrans F G) : F.toOplax ⟶ G.toOplax where
  app a := ⟨θ.X a.obj⟩
  naturality f := ⟨θ.x f.obj, θ.x_mem f.obj⟩
  naturality_naturality η := Subtype.ext (θ.naturality η.1)
  naturality_id a := Subtype.ext (by
    change θ.x (𝟙 a.obj) ≫ θ.X a.obj ◁ (G.mapId a.obj).inv =
      (F.mapId a.obj).inv ▷ θ.X a.obj ≫ (leftUnitor (θ.X a.obj)).hom ≫
        (rightUnitor (θ.X a.obj)).inv
    rw [x_id_eq]
    simp only [Category.assoc, whiskerLeft_hom_inv R, Category.comp_id])
  naturality_comp f g := Subtype.ext (by
    change θ.x (f.obj ≫ g.obj) ≫ θ.X _ ◁ (G.mapComp f.obj g.obj).inv =
      (F.mapComp f.obj g.obj).inv ▷ θ.X _ ≫ (associator (F.map f.obj) (F.map g.obj) (θ.X _)).hom ≫
        F.map f.obj ◁ θ.x g.obj ≫ (associator (F.map f.obj) (θ.X _) (G.map g.obj)).inv ≫
          θ.x f.obj ▷ G.map g.obj ≫ (associator (θ.X _) (G.map f.obj) (G.map g.obj)).hom
    rw [x_comp_eq]
    simp only [Category.assoc, whiskerLeft_hom_inv R, Category.comp_id])

@[simp] theorem toOplaxTrans_app (θ : TwoNatTrans F G) (a : Underlying2 R B) :
    ((toOplaxTrans θ).app a).obj = θ.X a.obj := rfl

@[simp] theorem toOplaxTrans_naturality (θ : TwoNatTrans F G) {a b : Underlying2 R B}
    (f : a ⟶ b) : ((toOplaxTrans θ).naturality f).1 = θ.x f.obj := rfl

/-- An oplax transformation of the induced oplax functors which is natural with respect to all
(not necessarily even) 2-morphisms, as a 2-natural transformation. -/
def ofOplaxTrans (η : F.toOplax ⟶ G.toOplax)
    (nat : ∀ {a b : B} {f g : a ⟶ b} (ε : f ⟶ g),
      F.map₂ ε ▷ (η.app ⟨b⟩).obj ≫ (η.naturality (Underlying2.hom1 g)).1 =
        (η.naturality (Underlying2.hom1 f)).1 ≫ (η.app ⟨a⟩).obj ◁ G.map₂ ε) :
    TwoNatTrans F G where
  X a := (η.app ⟨a⟩).obj
  x f := (η.naturality (Underlying2.hom1 f)).1
  x_mem f := (η.naturality (Underlying2.hom1 f)).2
  naturality ε := nat ε
  x_comp {a b c} f g := by
    have h := congrArg Subtype.val
      (η.naturality_comp (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩) (Underlying2.hom1 f)
        (Underlying2.hom1 g))
    change (η.naturality (Underlying2.hom1 f ≫ Underlying2.hom1 g)).1 ≫
        (η.app ⟨a⟩).obj ◁ (G.mapComp f g).inv =
      (F.mapComp f g).inv ▷ (η.app ⟨c⟩).obj ≫
        (associator (F.map f) (F.map g) (η.app ⟨c⟩).obj).hom ≫
          F.map f ◁ (η.naturality (Underlying2.hom1 g)).1 ≫
            (associator (F.map f) (η.app ⟨b⟩).obj (G.map g)).inv ≫
              (η.naturality (Underlying2.hom1 f)).1 ▷ G.map g ≫
                (associator (η.app ⟨a⟩).obj (G.map f) (G.map g)).hom at h
    change (F.mapComp f g).hom ▷ (η.app ⟨c⟩).obj ≫
        (η.naturality (Underlying2.hom1 f ≫ Underlying2.hom1 g)).1 = _
    rw [← cancel_mono (whiskerLeftIso (R := R) (η.app ⟨a⟩).obj (G.mapComp f g).symm).hom]
    simp only [whiskerLeftIso_hom, Iso.symm_hom]
    rw [Category.assoc, h]
    simp only [Category.assoc, whiskerLeft_hom_inv R, Category.comp_id,
      hom_inv_whiskerRight_assoc R]
  x_id a := by
    have h := congrArg Subtype.val (η.naturality_id (⟨a⟩ : Underlying2 R B))
    change (η.naturality (𝟙 (⟨a⟩ : Underlying2 R B))).1 ≫
        (η.app ⟨a⟩).obj ◁ (G.mapId a).inv =
      (F.mapId a).inv ▷ (η.app ⟨a⟩).obj ≫ (leftUnitor (η.app ⟨a⟩).obj).hom ≫
        (rightUnitor (η.app ⟨a⟩).obj).inv at h
    change _ ≫ _ ≫ _ ≫ (η.naturality (𝟙 (⟨a⟩ : Underlying2 R B))).1 = _
    rw [← cancel_mono (whiskerLeftIso (R := R) (η.app ⟨a⟩).obj (G.mapId a).symm).hom]
    simp only [whiskerLeftIso_hom, Iso.symm_hom]
    simp only [Category.assoc, h, whiskerLeft_hom_inv R, hom_inv_whiskerRight_assoc R,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id]

variable (F) in
/-- The identity 2-natural transformation: `X_λ = 1`, `x_F = λ_F⁻¹ ∘ ρ_F`. -/
def id : TwoNatTrans F F :=
  ofOplaxTrans (𝟙 F.toOplax) (fun ε => by
    change F.map₂ ε ▷ 𝟙 _ ≫ (rightUnitor _).hom ≫ (leftUnitor _).inv =
      ((rightUnitor _).hom ≫ (leftUnitor _).inv) ≫ 𝟙 _ ◁ F.map₂ ε
    rw [rightUnitor_naturality_assoc R, leftUnitor_inv_naturality R, Category.assoc])

@[simp] theorem id_X (a : B) : (id F).X a = 𝟙 (F.obj a) := rfl

theorem id_x {a b : B} (f : a ⟶ b) :
    (id F).x f = (rightUnitor (F.map f)).hom ≫ (leftUnitor (F.map f)).inv := rfl

/-- The vertical composite of 2-natural transformations: `X_λ := Y_λ X_λ` (i.e.
`X λ ≫ Y λ`), with `x` and `y` composed using the associators. -/
def vcomp (θ : TwoNatTrans F G) (θ' : TwoNatTrans G H) : TwoNatTrans F H :=
  ofOplaxTrans (toOplaxTrans θ ≫ toOplaxTrans θ') (by
    intro a b f g ε
    change F.map₂ ε ▷ (θ.X b ≫ θ'.X b) ≫ (associator (F.map g) (θ.X b) (θ'.X b)).inv ≫
        θ.x g ▷ θ'.X b ≫ (associator (θ.X a) (G.map g) (θ'.X b)).hom ≫
          θ.X a ◁ θ'.x g ≫ (associator (θ.X a) (θ'.X a) (H.map g)).inv =
      ((associator (F.map f) (θ.X b) (θ'.X b)).inv ≫ θ.x f ▷ θ'.X b ≫
          (associator (θ.X a) (G.map f) (θ'.X b)).hom ≫ θ.X a ◁ θ'.x f ≫
            (associator (θ.X a) (θ'.X a) (H.map f)).inv) ≫ (θ.X a ≫ θ'.X a) ◁ H.map₂ ε
    rw [associator_inv_naturality_left_assoc R, ← comp_whiskerRight'_assoc R, θ.naturality,
      comp_whiskerRight'_assoc R, associator_naturality_middle_assoc R,
      ← whiskerLeft_comp'_assoc R, θ'.naturality, whiskerLeft_comp'_assoc R,
      associator_inv_naturality_right R]
    simp only [Category.assoc])

@[simp] theorem vcomp_X (θ : TwoNatTrans F G) (θ' : TwoNatTrans G H) (a : B) :
    (vcomp θ θ').X a = θ.X a ≫ θ'.X a := rfl

theorem vcomp_x (θ : TwoNatTrans F G) (θ' : TwoNatTrans G H) {a b : B} (f : a ⟶ b) :
    (vcomp θ θ').x f = (associator (F.map f) (θ.X b) (θ'.X b)).inv ≫ θ.x f ▷ θ'.X b ≫
      (associator (θ.X a) (G.map f) (θ'.X b)).hom ≫ θ.X a ◁ θ'.x f ≫
        (associator (θ.X a) (θ'.X a) (H.map f)).inv := rfl

end TwoNatTrans

end StringDiagrams

end
