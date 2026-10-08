import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Whiskering oplax transformations by pseudofunctors

For pseudofunctors `P : B ⥤ C`, `F, G : C ⥤ D`, `H : D ⥤ E` and an oplax transformation
`η : F ⇒ G`, the whiskered oplax transformations `η P : P ⋙ F ⇒ P ⋙ G`
(`Oplax.OplaxTrans.precomp`, components `η_{Pλ}`, `η_{P f}`) and `H η : F ⋙ H ⇒ G ⋙ H`
(`Oplax.OplaxTrans.postcomp`, components `H η_λ`, `c ∘ H η_f ∘ c⁻¹`).
-/

namespace CategoryTheory

open Bicategory

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Oplax.OplaxTrans

theorem map₂_associator_inv' {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂}
    [Bicategory.{w₂, v₂} C] (H : Pseudofunctor B C) {a b c d : B} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) :
    H.map₂ (α_ f g h).inv = (H.mapComp f (g ≫ h)).hom ≫ H.map f ◁ (H.mapComp g h).hom ≫
      (α_ (H.map f) (H.map g) (H.map h)).inv ≫ (H.mapComp f g).inv ▷ H.map h ≫
        (H.mapComp (f ≫ g) h).inv := by
  rw [← cancel_mono (H.map₂ (α_ f g h).hom), ← H.map₂_comp, Iso.inv_hom_id, H.map₂_id,
    Pseudofunctor.map₂_associator]
  simp

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {D : Type u₃} [Bicategory.{w₃, v₃} D] {E : Type u₄} [Bicategory.{w₄, v₄} E]

/-- Precomposition of an oplax transformation of pseudofunctors with a pseudofunctor. -/
@[simps]
def precomp (P : Pseudofunctor B C) {F G : Pseudofunctor C D}
    (η : Oplax.OplaxTrans F.toOplax G.toOplax) :
    Oplax.OplaxTrans (P.comp F).toOplax (P.comp G).toOplax where
  app a := η.app (P.obj a)
  naturality f := η.naturality (P.map f)
  naturality_naturality ε := η.naturality_naturality (P.map₂ ε)
  naturality_id a := by
    have h1 := η.naturality_naturality (P.mapId a).hom
    have h2 := η.naturality_id (P.obj a)
    simp only [Pseudofunctor.toOplax_toPrelaxFunctor, Pseudofunctor.toOplax_mapId,
      Pseudofunctor.comp_mapId] at h1 h2 ⊢
    change η.naturality (P.map (𝟙 a)) ≫ η.app (P.obj a) ◁
        (G.map₂ (P.mapId a).hom ≫ (G.mapId (P.obj a)).hom) =
      (F.map₂ (P.mapId a).hom ≫ (F.mapId (P.obj a)).hom) ▷ η.app (P.obj a) ≫
        (λ_ (η.app (P.obj a))).hom ≫ (ρ_ (η.app (P.obj a))).inv
    rw [whiskerLeft_comp, ← Category.assoc, ← h1, Category.assoc, h2, comp_whiskerRight,
      Category.assoc]
  naturality_comp {a b c} f g := by
    have h1 := η.naturality_naturality (P.mapComp f g).hom
    have h2 := η.naturality_comp (P.map f) (P.map g)
    simp only [Pseudofunctor.toOplax_toPrelaxFunctor, Pseudofunctor.toOplax_mapComp] at h1 h2
    change η.naturality (P.map (f ≫ g)) ≫ η.app (P.obj a) ◁
        (G.map₂ (P.mapComp f g).hom ≫ (G.mapComp (P.map f) (P.map g)).hom) =
      (F.map₂ (P.mapComp f g).hom ≫ (F.mapComp (P.map f) (P.map g)).hom) ▷ η.app (P.obj c) ≫
        (α_ (F.map (P.map f)) (F.map (P.map g)) (η.app (P.obj c))).hom ≫
          F.map (P.map f) ◁ η.naturality (P.map g) ≫
            (α_ (F.map (P.map f)) (η.app (P.obj b)) (G.map (P.map g))).inv ≫
              η.naturality (P.map f) ▷ G.map (P.map g) ≫
                (α_ (η.app (P.obj a)) (G.map (P.map f)) (G.map (P.map g))).hom
    rw [whiskerLeft_comp, ← Category.assoc, ← h1, Category.assoc, h2, comp_whiskerRight,
      Category.assoc]

/-- Postcomposition of an oplax transformation of pseudofunctors with a pseudofunctor. -/
@[simps]
def postcomp {F G : Pseudofunctor C D} (η : Oplax.OplaxTrans F.toOplax G.toOplax)
    (H : Pseudofunctor D E) : Oplax.OplaxTrans (F.comp H).toOplax (G.comp H).toOplax where
  app a := H.map (η.app a)
  naturality {a b} f := (H.mapComp (F.map f) (η.app b)).inv ≫ H.map₂ (η.naturality f) ≫
    (H.mapComp (η.app a) (G.map f)).hom
  naturality_naturality {a b f g} ε := by
    have h := congrArg H.map₂ (η.naturality_naturality ε)
    simp only [Pseudofunctor.toOplax_toPrelaxFunctor, PrelaxFunctor.map₂_comp,
      Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_whisker_right, Category.assoc] at h
    change H.map₂ (F.map₂ ε) ▷ H.map (η.app b) ≫ (H.mapComp (F.map g) (η.app b)).inv ≫
        H.map₂ (η.naturality g) ≫ (H.mapComp (η.app a) (G.map g)).hom =
      ((H.mapComp (F.map f) (η.app b)).inv ≫ H.map₂ (η.naturality f) ≫
        (H.mapComp (η.app a) (G.map f)).hom) ≫ H.map (η.app a) ◁ H.map₂ (G.map₂ ε)
    rw [← cancel_epi (H.mapComp (F.map f) (η.app b)).hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% h]
    simp
  naturality_id a := by
    have h0 : η.naturality (𝟙 a) ≫ η.app a ◁ (G.mapId a).hom ≫ (ρ_ (η.app a)).hom =
        (F.mapId a).hom ▷ η.app a ≫ (λ_ (η.app a)).hom := by
      have := η.naturality_id a
      simp only [Pseudofunctor.toOplax_toPrelaxFunctor, Pseudofunctor.toOplax_mapId] at this
      rw [← Category.assoc, this]
      simp
    have h := congrArg H.map₂ h0
    simp only [PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_left,
      Pseudofunctor.map₂_whisker_right, Pseudofunctor.map₂_left_unitor,
      Pseudofunctor.map₂_right_unitor, Category.assoc] at h
    change ((H.mapComp (F.map (𝟙 a)) (η.app a)).inv ≫ H.map₂ (η.naturality (𝟙 a)) ≫
        (H.mapComp (η.app a) (G.map (𝟙 a))).hom) ≫
        H.map (η.app a) ◁ (H.map₂ (G.mapId a).hom ≫ (H.mapId (G.obj a)).hom) =
      (H.map₂ (F.mapId a).hom ≫ (H.mapId (F.obj a)).hom) ▷ H.map (η.app a) ≫
        (λ_ (H.map (η.app a))).hom ≫ (ρ_ (H.map (η.app a))).inv
    rw [← cancel_mono (ρ_ (H.map (η.app a))).hom, ← cancel_epi
      (H.mapComp (F.map (𝟙 a)) (η.app a)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc,
      whiskerLeft_comp, comp_whiskerRight]
    simpa using h
  naturality_comp {a b c} f g := by
    have h0 : η.naturality (f ≫ g) = (F.mapComp f g).hom ▷ η.app c ≫
        (α_ (F.map f) (F.map g) (η.app c)).hom ≫ F.map f ◁ η.naturality g ≫
          (α_ (F.map f) (η.app b) (G.map g)).inv ≫ η.naturality f ▷ G.map g ≫
            (α_ (η.app a) (G.map f) (G.map g)).hom ≫ η.app a ◁ (G.mapComp f g).inv := by
      have := η.naturality_comp f g
      simp only [Pseudofunctor.toOplax_toPrelaxFunctor, Pseudofunctor.toOplax_mapComp] at this
      rw [← cancel_mono (η.app a ◁ (G.mapComp f g).hom), this]
      simp
    change ((H.mapComp (F.map (f ≫ g)) (η.app c)).inv ≫ H.map₂ (η.naturality (f ≫ g)) ≫
        (H.mapComp (η.app a) (G.map (f ≫ g))).hom) ≫
        H.map (η.app a) ◁ (H.map₂ (G.mapComp f g).hom ≫ (H.mapComp (G.map f) (G.map g)).hom) =
      (H.map₂ (F.mapComp f g).hom ≫ (H.mapComp (F.map f) (F.map g)).hom) ▷ H.map (η.app c) ≫
        (α_ (H.map (F.map f)) (H.map (F.map g)) (H.map (η.app c))).hom ≫
          H.map (F.map f) ◁ ((H.mapComp (F.map g) (η.app c)).inv ≫ H.map₂ (η.naturality g) ≫
            (H.mapComp (η.app b) (G.map g)).hom) ≫
            (α_ (H.map (F.map f)) (H.map (η.app b)) (H.map (G.map g))).inv ≫
              ((H.mapComp (F.map f) (η.app b)).inv ≫ H.map₂ (η.naturality f) ≫
                (H.mapComp (η.app a) (G.map f)).hom) ▷ H.map (G.map g) ≫
                (α_ (H.map (η.app a)) (H.map (G.map f)) (H.map (G.map g))).hom
    rw [h0]
    simp only [PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_left,
      Pseudofunctor.map₂_whisker_right, Pseudofunctor.map₂_associator,
      map₂_associator_inv', Category.assoc,
      Iso.inv_hom_id_assoc, whiskerLeft_comp, comp_whiskerRight]
    have t : H.map (η.app a) ◁ (H.mapComp (G.map f) (G.map g)).inv ≫
        H.map (η.app a) ◁ H.map₂ (G.mapComp f g).inv ≫
          H.map (η.app a) ◁ H.map₂ (G.mapComp f g).hom ≫
            H.map (η.app a) ◁ (H.mapComp (G.map f) (G.map g)).hom = 𝟙 _ := by
      simp only [← whiskerLeft_comp, ← PrelaxFunctor.map₂_comp_assoc, Iso.inv_hom_id,
        PrelaxFunctor.map₂_id, Category.id_comp, whiskerLeft_id]
    erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, t, Category.comp_id]

/-! ### Compatibility with central families

A family `p_λ : λ → λ` with 2-morphisms `e_F : F p_μ ⟶ p_λ F` (such as `π`, `β` or `q`, `γ`),
pseudofunctors `F` with isomorphisms `j_F : p_{Fλ} ≅ F p_λ` and an oplax transformation `η`
with `η_{p_λ} ∘ j_F η_λ ∘ e_{η_λ} = η_λ j_G` (the Π-2-naturality condition of Definition
5.2(iii) for `(π, β)`). Whiskering preserves this condition, with the composite `j` of
`PiTwoFunctor.comp`. -/

theorem precomp_central {pB : ∀ a : B, a ⟶ a} {pC : ∀ a : C, a ⟶ a} {pD : ∀ a : D, a ⟶ a}
    (eD : ∀ {a b : D} (f : a ⟶ b), f ≫ pD b ⟶ pD a ≫ f)
    (P : Pseudofunctor B C) {F G : Pseudofunctor C D}
    (jP : ∀ a, pC (P.obj a) ≅ P.map (pB a)) (jF : ∀ a, pD (F.obj a) ≅ F.map (pC a))
    (jG : ∀ a, pD (G.obj a) ≅ G.map (pC a))
    (η : Oplax.OplaxTrans F.toOplax G.toOplax)
    (hη : ∀ a, eD (η.app a) ≫ (jF a).hom ▷ η.app a ≫ η.naturality (pC a) =
      η.app a ◁ (jG a).hom) (a : B) :
    eD ((precomp P η).app a) ≫ (jF (P.obj a) ≪≫ F.map₂Iso (jP a)).hom ▷ (precomp P η).app a ≫
        (precomp P η).naturality (pB a) =
      (precomp P η).app a ◁ (jG (P.obj a) ≪≫ G.map₂Iso (jP a)).hom := by
  have h1 := η.naturality_naturality (jP a).hom
  simp only [Pseudofunctor.toOplax_toPrelaxFunctor] at h1
  change eD (η.app (P.obj a)) ≫ ((jF (P.obj a)).hom ≫ F.map₂ (jP a).hom) ▷ η.app (P.obj a) ≫
      η.naturality (P.map (pB a)) = η.app (P.obj a) ◁ ((jG (P.obj a)).hom ≫ G.map₂ (jP a).hom)
  rw [comp_whiskerRight, Category.assoc, h1, reassoc_of% (hη (P.obj a)),
    whiskerLeft_comp]

theorem postcomp_central {pC : ∀ a : C, a ⟶ a} {pD : ∀ a : D, a ⟶ a} {pE : ∀ a : E, a ⟶ a}
    (eD : ∀ {a b : D} (f : a ⟶ b), f ≫ pD b ⟶ pD a ≫ f)
    (eE : ∀ {a b : E} (f : a ⟶ b), f ≫ pE b ⟶ pE a ≫ f)
    {F G : Pseudofunctor C D} (H : Pseudofunctor D E)
    (jF : ∀ a, pD (F.obj a) ≅ F.map (pC a)) (jG : ∀ a, pD (G.obj a) ≅ G.map (pC a))
    (jH : ∀ a, pE (H.obj a) ≅ H.map (pD a))
    (hH : ∀ {a b : D} (f : a ⟶ b), H.map f ◁ (jH b).hom ≫ (H.mapComp f (pD b)).inv ≫
      H.map₂ (eD f) = eE (H.map f) ≫ (jH a).hom ▷ H.map f ≫ (H.mapComp (pD a) f).inv)
    (η : Oplax.OplaxTrans F.toOplax G.toOplax)
    (hη : ∀ a, eD (η.app a) ≫ (jF a).hom ▷ η.app a ≫ η.naturality (pC a) =
      η.app a ◁ (jG a).hom) (a : C) :
    eE ((postcomp η H).app a) ≫ (jH (F.obj a) ≪≫ H.map₂Iso (jF a)).hom ▷ (postcomp η H).app a ≫
        (postcomp η H).naturality (pC a) =
      (postcomp η H).app a ◁ (jH (G.obj a) ≪≫ H.map₂Iso (jG a)).hom := by
  have e1 : eE (H.map (η.app a)) ≫ (jH (F.obj a)).hom ▷ H.map (η.app a) =
      H.map (η.app a) ◁ (jH (G.obj a)).hom ≫ (H.mapComp (η.app a) (pD (G.obj a))).inv ≫
        H.map₂ (eD (η.app a)) ≫ (H.mapComp (pD (F.obj a)) (η.app a)).hom := by
    have h : H.map (η.app a) ◁ (jH (G.obj a)).hom ≫ (H.mapComp (η.app a) (pD (G.obj a))).inv ≫
        H.map₂ (eD (η.app a)) = eE (H.map (η.app a)) ≫ (jH (F.obj a)).hom ▷ H.map (η.app a) ≫
          (H.mapComp (pD (F.obj a)) (η.app a)).inv := hH (η.app a)
    rw [reassoc_of% h]
    simp
  have e2 := congrArg H.map₂ (hη a)
  simp only [PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_left,
    Pseudofunctor.map₂_whisker_right, Category.assoc] at e2
  change eE (H.map (η.app a)) ≫ ((jH (F.obj a)).hom ≫ H.map₂ (jF a).hom) ▷ H.map (η.app a) ≫
      (H.mapComp (F.map (pC a)) (η.app a)).inv ≫ H.map₂ (η.naturality (pC a)) ≫
        (H.mapComp (η.app a) (G.map (pC a))).hom =
    H.map (η.app a) ◁ ((jH (G.obj a)).hom ≫ H.map₂ (jG a).hom)
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [reassoc_of% e1, reassoc_of% e2]
  simp [whiskerLeft_comp]

end Oplax.OplaxTrans

end CategoryTheory
