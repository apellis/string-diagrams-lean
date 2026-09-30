import StringDiagrams.Super.TwoSCat
import StringDiagrams.Super.QPiTwoFunctor

/-!
# Composition of (Q, Π)-2-functors

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Definition 6.3 and the discussion after Definition 6.14.

## Composition

* Graded 2-superfunctors (Definition 6.3) are closed under composition
  (`TwoSuperfunctor.IsGraded.comp`; identities: `TwoSuperfunctor.id_isGraded`), so the
  associativity and unit laws of `StringDiagrams.Super.TwoSCat` apply to them.
* Mathlib's composition of pseudofunctors is associative and unital up to equality
  (`pseudofunctor_comp_assoc`, `pseudofunctor_id_comp`, `pseudofunctor_comp_id`); the
  coherence maps are compared using `Pseudofunctor.map₂_comp`.
* Π-2-functors (Definition 5.2(ii)) and `(Q, Π)`-2-functors (`StringDiagrams.QPiTwoFunctor`, a
  definition not given in the paper) compose, with the coherence data composed as for
  2-superfunctors (`c_{𝕊ℝ} = 𝕊(c_ℝ) ∘ c_𝕊`) and for Π- and `(Q, Π)`-functors
  (`β_{GF} = Gβ_F ∘ β_G F`, `γ_{GF} = Gγ_F ∘ γ_G F`, Definition 6.12(ii)):
  `j_{𝕊ℝ} = 𝕊(j_ℝ) ∘ j_𝕊` and `k_{𝕊ℝ} = 𝕊(k_ℝ) ∘ k_𝕊` (`PiTwoFunctor.comp`,
  `QPiTwoFunctor.comp`); the identities have `j = 1`, `k = 1` (`PiTwoFunctor.id`,
  `QPiTwoFunctor.id`). The axioms `β_comm` and `γ_comm` of the composite follow from those of
  the factors by the same computation (`comp_centralComm`).
* Bundled with their pseudofunctors (`BundledPiTwoFunctor`, `BundledQPiTwoFunctor`),
  composition is associative and unital (`BundledPiTwoFunctor.comp_assoc`,
  `BundledQPiTwoFunctor.comp_assoc`, ...).

## The categories

As for `2-SCat` and `Π-2-SCat` (`StringDiagrams.Super.TwoSCat`), the 2-categories of §6 are
bundled at the level of objects and 1-morphisms, as Mathlib categories:

* `GTwoSCat R`: graded 2-supercategories (Definition 6.2) and graded 2-superfunctors
  (Definition 6.3), with the functor `GTwoSCat.forget` to `TwoSCat R` forgetting the gradings;
* `QPiTwoGSCat R` (the 1-truncation of `(Q, Π)-2-𝔊𝔖ℭ𝔄𝔗`): graded `(Q, Π)`-2-supercategories
  (Definition 6.5) and graded 2-superfunctors, with the forgetful functor
  `ν : (Q, Π)-2-GSCat → 2-GSCat` (`QPiTwoGSCat.forget`);
* `PiTwoCat R` (the 1-truncation of `Π-2-ℭ𝔄𝔗`): Π-2-categories (Definition 5.2(i)) and
  Π-2-functors;
* `QPiTwoCat R` (the 1-truncation of `(Q, Π)-2-ℭ𝔄𝔗`): `(Q, Π)`-2-categories (Definition 6.14)
  and `(Q, Π)`-2-functors, with the forgetful functor `QPiTwoCat.forget` to `PiTwoCat R`.

The 2-morphisms (2-natural transformations) are not included, for the reason explained in
`StringDiagrams.Super.TwoSCat`: their vertical composition is associative and unital only up to
the associators and unitors of the target.

## The functors `E₂` and `𝔼`

On objects and 1-morphisms, `E₂` of (5.4) and its §6 analogue `𝔼` (the underlying
`(Q, Π)`-2-category of a graded `(Q, Π)`-2-supercategory, and the restriction of a graded
2-superfunctor to degree zero, `StringDiagrams.Super.QPiTwoFunctor`) are functors
`PiTwoSCat.toPiTwoCat : Π-2-SCat ⥤ Π-2-Cat` and
`QPiTwoGSCat.toQPiTwoCat : (Q, Π)-2-GSCat ⥤ (Q, Π)-2-Cat`: the underlying pseudofunctor, the
restriction to degree zero and the coherence maps `j`, `k` are compatible with identities and
composition (`TwoSuperfunctor.toPseudofunctor_comp`, `TwoSuperfunctor.toDegreeZero2_comp`,
`TwoSuperfunctor.jIso_comp_hom`, `TwoSuperfunctor.kIso_comp_hom`, ...). The compatibility of
`𝔻` (`QPiTwoFunctor.mapQ`, `StringDiagrams.Super.QAssociatedTwoMap`) with composition is not
formalized.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory

universe w w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃ w₄ v₄ u₄

/-! ## Graded 2-superfunctors -/

namespace TwoSuperfunctor

open Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R C]
  {D : Type u₃} [BicategoryStruct.{w₃, v₃} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)]
  [∀ a b : D, Supercategory R (a ⟶ b)] [∀ a b : D, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R D]

omit [TwoSupercategory R B] [TwoSupercategory R C] in
/-- The composite of graded 2-superfunctors is graded. -/
theorem IsGraded.comp {F : TwoSuperfunctor R B C} {G : TwoSuperfunctor R C D}
    (hF : F.IsGraded) (hG : G.IsGraded) : (F.comp G).IsGraded where
  map₂_mem_degree h := hG.map₂_mem_degree (hF.map₂_mem_degree h)
  mapComp_hom_mem_degree f g := by
    have h := comp_mem_degree (hG.mapComp_hom_mem_degree (F.map f) (F.map g))
      (hG.map₂_mem_degree (hF.mapComp_hom_mem_degree f g))
    rw [add_zero] at h
    exact h
  mapId_hom_mem_degree a := by
    have h := comp_mem_degree (hG.mapId_hom_mem_degree (F.obj a))
      (hG.map₂_mem_degree (hF.mapId_hom_mem_degree a))
    rw [add_zero] at h
    exact h

end TwoSuperfunctor

/-! ## Composition of pseudofunctors -/

section Pseudofunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {D : Type u₃} [Bicategory.{w₃, v₃} D] {E : Type u₄} [Bicategory.{w₄, v₄} E]

/-- Extensionality for pseudofunctors. -/
theorem pseudofunctor_ext {F G : Pseudofunctor B C} (h_obj : F.obj = G.obj)
    (h_map : HEq @F.map @G.map) (h_map₂ : HEq @F.map₂ @G.map₂)
    (h_comp : HEq @F.mapComp @G.mapComp) (h_id : HEq F.mapId G.mapId) : F = G := by
  obtain ⟨⟨⟨⟨obj, map⟩, map₂⟩, _, _⟩, mapId, mapComp, _, _, _, _, _⟩ := F
  obtain ⟨⟨⟨⟨obj', map'⟩, map₂'⟩, _, _⟩, mapId', mapComp', _, _, _, _, _⟩ := G
  dsimp only at h_obj h_map h_map₂ h_comp h_id
  subst h_obj
  cases h_map
  cases h_map₂
  cases h_comp
  cases h_id
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Composition of pseudofunctors is associative. -/
theorem pseudofunctor_comp_assoc (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (H : Pseudofunctor D E) : (F.comp G).comp H = F.comp (G.comp H) := by
  refine pseudofunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    apply Iso.ext
    simp only [Pseudofunctor.comp_mapComp, Iso.trans_hom, PrelaxFunctor.map₂Iso_hom,
      PrelaxFunctor.map₂_comp, Category.assoc]
    rfl
  · funext a
    apply Iso.ext
    simp only [Pseudofunctor.comp_mapId, Iso.trans_hom, PrelaxFunctor.map₂Iso_hom,
      PrelaxFunctor.map₂_comp, Category.assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity pseudofunctor is a left unit for composition. -/
theorem pseudofunctor_id_comp (F : Pseudofunctor B C) : (Pseudofunctor.id B).comp F = F := by
  refine pseudofunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    apply Iso.ext
    change F.map₂ (𝟙 (f ≫ g)) ≫ (F.mapComp f g).hom = _
    rw [F.map₂_id, Category.id_comp]
  · funext a
    apply Iso.ext
    change F.map₂ (𝟙 (𝟙 a)) ≫ (F.mapId a).hom = _
    rw [F.map₂_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The identity pseudofunctor is a right unit for composition. -/
theorem pseudofunctor_comp_id (F : Pseudofunctor B C) : F.comp (Pseudofunctor.id C) = F := by
  refine pseudofunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    apply Iso.ext
    exact Category.comp_id _
  · funext a
    apply Iso.ext
    exact Category.comp_id _

/-- Naturality of `c = mapComp⁻¹` in the second variable, for 2-morphisms in the image. -/
@[reassoc]
theorem pseudofunctor_whiskerLeft_map₂_mapComp_inv (G : Pseudofunctor C D) {a b c : C}
    (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    G.map f ◁ G.map₂ η ≫ (G.mapComp f h).inv = (G.mapComp f g).inv ≫ G.map₂ (f ◁ η) := by
  simp

/-- Naturality of `c = mapComp⁻¹` in the first variable, for 2-morphisms in the image. -/
@[reassoc]
theorem pseudofunctor_map₂_whiskerRight_mapComp_inv (G : Pseudofunctor C D) {a b c : C}
    {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    G.map₂ η ▷ G.map h ≫ (G.mapComp g h).inv = (G.mapComp f h).inv ≫ G.map₂ (η ▷ h) := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The computation behind the first axiom of Definition 5.2(ii) (`PiTwoFunctor.β_comm`) and the
axiom `QPiTwoFunctor.γ_comm` for a composite: if `F` and `G` carry 2-isomorphisms
`j_F : p_{Fλ} ≅ F p_λ`, `j_G : p_{Gλ} ≅ G p_λ` compatible with families of 2-morphisms
`e_F : F ≫ p_μ ⟶ p_λ ≫ F` (such as the half-braidings `β`, `γ`), then so does `G ∘ F` with
`j_{GF} = G(j_F) ∘ j_G`. -/
theorem comp_centralComm {pB : ∀ a : B, a ⟶ a} {pC : ∀ a : C, a ⟶ a} {pD : ∀ a : D, a ⟶ a}
    (eB : ∀ {a b : B} (f : a ⟶ b), f ≫ pB b ⟶ pB a ≫ f)
    (eC : ∀ {a b : C} (f : a ⟶ b), f ≫ pC b ⟶ pC a ≫ f)
    (eD : ∀ {a b : D} (f : a ⟶ b), f ≫ pD b ⟶ pD a ≫ f)
    {F : Pseudofunctor B C} {G : Pseudofunctor C D}
    (jF : ∀ a, pC (F.obj a) ≅ F.map (pB a)) (jG : ∀ a, pD (G.obj a) ≅ G.map (pC a))
    (hF : ∀ {a b : B} (f : a ⟶ b), F.map f ◁ (jF b).hom ≫ (F.mapComp f (pB b)).inv ≫
      F.map₂ (eB f) = eC (F.map f) ≫ (jF a).hom ▷ F.map f ≫ (F.mapComp (pB a) f).inv)
    (hG : ∀ {a b : C} (f : a ⟶ b), G.map f ◁ (jG b).hom ≫ (G.mapComp f (pC b)).inv ≫
      G.map₂ (eC f) = eD (G.map f) ≫ (jG a).hom ▷ G.map f ≫ (G.mapComp (pC a) f).inv)
    {a b : B} (f : a ⟶ b) :
    (F.comp G).map f ◁ (jG (F.obj b) ≪≫ G.map₂Iso (jF b)).hom ≫
        ((F.comp G).mapComp f (pB b)).inv ≫ (F.comp G).map₂ (eB f) =
      eD ((F.comp G).map f) ≫ (jG (F.obj a) ≪≫ G.map₂Iso (jF a)).hom ▷ (F.comp G).map f ≫
        ((F.comp G).mapComp (pB a) f).inv := by
  have h3 := congrArg G.map₂ (hF f)
  simp only [PrelaxFunctor.map₂_comp] at h3
  change G.map (F.map f) ◁ ((jG (F.obj b)).hom ≫ G.map₂ (jF b).hom) ≫
      ((G.mapComp (F.map f) (F.map (pB b))).inv ≫ G.map₂ (F.mapComp f (pB b)).inv) ≫
        G.map₂ (F.map₂ (eB f)) =
    eD (G.map (F.map f)) ≫ ((jG (F.obj a)).hom ≫ G.map₂ (jF a).hom) ▷ G.map (F.map f) ≫
      ((G.mapComp (F.map (pB a)) (F.map f)).inv ≫ G.map₂ (F.mapComp (pB a) f).inv)
  rw [Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [pseudofunctor_whiskerLeft_map₂_mapComp_inv_assoc, h3, reassoc_of% (hG (F.map f)),
    pseudofunctor_map₂_whiskerRight_mapComp_inv_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The computation behind the second axiom of Definition 5.2(ii) (`PiTwoFunctor.ξ_comm`) for a
composite, with `j_{GF} = G(j_F) ∘ j_G`. -/
theorem comp_ξComm {pB : ∀ a : B, a ⟶ a} {pC : ∀ a : C, a ⟶ a} {pD : ∀ a : D, a ⟶ a}
    (xB : ∀ a : B, pB a ≫ pB a ⟶ 𝟙 a) (xC : ∀ a : C, pC a ≫ pC a ⟶ 𝟙 a)
    (xD : ∀ a : D, pD a ≫ pD a ⟶ 𝟙 a)
    {F : Pseudofunctor B C} {G : Pseudofunctor C D}
    (jF : ∀ a, pC (F.obj a) ≅ F.map (pB a)) (jG : ∀ a, pD (G.obj a) ≅ G.map (pC a))
    (hF : ∀ a : B, (jF a).hom ▷ pC (F.obj a) ≫ F.map (pB a) ◁ (jF a).hom ≫
      (F.mapComp (pB a) (pB a)).inv ≫ F.map₂ (xB a) = xC (F.obj a) ≫ (F.mapId a).inv)
    (hG : ∀ a : C, (jG a).hom ▷ pD (G.obj a) ≫ G.map (pC a) ◁ (jG a).hom ≫
      (G.mapComp (pC a) (pC a)).inv ≫ G.map₂ (xC a) = xD (G.obj a) ≫ (G.mapId a).inv)
    (a : B) :
    (jG (F.obj a) ≪≫ G.map₂Iso (jF a)).hom ▷ pD ((F.comp G).obj a) ≫
        (F.comp G).map (pB a) ◁ (jG (F.obj a) ≪≫ G.map₂Iso (jF a)).hom ≫
          ((F.comp G).mapComp (pB a) (pB a)).inv ≫ (F.comp G).map₂ (xB a) =
      xD ((F.comp G).obj a) ≫ ((F.comp G).mapId a).inv := by
  have h3 := congrArg G.map₂ (hF a)
  simp only [PrelaxFunctor.map₂_comp] at h3
  change ((jG (F.obj a)).hom ≫ G.map₂ (jF a).hom) ▷ pD (G.obj (F.obj a)) ≫
      G.map (F.map (pB a)) ◁ ((jG (F.obj a)).hom ≫ G.map₂ (jF a).hom) ≫
        ((G.mapComp (F.map (pB a)) (F.map (pB a))).inv ≫ G.map₂ (F.mapComp (pB a) (pB a)).inv) ≫
          G.map₂ (F.map₂ (xB a)) =
    xD (G.obj (F.obj a)) ≫ ((G.mapId (F.obj a)).inv ≫ G.map₂ (F.mapId a).inv)
  rw [Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, pseudofunctor_whiskerLeft_map₂_mapComp_inv_assoc,
    pseudofunctor_map₂_whiskerRight_mapComp_inv_assoc, h3, reassoc_of% (hG (F.obj a))]

end Pseudofunctor

/-! ## Composition of Π-2-functors and `(Q, Π)`-2-functors -/

section PiTwoFunctor

variable {R : Type w} [CommRing R]
  {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C]
  {D : Type u₃} [Bicategory.{w₃, v₃} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)] [PreadditiveBicategory D]
  [LinearBicategory R D]

namespace PiTwoFunctor

variable [PiTwoCategory R B] [PiTwoCategory R C] [PiTwoCategory R D]

open PiTwoCategory

variable (R B) in
set_option backward.isDefEq.respectTransparency false in
/-- The identity Π-2-functor, with `j = 1`. -/
def id : PiTwoFunctor R (Pseudofunctor.id B) where
  map₂_add _ _ := rfl
  map₂_smul _ _ := rfl
  j a := Iso.refl _
  β_comm f := by
    change f ◁ 𝟙 _ ≫ 𝟙 _ ≫ (β (R := R) f).hom = (β (R := R) f).hom ≫ 𝟙 _ ▷ f ≫ 𝟙 _
    simp
  ξ_comm a := by
    change 𝟙 _ ▷ pi (R := R) a ≫ pi (R := R) a ◁ 𝟙 _ ≫ 𝟙 _ ≫ (ξ (R := R) a).hom =
      (ξ (R := R) a).hom ≫ 𝟙 _
    simp

theorem id_j (a : B) : (PiTwoFunctor.id R B).j a = Iso.refl _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The composite of Π-2-functors, with `j_{𝕊ℝ} = 𝕊(j_ℝ) ∘ j_𝕊` (as for the coherence maps
`c`, `i` of a composite of 2-superfunctors, Definition 2.2(ii), and for `β` of a composite of
Π-functors, Definition 1.6(ii)). -/
def comp {F : Pseudofunctor B C} {G : Pseudofunctor C D} (hF : PiTwoFunctor R F)
    (hG : PiTwoFunctor R G) : PiTwoFunctor R (F.comp G) where
  map₂_add η θ := by
    change G.map₂ (F.map₂ (η + θ)) = G.map₂ (F.map₂ η) + G.map₂ (F.map₂ θ)
    rw [hF.map₂_add, hG.map₂_add]
  map₂_smul r η := by
    change G.map₂ (F.map₂ (r • η)) = r • G.map₂ (F.map₂ η)
    rw [hF.map₂_smul, hG.map₂_smul]
  j a := hG.j (F.obj a) ≪≫ G.map₂Iso (hF.j a)
  β_comm f := comp_centralComm (fun f => (β (R := R) f).hom) (fun f => (β (R := R) f).hom)
    (fun f => (β (R := R) f).hom) hF.j hG.j hF.β_comm hG.β_comm f
  ξ_comm a := comp_ξComm (fun a => (ξ (R := R) a).hom) (fun a => (ξ (R := R) a).hom)
    (fun a => (ξ (R := R) a).hom) hF.j hG.j hF.ξ_comm hG.ξ_comm a

theorem comp_j {F : Pseudofunctor B C} {G : Pseudofunctor C D} (hF : PiTwoFunctor R F)
    (hG : PiTwoFunctor R G) (a : B) :
    (hF.comp hG).j a = hG.j (F.obj a) ≪≫ G.map₂Iso (hF.j a) := rfl

end PiTwoFunctor

namespace QPiTwoFunctor

variable [QPiTwoCategory R B] [QPiTwoCategory R C] [QPiTwoCategory R D]

open QPiTwoCategory

variable (R B) in
set_option backward.isDefEq.respectTransparency false in
/-- The identity `(Q, Π)`-2-functor, with `j = 1` and `k = 1`. -/
def id : QPiTwoFunctor R (Pseudofunctor.id B) where
  toPiTwoFunctor := PiTwoFunctor.id R B
  k a := Iso.refl _
  γ_comm f := by
    change f ◁ 𝟙 _ ≫ 𝟙 _ ≫ (γ (R := R) f).hom = (γ (R := R) f).hom ≫ 𝟙 _ ▷ f ≫ 𝟙 _
    simp

theorem id_k (a : B) : (QPiTwoFunctor.id R B).k a = Iso.refl _ := rfl

theorem id_toPiTwoFunctor : (QPiTwoFunctor.id R B).toPiTwoFunctor = PiTwoFunctor.id R B := rfl

/-- The composite of `(Q, Π)`-2-functors, with `j_{𝕊ℝ} = 𝕊(j_ℝ) ∘ j_𝕊` and
`k_{𝕊ℝ} = 𝕊(k_ℝ) ∘ k_𝕊` (as for `β` and `γ` of a composite of `(Q, Π)`-functors,
Definition 6.12(ii), `QPiFunctor.comp`). -/
def comp {F : Pseudofunctor B C} {G : Pseudofunctor C D} (hF : QPiTwoFunctor R F)
    (hG : QPiTwoFunctor R G) : QPiTwoFunctor R (F.comp G) where
  toPiTwoFunctor := hF.toPiTwoFunctor.comp hG.toPiTwoFunctor
  k a := hG.k (F.obj a) ≪≫ G.map₂Iso (hF.k a)
  γ_comm f := comp_centralComm (fun f => (γ (R := R) f).hom) (fun f => (γ (R := R) f).hom)
    (fun f => (γ (R := R) f).hom) hF.k hG.k hF.γ_comm hG.γ_comm f

theorem comp_k {F : Pseudofunctor B C} {G : Pseudofunctor C D} (hF : QPiTwoFunctor R F)
    (hG : QPiTwoFunctor R G) (a : B) :
    (hF.comp hG).k a = hG.k (F.obj a) ≪≫ G.map₂Iso (hF.k a) := rfl

theorem comp_toPiTwoFunctor {F : Pseudofunctor B C} {G : Pseudofunctor C D}
    (hF : QPiTwoFunctor R F) (hG : QPiTwoFunctor R G) :
    (hF.comp hG).toPiTwoFunctor = hF.toPiTwoFunctor.comp hG.toPiTwoFunctor := rfl

end QPiTwoFunctor

end PiTwoFunctor

/-! ## Bundled Π-2-functors and `(Q, Π)`-2-functors: associativity and unit laws -/

section Bundled

variable (R : Type w) [CommRing R]
  (B : Type u₁) [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B]
  (C : Type u₂) [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C]

/-- A Π-2-functor (Definition 5.2(ii)), bundled with its underlying pseudofunctor. -/
structure BundledPiTwoFunctor [PiTwoCategory R B] [PiTwoCategory R C] where
  /-- The underlying pseudofunctor. -/
  toPseudofunctor : Pseudofunctor B C
  /-- The Π-2-functor structure. -/
  toPiTwoFunctor : PiTwoFunctor R toPseudofunctor

/-- A `(Q, Π)`-2-functor (`QPiTwoFunctor`), bundled with its underlying pseudofunctor. -/
structure BundledQPiTwoFunctor [QPiTwoCategory R B] [QPiTwoCategory R C] where
  /-- The underlying pseudofunctor. -/
  toPseudofunctor : Pseudofunctor B C
  /-- The `(Q, Π)`-2-functor structure. -/
  toQPiTwoFunctor : QPiTwoFunctor R toPseudofunctor

end Bundled

section BundledLaws

variable {R : Type w} [CommRing R]
  {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C]
  {D : Type u₃} [Bicategory.{w₃, v₃} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)] [PreadditiveBicategory D]
  [LinearBicategory R D]
  {E : Type u₄} [Bicategory.{w₄, v₄} E]
  [∀ a b : E, Preadditive (a ⟶ b)] [∀ a b : E, Linear R (a ⟶ b)] [PreadditiveBicategory E]
  [LinearBicategory R E]

namespace BundledPiTwoFunctor

variable [PiTwoCategory R B] [PiTwoCategory R C] [PiTwoCategory R D] [PiTwoCategory R E]

/-- Extensionality for bundled Π-2-functors. -/
theorem ext' {P Q : BundledPiTwoFunctor R B C} (h : P.toPseudofunctor = Q.toPseudofunctor)
    (hj : ∀ a, HEq (P.toPiTwoFunctor.j a).hom (Q.toPiTwoFunctor.j a).hom) : P = Q := by
  obtain ⟨F, ⟨_, _, j, _, _⟩⟩ := P
  obtain ⟨G, ⟨_, _, j', _, _⟩⟩ := Q
  dsimp only at h hj
  subst h
  obtain rfl : j = j' := funext fun a => Iso.ext (eq_of_heq (hj a))
  rfl

variable (R B) in
/-- The identity Π-2-functor. -/
def id : BundledPiTwoFunctor R B B := ⟨Pseudofunctor.id B, PiTwoFunctor.id R B⟩

/-- The composite of Π-2-functors. -/
def comp (P : BundledPiTwoFunctor R B C) (Q : BundledPiTwoFunctor R C D) :
    BundledPiTwoFunctor R B D :=
  ⟨P.toPseudofunctor.comp Q.toPseudofunctor, P.toPiTwoFunctor.comp Q.toPiTwoFunctor⟩

@[simp] theorem id_toPseudofunctor : (id R B).toPseudofunctor = Pseudofunctor.id B := rfl

@[simp] theorem comp_toPseudofunctor (P : BundledPiTwoFunctor R B C)
    (Q : BundledPiTwoFunctor R C D) :
    (P.comp Q).toPseudofunctor = P.toPseudofunctor.comp Q.toPseudofunctor := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Composition of Π-2-functors is associative. -/
theorem comp_assoc (P : BundledPiTwoFunctor R B C) (Q : BundledPiTwoFunctor R C D)
    (S : BundledPiTwoFunctor R D E) : (P.comp Q).comp S = P.comp (Q.comp S) :=
  ext' (pseudofunctor_comp_assoc _ _ _) fun a => heq_of_eq (by
    simp only [comp, PiTwoFunctor.comp_j, Iso.trans_hom, PrelaxFunctor.map₂Iso_hom,
      PrelaxFunctor.map₂_comp, Category.assoc]
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The identity Π-2-functor is a left unit for composition. -/
theorem id_comp (P : BundledPiTwoFunctor R B C) : (id R B).comp P = P :=
  ext' (pseudofunctor_id_comp _) fun a => heq_of_eq (by
    change (P.toPiTwoFunctor.j a).hom ≫ P.toPseudofunctor.map₂ (𝟙 _) = _
    rw [PrelaxFunctor.map₂_id, Category.comp_id])

set_option backward.isDefEq.respectTransparency false in
/-- The identity Π-2-functor is a right unit for composition. -/
theorem comp_id (P : BundledPiTwoFunctor R B C) : P.comp (id R C) = P :=
  ext' (pseudofunctor_comp_id _) fun _ => heq_of_eq (Category.id_comp _)

end BundledPiTwoFunctor

namespace BundledQPiTwoFunctor

variable [QPiTwoCategory R B] [QPiTwoCategory R C] [QPiTwoCategory R D] [QPiTwoCategory R E]

/-- Extensionality for bundled `(Q, Π)`-2-functors. -/
theorem ext' {P Q : BundledQPiTwoFunctor R B C} (h : P.toPseudofunctor = Q.toPseudofunctor)
    (hj : ∀ a, HEq (P.toQPiTwoFunctor.j a).hom (Q.toQPiTwoFunctor.j a).hom)
    (hk : ∀ a, HEq (P.toQPiTwoFunctor.k a).hom (Q.toQPiTwoFunctor.k a).hom) : P = Q := by
  obtain ⟨F, ⟨⟨_, _, j, _, _⟩, k, _⟩⟩ := P
  obtain ⟨G, ⟨⟨_, _, j', _, _⟩, k', _⟩⟩ := Q
  dsimp only at h hj hk
  subst h
  obtain rfl : j = j' := funext fun a => Iso.ext (eq_of_heq (hj a))
  obtain rfl : k = k' := funext fun a => Iso.ext (eq_of_heq (hk a))
  rfl

variable (R B) in
/-- The identity `(Q, Π)`-2-functor. -/
def id : BundledQPiTwoFunctor R B B := ⟨Pseudofunctor.id B, QPiTwoFunctor.id R B⟩

/-- The composite of `(Q, Π)`-2-functors. -/
def comp (P : BundledQPiTwoFunctor R B C) (Q : BundledQPiTwoFunctor R C D) :
    BundledQPiTwoFunctor R B D :=
  ⟨P.toPseudofunctor.comp Q.toPseudofunctor, P.toQPiTwoFunctor.comp Q.toQPiTwoFunctor⟩

@[simp] theorem id_toPseudofunctor : (id R B).toPseudofunctor = Pseudofunctor.id B := rfl

@[simp] theorem comp_toPseudofunctor (P : BundledQPiTwoFunctor R B C)
    (Q : BundledQPiTwoFunctor R C D) :
    (P.comp Q).toPseudofunctor = P.toPseudofunctor.comp Q.toPseudofunctor := rfl

/-- The underlying Π-2-functor of a `(Q, Π)`-2-functor. -/
def toBundledPiTwoFunctor (P : BundledQPiTwoFunctor R B C) : BundledPiTwoFunctor R B C :=
  ⟨P.toPseudofunctor, P.toQPiTwoFunctor.toPiTwoFunctor⟩

set_option backward.isDefEq.respectTransparency false in
/-- Composition of `(Q, Π)`-2-functors is associative. -/
theorem comp_assoc (P : BundledQPiTwoFunctor R B C) (Q : BundledQPiTwoFunctor R C D)
    (S : BundledQPiTwoFunctor R D E) : (P.comp Q).comp S = P.comp (Q.comp S) :=
  ext' (pseudofunctor_comp_assoc _ _ _)
    (fun a => heq_of_eq (by
      simp only [comp, QPiTwoFunctor.comp_toPiTwoFunctor, PiTwoFunctor.comp_j, Iso.trans_hom,
        PrelaxFunctor.map₂Iso_hom, PrelaxFunctor.map₂_comp, Category.assoc]
      rfl))
    (fun a => heq_of_eq (by
      simp only [comp, QPiTwoFunctor.comp_k, Iso.trans_hom, PrelaxFunctor.map₂Iso_hom,
        PrelaxFunctor.map₂_comp, Category.assoc]
      rfl))

set_option backward.isDefEq.respectTransparency false in
/-- The identity `(Q, Π)`-2-functor is a left unit for composition. -/
theorem id_comp (P : BundledQPiTwoFunctor R B C) : (id R B).comp P = P :=
  ext' (pseudofunctor_id_comp _)
    (fun a => heq_of_eq (by
      change (P.toQPiTwoFunctor.j a).hom ≫ P.toPseudofunctor.map₂ (𝟙 _) = _
      rw [PrelaxFunctor.map₂_id, Category.comp_id]))
    (fun a => heq_of_eq (by
      change (P.toQPiTwoFunctor.k a).hom ≫ P.toPseudofunctor.map₂ (𝟙 _) = _
      rw [PrelaxFunctor.map₂_id, Category.comp_id]))

set_option backward.isDefEq.respectTransparency false in
/-- The identity `(Q, Π)`-2-functor is a right unit for composition. -/
theorem comp_id (P : BundledQPiTwoFunctor R B C) : P.comp (id R C) = P :=
  ext' (pseudofunctor_comp_id _) (fun _ => heq_of_eq (Category.id_comp _))
    (fun _ => heq_of_eq (Category.id_comp _))

theorem toBundledPiTwoFunctor_id :
    (id R B).toBundledPiTwoFunctor = BundledPiTwoFunctor.id R B := rfl

theorem toBundledPiTwoFunctor_comp (P : BundledQPiTwoFunctor R B C)
    (Q : BundledQPiTwoFunctor R C D) :
    (P.comp Q).toBundledPiTwoFunctor = P.toBundledPiTwoFunctor.comp Q.toBundledPiTwoFunctor :=
  rfl

end BundledQPiTwoFunctor

end BundledLaws

/-! ## The category `2-GSCat` -/

section Categories

variable (R : Type w) [CommRing R]

/-- A graded 2-supercategory over `R` (Brundan–Ellis, Definition 6.2), bundled. -/
structure GTwoSCat extends TwoSCat.{w, w₁, v₁, u₁} R where
  [graded : ∀ a b : carrier, GradedSupercategory R (a ⟶ b)]
  [gradedTwo : GradedTwoSupercategory R carrier]

namespace GTwoSCat

attribute [instance] graded gradedTwo

variable {R}

instance : CoeSort (GTwoSCat.{w, w₁, v₁, u₁} R) (Type u₁) := ⟨fun B => B.carrier⟩

variable (R) in
/-- The bundled graded 2-supercategory of a graded 2-supercategory. -/
abbrev of (B : Type u₁) [BicategoryStruct.{w₁, v₁} B] [∀ a b : B, Preadditive (a ⟶ b)]
    [∀ a b : B, Linear R (a ⟶ b)] [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
    [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B] :
    GTwoSCat.{w, w₁, v₁, u₁} R :=
  ⟨TwoSCat.of R B⟩

/-- **Brundan–Ellis, §6.** The category `2-GSCat` of graded 2-supercategories and graded
2-superfunctors (Definition 6.3). -/
instance : Category (GTwoSCat.{w, w₁, v₁, u₁} R) where
  Hom B C := { F : TwoSuperfunctor R B C // F.IsGraded }
  id B := ⟨TwoSuperfunctor.id R B, TwoSuperfunctor.id_isGraded⟩
  comp F G := ⟨F.1.comp G.1, F.2.comp G.2⟩
  id_comp F := Subtype.ext (TwoSuperfunctor.id_comp F.1)
  comp_id F := Subtype.ext (TwoSuperfunctor.comp_id F.1)
  assoc F G H := Subtype.ext (TwoSuperfunctor.comp_assoc F.1 G.1 H.1)

theorem hom_def (B C : GTwoSCat.{w, w₁, v₁, u₁} R) :
    (B ⟶ C) = { F : TwoSuperfunctor R B C // F.IsGraded } := rfl

@[simp] theorem id_val (B : GTwoSCat.{w, w₁, v₁, u₁} R) :
    (𝟙 B : B ⟶ B).1 = TwoSuperfunctor.id R B := rfl

@[simp] theorem comp_val {B C D : GTwoSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) (G : C ⟶ D) :
    (F ≫ G).1 = F.1.comp G.1 := rfl

/-- The functor `2-GSCat → 2-SCat` forgetting the gradings. -/
@[simps]
def forget : GTwoSCat.{w, w₁, v₁, u₁} R ⥤ TwoSCat.{w, w₁, v₁, u₁} R where
  obj B := B.toTwoSCat
  map F := F.1

end GTwoSCat

/-! ## The category `(Q, Π)-2-GSCat` -/

/-- A graded `(Q, Π)`-2-supercategory over `R` (Brundan–Ellis, Definition 6.5), bundled. -/
structure QPiTwoGSCat extends GTwoSCat.{w, w₁, v₁, u₁} R where
  [qpiTwo : QPiTwoSupercategory R carrier]

namespace QPiTwoGSCat

attribute [instance] qpiTwo

variable {R}

instance : CoeSort (QPiTwoGSCat.{w, w₁, v₁, u₁} R) (Type u₁) := ⟨fun B => B.carrier⟩

variable (R) in
/-- The bundled graded `(Q, Π)`-2-supercategory of a graded `(Q, Π)`-2-supercategory. -/
abbrev of (B : Type u₁) [BicategoryStruct.{w₁, v₁} B] [∀ a b : B, Preadditive (a ⟶ b)]
    [∀ a b : B, Linear R (a ⟶ b)] [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
    [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B]
    [QPiTwoSupercategory R B] : QPiTwoGSCat.{w, w₁, v₁, u₁} R :=
  ⟨GTwoSCat.of R B⟩

/-- **Brundan–Ellis, §6.** The category `(Q, Π)-2-GSCat` of graded `(Q, Π)`-2-supercategories
and graded 2-superfunctors (the 1-truncation of the 2-category `(Q, Π)-2-𝔊𝔖ℭ𝔄𝔗`). -/
instance : Category (QPiTwoGSCat.{w, w₁, v₁, u₁} R) where
  Hom B C := { F : TwoSuperfunctor R B C // F.IsGraded }
  id B := ⟨TwoSuperfunctor.id R B, TwoSuperfunctor.id_isGraded⟩
  comp F G := ⟨F.1.comp G.1, F.2.comp G.2⟩
  id_comp F := Subtype.ext (TwoSuperfunctor.id_comp F.1)
  comp_id F := Subtype.ext (TwoSuperfunctor.comp_id F.1)
  assoc F G H := Subtype.ext (TwoSuperfunctor.comp_assoc F.1 G.1 H.1)

theorem hom_def (B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (B ⟶ C) = { F : TwoSuperfunctor R B C // F.IsGraded } := rfl

@[simp] theorem id_val (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (𝟙 B : B ⟶ B).1 = TwoSuperfunctor.id R B := rfl

@[simp] theorem comp_val {B C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) (G : C ⟶ D) :
    (F ≫ G).1 = F.1.comp G.1 := rfl

/-- The forgetful functor `ν : (Q, Π)-2-GSCat → 2-GSCat` (Theorem 6.9 and after Lemma 6.11). -/
@[simps]
def forget : QPiTwoGSCat.{w, w₁, v₁, u₁} R ⥤ GTwoSCat.{w, w₁, v₁, u₁} R where
  obj B := B.toGTwoSCat
  map F := F

end QPiTwoGSCat

/-! ## The categories `Π-2-Cat` and `(Q, Π)-2-Cat` -/

/-- A Π-2-category over `R` (Brundan–Ellis, Definition 5.2(i)), bundled. -/
structure PiTwoCat where
  /-- The objects. -/
  carrier : Type u₁
  [str : Bicategory.{w₁, v₁} carrier]
  [preadditive : ∀ a b : carrier, Preadditive (a ⟶ b)]
  [linear : ∀ a b : carrier, Linear R (a ⟶ b)]
  [preadditiveBicategory : PreadditiveBicategory carrier]
  [linearBicategory : LinearBicategory R carrier]
  [piTwo : PiTwoCategory R carrier]

namespace PiTwoCat

attribute [instance] str preadditive linear preadditiveBicategory linearBicategory piTwo

variable {R}

instance : CoeSort (PiTwoCat.{w, w₁, v₁, u₁} R) (Type u₁) := ⟨PiTwoCat.carrier⟩

variable (R) in
/-- The bundled Π-2-category of a Π-2-category. -/
abbrev of (B : Type u₁) [Bicategory.{w₁, v₁} B] [∀ a b : B, Preadditive (a ⟶ b)]
    [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B] [LinearBicategory R B]
    [PiTwoCategory R B] : PiTwoCat.{w, w₁, v₁, u₁} R :=
  ⟨B⟩

/-- **Brundan–Ellis, Section 5.** The category `Π-2-Cat` of Π-2-categories and Π-2-functors
(Definition 5.2(ii); the 1-truncation of the 2-category `Π-2-ℭ𝔄𝔗`). -/
instance : Category (PiTwoCat.{w, w₁, v₁, u₁} R) where
  Hom B C := BundledPiTwoFunctor R B C
  id B := BundledPiTwoFunctor.id R B
  comp P Q := P.comp Q
  id_comp := BundledPiTwoFunctor.id_comp
  comp_id := BundledPiTwoFunctor.comp_id
  assoc := BundledPiTwoFunctor.comp_assoc

theorem hom_def (B C : PiTwoCat.{w, w₁, v₁, u₁} R) : (B ⟶ C) = BundledPiTwoFunctor R B C := rfl

theorem id_def (B : PiTwoCat.{w, w₁, v₁, u₁} R) : 𝟙 B = BundledPiTwoFunctor.id R B := rfl

theorem comp_def {B C D : PiTwoCat.{w, w₁, v₁, u₁} R} (P : B ⟶ C) (Q : C ⟶ D) :
    P ≫ Q = BundledPiTwoFunctor.comp P Q := rfl

end PiTwoCat

/-- A `(Q, Π)`-2-category over `R` (Brundan–Ellis, Definition 6.14), bundled. -/
structure QPiTwoCat where
  /-- The objects. -/
  carrier : Type u₁
  [str : Bicategory.{w₁, v₁} carrier]
  [preadditive : ∀ a b : carrier, Preadditive (a ⟶ b)]
  [linear : ∀ a b : carrier, Linear R (a ⟶ b)]
  [preadditiveBicategory : PreadditiveBicategory carrier]
  [linearBicategory : LinearBicategory R carrier]
  [qpiTwo : QPiTwoCategory R carrier]

namespace QPiTwoCat

attribute [instance] str preadditive linear preadditiveBicategory linearBicategory qpiTwo

variable {R}

instance : CoeSort (QPiTwoCat.{w, w₁, v₁, u₁} R) (Type u₁) := ⟨QPiTwoCat.carrier⟩

variable (R) in
/-- The bundled `(Q, Π)`-2-category of a `(Q, Π)`-2-category. -/
abbrev of (B : Type u₁) [Bicategory.{w₁, v₁} B] [∀ a b : B, Preadditive (a ⟶ b)]
    [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B] [LinearBicategory R B]
    [QPiTwoCategory R B] : QPiTwoCat.{w, w₁, v₁, u₁} R :=
  ⟨B⟩

/-- **Brundan–Ellis, §6.** The category `(Q, Π)-2-Cat` of `(Q, Π)`-2-categories and
`(Q, Π)`-2-functors (in the sense of `StringDiagrams.Super.QPiTwoFunctor`; the 1-truncation of
the 2-category `(Q, Π)-2-ℭ𝔄𝔗`). -/
instance : Category (QPiTwoCat.{w, w₁, v₁, u₁} R) where
  Hom B C := BundledQPiTwoFunctor R B C
  id B := BundledQPiTwoFunctor.id R B
  comp P Q := P.comp Q
  id_comp := BundledQPiTwoFunctor.id_comp
  comp_id := BundledQPiTwoFunctor.comp_id
  assoc := BundledQPiTwoFunctor.comp_assoc

theorem hom_def (B C : QPiTwoCat.{w, w₁, v₁, u₁} R) :
    (B ⟶ C) = BundledQPiTwoFunctor R B C := rfl

theorem id_def (B : QPiTwoCat.{w, w₁, v₁, u₁} R) : 𝟙 B = BundledQPiTwoFunctor.id R B := rfl

theorem comp_def {B C D : QPiTwoCat.{w, w₁, v₁, u₁} R} (P : B ⟶ C) (Q : C ⟶ D) :
    P ≫ Q = BundledQPiTwoFunctor.comp P Q := rfl

/-- The functor `(Q, Π)-2-Cat → Π-2-Cat` forgetting `q`, `q⁻¹`, `γ`, `ii`, `jj` and `k`. -/
@[simps]
def forget : QPiTwoCat.{w, w₁, v₁, u₁} R ⥤ PiTwoCat.{w, w₁, v₁, u₁} R where
  obj B := PiTwoCat.of R B
  map P := P.toBundledPiTwoFunctor

end QPiTwoCat

end Categories

/-! ## `E₂` and `𝔼` preserve identities and composition -/

namespace TwoSuperfunctor

open Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

section Underlying

variable {R : Type w} [CommRing R]
  {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [TwoSupercategory R A']
  {A'' : Type u₃} [BicategoryStruct.{w₃, v₃} A'']
  [∀ a b : A'', Preadditive (a ⟶ b)] [∀ a b : A'', Linear R (a ⟶ b)]
  [∀ a b : A'', Supercategory R (a ⟶ b)] [TwoSupercategory R A'']

variable (R A) in
set_option backward.isDefEq.respectTransparency false in
/-- `E₂` of (5.4) preserves identities: the restriction of `𝕀` is the identity pseudofunctor. -/
theorem toPseudofunctor_id :
    (TwoSuperfunctor.id R A).toPseudofunctor = Pseudofunctor.id (Underlying2 R A) := by
  refine pseudofunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    exact Iso.ext (Subtype.ext rfl)
  · funext a
    exact Iso.ext (Subtype.ext rfl)

set_option backward.isDefEq.respectTransparency false in
/-- `E₂` of (5.4) preserves composition. -/
theorem toPseudofunctor_comp (F : TwoSuperfunctor R A A') (G : TwoSuperfunctor R A' A'') :
    (F.comp G).toPseudofunctor = F.toPseudofunctor.comp G.toPseudofunctor := by
  refine pseudofunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    exact Iso.ext (Subtype.ext rfl)
  · funext a
    exact Iso.ext (Subtype.ext rfl)

variable [PiTwoSupercategory R A] [PiTwoSupercategory R A'] [PiTwoSupercategory R A'']

/-- The `j` of (5.4) for `𝕀` is the identity. -/
theorem jIso_id_hom (a : A) : ((TwoSuperfunctor.id R A).jIso a).hom = 𝟙 _ := by
  rw [jIso_hom]
  simp

omit [TwoSupercategory R A] [TwoSupercategory R A'] in
/-- The `j` of (5.4) for a composite: `j_{𝕊ℝ} = 𝕊(j_ℝ) ∘ j_𝕊`. -/
theorem jIso_comp_hom (F : TwoSuperfunctor R A A') (G : TwoSuperfunctor R A' A'') (a : A) :
    ((F.comp G).jIso a).hom = (G.jIso (F.obj a)).hom ≫ G.map₂ (F.jIso a).hom := by
  change (PiTwoSupercategory.ζ (R := R) (G.obj (F.obj a))).hom ≫
      ((G.mapId (F.obj a)).hom ≫ G.map₂ (F.mapId a).hom) ≫
        G.map₂ (F.map₂ (PiTwoSupercategory.ζ (R := R) a).inv) = _
  rw [jIso_hom, jIso_hom, G.map₂_comp, G.map₂_comp]
  simp only [Category.assoc]
  rw [← G.map₂_comp_assoc, Iso.inv_hom_id, G.map₂_id, Category.id_comp]

end Underlying

section DegreeZero

variable {R : Type w} [CommRing R]
  {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [∀ a b : A, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A] [GradedTwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [∀ a b : A', GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A'] [GradedTwoSupercategory R A']
  {A'' : Type u₃} [BicategoryStruct.{w₃, v₃} A'']
  [∀ a b : A'', Preadditive (a ⟶ b)] [∀ a b : A'', Linear R (a ⟶ b)]
  [∀ a b : A'', Supercategory R (a ⟶ b)] [∀ a b : A'', GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A''] [GradedTwoSupercategory R A'']

variable (R A) in
set_option backward.isDefEq.respectTransparency false in
/-- The restriction of `𝕀` to degree zero is the identity. -/
theorem toDegreeZero2_id :
    (TwoSuperfunctor.id R A).toDegreeZero2 TwoSuperfunctor.id_isGraded =
      TwoSuperfunctor.id R (DegreeZero2 R A) := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    exact Iso.ext (GradedSupercategory.DegreeZero.hom_ext rfl)
  · funext a
    exact Iso.ext (GradedSupercategory.DegreeZero.hom_ext rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to degree zero preserves composition. -/
theorem toDegreeZero2_comp {F : TwoSuperfunctor R A A'} {G : TwoSuperfunctor R A' A''}
    (hF : F.IsGraded) (hG : G.IsGraded) :
    (F.comp G).toDegreeZero2 (hF.comp hG) = (F.toDegreeZero2 hF).comp (G.toDegreeZero2 hG) := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    exact Iso.ext (GradedSupercategory.DegreeZero.hom_ext rfl)
  · funext a
    exact Iso.ext (GradedSupercategory.DegreeZero.hom_ext rfl)

variable [QPiTwoSupercategory R A] [QPiTwoSupercategory R A'] [QPiTwoSupercategory R A'']

/-- The `k` of `𝔼 𝕀` is the identity. -/
theorem kIso_id_hom (a : A) : ((TwoSuperfunctor.id R A).kIso a).hom = 𝟙 _ := by
  rw [kIso_hom]
  simp

/-- The `k` of `𝔼` of a composite: `k_{𝕊ℝ} = 𝕊(k_ℝ) ∘ k_𝕊`. -/
theorem kIso_comp_hom (F : TwoSuperfunctor R A A') (G : TwoSuperfunctor R A' A'') (a : A) :
    ((F.comp G).kIso a).hom = (G.kIso (F.obj a)).hom ≫ G.map₂ (F.kIso a).hom := by
  change (QPiTwoSupercategory.σ (R := R) (G.obj (F.obj a))).hom ≫
      ((G.mapId (F.obj a)).hom ≫ G.map₂ (F.mapId a).hom) ≫
        G.map₂ (F.map₂ (QPiTwoSupercategory.σ (R := R) a).inv) = _
  rw [kIso_hom, kIso_hom, G.map₂_comp, G.map₂_comp]
  simp only [Category.assoc]
  rw [← G.map₂_comp_assoc, Iso.inv_hom_id, G.map₂_id, Category.id_comp]

end DegreeZero

end TwoSuperfunctor

namespace PiTwoSCat

variable {R : Type w} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- **Brundan–Ellis, (5.4).** The functor `E₂ : Π-2-SCat → Π-2-Cat`, sending a
Π-2-supercategory to its underlying Π-2-category (`Underlying2.instPiTwoCategory`) and a
2-superfunctor to its restriction (`TwoSuperfunctor.toPiTwoFunctor`). -/
def toPiTwoCat : PiTwoSCat.{w, w₁, v₁, u₁} R ⥤ PiTwoCat.{w, w₁, v₁, u₁} R where
  obj B := PiTwoCat.of R (Underlying2 R B)
  map F := ⟨TwoSuperfunctor.toPseudofunctor F, TwoSuperfunctor.toPiTwoFunctor F⟩
  map_id B := BundledPiTwoFunctor.ext' (TwoSuperfunctor.toPseudofunctor_id R B) fun a =>
    heq_of_eq (Subtype.ext (TwoSuperfunctor.jIso_id_hom a.obj))
  map_comp F G := BundledPiTwoFunctor.ext' (TwoSuperfunctor.toPseudofunctor_comp F G) fun a =>
    heq_of_eq (Subtype.ext (TwoSuperfunctor.jIso_comp_hom F G a.obj))

@[simp] theorem toPiTwoCat_obj (B : PiTwoSCat.{w, w₁, v₁, u₁} R) :
    toPiTwoCat.obj B = PiTwoCat.of R (Underlying2 R B) := rfl

@[simp] theorem toPiTwoCat_map {B C : PiTwoSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    toPiTwoCat.map F =
      (⟨TwoSuperfunctor.toPseudofunctor F, TwoSuperfunctor.toPiTwoFunctor F⟩ :
        BundledPiTwoFunctor R (Underlying2 R B) (Underlying2 R C)) := rfl

end PiTwoSCat

namespace QPiTwoGSCat

variable {R : Type w} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- **Brundan–Ellis, §6 (the analogue of (5.4) and (6.3)).** The functor
`𝔼 : (Q, Π)-2-GSCat → (Q, Π)-2-Cat`, sending a graded `(Q, Π)`-2-supercategory to its
underlying `(Q, Π)`-2-category (`GUnderlying2.instQPiTwoCategory`) and a graded 2-superfunctor
to its restriction to degree zero (`TwoSuperfunctor.toQPiTwoFunctor`). -/
def toQPiTwoCat : QPiTwoGSCat.{w, w₁, v₁, u₁} R ⥤ QPiTwoCat.{w, w₁, v₁, u₁} R where
  obj B := QPiTwoCat.of R (GUnderlying2 R B)
  map F := ⟨(F.1.toDegreeZero2 F.2).toPseudofunctor, F.1.toQPiTwoFunctor F.2⟩
  map_id B := BundledQPiTwoFunctor.ext'
    ((congrArg TwoSuperfunctor.toPseudofunctor (TwoSuperfunctor.toDegreeZero2_id R B)).trans
      (TwoSuperfunctor.toPseudofunctor_id R (DegreeZero2 R B)))
    (fun a => heq_of_eq (Subtype.ext (GradedSupercategory.DegreeZero.hom_ext (TwoSuperfunctor.jIso_id_hom a.obj.as))))
    (fun a => heq_of_eq (Subtype.ext (GradedSupercategory.DegreeZero.hom_ext (TwoSuperfunctor.kIso_id_hom a.obj.as))))
  map_comp F G := BundledQPiTwoFunctor.ext'
    ((congrArg TwoSuperfunctor.toPseudofunctor (TwoSuperfunctor.toDegreeZero2_comp F.2 G.2)).trans
      (TwoSuperfunctor.toPseudofunctor_comp _ _))
    (fun a => heq_of_eq (Subtype.ext (GradedSupercategory.DegreeZero.hom_ext
      (TwoSuperfunctor.jIso_comp_hom F.1 G.1 a.obj.as))))
    (fun a => heq_of_eq (Subtype.ext (GradedSupercategory.DegreeZero.hom_ext
      (TwoSuperfunctor.kIso_comp_hom F.1 G.1 a.obj.as))))

@[simp] theorem toQPiTwoCat_obj (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    toQPiTwoCat.obj B = QPiTwoCat.of R (GUnderlying2 R B) := rfl

@[simp] theorem toQPiTwoCat_map {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    toQPiTwoCat.map F =
      (⟨(F.1.toDegreeZero2 F.2).toPseudofunctor, F.1.toQPiTwoFunctor F.2⟩ :
        BundledQPiTwoFunctor R (GUnderlying2 R B) (GUnderlying2 R C)) := rfl

end QPiTwoGSCat

end StringDiagrams

end
