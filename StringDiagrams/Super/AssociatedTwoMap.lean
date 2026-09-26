import StringDiagrams.Super.AssociatedTwoT

/-!
# `D₂` on Π-2-functors

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (5.5): a
Π-2-functor `ℝ : 𝔄 → 𝔅` induces a 2-superfunctor `ℝ̂ : 𝔄̂ → 𝔅̂`, equal to `ℝ` on objects and
1-morphisms, with `ℝ̂ x̂ = ℝ x` on even and `ℝ̂ x̂ = j⁻¹(ℝG) ∘ c⁻¹ ∘ ℝx` on odd 2-morphisms, and
with the coherence maps of `ℝ`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace PiTwoFunctor

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [PiTwoCategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [PiTwoCategory R C]
  {F : Pseudofunctor B C} (hF : PiTwoFunctor R F)

open PiTwoCategory

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)
local notation "𝛏" => PiTwoCategory.ξ (R := R)

/-- The functor `ℋom(λ, μ) → ℋom(ℝλ, ℝμ)` of a Π-2-functor. -/
@[simps]
def homFunctor (_hF : PiTwoFunctor R F) (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) where
  obj := F.map
  map := F.map₂

instance (a b : B) : (hF.homFunctor a b).Additive where
  map_add := hF.map₂_add _ _

instance (a b : B) : (hF.homFunctor a b).Linear R where
  map_smul η r := hF.map₂_smul r η

/-- The isomorphism `c ∘ (ℝG) j : (ℝG) π_{ℝμ} ≅ ℝ(G π_μ)`: the Π-functor structure of `ℝ` on a
hom category. -/
def βHom {a b : B} (g : a ⟶ b) : F.map g ≫ 𝛑 (F.obj b) ≅ F.map (g ≫ 𝛑 b) :=
  whiskerLeftIso (F.map g) (hF.j b) ≪≫ (F.mapComp g (𝛑 b)).symm

theorem βHom_hom {a b : B} (g : a ⟶ b) :
    (hF.βHom g).hom = F.map g ◁ (hF.j b).hom ≫ (F.mapComp g (𝛑 b)).inv := rfl

theorem βHom_inv {a b : B} (g : a ⟶ b) :
    (hF.βHom g).inv = (F.mapComp g (𝛑 b)).hom ≫ F.map g ◁ (hF.j b).inv := by
  simp [βHom]

@[reassoc]
theorem βHom_naturality {a b : B} {g g' : a ⟶ b} (η : g ⟶ g') :
    F.map₂ η ▷ 𝛑 (F.obj b) ≫ (hF.βHom g').hom = (hF.βHom g).hom ≫ F.map₂ (η ▷ 𝛑 b) := by
  rw [βHom_hom, βHom_hom, ← whisker_exchange_assoc]
  simp

/-- The Π-functor axiom for `ℝ` on a hom category, from the second axiom of
Definition 5.2(ii). -/
theorem βHom_comm {a b : B} (g : a ⟶ b) :
    (ξHom (R := R) (F.map g)).hom ≫ F.map₂ (ξHom (R := R) g).inv =
      (hF.βHom g).hom ▷ 𝛑 (F.obj b) ≫ (hF.βHom (g ≫ 𝛑 b)).hom := by
  have hξ := hF.ξ_comm b
  have key : (ξHom (R := R) (F.map g)).hom = (hF.βHom g).hom ▷ 𝛑 (F.obj b) ≫
      (hF.βHom (g ≫ 𝛑 b)).hom ≫ F.map₂ (ξHom (R := R) g).hom := by
    rw [ξHom_hom, ξHom_hom, F.map₂_comp, F.map₂_comp, Pseudofunctor.map₂_associator,
      Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_right_unitor, βHom_hom, βHom_hom]
    simp only [Bicategory.comp_whiskerRight, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← whisker_exchange_assoc, Bicategory.inv_hom_whiskerRight_assoc]
    have c1 : (F.map g ◁ (hF.j b).hom) ▷ 𝛑 (F.obj b) ≫
        (F.map g ≫ F.map (𝛑 b)) ◁ (hF.j b).hom ≫
          (α_ (F.map g) (F.map (𝛑 b)) (F.map (𝛑 b))).hom =
        (α_ (F.map g) (𝛑 (F.obj b)) (𝛑 (F.obj b))).hom ≫
          F.map g ◁ ((hF.j b).hom ▷ 𝛑 (F.obj b)) ≫ F.map g ◁ (F.map (𝛑 b) ◁ (hF.j b).hom) := by
      bicategory
    rw [reassoc_of% c1]
    simp only [← Bicategory.whiskerLeft_comp_assoc, Category.assoc]
    rw [reassoc_of% hξ]
    simp
  rw [key]
  simp [← F.map₂_comp]

variable (R) in
/-- **Brundan–Ellis, (5.5).** A Π-2-functor gives Π-functors between the hom Π-categories. -/
def homPi (a b : B) : PiFunctor R (hF.homFunctor a b) where
  β := NatIso.ofComponents (fun g => hF.βHom g) fun η => hF.βHom_naturality η
  comm g := hF.βHom_comm g

include hF in
theorem map₂_zero {a b : B} {f g : a ⟶ b} : F.map₂ (0 : f ⟶ g) = 0 := by
  have h := hF.map₂_add (0 : f ⟶ g) 0
  rw [add_zero] at h
  exact left_eq_add.mp h

@[simp] theorem homPi_β_hom_app {a b : B} (g : a ⟶ b) :
    (hF.homPi R a b).β.hom.app g = (hF.βHom g).hom := rfl

@[simp] theorem homPi_β_inv_app {a b : B} (g : a ⟶ b) :
    (hF.homPi R a b).β.inv.app g = (hF.βHom g).inv := rfl

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [PiTwoCategory R B] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C] [LinearBicategory R C]
  [PiTwoCategory R C] in
theorem _root_.CategoryTheory.Pseudofunctor.map₂_associator_inv' (F : Pseudofunctor B C)
    {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map₂ (α_ f g h).inv = (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom ≫
      (α_ (F.map f) (F.map g) (F.map h)).inv ≫ (F.mapComp f g).inv ▷ F.map h ≫
        (F.mapComp (f ≫ g) h).inv := by
  apply (cancel_epi (F.map₂ (α_ f g h).hom)).1
  rw [← F.map₂_comp, Iso.hom_inv_id, F.map₂_id, Pseudofunctor.map₂_associator]
  simp

/-- `c : (ℝF)(ℝG) ⇒ ℝ(F G)`, as a natural transformation in `G`. -/
def mapCompRight {a b : B} (c : B) (f : a ⟶ b) :
    hF.homFunctor b c ⋙ precomp (F.obj c) (F.map f) ⟶ precomp c f ⋙ hF.homFunctor a c where
  app g := (F.mapComp f g).inv
  naturality _ _ η := by simp

theorem mapCompRight_isPiNatural {a b : B} (c : B) (f : a ⟶ b) :
    PiFunctor.IsPiNatural R ((hF.homPi R b c).comp (precompPi R (F.obj c) (F.map f)))
      ((precompPi R c f).comp (hF.homPi R a c)) (hF.mapCompRight c f) := fun g => by
  simp only [mapCompRight, PiFunctor.comp_β, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.comp_obj, homFunctor_obj, homFunctor_map,
    precomp_obj, precomp_map, precompPi_β_hom_app, homPi_β_hom_app, βHom_hom, pi_obj, pi_map,
    Pseudofunctor.map₂_associator]
  simp only [Bicategory.whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_assoc, Bicategory.inv_hom_whiskerRight_assoc]
  bicategory

/-- `c : (ℝF)(ℝG) ⇒ ℝ(F G)`, as a natural transformation in `F`. -/
def mapCompLeft (a : B) {b c : B} (h : b ⟶ c) :
    hF.homFunctor a b ⋙ postcomp (F.obj a) (F.map h) ⟶ postcomp a h ⋙ hF.homFunctor a c where
  app f := (F.mapComp f h).inv
  naturality _ _ η := by simp

theorem mapCompLeft_isPiNatural (a : B) {b c : B} (h : b ⟶ c) :
    PiFunctor.IsPiNatural R ((hF.homPi R a b).comp (postcompPi R (F.obj a) (F.map h)))
      ((postcompPi R a h).comp (hF.homPi R a c)) (hF.mapCompLeft a h) := fun f => by
  have hβ : (F.mapComp h (𝛑 c)).inv ≫ F.map₂ (𝛃 h).hom ≫ (F.mapComp (𝛑 b) h).hom =
      F.map h ◁ (hF.j c).inv ≫ (𝛃 (F.map h)).hom ≫ (hF.j b).hom ▷ F.map h := by
    have e := hF.β_comm h
    rw [← cancel_epi (F.map h ◁ (hF.j c).hom)]
    simp only [← Category.assoc] at e ⊢
    rw [e]
    simp
  simp only [mapCompLeft, PiFunctor.comp_β, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.comp_obj, homFunctor_obj, homFunctor_map,
    postcomp_obj, postcomp_map, postcompPi_β_hom_app, homPi_β_hom_app, βHom_hom, pi_obj,
    pi_map]
  rw [← cancel_mono ((F.mapComp (f ≫ 𝛑 b) h).hom ≫ (F.mapComp f (𝛑 b)).hom ▷ F.map h)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Bicategory.comp_whiskerRight,
    Bicategory.inv_hom_whiskerRight, Category.comp_id, βR_hom, F.map₂_comp,
    Pseudofunctor.map₂_associator, Pseudofunctor.map₂_whisker_left,
    Pseudofunctor.map₂_associator_inv', Iso.hom_inv_id_assoc, Bicategory.whiskerLeft_comp]
  rw [F.map₂_comp, F.map₂_comp, Pseudofunctor.map₂_associator, Pseudofunctor.map₂_whisker_left,
    Pseudofunctor.map₂_associator_inv']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Bicategory.inv_hom_whiskerRight, Bicategory.inv_hom_whiskerRight_assoc, Category.comp_id]
  rw [← whisker_exchange_assoc, Bicategory.inv_hom_whiskerRight_assoc]
  simp only [← Bicategory.whiskerLeft_comp_assoc, Category.assoc]
  rw [hβ, associator_naturality_right_assoc, ← Bicategory.whiskerLeft_comp_assoc,
    Bicategory.whiskerLeft_hom_inv_assoc]
  bicategory

open Associated2 in
/-- **Brundan–Ellis, (5.5), `D₂` on Π-2-functors.** A Π-2-functor `ℝ` induces a 2-superfunctor
`ℝ̂ : 𝔄̂ → 𝔅̂`: `ℝ` on objects and 1-morphisms, `D₁` of the Π-functors `ℋom(λ, μ) → ℋom(ℝλ, ℝμ)`
on 2-morphisms (`ℝ̂ x̂ = ℝ x` for even and `j⁻¹(ℝG) ∘ c⁻¹ ∘ ℝx` for odd `x̂`), and the coherence
maps `c`, `i` of `ℝ` viewed as even 2-isomorphisms. -/
@[simps]
def mapTwo : TwoSuperfunctor R (Associated2 R B) (Associated2 R C) where
  obj a := ⟨F.obj a.obj⟩
  map f := ⟨F.map f.obj⟩
  map₂ {a b f g} x := (Associated.map (hF.homPi R a.obj b.obj)).map x
  map₂_id f := (Associated.map (hF.homPi R _ _)).map_id f
  map₂_comp x y := (Associated.map (hF.homPi R _ _)).map_comp x y
  map₂_add x y := (Associated.map (hF.homPi R _ _)).map_add
  map₂_smul r x := Functor.Linear.map_smul (F := Associated.map (hF.homPi R _ _)) x r
  map₂_mem hx := IsSuperfunctor.map_mem (F := Associated.map (hF.homPi R _ _)) hx
  mapComp f g := Associated.evenIso (F.mapComp f.obj g.obj).symm
  mapId a := Associated.evenIso (F.mapId a.obj).symm
  mapComp_hom_mem _ _ := Associated.mem_parity_zero.2 rfl
  mapId_hom_mem _ := Associated.mem_parity_zero.2 rfl
  mapComp_naturality_left {a b c f f'} η g := by
    have e := Associated.map_naturality (hF.mapCompLeft_isPiNatural a.obj g.obj) η
    rw [← map_map_map, ← map_map_map] at e
    exact e
  mapComp_naturality_right {a b c} f g g' η := by
    have e := Associated.map_naturality (hF.mapCompRight_isPiNatural c.obj f.obj) η
    rw [← map_map_map, ← map_map_map] at e
    exact e
  map₂_associator f g h := by
    apply hom₂_ext
    · simp [Pseudofunctor.map₂_associator_inv']
    · simp only [comp₂_snd, whiskerLeft_snd, whiskerRight_snd, Associated.evenIso_hom,
        Associated.homMk_fst, Associated.homMk_snd, Associated.map_map, associator_inv_snd,
        associator_inv_fst, whiskerLeft_fst, whiskerRight_fst, Iso.symm_hom, hF.map₂_zero,
        Limits.zero_comp, Limits.comp_zero, add_zero, PreadditiveBicategory.whiskerLeft_zero,
        PreadditiveBicategory.zero_whiskerRight, pi_map]
      erw [homFunctor_map, hF.map₂_zero]
      simp
  map₂_leftUnitor f := by
    apply hom₂_ext
    · simp only [comp₂_fst, whiskerRight_fst, whiskerRight_snd, Associated.evenIso_hom,
        Associated.homMk_fst, Associated.homMk_snd, Associated.map_map, leftUnitor_hom_fst,
        leftUnitor_hom_snd, PreadditiveBicategory.zero_whiskerRight, Limits.zero_comp,
        sub_zero, Iso.symm_hom, homFunctor_map, Pseudofunctor.map₂_left_unitor]
      simp
    · simp only [comp₂_snd, whiskerRight_snd, Associated.evenIso_hom, Associated.homMk_fst,
        Associated.homMk_snd, Associated.map_map, leftUnitor_hom_snd, leftUnitor_hom_fst,
        whiskerRight_fst, Iso.symm_hom, homFunctor_map, hF.map₂_zero, Limits.zero_comp, Limits.comp_zero,
        add_zero, PreadditiveBicategory.zero_whiskerRight, pi_map]
      erw [hF.map₂_zero]
      simp
  map₂_rightUnitor f := by
    apply hom₂_ext
    · simp only [comp₂_fst, whiskerLeft_fst, whiskerLeft_snd, Associated.evenIso_hom,
        Associated.homMk_fst, Associated.homMk_snd, Associated.map_map, rightUnitor_hom_fst,
        rightUnitor_hom_snd, PreadditiveBicategory.whiskerLeft_zero, Limits.zero_comp,
        sub_zero, Iso.symm_hom, homFunctor_map, Pseudofunctor.map₂_right_unitor]
      erw [Iso.inv_hom_id_assoc]
      simp
    · simp only [comp₂_snd, whiskerLeft_snd, Associated.evenIso_hom, Associated.homMk_fst,
        Associated.homMk_snd, Associated.map_map, rightUnitor_hom_snd, rightUnitor_hom_fst,
        whiskerLeft_fst, Iso.symm_hom, homFunctor_map, hF.map₂_zero, Limits.zero_comp, Limits.comp_zero,
        add_zero, PreadditiveBicategory.whiskerLeft_zero, pi_map]
      erw [hF.map₂_zero]
      simp

/-- **Lemma 5.4, `E₂ ∘ D₂ = I` on morphisms.** The coherence map
`ĵ := (ℝ̂ζ)⁻¹ ∘ i ∘ ζ` of the Π-2-functor `E₂ ℝ̂` is `j`, viewed as an even 2-isomorphism. -/
theorem jIso_mapTwo_hom (a : Associated2 R B) :
    ((hF.mapTwo).jIso a).hom =
      Associated.homMk (R := R) (X := ⟨𝛑 (F.obj a.obj)⟩) (Y := ⟨F.map (𝛑 a.obj)⟩)
        (hF.j a.obj).hom 0 := by
  rw [← cancel_mono ((hF.mapTwo).map₂Iso (PiTwoSupercategory.ζ (R := R) a)).hom,
    TwoSuperfunctor.map₂Iso_hom, TwoSuperfunctor.jIso_hom_comp_map₂_ζ]
  apply Associated2.hom₂_ext
  · simp [Associated2.ζ_eq]
    erw [hF.map₂_zero]
    simp
  · simp only [Associated2.ζ_eq, Associated2.comp₂_snd, Associated2.ζ_hom_fst,
      Associated2.ζ_hom_snd, mapTwo_map₂, mapTwo_mapId, Associated.evenIso_hom,
      Associated.homMk_fst, Associated.homMk_snd, Associated.map_map, homFunctor_map,
      homPi_β_inv_app, βHom_inv, Iso.symm_hom, Limits.zero_comp, zero_add, add_zero,
      pi_map, Functor.map_zero]
    have e : F.map₂ (λ_ (𝛑 a.obj)).inv ≫ (F.mapComp (𝟙 a.obj) (𝛑 a.obj)).hom =
        (λ_ (F.map (𝛑 a.obj))).inv ≫ (F.mapId a.obj).inv ▷ F.map (𝛑 a.obj) := by
      apply (cancel_epi (F.map₂ (λ_ (𝛑 a.obj)).hom)).1
      rw [← F.map₂_comp_assoc, Iso.hom_inv_id, F.map₂_id, Category.id_comp,
        Pseudofunctor.map₂_left_unitor]
      simp
    erw [reassoc_of% e]
    have e2 := Bicategory.leftUnitor_inv_naturality (hF.j a.obj).hom
    rw [← Category.assoc]
    erw [e2]
    rw [Category.assoc, whisker_exchange_assoc]
    simp

end PiTwoFunctor

/-! ## Lemma 5.4: naturality of `𝕋` -/

namespace Associated2

open BicategoryStruct TwoSupercategory

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A] [PiTwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [TwoSupercategory R A'] [PiTwoSupercategory R A']
  (G : TwoSuperfunctor R A A')

/-- `ℝ(ζ_μ F) = ζ_{ℝμ}(ℝF) ∘ (ℝF) j⁻¹ ∘ c⁻¹`. -/
theorem map₂_ζG {a b : A} (g : a ⟶ b) :
    G.map₂ (ζG (R := R) g).hom = (G.mapComp g (PiTwoSupercategory.pi (R := R) b)).inv ≫
      G.map g ◁ (G.jIso b).inv ≫ (ζG (R := R) (G.map g)).hom := by
  have hr := G.map₂_rightUnitor g
  have hj : (G.jIso b).inv ≫ (PiTwoSupercategory.ζ (R := R) (G.obj b)).hom =
      G.map₂ (PiTwoSupercategory.ζ (R := R) b).hom ≫ (G.mapId b).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, TwoSuperfunctor.jIso_hom_comp_map₂_ζ,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have n : G.map₂ (g ◁ (PiTwoSupercategory.ζ (R := R) b).hom) =
      (G.mapComp g (PiTwoSupercategory.pi (R := R) b)).inv ≫
        G.map g ◁ G.map₂ (PiTwoSupercategory.ζ (R := R) b).hom ≫ (G.mapComp g (𝟙 b)).hom := by
    rw [G.mapComp_naturality_right, Iso.inv_hom_id_assoc]
  have r : (G.mapComp g (𝟙 b)).hom ≫ G.map₂ (rightUnitor g).hom =
      G.map g ◁ (G.mapId b).inv ≫ (rightUnitor (G.map g)).hom := by
    rw [← hr, TwoSupercategory.whiskerLeft_inv_hom_assoc R]
  rw [ζG_hom, ζG_hom, G.map₂_comp, n, Category.assoc, Category.assoc, r,
    ← whiskerLeft_comp'_assoc R, ← hj, whiskerLeft_comp'_assoc R]

/-- **Lemma 5.4, naturality of `𝕋`.** For a 2-superfunctor `ℝ : 𝔄 → 𝔄'` of Π-2-supercategories,
`ℝ ∘ 𝕋_𝔄 = 𝕋_𝔄' ∘ (E₂ ℝ)^` on 2-morphisms (both are `ℝ` on objects and 1-morphisms). -/
theorem T_map₂_mapTwo {a b : Associated2 R (Underlying2 R A)} {f g : a ⟶ b} (x : f ⟶ g) :
    (T R A').map₂ ((G.toPiTwoFunctor.mapTwo).map₂ x) = G.map₂ ((T R A).map₂ x) := by
  rw [T_map₂, T_map₂, G.map₂_add, G.map₂_comp]
  erw [map₂_ζG G g.obj.obj]
  congr 1
  change (G.map₂ x.2.1 ≫ ((G.mapComp g.obj.obj (PiTwoSupercategory.pi (R := R) b.obj.obj)).inv ≫
    G.map g.obj.obj ◁ (G.jIso b.obj.obj).inv)) ≫ _ = _
  simp only [Category.assoc]
  rfl

/-- **Lemma 5.4, naturality of `𝕋`**, on the coherence maps `c`: both composites have coherence
maps `c_ℝ`. -/
theorem T_map₂_mapTwo_mapComp {a b c : Associated2 R (Underlying2 R A)} (f : a ⟶ b) (g : b ⟶ c) :
    (T R A').map₂ ((G.toPiTwoFunctor.mapTwo).mapComp f g).hom =
      (G.mapComp f.obj.obj g.obj.obj).hom := by
  simp [T_map₂]

/-- **Lemma 5.4, naturality of `𝕋`**, on the coherence maps `i`. -/
theorem T_map₂_mapTwo_mapId (a : Associated2 R (Underlying2 R A)) :
    (T R A').map₂ ((G.toPiTwoFunctor.mapTwo).mapId a).hom = (G.mapId a.obj.obj).hom := by
  simp [T_map₂]

end Associated2

end StringDiagrams

end
