import StringDiagrams.Super.AssociatedTwoNat
import StringDiagrams.Super.AssociatedTwoEquivalence

/-!
# Theorem 5.5 on 2-morphisms: `𝔻₂` is bijective on 2-natural transformations

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (5.6) and
Theorem 5.5 (whose proof the paper leaves to the reader).

For Π-2-functors `ℝ, 𝕊 : 𝔄 → 𝔅` between Π-2-categories, the strict 2-functor `𝔻₂` of (5.6) sends a
Π-2-natural transformation `(Y, y) : ℝ ⇒ 𝕊` to the 2-natural transformation
`(Ŷ, ŷ) : ℝ̂ ⇒ 𝕊̂` (`PiTwoFunctor.mapTwoNat`). This file shows that this is a bijection:

* every 2-natural transformation `(X, x) : ℝ̂ ⇒ 𝕊̂` is even, so its components `x_F` are
  2-morphisms of `𝔅` (`PiTwoFunctor.mapTwo_x_snd`); they form an oplax transformation
  `ℝ ⇒ 𝕊` (`PiTwoFunctor.unmapTwoNat`, which is `𝔼₂(X, x)` read in `𝔄`, `𝔅` through the
  identification `E₂ ∘ D₂ = I` of Lemma 5.4), and it is Π-2-natural
  (`PiTwoFunctor.unmapTwoNat_isPiTwoNatural`, from the Π-2-naturality of `𝔼₂(X, x)`,
  `TwoNatTrans.isPiTwoNatural`);
* the two constructions are mutually inverse (`PiTwoFunctor.mapTwoNat_unmapTwoNat`,
  `PiTwoFunctor.unmapTwoNat_mapTwoNat`), giving the bijection `PiTwoFunctor.mapTwoNatEquiv`
  between Π-2-natural transformations `ℝ ⇒ 𝕊` and 2-natural transformations `ℝ̂ ⇒ 𝕊̂`, which
  preserves identities and vertical composition (`PiTwoFunctor.mapTwoNat_id`,
  `PiTwoFunctor.mapTwoNat_vcomp`, `PiTwoFunctor.mapTwoNatEquiv_symm_id`,
  `PiTwoFunctor.mapTwoNatEquiv_symm_vcomp`).

With Lemma 5.4 as an equivalence of categories `Π-2-Cat ≌ Π-2-SCat` (`PiTwoCat.equivalence`,
`StringDiagrams.Super.AssociatedTwoEquivalence`) this is Theorem 5.5 read on 1-truncations:
`𝔻₂` is an equivalence of the 1-truncations and induces bijections on 2-morphisms compatible
with identities and vertical composition (`PiTwoCat.toPiTwoSCat_isTwoEquivalence`). From the side
of `𝔼₂`: every Π-2-natural transformation `E₂ ℝ ⇒ E₂ 𝕊` between the underlying Π-2-functors of
2-superfunctors is natural with respect to all 2-morphisms (`TwoNatTrans.ofPiTwoNatural`, via
`𝕋`), so `𝔼₂` is bijective on 2-morphisms (`TwoNatTrans.toOplaxTransEquiv`); with
`E₂ : Π-2-SCat ≌ Π-2-Cat` this is Corollary 5.6 read on 1-truncations
(`PiTwoSCat.toPiTwoCat_isTwoEquivalence`, see its docstring and the README). The 2-morphisms of the
paper's `Π-2-𝔖ℭ𝔄𝔗` are oplax, so whiskering them does not satisfy the interchange law and these
2-categories are not formalized as Lean bicategories (see the README).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory
open scoped Oplax.OplaxTrans

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace PiTwoFunctor

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [PiTwoCategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [PiTwoCategory R C]
  {F G H : Pseudofunctor B C} {hF : PiTwoFunctor R F} {hG : PiTwoFunctor R G}
  {hH : PiTwoFunctor R H}

open PiTwoCategory

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)

/-- The components of a 2-natural transformation `ℝ̂ ⇒ 𝕊̂` are even. -/
theorem mapTwo_x_snd (θ : TwoNatTrans hF.mapTwo hG.mapTwo) {a b : Associated2 R B}
    (f : a ⟶ b) : (θ.x f).2 = 0 :=
  Associated.mem_parity_zero.1 (θ.x_mem f)

set_option backward.isDefEq.respectTransparency false in
variable (hF hG) in
/-- **Theorem 5.5, `𝔻₂⁻¹` on 2-morphisms.** The oplax transformation `ℝ ⇒ 𝕊` with components
`X_λ` and `x_F` (the even parts of the components of a 2-natural transformation
`(X, x) : ℝ̂ ⇒ 𝕊̂`). -/
@[simps]
def unmapTwoNat (θ : TwoNatTrans hF.mapTwo hG.mapTwo) : Oplax.OplaxTrans F.toOplax G.toOplax where
  app a := (θ.X ⟨a⟩).obj
  naturality {a b} f := (θ.x (a := ⟨a⟩) (b := ⟨b⟩) ⟨f⟩).1
  naturality_naturality {a b f g} η := by
    have e := congrArg Prod.fst (θ.naturality (a := ⟨a⟩) (b := ⟨b⟩) (f := ⟨f⟩) (g := ⟨g⟩)
      (Associated.homMk η 0))
    simp only [Associated2.comp₂_fst, Associated2.whiskerRight_fst, Associated2.whiskerRight_snd,
      Associated2.whiskerLeft_fst, Associated2.whiskerLeft_snd, mapTwo_map₂, Associated.map_map,
      Associated.homMk_fst, Associated.homMk_snd, mapTwo_x_snd, Limits.zero_comp,
      PreadditiveBicategory.zero_whiskerRight, sub_zero] at e
    simpa using e
  naturality_id a := by
    have e := congrArg Prod.fst (θ.x_id_eq (a := ⟨a⟩))
    simp only [Associated2.comp₂_fst, Associated2.whiskerRight_fst, Associated2.whiskerRight_snd,
      Associated2.whiskerLeft_fst, Associated2.whiskerLeft_snd, mapTwo_mapId,
      Associated.evenIso_hom, Associated.evenIso_inv, Associated.homMk_fst, Associated.homMk_snd,
      Associated2.leftUnitor_hom_fst, Associated2.leftUnitor_hom_snd,
      Associated2.rightUnitor_inv_fst, Associated2.rightUnitor_inv_snd, Iso.symm_hom,
      Iso.symm_inv, Limits.zero_comp, Limits.comp_zero,
      PreadditiveBicategory.zero_whiskerRight, PreadditiveBicategory.whiskerLeft_zero,
      sub_zero] at e
    simp only [Pseudofunctor.toOplax_mapId, Pseudofunctor.toOplax_toPrelaxFunctor]
    refine Eq.trans (congrArg (· ≫ _) e) ?_
    simp
  naturality_comp {a b c} f g := by
    have e := congrArg Prod.fst (θ.x_comp_eq (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩) ⟨f⟩ ⟨g⟩)
    simp only [Associated2.comp₂_fst, Associated2.whiskerRight_fst, Associated2.whiskerRight_snd,
      Associated2.whiskerLeft_fst, Associated2.whiskerLeft_snd, mapTwo_mapComp,
      Associated.evenIso_hom, Associated.evenIso_inv, Associated.homMk_fst, Associated.homMk_snd,
      Associated2.associator_hom_fst, Associated2.associator_hom_snd,
      Associated2.associator_inv_fst, Associated2.associator_inv_snd, Iso.symm_hom,
      Iso.symm_inv, mapTwo_x_snd, Limits.zero_comp, Limits.comp_zero,
      PreadditiveBicategory.zero_whiskerRight, PreadditiveBicategory.whiskerLeft_zero,
      sub_zero] at e
    simp only [Pseudofunctor.toOplax_mapComp, Pseudofunctor.toOplax_toPrelaxFunctor]
    refine Eq.trans (congrArg (· ≫ _) e) ?_
    simp
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Theorem 5.5.** The oplax transformation `𝔻₂⁻¹(X, x)` is Π-2-natural: the axiom of
Definition 5.2(iii) is the even part of the Π-2-naturality of `𝔼₂(X, x)`
(`TwoNatTrans.isPiTwoNatural`), using `β̂ = β` (`Associated2.β_hom_eq`) and `ĵ = j`
(`PiTwoFunctor.jIso_mapTwo_hom`). -/
theorem unmapTwoNat_isPiTwoNatural (θ : TwoNatTrans hF.mapTwo hG.mapTwo) :
    hF.IsPiTwoNatural hG (unmapTwoNat hF hG θ) := fun a => by
  have e0 := congrArg Subtype.val (θ.isPiTwoNatural (⟨⟨a⟩⟩ : Underlying2 R (Associated2 R B)))
  change (PiTwoSupercategory.β (R := R) (θ.X (⟨a⟩ : Associated2 R B))).hom ≫
      BicategoryStruct.whiskerRight ((hF.mapTwo).jIso (⟨a⟩ : Associated2 R B)).hom
        (θ.X (⟨a⟩ : Associated2 R B)) ≫
        θ.x (PiTwoSupercategory.pi (R := R) (⟨a⟩ : Associated2 R B)) =
      BicategoryStruct.whiskerLeft (θ.X (⟨a⟩ : Associated2 R B))
        ((hG.mapTwo).jIso (⟨a⟩ : Associated2 R B)).hom at e0
  have e := congrArg Prod.fst e0
  simp only [Associated2.comp₂_fst, Associated2.comp₂_snd, Associated2.whiskerRight_fst,
    Associated2.whiskerRight_snd, Associated2.whiskerLeft_fst,
    Associated2.β_hom_eq, jIso_mapTwo_hom, Associated.homMk_fst, Associated.homMk_snd,
    mapTwo_x_snd, Limits.zero_comp, Limits.comp_zero, PreadditiveBicategory.zero_whiskerRight,
    sub_zero, add_zero] at e
  exact e

set_option backward.isDefEq.respectTransparency false in
/-- **Theorem 5.5, `𝔻₂ ∘ 𝔻₂⁻¹ = 𝕀` on 2-morphisms.** -/
theorem mapTwoNat_unmapTwoNat (θ : TwoNatTrans hF.mapTwo hG.mapTwo) :
    mapTwoNat hF hG (unmapTwoNat_isPiTwoNatural θ) = θ := by
  refine TwoNatTrans.ext_of_eq rfl fun f => ?_
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact Associated2.hom₂_ext rfl (mapTwo_x_snd θ f).symm

/-- **Theorem 5.5, `𝔻₂⁻¹ ∘ 𝔻₂ = 𝕀` on 2-morphisms.** -/
theorem unmapTwoNat_mapTwoNat {η : Oplax.OplaxTrans F.toOplax G.toOplax}
    (hη : hF.IsPiTwoNatural hG η) : unmapTwoNat hF hG (mapTwoNat hF hG hη) = η :=
  rfl

variable (hF hG) in
/-- **Brundan–Ellis, Theorem 5.5, on 2-morphisms.** `𝔻₂` is a bijection between Π-2-natural
transformations `ℝ ⇒ 𝕊` and 2-natural transformations `ℝ̂ ⇒ 𝕊̂`. -/
@[simps]
def mapTwoNatEquiv :
    { η : Oplax.OplaxTrans F.toOplax G.toOplax // hF.IsPiTwoNatural hG η } ≃
      TwoNatTrans hF.mapTwo hG.mapTwo where
  toFun η := mapTwoNat hF hG η.2
  invFun θ := ⟨unmapTwoNat hF hG θ, unmapTwoNat_isPiTwoNatural θ⟩
  left_inv η := Subtype.ext (unmapTwoNat_mapTwoNat η.2)
  right_inv θ := mapTwoNat_unmapTwoNat θ

theorem mapTwoNat_injective {η η' : Oplax.OplaxTrans F.toOplax G.toOplax}
    (hη : hF.IsPiTwoNatural hG η) (hη' : hF.IsPiTwoNatural hG η')
    (h : mapTwoNat hF hG hη = mapTwoNat hF hG hη') : η = η' :=
  congrArg Subtype.val ((mapTwoNatEquiv hF hG).injective (a₁ := ⟨η, hη⟩) (a₂ := ⟨η', hη'⟩) h)

/-- `𝔻₂⁻¹` preserves identities. -/
theorem mapTwoNatEquiv_symm_id (hF : PiTwoFunctor R F) :
    ((mapTwoNatEquiv hF hF).symm (TwoNatTrans.id hF.mapTwo)).1 =
      Oplax.OplaxTrans.id F.toOplax := by
  rw [← mapTwoNat_id hF]
  rfl

/-- `𝔻₂⁻¹` preserves vertical composition. -/
theorem mapTwoNatEquiv_symm_vcomp (θ : TwoNatTrans hF.mapTwo hG.mapTwo)
    (ψ : TwoNatTrans hG.mapTwo hH.mapTwo) :
    ((mapTwoNatEquiv hF hH).symm (θ.vcomp ψ)).1 =
      Oplax.OplaxTrans.vcomp ((mapTwoNatEquiv hF hG).symm θ).1
        ((mapTwoNatEquiv hG hH).symm ψ).1 := by
  conv_lhs => rw [← mapTwoNat_unmapTwoNat θ, ← mapTwoNat_unmapTwoNat ψ,
    ← mapTwoNat_vcomp (unmapTwoNat_isPiTwoNatural θ) (unmapTwoNat_isPiTwoNatural ψ)]
  rfl

end PiTwoFunctor

/-! ## `𝔼₂` is bijective on 2-morphisms -/

namespace TwoNatTrans

open BicategoryStruct TwoSupercategory

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A] [PiTwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [TwoSupercategory R A'] [PiTwoSupercategory R A']
  {F G H : TwoSuperfunctor R A A'}

set_option backward.isDefEq.respectTransparency false in
/-- **Theorem 5.5, `𝔼₂⁻¹` on 2-morphisms.** A Π-2-natural transformation `E₂ ℝ ⇒ E₂ 𝕊` between
the underlying Π-2-functors of 2-superfunctors `ℝ, 𝕊 : 𝔄 → 𝔄'` is natural with respect to all
(not only even) 2-morphisms, hence a 2-natural transformation `ℝ ⇒ 𝕊`. Proof: a 2-morphism `x`
of `𝔄` is `𝕋_𝔄` of `𝕋_𝔄⁻¹ x`, and `𝕋` carries the supernaturality of `𝔻₂(X, x)`
(`PiTwoFunctor.mapTwoNat`) at `𝕋_𝔄⁻¹ x` to the naturality of `x` at `x` (naturality of `𝕋`,
`Associated2.T_map₂_mapTwo`). -/
def ofPiTwoNatural (η : F.toOplax ⟶ G.toOplax)
    (hη : F.toPiTwoFunctor.IsPiTwoNatural G.toPiTwoFunctor η) : TwoNatTrans F G :=
  ofOplaxTrans η fun {a b f g} ε => by
    have e := congrArg (Associated2.T R A').map₂
      ((PiTwoFunctor.mapTwoNat F.toPiTwoFunctor G.toPiTwoFunctor hη).naturality
        (a := ⟨⟨a⟩⟩) (b := ⟨⟨b⟩⟩) (f := ⟨⟨f⟩⟩) (g := ⟨⟨g⟩⟩)
        (Associated2.Tinv₂ R A (f := (⟨⟨f⟩⟩ : (⟨⟨a⟩⟩ : Associated2 R (Underlying2 R A)) ⟶ ⟨⟨b⟩⟩))
          (g := ⟨⟨g⟩⟩) ε))
    rw [(Associated2.T R A').map₂_comp, (Associated2.T R A').map₂_comp,
      Associated2.T_map₂_whiskerRight, Associated2.T_map₂_whiskerLeft,
      Associated2.T_map₂_mapTwo, Associated2.T_map₂_mapTwo, Associated2.T_map₂_Tinv₂] at e
    simp [Associated2.T_map₂] at e
    exact e

/-- `𝔼₂ ∘ 𝔼₂⁻¹ = 𝕀` on 2-morphisms. -/
theorem toOplaxTrans_ofPiTwoNatural (η : F.toOplax ⟶ G.toOplax)
    (hη : F.toPiTwoFunctor.IsPiTwoNatural G.toPiTwoFunctor η) :
    (ofPiTwoNatural η hη).toOplaxTrans = η :=
  rfl

/-- `𝔼₂⁻¹ ∘ 𝔼₂ = 𝕀` on 2-morphisms. -/
theorem ofPiTwoNatural_toOplaxTrans (θ : TwoNatTrans F G) :
    ofPiTwoNatural θ.toOplaxTrans θ.isPiTwoNatural = θ := by
  obtain ⟨X, x, _, _, _, _⟩ := θ
  rfl

variable (F G) in
/-- **Brundan–Ellis, Theorem 5.5, `𝔼₂` on 2-morphisms.** `𝔼₂` is a bijection between
2-natural transformations `ℝ ⇒ 𝕊` and Π-2-natural transformations `E₂ ℝ ⇒ E₂ 𝕊`. -/
@[simps]
def toOplaxTransEquiv :
    TwoNatTrans F G ≃
      { η : F.toOplax ⟶ G.toOplax // F.toPiTwoFunctor.IsPiTwoNatural G.toPiTwoFunctor η } where
  toFun θ := ⟨θ.toOplaxTrans, θ.isPiTwoNatural⟩
  invFun η := ofPiTwoNatural η.1 η.2
  left_inv θ := ofPiTwoNatural_toOplaxTrans θ
  right_inv η := Subtype.ext (toOplaxTrans_ofPiTwoNatural η.1 η.2)

end TwoNatTrans

/-! ## Theorem 5.5 and Corollary 5.6 on 1-truncations -/

namespace PiTwoCat

variable {R : Type w} [CommRing R]

/-- **Brundan–Ellis, Theorem 5.5**, read on 1-truncations: `𝔻₂` is an equivalence of the
categories `Π-2-Cat ≌ Π-2-SCat` (Lemma 5.4, `PiTwoCat.equivalence`), and for Π-2-functors
`ℝ, 𝕊 : 𝔄 → 𝔅` it is a bijection from Π-2-natural transformations `ℝ ⇒ 𝕊` to 2-natural
transformations `ℝ̂ ⇒ 𝕊̂` (`PiTwoFunctor.mapTwoNatEquiv`), compatible with identities and
vertical composition (`PiTwoFunctor.mapTwoNat_id`, `PiTwoFunctor.mapTwoNat_vcomp`). -/
theorem toPiTwoSCat_isTwoEquivalence :
    (toPiTwoSCat : PiTwoCat.{w, w₁, v₁, u₁} R ⥤ PiTwoSCat.{w, w₁, v₁, u₁} R).IsEquivalence ∧
      ∀ {B C : PiTwoCat.{w, w₁, v₁, u₁} R} (P Q : B ⟶ C),
        Function.Bijective (fun η : { η : Oplax.OplaxTrans P.toPseudofunctor.toOplax
            Q.toPseudofunctor.toOplax // P.toPiTwoFunctor.IsPiTwoNatural Q.toPiTwoFunctor η } =>
          PiTwoFunctor.mapTwoNat P.toPiTwoFunctor Q.toPiTwoFunctor η.2) :=
  ⟨inferInstance, fun P Q => (PiTwoFunctor.mapTwoNatEquiv P.toPiTwoFunctor Q.toPiTwoFunctor).bijective⟩

end PiTwoCat

namespace PiTwoSCat

variable {R : Type w} [CommRing R]

/-- **Brundan–Ellis, Corollary 5.6** at the printed level, read on 1-truncations (as for the
2-adjunctions of Theorem 4.9 and after Lemma 6.11): the 2-categories `Π-2-𝔖ℭ𝔄𝔗` of
Π-2-supercategories and `Π-2-ℭ𝔄𝔗` of Π-2-categories are 2-equivalent via `𝔼₂`. That is, `E₂` is an
equivalence of the 1-truncations `Π-2-SCat ≌ Π-2-Cat` (inverse to `D₂`, Lemma 5.4), and for
2-superfunctors `ℝ, 𝕊 : 𝔄 → 𝔄'` the map `(X, x) ↦ 𝔼₂(X, x)` is a bijection from 2-natural
transformations `ℝ ⇒ 𝕊` to Π-2-natural transformations `E₂ ℝ ⇒ E₂ 𝕊`
(`TwoNatTrans.toOplaxTransEquiv`), compatible with identities and vertical composition
(`TwoNatTrans.toOplaxTrans_id`, `TwoNatTrans.toOplaxTrans_vcomp`). The 2-morphisms of both
2-categories are even (Definitions 2.2(iii), 5.2(iii)); see the README for the statement as
printed. The statement one level down (`Π-𝔖ℭ𝔞𝔱` and `Π-ℭ𝔞𝔱̂` are 2-superequivalent) is
`PiCat.twoSuperequivalent_piSCat_associated2`. -/
theorem toPiTwoCat_isTwoEquivalence :
    (toPiTwoCat : PiTwoSCat.{w, w₁, v₁, u₁} R ⥤ PiTwoCat.{w, w₁, v₁, u₁} R).IsEquivalence ∧
      ∀ {A A' : PiTwoSCat.{w, w₁, v₁, u₁} R} (F G : TwoSuperfunctor R A A'),
        Function.Bijective (fun θ : TwoNatTrans F G =>
          (⟨θ.toOplaxTrans, θ.isPiTwoNatural⟩ : { η : F.toOplax ⟶ G.toOplax //
            F.toPiTwoFunctor.IsPiTwoNatural G.toPiTwoFunctor η })) :=
  ⟨inferInstance, fun F G => (TwoNatTrans.toOplaxTransEquiv F G).bijective⟩

end PiTwoSCat

end StringDiagrams

end
