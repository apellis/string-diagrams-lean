import StringDiagrams.Super.OplaxWhisker
import StringDiagrams.Super.QAssociatedTwoNatEquiv
import StringDiagrams.Super.TwoFunctorPrecomposition
import StringDiagrams.Super.TwoFunctorPostcomposition

/-!
# Theorem 5.5 and its §6 analogue: whiskering

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Theorem 5.5
and its §6 analogue (after Definition 6.14), both left to the reader.

Because 2-natural transformations are oplax (Definition 2.2(iii)), `Π-2-𝔖ℭ𝔄𝔗` and `Π-2-ℭ𝔄𝔗`
are sesquicategories rather than 2-categories (the interchange law fails,
`StringDiagrams.Super.TwoSCatInterchange`; see the README erratum). This file supplies the
whiskering part of Theorem 5.5 in that corrected form:

* whiskering a Π-2-natural (resp. `(Q, Π)`-2-natural) transformation by a Π-2-functor (resp.
  `(Q, Π)`-2-functor) on either side is Π-2-natural (resp. `(Q, Π)`-2-natural), with the
  composite `j` (and `k`) of `PiTwoFunctor.comp` (`PiTwoFunctor.IsPiTwoNatural.precomp`,
  `PiTwoFunctor.IsPiTwoNatural.postcomp`, `QPiTwoFunctor.IsQPiTwoNatural.precomp`,
  `QPiTwoFunctor.IsQPiTwoNatural.postcomp`), using the whiskerings of oplax transformations of
  `StringDiagrams.Super.OplaxWhisker`;
* `𝔼₂` (resp. `𝔼`) commutes with whiskering by 2-superfunctors (resp. graded 2-superfunctors)
  on either side (`TwoNatTrans.toOplaxTrans_precompose`, `TwoNatTrans.toOplaxTrans_postcompose`,
  `TwoNatTrans.toOplaxTrans_toDegreeZero2_precompose`,
  `TwoNatTrans.toOplaxTrans_toDegreeZero2_postcompose`);
* Theorem 5.5 and its §6 analogue in sesquicategory form: `𝔼₂`, `𝔼` are equivalences of the
  1-truncations, bijective on 2-morphisms and compatible with whiskering
  (`PiTwoSCat.toPiTwoCat_isSesquiEquivalence`, `QPiTwoGSCat.toQPiTwoCat_isSesquiEquivalence`).
  `𝔻₂`, `𝔻` are their quasi-inverses (Lemma 5.4, `PiTwoCat.equivalence`, `QPiTwoCat.equivalence`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory
open scoped Oplax.OplaxTrans

universe w w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃ w₄ v₄ u₄

section PiNat

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

namespace PiTwoFunctor

variable [PiTwoCategory R B] [PiTwoCategory R C] [PiTwoCategory R D] [PiTwoCategory R E]

/-- Whiskering a Π-2-natural transformation on the left by a Π-2-functor gives a Π-2-natural
transformation. -/
theorem IsPiTwoNatural.precomp {P : Pseudofunctor B C} (hP : PiTwoFunctor R P)
    {F G : Pseudofunctor C D} {hF : PiTwoFunctor R F} {hG : PiTwoFunctor R G}
    {η : Oplax.OplaxTrans F.toOplax G.toOplax} (hη : hF.IsPiTwoNatural hG η) :
    (hP.comp hF).IsPiTwoNatural (hP.comp hG) (Oplax.OplaxTrans.precomp P η) := fun a =>
  Oplax.OplaxTrans.precomp_central (fun f => (PiTwoCategory.β (R := R) f).hom) P hP.j hF.j
    hG.j η hη a

/-- Whiskering a Π-2-natural transformation on the right by a Π-2-functor gives a Π-2-natural
transformation. -/
theorem IsPiTwoNatural.postcomp {F G : Pseudofunctor B C} {hF : PiTwoFunctor R F}
    {hG : PiTwoFunctor R G} {η : Oplax.OplaxTrans F.toOplax G.toOplax}
    (hη : hF.IsPiTwoNatural hG η) {H : Pseudofunctor C D} (hH : PiTwoFunctor R H) :
    (hF.comp hH).IsPiTwoNatural (hG.comp hH) (Oplax.OplaxTrans.postcomp η H) := fun a =>
  Oplax.OplaxTrans.postcomp_central (fun f => (PiTwoCategory.β (R := R) f).hom)
    (fun f => (PiTwoCategory.β (R := R) f).hom) H hF.j hG.j hH.j hH.β_comm η hη a

end PiTwoFunctor

namespace QPiTwoFunctor

variable [QPiTwoCategory R B] [QPiTwoCategory R C] [QPiTwoCategory R D]

/-- Whiskering a `(Q, Π)`-2-natural transformation on the left by a `(Q, Π)`-2-functor gives a
`(Q, Π)`-2-natural transformation. -/
theorem IsQPiTwoNatural.precomp {P : Pseudofunctor B C} (hP : QPiTwoFunctor R P)
    {F G : Pseudofunctor C D} {hF : QPiTwoFunctor R F} {hG : QPiTwoFunctor R G}
    {η : Oplax.OplaxTrans F.toOplax G.toOplax} (hη : hF.IsQPiTwoNatural hG η) :
    (hP.comp hF).IsQPiTwoNatural (hP.comp hG) (Oplax.OplaxTrans.precomp P η) :=
  ⟨hη.1.precomp hP.toPiTwoFunctor, fun a =>
    Oplax.OplaxTrans.precomp_central (fun f => (QPiTwoCategory.γ (R := R) f).hom) P hP.k hF.k
      hG.k η hη.2 a⟩

/-- Whiskering a `(Q, Π)`-2-natural transformation on the right by a `(Q, Π)`-2-functor gives a
`(Q, Π)`-2-natural transformation. -/
theorem IsQPiTwoNatural.postcomp {F G : Pseudofunctor B C} {hF : QPiTwoFunctor R F}
    {hG : QPiTwoFunctor R G} {η : Oplax.OplaxTrans F.toOplax G.toOplax}
    (hη : hF.IsQPiTwoNatural hG η) {H : Pseudofunctor C D} (hH : QPiTwoFunctor R H) :
    (hF.comp hH).IsQPiTwoNatural (hG.comp hH) (Oplax.OplaxTrans.postcomp η H) :=
  ⟨hη.1.postcomp hH.toPiTwoFunctor, fun a =>
    Oplax.OplaxTrans.postcomp_central (fun f => (QPiTwoCategory.γ (R := R) f).hom)
      (fun f => (QPiTwoCategory.γ (R := R) f).hom) H hF.k hG.k hH.k hH.γ_comm η hη.2 a⟩

end QPiTwoFunctor

end PiNat

section Super

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

namespace TwoNatTrans

theorem toOplaxTrans_precompose (P : TwoSuperfunctor R A A') {F G : TwoSuperfunctor R A' A''}
    (θ : TwoNatTrans F G) :
    (θ.precompose P).toOplaxTrans = (Oplax.OplaxTrans.precomp P.toPseudofunctor
      (F := F.toPseudofunctor) (G := G.toPseudofunctor) θ.toOplaxTrans :
        (P.comp F).toOplax ⟶ (P.comp G).toOplax) := rfl

theorem toOplaxTrans_postcompose {F G : TwoSuperfunctor R A A'} (θ : TwoNatTrans F G)
    (H : TwoSuperfunctor R A' A'') :
    (θ.postcompose H).toOplaxTrans = (Oplax.OplaxTrans.postcomp (F := F.toPseudofunctor)
      (G := G.toPseudofunctor) θ.toOplaxTrans H.toPseudofunctor :
        (F.comp H).toOplax ⟶ (G.comp H).toOplax) := rfl

section Graded

variable [∀ a b : A, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R A]
  [∀ a b : A', GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R A']
  [∀ a b : A'', GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R A'']

theorem toOplaxTrans_toDegreeZero2_precompose {P : TwoSuperfunctor R A A'}
    {F G : TwoSuperfunctor R A' A''} (hP : P.IsGraded) (hF : F.IsGraded) (hG : G.IsGraded)
    (θ : TwoNatTrans F G) (hθ : θ.IsGraded) :
    ((θ.precompose P).toDegreeZero2 (hP.comp hF) (hP.comp hG)
        (precompose_isGraded P hθ)).toOplaxTrans =
      (Oplax.OplaxTrans.precomp (P.toDegreeZero2 hP).toPseudofunctor
        (F := (F.toDegreeZero2 hF).toPseudofunctor) (G := (G.toDegreeZero2 hG).toPseudofunctor)
        (θ.toDegreeZero2 hF hG hθ).toOplaxTrans :
          ((P.comp F).toDegreeZero2 (hP.comp hF)).toOplax ⟶
            ((P.comp G).toDegreeZero2 (hP.comp hG)).toOplax) := rfl

theorem toOplaxTrans_toDegreeZero2_postcompose {F G : TwoSuperfunctor R A A'}
    {H : TwoSuperfunctor R A' A''} (hF : F.IsGraded) (hG : G.IsGraded) (hH : H.IsGraded)
    (θ : TwoNatTrans F G) (hθ : θ.IsGraded) :
    ((θ.postcompose H).toDegreeZero2 (hF.comp hH) (hG.comp hH)
        (postcompose_isGraded H hH hθ)).toOplaxTrans =
      (Oplax.OplaxTrans.postcomp (F := (F.toDegreeZero2 hF).toPseudofunctor)
        (G := (G.toDegreeZero2 hG).toPseudofunctor) (θ.toDegreeZero2 hF hG hθ).toOplaxTrans
        (H.toDegreeZero2 hH).toPseudofunctor :
          ((F.comp H).toDegreeZero2 (hF.comp hH)).toOplax ⟶
            ((G.comp H).toDegreeZero2 (hG.comp hH)).toOplax) := rfl

end Graded

end TwoNatTrans

end Super

/-! ## Theorem 5.5 and its §6 analogue in sesquicategory form -/

namespace PiTwoSCat

variable {R : Type w} [CommRing R]

/-- **Brundan–Ellis, Theorem 5.5 (corrected; see the README erratum to Definition 2.2(iii)).**
`𝔼₂` is an equivalence of the 1-truncations `Π-2-SCat ≌ Π-2-Cat`, it is bijective on
2-morphisms (2-natural transformations `ℝ ⇒ 𝕊` correspond to Π-2-natural transformations
`E₂ ℝ ⇒ E₂ 𝕊`), and it commutes with whiskering by 2-superfunctors on either side: whiskering
`(X, x)` by `ℙ` or `ℍ` and then applying `𝔼₂` gives the whiskering of `𝔼₂(X, x)` by `E₂ ℙ` or
`E₂ ℍ`. Together with the compatibility with identities and vertical composition
(`TwoNatTrans.toOplaxTrans_id`, `TwoNatTrans.toOplaxTrans_vcomp`) this is the statement of
Theorem 5.5 for the sesquicategories `Π-2-𝔖ℭ𝔄𝔗`, `Π-2-ℭ𝔄𝔗`. Whiskering in `Π-2-ℭ𝔄𝔗` preserves
Π-2-naturality (`PiTwoFunctor.IsPiTwoNatural.precomp`, `PiTwoFunctor.IsPiTwoNatural.postcomp`). -/
theorem toPiTwoCat_isSesquiEquivalence :
    (toPiTwoCat : PiTwoSCat.{w, w₁, v₁, u₁} R ⥤ PiTwoCat.{w, w₁, v₁, u₁} R).IsEquivalence ∧
      (∀ {A A' : PiTwoSCat.{w, w₁, v₁, u₁} R} (F G : TwoSuperfunctor R A A'),
        Function.Bijective (fun θ : TwoNatTrans F G =>
          (⟨θ.toOplaxTrans, θ.isPiTwoNatural⟩ : { η : F.toOplax ⟶ G.toOplax //
            F.toPiTwoFunctor.IsPiTwoNatural G.toPiTwoFunctor η }))) ∧
      (∀ {A A' A'' : PiTwoSCat.{w, w₁, v₁, u₁} R} (P : TwoSuperfunctor R A A')
        {F G : TwoSuperfunctor R A' A''} (θ : TwoNatTrans F G),
        (θ.precompose P).toOplaxTrans = (Oplax.OplaxTrans.precomp P.toPseudofunctor
          (F := F.toPseudofunctor) (G := G.toPseudofunctor) θ.toOplaxTrans :
            (P.comp F).toOplax ⟶ (P.comp G).toOplax)) ∧
      (∀ {A A' A'' : PiTwoSCat.{w, w₁, v₁, u₁} R} {F G : TwoSuperfunctor R A A'}
        (θ : TwoNatTrans F G) (H : TwoSuperfunctor R A' A''),
        (θ.postcompose H).toOplaxTrans = (Oplax.OplaxTrans.postcomp (F := F.toPseudofunctor)
          (G := G.toPseudofunctor) θ.toOplaxTrans H.toPseudofunctor :
            (F.comp H).toOplax ⟶ (G.comp H).toOplax)) :=
  ⟨toPiTwoCat_isTwoEquivalence.1, toPiTwoCat_isTwoEquivalence.2,
    fun P _ _ θ => TwoNatTrans.toOplaxTrans_precompose P θ,
    fun θ H => TwoNatTrans.toOplaxTrans_postcompose θ H⟩

end PiTwoSCat

namespace QPiTwoGSCat

variable {R : Type w} [CommRing R]

/-- **Brundan–Ellis, §6, the analogue of Theorem 5.5 (corrected)**, in sesquicategory form:
`𝔼` is an equivalence of the 1-truncations `(Q, Π)-2-GSCat ≌ (Q, Π)-2-Cat`, bijective from
graded 2-natural transformations `ℝ ⇒ 𝕊` to `(Q, Π)`-2-natural transformations `𝔼 ℝ ⇒ 𝔼 𝕊`,
and commutes with whiskering by graded 2-superfunctors on either side. Whiskering in
`(Q, Π)-2-ℭ𝔄𝔗` preserves `(Q, Π)`-2-naturality (`QPiTwoFunctor.IsQPiTwoNatural.precomp`,
`QPiTwoFunctor.IsQPiTwoNatural.postcomp`). -/
theorem toQPiTwoCat_isSesquiEquivalence :
    (toQPiTwoCat : QPiTwoGSCat.{w, w₁, v₁, u₁} R ⥤ QPiTwoCat.{w, w₁, v₁, u₁} R).IsEquivalence ∧
      (∀ {A A' : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F G : A ⟶ A'),
        Function.Bijective (fun θ : { θ : TwoNatTrans F.1 G.1 // θ.IsGraded } =>
          (⟨(θ.1.toDegreeZero2 F.2 G.2 θ.2).toOplaxTrans, θ.1.isQPiTwoNatural F.2 G.2 θ.2⟩ :
            { η : Oplax.OplaxTrans (F.1.toDegreeZero2 F.2).toPseudofunctor.toOplax
                (G.1.toDegreeZero2 G.2).toPseudofunctor.toOplax //
              (F.1.toQPiTwoFunctor F.2).IsQPiTwoNatural (G.1.toQPiTwoFunctor G.2) η }))) ∧
      (∀ {A A' A'' : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (P : A ⟶ A') (F G : A' ⟶ A'')
        (θ : TwoNatTrans F.1 G.1) (hθ : θ.IsGraded),
        ((θ.precompose P.1).toDegreeZero2 (P.2.comp F.2) (P.2.comp G.2)
            (TwoNatTrans.precompose_isGraded P.1 hθ)).toOplaxTrans =
          (Oplax.OplaxTrans.precomp (P.1.toDegreeZero2 P.2).toPseudofunctor
            (F := (F.1.toDegreeZero2 F.2).toPseudofunctor)
            (G := (G.1.toDegreeZero2 G.2).toPseudofunctor)
            (θ.toDegreeZero2 F.2 G.2 hθ).toOplaxTrans :
              ((P.1.comp F.1).toDegreeZero2 (P.2.comp F.2)).toOplax ⟶
                ((P.1.comp G.1).toDegreeZero2 (P.2.comp G.2)).toOplax)) ∧
      (∀ {A A' A'' : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F G : A ⟶ A') (H : A' ⟶ A'')
        (θ : TwoNatTrans F.1 G.1) (hθ : θ.IsGraded),
        ((θ.postcompose H.1).toDegreeZero2 (F.2.comp H.2) (G.2.comp H.2)
            (TwoNatTrans.postcompose_isGraded H.1 H.2 hθ)).toOplaxTrans =
          (Oplax.OplaxTrans.postcomp (F := (F.1.toDegreeZero2 F.2).toPseudofunctor)
            (G := (G.1.toDegreeZero2 G.2).toPseudofunctor)
            (θ.toDegreeZero2 F.2 G.2 hθ).toOplaxTrans (H.1.toDegreeZero2 H.2).toPseudofunctor :
              ((F.1.comp H.1).toDegreeZero2 (F.2.comp H.2)).toOplax ⟶
                ((G.1.comp H.1).toDegreeZero2 (G.2.comp H.2)).toOplax)) :=
  ⟨toQPiTwoCat_isTwoEquivalence.1, toQPiTwoCat_isTwoEquivalence.2,
    fun P F G θ hθ => TwoNatTrans.toOplaxTrans_toDegreeZero2_precompose P.2 F.2 G.2 θ hθ,
    fun F G H θ hθ => TwoNatTrans.toOplaxTrans_toDegreeZero2_postcompose F.2 G.2 H.2 θ hθ⟩

end QPiTwoGSCat

end StringDiagrams

end
