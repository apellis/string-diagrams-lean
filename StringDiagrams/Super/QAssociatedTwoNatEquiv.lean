import StringDiagrams.Super.QAssociatedTwoNat
import StringDiagrams.Super.QAssociatedTwoEquivalence
import StringDiagrams.Super.AssociatedTwoNatEquiv

/-!
# The §6 analogue of Theorem 5.5 on 2-morphisms: `𝔻` and `𝔼` are bijective on 2-morphisms

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6, the
discussion after Definition 6.14 (the analogue of Theorem 5.5, which the paper leaves to the
reader), for the `(Q, Π)`-2-functors and `(Q, Π)`-2-natural transformations of
`StringDiagrams.Super.QPiTwoFunctor` (definitions not given in the paper), and graded 2-natural
transformations (`TwoNatTrans.IsGraded`, components of degree zero) between graded
2-superfunctors.

* **`𝔻` is bijective on 2-morphisms.** For `(Q, Π)`-2-functors `ℝ, 𝕊 : 𝔄 → 𝔅`, every graded
  2-natural transformation `(X, x) : ℝ̂ ⇒ 𝕊̂` has even components of degree zero, which are
  2-morphisms of `𝔅` (`QAssociated2.ofHom2`); they form an oplax transformation `ℝ ⇒ 𝕊`
  (`QPiTwoFunctor.unmapQNat`) which is `(Q, Π)`-2-natural
  (`QPiTwoFunctor.unmapQNat_isQPiTwoNatural`: the Π-condition is the Π-2-naturality of
  `𝔼(X, x)`, `TwoNatTrans.isPiTwoNatural`, and the `q`-condition is `TwoNatTrans.kNat`), and this
  is inverse to `𝔻` (`QPiTwoFunctor.mapQNat_unmapQNat`, `QPiTwoFunctor.unmapQNat_mapQNat`,
  `QPiTwoFunctor.mapQNatEquiv`).
* **`𝔼` is bijective on 2-morphisms.** For graded 2-superfunctors `ℝ, 𝕊 : 𝔄 → 𝔄'` between
  graded `(Q, Π)`-2-supercategories, a `(Q, Π)`-2-natural transformation `𝔼 ℝ ⇒ 𝔼 𝕊` is
  natural with respect to all 2-morphisms of `𝔄` (of every degree and parity): a 2-morphism
  `x` of `𝔄` is `𝕋_𝔄` of `𝕋_𝔄⁻¹ x`, and `𝕋` carries the supernaturality of `𝔻` of the
  transformation to the naturality at `x` (`QAssociated2.T_map₂_mapQ`). Hence it is `𝔼` of a
  unique graded 2-natural transformation `ℝ ⇒ 𝕊` (`TwoNatTrans.ofQPiTwoNatural`,
  `TwoNatTrans.toQPiOplaxTransEquiv`).
* With the §6 analogue of Lemma 5.4 (`QPiTwoCat.equivalence`): the analogue of Theorem 5.5 read on
  1-truncations, from both sides (`QPiTwoCat.toQPiTwoGSCat_isTwoEquivalence`,
  `QPiTwoGSCat.toQPiTwoCat_isTwoEquivalence`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

/-! ### 2-morphisms of degree zero of `𝔄̂` -/

namespace QAssociated2

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [QPiTwoCategory R B]

theorem hom2_injective {a b : B} {f g : a ⟶ b} :
    Function.Injective (hom2 (R := R) : (f ⟶ g) → (hom1 (R := R) f ⟶ hom1 g)) := fun η θ h => by
  have h' : unitInv₂ (hom2U (R := R) η) = unitInv₂ (hom2U θ) :=
    congrArg unitInv₂ (Subtype.ext (Subtype.ext h))
  rwa [unitInv₂_hom2U, unitInv₂_hom2U] at h'

/-- The 2-morphism of `𝔄` underlying an even 2-morphism of degree zero of `𝔄̂`. -/
def ofHom2 {a b : B} {f g : a ⟶ b} (x : hom1 (R := R) f ⟶ hom1 g)
    (h0 : x ∈ GradedSupercategory.degree (R := R) _ _ 0) (he : x ∈ parity (R := R) _ _ 0) :
    f ⟶ g :=
  unitInv₂ (⟨⟨x, h0⟩, he⟩ : hom1U (R := R) f ⟶ hom1U g)

theorem hom2_ofHom2 {a b : B} {f g : a ⟶ b} (x : hom1 (R := R) f ⟶ hom1 g)
    (h0 : x ∈ GradedSupercategory.degree (R := R) _ _ 0) (he : x ∈ parity (R := R) _ _ 0) :
    hom2 (ofHom2 x h0 he) = x :=
  congrArg (fun y => y.1.1) (hom2U_unitInv₂ (⟨⟨x, h0⟩, he⟩ : hom1U (R := R) f ⟶ hom1U g))

/-- The 2-morphism of `𝔄` underlying an even 2-morphism of degree zero of `𝔄̂`, between
1-morphisms of `𝔄̂`. -/
def ofHom2' {a b : QAssociated2 R B} {f g : a ⟶ b} (x : f ⟶ g)
    (h0 : x ∈ GradedSupercategory.degree (R := R) _ _ 0) (he : x ∈ parity (R := R) _ _ 0) :
    f.obj.obj ⟶ g.obj.obj :=
  ofHom2 (a := a.obj.obj) (b := b.obj.obj) (f := f.obj.obj) (g := g.obj.obj) x h0 he

theorem hom2_ofHom2' {a b : QAssociated2 R B} {f g : a ⟶ b} (x : f ⟶ g)
    (h0 : x ∈ GradedSupercategory.degree (R := R) _ _ 0) (he : x ∈ parity (R := R) _ _ 0) :
    hom2 (R := R) (ofHom2' x h0 he) = x :=
  hom2_ofHom2 (a := a.obj.obj) (b := b.obj.obj) (f := f.obj.obj) (g := g.obj.obj) x h0 he

theorem ofHom2_hom2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    ofHom2 (hom2 (R := R) η) (hom2_mem_degree η) (hom2_mem η) = η :=
  unitInv₂_hom2U η

set_option backward.isDefEq.respectTransparency false in
theorem β_hom1 {a b : B} (f : a ⟶ b) :
    (PiTwoSupercategory.β (R := R) (hom1 (R := R) f)).hom =
      hom2 (PiTwoCategory.β (R := R) f).hom := by
  rw [Orbit2.β_hom_eq, Associated2.β_hom_eq]

set_option backward.isDefEq.respectTransparency false in
theorem γ_hom1 {a b : B} (f : a ⟶ b) :
    (QPiTwoSupercategory.γ (R := R) (hom1 (R := R) f)).hom =
      hom2 (QPiTwoCategory.γ (R := R) f).hom := by
  rw [Orbit2.γ_hom_eq, Associated2.centralShift_γ_eq]
  rfl

end QAssociated2

/-! ### `𝔻` is bijective on 2-morphisms -/

namespace QPiTwoFunctor

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [QPiTwoCategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [QPiTwoCategory R C]
  {F G : Pseudofunctor B C} {hF : QPiTwoFunctor R F} {hG : QPiTwoFunctor R G}

open QAssociated2

/-- **`𝔼 ∘ 𝔻 = 𝕀`, the coherence maps `c`**, inverse direction. -/
theorem mapQ_mapComp_inv {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (hF.mapQ.mapComp (hom1 (R := R) f) (hom1 g)).inv = hom2 (F.mapComp f g).hom := rfl

/-- **`𝔼 ∘ 𝔻 = 𝕀`, the coherence maps `i`**, inverse direction. -/
theorem mapQ_mapId_inv (a : B) :
    (hF.mapQ.mapId (⟨⟨a⟩⟩ : QAssociated2 R B)).inv = hom2 (F.mapId a).hom := rfl

variable (hF hG) in
/-- The components `X_λ : ℝλ → 𝕊λ` of a 2-natural transformation `ℝ̂ ⇒ 𝕊̂`, as 1-morphisms of
`𝔅`. -/
def unmapQNatApp (θ : TwoNatTrans hF.mapQ hG.mapQ) (a : B) : F.obj a ⟶ G.obj a :=
  (θ.X (⟨⟨a⟩⟩ : QAssociated2 R B)).obj.obj

variable (hF hG) in
/-- The components of a graded 2-natural transformation `ℝ̂ ⇒ 𝕊̂`, as 2-morphisms of `𝔅`. -/
def unmapQNatHom (θ : TwoNatTrans hF.mapQ hG.mapQ) (hθ : θ.IsGraded) {a b : B} (f : a ⟶ b) :
    F.map f ≫ unmapQNatApp hF hG θ b ⟶ unmapQNatApp hF hG θ a ≫ G.map f :=
  ofHom2' (θ.x (hom1 (R := R) f)) (hθ _) (θ.x_mem _)

theorem hom2_unmapQNatHom (θ : TwoNatTrans hF.mapQ hG.mapQ) (hθ : θ.IsGraded) {a b : B}
    (f : a ⟶ b) : hom2 (R := R) (unmapQNatHom hF hG θ hθ f) = θ.x (hom1 (R := R) f) :=
  hom2_ofHom2' _ _ _

/-- The second coherence condition of `(X, x)`, in the form used for `𝔻⁻¹(X, x)`. -/
theorem x_id_mapQ (θ : TwoNatTrans hF.mapQ hG.mapQ) (a : B) :
    θ.x (𝟙 (⟨⟨a⟩⟩ : QAssociated2 R B)) ≫
        BicategoryStruct.whiskerLeft (θ.X ⟨⟨a⟩⟩) (hG.mapQ.mapId ⟨⟨a⟩⟩).inv =
      BicategoryStruct.whiskerRight (hF.mapQ.mapId ⟨⟨a⟩⟩).inv (θ.X ⟨⟨a⟩⟩) ≫
        (BicategoryStruct.leftUnitor (θ.X ⟨⟨a⟩⟩)).hom ≫
          (BicategoryStruct.rightUnitor (θ.X ⟨⟨a⟩⟩)).inv := by
  rw [θ.x_id_eq]
  simp only [Category.assoc, TwoSupercategory.whiskerLeft_hom_inv R, Category.comp_id]

/-- The first coherence condition of `(X, x)`, in the form used for `𝔻⁻¹(X, x)`. -/
theorem x_comp_mapQ (θ : TwoNatTrans hF.mapQ hG.mapQ) {a b c : QAssociated2 R B} (f : a ⟶ b)
    (g : b ⟶ c) :
    θ.x (f ≫ g) ≫ BicategoryStruct.whiskerLeft (θ.X a) (hG.mapQ.mapComp f g).inv =
      BicategoryStruct.whiskerRight (hF.mapQ.mapComp f g).inv (θ.X c) ≫
        (BicategoryStruct.associator (hF.mapQ.map f) (hF.mapQ.map g) (θ.X c)).hom ≫
          BicategoryStruct.whiskerLeft (hF.mapQ.map f) (θ.x g) ≫
            (BicategoryStruct.associator (hF.mapQ.map f) (θ.X b) (hG.mapQ.map g)).inv ≫
              BicategoryStruct.whiskerRight (θ.x f) (hG.mapQ.map g) ≫
                (BicategoryStruct.associator (θ.X a) (hG.mapQ.map f) (hG.mapQ.map g)).hom := by
  rw [θ.x_comp_eq]
  simp only [Category.assoc, TwoSupercategory.whiskerLeft_hom_inv R, Category.comp_id]

variable (hF hG) in
/-- **The §6 analogue of Theorem 5.5, `𝔻⁻¹` on 2-morphisms.** The oplax transformation
`ℝ ⇒ 𝕊` with components `X_λ` and the 2-morphisms of `𝔅` underlying the components (even, of
degree zero) of a graded 2-natural transformation `(X, x) : ℝ̂ ⇒ 𝕊̂`. -/
@[simps]
def unmapQNat (θ : TwoNatTrans hF.mapQ hG.mapQ) (hθ : θ.IsGraded) :
    Oplax.OplaxTrans F.toOplax G.toOplax where
  app a := unmapQNatApp hF hG θ a
  naturality f := unmapQNatHom hF hG θ hθ f
  naturality_naturality {a b f g} η := by
    apply hom2_injective (R := R)
    simp only [Pseudofunctor.toOplax_toPrelaxFunctor]
    rw [hom2_comp, hom2_comp, hom2_whiskerRight, hom2_whiskerLeft, hom2_unmapQNatHom,
      hom2_unmapQNatHom, ← hF.mapQ_map₂_hom2, ← hG.mapQ_map₂_hom2]
    exact θ.naturality (hom2 η)
  naturality_id a := by
    apply hom2_injective (R := R)
    simp only [Pseudofunctor.toOplax_mapId, Pseudofunctor.toOplax_toPrelaxFunctor]
    rw [hom2_comp, hom2_comp, hom2_comp, hom2_whiskerRight, hom2_whiskerLeft, hom2_unmapQNatHom,
      hom2_leftUnitor_hom, hom2_rightUnitor_inv]
    exact x_id_mapQ θ a
  naturality_comp {a b c} f g := by
    apply hom2_injective (R := R)
    simp only [Pseudofunctor.toOplax_mapComp, Pseudofunctor.toOplax_toPrelaxFunctor]
    rw [hom2_comp, hom2_comp, hom2_comp, hom2_comp, hom2_comp, hom2_comp, hom2_whiskerRight,
      hom2_whiskerLeft, hom2_whiskerLeft, hom2_whiskerRight, hom2_unmapQNatHom, hom2_unmapQNatHom,
      hom2_unmapQNatHom, hom2_associator_hom, hom2_associator_inv, hom2_associator_hom]
    exact x_comp_mapQ θ (hom1 (R := R) f) (hom1 g)

theorem unmapQNat_naturality_eq (θ : TwoNatTrans hF.mapQ hG.mapQ) (hθ : θ.IsGraded) {a b : B}
    (f : a ⟶ b) : (unmapQNat hF hG θ hθ).naturality f = unmapQNatHom hF hG θ hθ f := rfl

/-- The Π-2-naturality of `𝔼(X, x)` in `𝔄̂` (`TwoNatTrans.isPiTwoNatural`). -/
theorem isPiTwoNatural_mapQ (θ : TwoNatTrans hF.mapQ hG.mapQ) (a : B) :
    (PiTwoSupercategory.β (R := R) (θ.X (⟨⟨a⟩⟩ : QAssociated2 R B))).hom ≫
        BicategoryStruct.whiskerRight (hF.mapQ.jIso (⟨⟨a⟩⟩ : QAssociated2 R B)).hom
          (θ.X (⟨⟨a⟩⟩ : QAssociated2 R B)) ≫
          θ.x (PiTwoSupercategory.pi (R := R) (⟨⟨a⟩⟩ : QAssociated2 R B)) =
      BicategoryStruct.whiskerLeft (θ.X (⟨⟨a⟩⟩ : QAssociated2 R B))
        (hG.mapQ.jIso (⟨⟨a⟩⟩ : QAssociated2 R B)).hom :=
  congrArg Subtype.val (θ.isPiTwoNatural (⟨⟨⟨a⟩⟩⟩ : Underlying2 R (QAssociated2 R B)))

/-- **The §6 analogue of Theorem 5.5.** `𝔻⁻¹(X, x)` is `(Q, Π)`-2-natural: the Π-condition is the
Π-2-naturality of `𝔼(X, x)` (`TwoNatTrans.isPiTwoNatural`) and the `q`-condition is
`TwoNatTrans.kNat`, read through `β̂ = β`, `γ̂ = γ`, `ĵ = j`, `k̂ = k`. -/
theorem unmapQNat_isQPiTwoNatural (θ : TwoNatTrans hF.mapQ hG.mapQ) (hθ : θ.IsGraded) :
    hF.IsQPiTwoNatural hG (unmapQNat hF hG θ hθ) := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · change (PiTwoCategory.β (R := R) (unmapQNatApp hF hG θ a)).hom ≫
        (hF.j a).hom ▷ unmapQNatApp hF hG θ a ≫ unmapQNatHom hF hG θ hθ (PiTwoCategory.pi R a) =
      unmapQNatApp hF hG θ a ◁ (hG.j a).hom
    apply hom2_injective (R := R)
    rw [hom2_comp, hom2_comp, hom2_whiskerRight, hom2_whiskerLeft,
      hom2_unmapQNatHom θ hθ, ← β_hom1,
      ← jIso_mapQ_hom, ← jIso_mapQ_hom]
    exact isPiTwoNatural_mapQ θ a
  · change (QPiTwoCategory.γ (R := R) (unmapQNatApp hF hG θ a)).hom ≫
        (hF.k a).hom ▷ unmapQNatApp hF hG θ a ≫ unmapQNatHom hF hG θ hθ (QPiTwoCategory.q R a) =
      unmapQNatApp hF hG θ a ◁ (hG.k a).hom
    apply hom2_injective (R := R)
    rw [hom2_comp, hom2_comp, hom2_whiskerRight, hom2_whiskerLeft,
      hom2_unmapQNatHom θ hθ, ← γ_hom1,
      ← kIso_mapQ_hom, ← kIso_mapQ_hom]
    exact θ.kNat (⟨⟨a⟩⟩ : QAssociated2 R B)

set_option backward.isDefEq.respectTransparency false in
/-- **The §6 analogue of Theorem 5.5, `𝔻 ∘ 𝔻⁻¹ = 𝕀` on 2-morphisms.** -/
theorem mapQNat_unmapQNat (θ : TwoNatTrans hF.mapQ hG.mapQ) (hθ : θ.IsGraded) :
    mapQNat (unmapQNat_isQPiTwoNatural θ hθ) = θ := by
  refine TwoNatTrans.ext_of_eq rfl fun f => ?_
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact hom2_unmapQNatHom θ hθ f.obj.obj

/-- **The §6 analogue of Theorem 5.5, `𝔻⁻¹ ∘ 𝔻 = 𝕀` on 2-morphisms.** -/
theorem unmapQNat_mapQNat {η : Oplax.OplaxTrans F.toOplax G.toOplax}
    (hη : hF.IsQPiTwoNatural hG η) :
    unmapQNat hF hG (mapQNat hη) (mapQNat_isGraded hη) = η := by
  have h : ∀ {a b : B} (f : a ⟶ b),
      (unmapQNat hF hG (mapQNat hη) (mapQNat_isGraded hη)).naturality f = η.naturality f :=
    fun f => hom2_injective (R := R) (hom2_unmapQNatHom (mapQNat hη) (mapQNat_isGraded hη) f)
  obtain ⟨app, nat, _, _, _⟩ := η
  change Oplax.OplaxTrans.mk app _ _ _ _ = Oplax.OplaxTrans.mk app nat _ _ _
  congr
  funext a b f
  exact h f

variable (hF hG) in
/-- **The §6 analogue of Theorem 5.5, on 2-morphisms.** `𝔻` is a bijection between
`(Q, Π)`-2-natural transformations `ℝ ⇒ 𝕊` and graded 2-natural transformations `ℝ̂ ⇒ 𝕊̂`. -/
@[simps]
def mapQNatEquiv :
    { η : Oplax.OplaxTrans F.toOplax G.toOplax // hF.IsQPiTwoNatural hG η } ≃
      { θ : TwoNatTrans hF.mapQ hG.mapQ // θ.IsGraded } where
  toFun η := ⟨mapQNat η.2, mapQNat_isGraded η.2⟩
  invFun θ := ⟨unmapQNat hF hG θ.1 θ.2, unmapQNat_isQPiTwoNatural θ.1 θ.2⟩
  left_inv η := Subtype.ext (unmapQNat_mapQNat η.2)
  right_inv θ := Subtype.ext (mapQNat_unmapQNat θ.1 θ.2)

end QPiTwoFunctor

/-! ### `𝔼` is bijective on 2-morphisms -/

namespace QAssociated2

open Supercategory GradedSupercategory BicategoryStruct TwoSupercategory CentralShift Orbit

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [∀ a b : A, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A] [GradedTwoSupercategory R A] [QPiTwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [∀ a b : A', GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A'] [GradedTwoSupercategory R A'] [QPiTwoSupercategory R A']
  {F G : TwoSuperfunctor R A A'} {hF : F.IsGraded} {hG : G.IsGraded}

attribute [local instance] QPiTwoSupercategory.centralShift

set_option backward.isDefEq.respectTransparency false in
/-- `𝕋` sends the components of `𝔻` of a `(Q, Π)`-2-natural transformation `𝔼 ℝ ⇒ 𝔼 𝕊` to its
components. -/
theorem T_map₂_mapQNat_x {η : Oplax.OplaxTrans (F.toDegreeZero2 hF).toPseudofunctor.toOplax
      (G.toDegreeZero2 hG).toPseudofunctor.toOplax}
    (hη : (F.toQPiTwoFunctor hF).IsQPiTwoNatural (G.toQPiTwoFunctor hG) η)
    {a b : QAssociated2 R (GUnderlying2 R A)} (f : a ⟶ b) :
    (T R A').map₂ ((QPiTwoFunctor.mapQNat hη).x f) = (η.naturality f.obj.obj).1.1 := by
  rw [T_map₂, QPiTwoFunctor.mapQNat_x, Thom_ι_map, TF_map]
  simp [Associated2.T_map₂]

end QAssociated2

namespace TwoNatTrans

open Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [∀ a b : A, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A] [GradedTwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [∀ a b : A', GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A'] [GradedTwoSupercategory R A']
  {F G : TwoSuperfunctor R A A'} {hF : F.IsGraded} {hG : G.IsGraded}

/-- A 2-natural transformation between the restrictions to degree zero of graded
2-superfunctors which is natural with respect to all 2-morphisms, as a 2-natural transformation
`ℝ ⇒ 𝕊` (graded: `TwoNatTrans.ofDegreeZero2_isGraded`). -/
def ofDegreeZero2 (θ : TwoNatTrans (F.toDegreeZero2 hF) (G.toDegreeZero2 hG))
    (nat : ∀ {a b : A} {f g : a ⟶ b} (ε : f ⟶ g),
      F.map₂ ε ▷ (θ.X ⟨b⟩).obj ≫ (θ.x (⟨g⟩ : (⟨a⟩ : DegreeZero2 R A) ⟶ ⟨b⟩)).1 =
        (θ.x (⟨f⟩ : (⟨a⟩ : DegreeZero2 R A) ⟶ ⟨b⟩)).1 ≫ (θ.X ⟨a⟩).obj ◁ G.map₂ ε) :
    TwoNatTrans F G where
  X a := (θ.X ⟨a⟩).obj
  x f := (θ.x (⟨f⟩ : (⟨_⟩ : DegreeZero2 R A) ⟶ ⟨_⟩)).1
  x_mem f := θ.x_mem (⟨f⟩ : (⟨_⟩ : DegreeZero2 R A) ⟶ ⟨_⟩)
  naturality ε := nat ε
  x_comp f g := congrArg Subtype.val
    (θ.x_comp (⟨f⟩ : (⟨_⟩ : DegreeZero2 R A) ⟶ ⟨_⟩) (⟨g⟩ : (⟨_⟩ : DegreeZero2 R A) ⟶ ⟨_⟩))
  x_id a := congrArg Subtype.val (θ.x_id (⟨a⟩ : DegreeZero2 R A))

theorem ofDegreeZero2_isGraded (θ : TwoNatTrans (F.toDegreeZero2 hF) (G.toDegreeZero2 hG))
    (nat : ∀ {a b : A} {f g : a ⟶ b} (ε : f ⟶ g),
      F.map₂ ε ▷ (θ.X ⟨b⟩).obj ≫ (θ.x (⟨g⟩ : (⟨a⟩ : DegreeZero2 R A) ⟶ ⟨b⟩)).1 =
        (θ.x (⟨f⟩ : (⟨a⟩ : DegreeZero2 R A) ⟶ ⟨b⟩)).1 ≫ (θ.X ⟨a⟩).obj ◁ G.map₂ ε) :
    (ofDegreeZero2 θ nat).IsGraded := fun f =>
  (θ.x (⟨f⟩ : (⟨_⟩ : DegreeZero2 R A) ⟶ ⟨_⟩)).2

variable [QPiTwoSupercategory R A] [QPiTwoSupercategory R A']

attribute [local instance] QPiTwoSupercategory.centralShift

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- A `(Q, Π)`-2-natural transformation `𝔼 ℝ ⇒ 𝔼 𝕊` is natural with respect to all 2-morphisms
of `𝔄` (of every degree and parity): a 2-morphism `ε` of `𝔄` is `𝕋_𝔄(𝕋_𝔄⁻¹ ε)`, and `𝕋_{𝔄'}`
carries the supernaturality of `𝔻` of the transformation at `𝕋_𝔄⁻¹ ε` to the naturality at `ε`
(`QAssociated2.T_map₂_mapQ`). -/
theorem naturality_of_isQPiTwoNatural {η : Oplax.OplaxTrans
      (F.toDegreeZero2 hF).toPseudofunctor.toOplax (G.toDegreeZero2 hG).toPseudofunctor.toOplax}
    (hη : (F.toQPiTwoFunctor hF).IsQPiTwoNatural (G.toQPiTwoFunctor hG) η)
    {a b : A} {f g : a ⟶ b} (ε : f ⟶ g) :
    F.map₂ ε ▷ (η.app ⟨⟨b⟩⟩).obj.obj ≫
        (η.naturality (⟨⟨g⟩⟩ : (⟨⟨a⟩⟩ : GUnderlying2 R A) ⟶ ⟨⟨b⟩⟩)).1.1 =
      (η.naturality (⟨⟨f⟩⟩ : (⟨⟨a⟩⟩ : GUnderlying2 R A) ⟶ ⟨⟨b⟩⟩)).1.1 ≫
        (η.app ⟨⟨a⟩⟩).obj.obj ◁ G.map₂ ε := by
  have n := (QPiTwoFunctor.mapQNat hη).naturality (QAssociated2.tinv₂ R A ε)
  have e := congrArg (QAssociated2.T R A').map₂ n
  rw [(QAssociated2.T R A').map₂_comp, (QAssociated2.T R A').map₂_comp] at e
  rw [QAssociated2.T_map₂_whiskerRight, QAssociated2.T_map₂_whiskerLeft] at e
  rw [QAssociated2.T_map₂_mapQ, QAssociated2.T_map₂_mapQ, QAssociated2.T_map₂_tinv₂] at e
  rw [QAssociated2.T_map₂_mapQNat_x, QAssociated2.T_map₂_mapQNat_x] at e
  exact e

/-- **The §6 analogue of Theorem 5.5, `𝔼⁻¹` on 2-morphisms.** A `(Q, Π)`-2-natural
transformation `𝔼 ℝ ⇒ 𝔼 𝕊` between the underlying `(Q, Π)`-2-functors of graded
2-superfunctors `ℝ, 𝕊 : 𝔄 → 𝔄'` is natural with respect to all 2-morphisms
(`TwoNatTrans.naturality_of_isQPiTwoNatural`), hence a graded 2-natural transformation `ℝ ⇒ 𝕊`. -/
def ofQPiTwoNatural (η : Oplax.OplaxTrans
      (F.toDegreeZero2 hF).toPseudofunctor.toOplax (G.toDegreeZero2 hG).toPseudofunctor.toOplax)
    (hη : (F.toQPiTwoFunctor hF).IsQPiTwoNatural (G.toQPiTwoFunctor hG) η) : TwoNatTrans F G :=
  ofDegreeZero2 (ofOplaxTrans η fun ε => DegreeZero.hom_ext (naturality_of_isQPiTwoNatural hη ε.1))
    fun ε => naturality_of_isQPiTwoNatural hη ε

theorem ofQPiTwoNatural_isGraded (η : Oplax.OplaxTrans
      (F.toDegreeZero2 hF).toPseudofunctor.toOplax (G.toDegreeZero2 hG).toPseudofunctor.toOplax)
    (hη : (F.toQPiTwoFunctor hF).IsQPiTwoNatural (G.toQPiTwoFunctor hG) η) :
    (ofQPiTwoNatural η hη).IsGraded :=
  ofDegreeZero2_isGraded _ _

/-- `𝔼 ∘ 𝔼⁻¹ = 𝕀` on 2-morphisms. -/
theorem toOplaxTrans_ofQPiTwoNatural (η : Oplax.OplaxTrans
      (F.toDegreeZero2 hF).toPseudofunctor.toOplax (G.toDegreeZero2 hG).toPseudofunctor.toOplax)
    (hη : (F.toQPiTwoFunctor hF).IsQPiTwoNatural (G.toQPiTwoFunctor hG) η) :
    ((ofQPiTwoNatural η hη).toDegreeZero2 hF hG (ofQPiTwoNatural_isGraded η hη)).toOplaxTrans =
      η :=
  rfl

/-- `𝔼⁻¹ ∘ 𝔼 = 𝕀` on 2-morphisms. -/
theorem ofQPiTwoNatural_toOplaxTrans (θ : TwoNatTrans F G) (hθ : θ.IsGraded) :
    ofQPiTwoNatural (θ.toDegreeZero2 hF hG hθ).toOplaxTrans (θ.isQPiTwoNatural hF hG hθ) = θ := by
  obtain ⟨X, x, _, _, _, _⟩ := θ
  rfl

variable (hF hG) in
/-- **Brundan–Ellis, §6, the analogue of Theorem 5.5, `𝔼` on 2-morphisms.** `𝔼` is a bijection
between graded 2-natural transformations `ℝ ⇒ 𝕊` and `(Q, Π)`-2-natural transformations
`𝔼 ℝ ⇒ 𝔼 𝕊`. -/
@[simps]
def toQPiOplaxTransEquiv :
    { θ : TwoNatTrans F G // θ.IsGraded } ≃
      { η : Oplax.OplaxTrans (F.toDegreeZero2 hF).toPseudofunctor.toOplax
          (G.toDegreeZero2 hG).toPseudofunctor.toOplax //
        (F.toQPiTwoFunctor hF).IsQPiTwoNatural (G.toQPiTwoFunctor hG) η } where
  toFun θ := ⟨(θ.1.toDegreeZero2 hF hG θ.2).toOplaxTrans, θ.1.isQPiTwoNatural hF hG θ.2⟩
  invFun η := ⟨ofQPiTwoNatural η.1 η.2, ofQPiTwoNatural_isGraded η.1 η.2⟩
  left_inv θ := Subtype.ext (ofQPiTwoNatural_toOplaxTrans θ.1 θ.2)
  right_inv η := Subtype.ext (toOplaxTrans_ofQPiTwoNatural η.1 η.2)

end TwoNatTrans

/-! ### The §6 analogue of Theorem 5.5 on 1-truncations -/

namespace QPiTwoCat

variable {R : Type w} [CommRing R]

/-- **Brundan–Ellis, §6, the analogue of Theorem 5.5** (left to the reader in the paper), read on
1-truncations: `𝔻` is an equivalence of the categories `(Q, Π)-2-Cat ≌ (Q, Π)-2-GSCat`
(`QPiTwoCat.equivalence`), and for `(Q, Π)`-2-functors `ℝ, 𝕊 : 𝔄 → 𝔅` it is a bijection from
`(Q, Π)`-2-natural transformations `ℝ ⇒ 𝕊` to graded 2-natural transformations `ℝ̂ ⇒ 𝕊̂`
(`QPiTwoFunctor.mapQNatEquiv`), compatible with identities and vertical composition
(`QPiTwoFunctor.mapQNat_id`, `QPiTwoFunctor.mapQNat_vcomp`). -/
theorem toQPiTwoGSCat_isTwoEquivalence :
    (toQPiTwoGSCat : QPiTwoCat.{w, w₁, v₁, u₁} R ⥤ QPiTwoGSCat.{w, w₁, v₁, u₁} R).IsEquivalence ∧
      ∀ {B C : QPiTwoCat.{w, w₁, v₁, u₁} R} (P Q : B ⟶ C),
        Function.Bijective (fun η : { η : Oplax.OplaxTrans P.toPseudofunctor.toOplax
            Q.toPseudofunctor.toOplax // P.toQPiTwoFunctor.IsQPiTwoNatural Q.toQPiTwoFunctor η } =>
          (⟨QPiTwoFunctor.mapQNat η.2, QPiTwoFunctor.mapQNat_isGraded η.2⟩ :
            { θ : TwoNatTrans P.toQPiTwoFunctor.mapQ Q.toQPiTwoFunctor.mapQ // θ.IsGraded })) :=
  ⟨inferInstance, fun P Q =>
    (QPiTwoFunctor.mapQNatEquiv P.toQPiTwoFunctor Q.toQPiTwoFunctor).bijective⟩

end QPiTwoCat

namespace QPiTwoGSCat

variable {R : Type w} [CommRing R]

/-- **Brundan–Ellis, §6, the analogue of Theorem 5.5** from the side of `𝔼`, read on
1-truncations: `𝔼` is an equivalence of the categories `(Q, Π)-2-GSCat ≌ (Q, Π)-2-Cat`, and for
graded 2-superfunctors `ℝ, 𝕊 : 𝔄 → 𝔄'` it is a bijection from graded 2-natural transformations
`ℝ ⇒ 𝕊` to `(Q, Π)`-2-natural transformations `𝔼 ℝ ⇒ 𝔼 𝕊`
(`TwoNatTrans.toQPiOplaxTransEquiv`). -/
theorem toQPiTwoCat_isTwoEquivalence :
    (toQPiTwoCat : QPiTwoGSCat.{w, w₁, v₁, u₁} R ⥤ QPiTwoCat.{w, w₁, v₁, u₁} R).IsEquivalence ∧
      ∀ {A A' : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F G : A ⟶ A'),
        Function.Bijective (fun θ : { θ : TwoNatTrans F.1 G.1 // θ.IsGraded } =>
          (⟨(θ.1.toDegreeZero2 F.2 G.2 θ.2).toOplaxTrans, θ.1.isQPiTwoNatural F.2 G.2 θ.2⟩ :
            { η : Oplax.OplaxTrans (F.1.toDegreeZero2 F.2).toPseudofunctor.toOplax
                (G.1.toDegreeZero2 G.2).toPseudofunctor.toOplax //
              (F.1.toQPiTwoFunctor F.2).IsQPiTwoNatural (G.1.toQPiTwoFunctor G.2) η })) :=
  ⟨inferInstance, fun F G => (TwoNatTrans.toQPiOplaxTransEquiv F.2 G.2).bijective⟩

end QPiTwoGSCat

end StringDiagrams

end
