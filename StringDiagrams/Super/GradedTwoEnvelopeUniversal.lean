import StringDiagrams.Super.QTwoEnvelopeUniversal
import StringDiagrams.Super.TwoEnvelopePi

/-!
# The universal property of the (Q, Π)-envelope of a graded 2-supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Lemma 6.11 and the analogue of Theorem 4.9 stated after Definition 6.10.

Let `𝔄` be a graded 2-supercategory and `𝔅` a graded `(Q, Π)`-2-supercategory (Definition 6.5),
or more generally a graded 2-supercategory whose morphism supercategories carry graded
`(Q, Π)`-supercategory structures. For a graded `(Q, Π)`-2-supercategory these are
`Q = q_μ -`, `Q⁻¹ = q_μ⁻¹ -`, `Π = π_μ -` on `ℋom(λ, μ)` (`QPiTwoSupercategory.homQPiLeft`,
extending `PiTwoSupercategory.homPiLeft`).

The `(Q, Π)`-envelope `𝔄_{q,π}` of Definition 6.10 is `TwoEnvelope R (QTwoEnvelope R 𝔄)`
(`StringDiagrams.Super.GradedTwoEnvelope`), the Π-envelope of the `Q`-envelope, so the
extension of Lemma 6.11 is the extension of Lemma 4.7 (`TwoEnvelope.extend`,
`StringDiagrams.Super.TwoEnvelopeUniversal`) applied to the extension along the `Q`-envelope
(`QTwoEnvelope.extend`, `StringDiagrams.Super.QTwoEnvelopeUniversal`). The canonical strict
graded 2-superfunctor `𝕁 : 𝔄 → 𝔄_{q,π}` is `QPiTwoEnvelope.twoJ` (`F ↦ Q⁰Π⁰F`,
`x ↦ x^{0,0}_{0,0}`).

## Lemma 6.11(i)

A 2-superfunctor `ℝ : 𝔄 → 𝔅` extends to `ℝ̃ : 𝔄_{q,π} → 𝔅` (`QPiTwoEnvelope.extend`, and
`QPiTwoEnvelope.extendQPi` for a graded `(Q, Π)`-2-supercategory `𝔅`) with `ℝ̃λ = ℝλ`,

  `ℝ̃(Q^m Π^a F) = Π^a Q^m (ℝF)`  (for a graded `(Q, Π)`-2-supercategory: `π^a_{ℝμ} q^m_{ℝμ} (ℝF)`),

  `ℝ̃(x^{n,b}_{m,a}) = (σ^n_{ℝμ} ζ^b_{ℝμ} (ℝG))⁻¹ ∘ ℝx ∘ (σ^m_{ℝμ} ζ^a_{ℝμ} (ℝF))`,

with `ζ^a` and `σ^m` as in the proof of Lemma 6.11 (`Envelope.ζPow`, `QPiSupercategory.σPow`),
`ĩ = i`, and coherence maps

  `c̃_{Q^nΠ^bG, Q^mΠ^aF} = (-1)^{ab} (ζ^{a+b})⁻¹ ∘ (σ^{m+n})⁻¹ ∘ c_{G,F} ∘ (σ^n σ^m) ∘ (ζ^b ζ^a)`

(`QPiTwoEnvelope.extendComp_hom`): the powers of `q` are collapsed by the `σ`'s, i.e. by the
2-isomorphisms of Lemma 6.6(iii), the two copies of `π` by `-ξ` when `a = b = 1` (the sign
`(-1)^{ab}`; see `StringDiagrams.Super.TwoEnvelopePi`), and the rearrangement of the shift
1-morphisms past `ℝG` in the paper's description of `c̃` is the composite of the `σ`'s and
`ζ`'s with their inverses, i.e. of the half-braidings `γ` and `β` of Lemma 6.6(i)–(ii)
(`QPiTwoEnvelope.extendComp_Q_one_zero` for `γ`, `TwoEnvelope.extendComp_one_zero`,
`TwoEnvelope.extendComp_one_one` for `β` and `-ξ`). The convention `Π^a Q^m` (rather than
the paper's `q^m π^a`) is that of `QPiEnvelope.extend`; the two orders give 2-superfunctors
isomorphic through `γ_{π}` (Lemma 6.6(ii)). `ℝ = ℝ̃ 𝕁` as 2-superfunctors
(`QPiTwoEnvelope.twoJ_comp_extend`), and `ℝ̃` is graded when `ℝ` is
(`QPiTwoEnvelope.extend_isGraded`).

## Lemma 6.11(ii)

A 2-natural transformation `(X, x) : ℝ ⇒ 𝕊` extends to `(X̃, x̃) : ℝ̃ ⇒ 𝕊̃` with `X̃_λ = X_λ`
and `x̃_{Q^mΠ^aF} = (σ^m ζ^a_{𝕊F} X_λ)⁻¹ ∘ x_F ∘ (X_μ σ^m ζ^a_{ℝF})`
(`QPiTwoEnvelope.extendTwoNatTrans`), uniquely (`QPiTwoEnvelope.extendTwoNatTrans_unique`);
it is graded if and only if `(X, x)` is (`QPiTwoEnvelope.extendTwoNatTrans_isGraded_iff`).

## The analogue of Theorem 4.9

Restriction along `𝕁` is a bijection on 2-natural transformations
(`QPiTwoEnvelope.extendTwoNatTransEquiv`, and on graded ones,
`QPiTwoEnvelope.extendGradedTwoNatTransEquiv`), functorial
(`QPiTwoEnvelope.extendTwoNatTrans_id`, `QPiTwoEnvelope.extendTwoNatTrans_vcomp`); with the
extension of supermodifications `α̃_λ = α_λ` it is a superequivalence
`ℋom(ℝ, 𝕊) → ℋom(ℝ̃, 𝕊̃)` (`QPiTwoEnvelope.extendHomSuperequivalence`), bijective on
supermodifications homogeneous of each parity and degree
(`QPiTwoEnvelope.extendSupermodification_isHomogeneous_iff`); every graded 2-superfunctor
`𝕋 : 𝔄_{q,π} → 𝔅` is isomorphic to `(𝕋𝕁)~` by graded strong 2-natural transformations with
identity 1-morphisms (`QPiTwoEnvelope.extendRestrictNatTrans`,
`QPiTwoEnvelope.extendRestrictNatTransInv`), whose composites are isomorphic to the
identities by even invertible supermodifications of degree zero
(`QPiTwoEnvelope.extendRestrictCounitIso`, `QPiTwoEnvelope.extendRestrictUnitIso`). The
2-adjunction `-_{q,π} ⊣ ν` itself is not packaged (the 2-categories `2-𝔊𝔖ℭ𝔄𝔗` and
`(Q, Π)-2-𝔊𝔖ℭ𝔄𝔗` are not constructed).

The analogue of Lemma 4.6: `𝕁` induces graded superequivalences on all morphism
supercategories if and only if `𝔄` is `(Q, Π)`-complete
(`QPiTwoEnvelope.gradedSuperequivalenceJ_iff`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

/-! ## The graded `(Q, Π)`-supercategories `ℋom(λ, μ)` of a graded `(Q, Π)`-2-supercategory -/

namespace QPiTwoSupercategory

open PiTwoSupercategory GradedTwoSupercategory

variable {R : Type w} [CommRing R]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R C] [GradedTwoSupercategory R C] [QPiTwoSupercategory R C]

variable (a b : C) in
/-- Each morphism supercategory `ℋom(λ, μ)` of a graded `(Q, Π)`-2-supercategory is a graded
`(Q, Π)`-supercategory with `Π := π_μ -`, `Q := q_μ -`, `Q⁻¹ := q_μ⁻¹ -` (i.e. `f ↦ f ≫ π_μ`,
`f ↦ f ≫ q_μ`, `f ↦ f ≫ q_μ⁻¹`) and `ζ_F := F ζ_μ`, `σ_F := F σ_μ`, `σ̄_F := F σ̄_μ` (followed
by the unitors); its Π-part is `PiTwoSupercategory.homPiLeft`. -/
def homQPiLeft : QPiSupercategory R (a ⟶ b) :=
  letI := homPiLeft (R := R) a b
  QPiSupercategory.ofIso
    (fun f => by
      have := comp_mem_degree (whiskerLeft_mem_degree f (ζ_hom_mem_degree (R := R) b))
        (rightUnitor_hom_mem_degree (R := R) f)
      simpa using this)
    (fun f => f ≫ q (R := R) b)
    (fun f => whiskerLeftIso (R := R) f (σ (R := R) b) ≪≫ rightUnitor f)
    (fun f => by
      simpa using comp_mem (whiskerLeft_mem f (σ_hom_mem (R := R) b))
        (rightUnitor_hom_mem (R := R) f))
    (fun f => by
      have := comp_mem_degree (whiskerLeft_mem_degree f (σ_hom_mem_degree (R := R) b))
        (rightUnitor_hom_mem_degree (R := R) f)
      simpa using this)
    (fun f => f ≫ qinv (R := R) b)
    (fun f => whiskerLeftIso (R := R) f (σbar (R := R) b) ≪≫ rightUnitor f)
    (fun f => by
      simpa using comp_mem (whiskerLeft_mem f (σbar_hom_mem (R := R) b))
        (rightUnitor_hom_mem (R := R) f))
    (fun f => by
      have := comp_mem_degree (whiskerLeft_mem_degree f (σbar_hom_mem_degree (R := R) b))
        (rightUnitor_hom_mem_degree (R := R) f)
      simpa using this)

theorem γ_inv {a b : C} (f : a ⟶ b) : (γ (R := R) f).inv =
    (σ (R := R) a).hom ▷ f ≫ (leftUnitor f).hom ≫ (rightUnitor f).inv ≫
      f ◁ (σ (R := R) b).inv := by
  simp [γ]

theorem homQPiLeft_toPiSupercategory (a b : C) :
    (homQPiLeft (R := R) a b).toPiSupercategory = homPiLeft a b := rfl

theorem homQPiLeft_Q_obj (a b : C) (f : a ⟶ b) :
    (homQPiLeft (R := R) a b).Q.obj f = f ≫ q (R := R) b := rfl

theorem homQPiLeft_σ_hom (a b : C) (f : a ⟶ b) :
    ((homQPiLeft (R := R) a b).σ f).hom = f ◁ (σ (R := R) b).hom ≫ (rightUnitor f).hom := by
  simp [homQPiLeft, QPiSupercategory.ofIso]

end QPiTwoSupercategory

/-! ## The canonical `𝕁 : 𝔄 → 𝔄_{q,π}` and restriction along it -/

namespace QPiTwoEnvelope

open Envelope QEnvelope

section J

variable {R : Type w} {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [CommRing R] [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]

/-- The 1-morphism `Q⁰Π⁰F` of `𝔄_{q,π}`. -/
def Jm {a b : B} (f : a ⟶ b) : (⟨⟨a⟩⟩ : QPiTwoEnvelope R B) ⟶ ⟨⟨b⟩⟩ := ⟨0, ⟨0, f⟩⟩

/-- The 2-morphism `x^{0,0}_{0,0} : Q⁰Π⁰F ⇒ Q⁰Π⁰G` of `𝔄_{q,π}`. -/
def J2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : Jm (R := R) f ⟶ Jm g :=
  Envelope.ofHom (QEnvelope.ofHom η)

theorem Jm_eq {a b : B} (f : a ⟶ b) : Jm (R := R) f = (QPiEnvelope.J R (a ⟶ b)).obj f := rfl

theorem J2_eq {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    J2 (R := R) η = (QPiEnvelope.J R (a ⟶ b)).map η := rfl

theorem Jm_eq' {a b : B} (f : a ⟶ b) :
    Jm (R := R) f = TwoEnvelope.Jm (R := R) (QTwoEnvelope.Jm (R := R) f) := rfl

theorem J2_eq' {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    J2 (R := R) η = TwoEnvelope.J2 (R := R) (QTwoEnvelope.J2 (R := R) η) := rfl

variable {a b c : QPiTwoEnvelope R B}

@[simp] theorem comp_par (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).par = f.par + g.par := rfl

@[simp] theorem comp_obj_shift (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).obj.shift = f.obj.shift + g.obj.shift := rfl

@[simp] theorem comp_obj_obj (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).obj.obj = f.obj.obj ≫ g.obj.obj := rfl

/-- The 2-isomorphism `(1_F)^{m,a}_{0,0} : Q⁰Π⁰F ≅ Q^mΠ^aF` (homogeneous of parity `a` and
degree `m`). -/
def shiftIso (f : a ⟶ b) : (Jm (R := R) f.obj.obj : a ⟶ b) ≅ f :=
  Envelope.isoOfIso (QEnvelope.isoOfIso (Iso.refl f.obj.obj))

variable [TwoSupercategory R B]

variable (R B) in
/-- The canonical strict 2-superfunctor `𝕁 : 𝔄 → 𝔄_{q,π}` (after Definition 6.10): the identity
on objects, `F ↦ Q⁰Π⁰F`, `x ↦ x^{0,0}_{0,0}`, with identity coherence maps. -/
def twoJ : TwoSuperfunctor R B (QPiTwoEnvelope R B) where
  obj a := ⟨⟨a⟩⟩
  map f := Jm f
  map₂ η := J2 η
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  map₂_add _ _ := rfl
  map₂_smul _ _ := rfl
  map₂_mem {a b f g p η} hη := by
    show η ∈ parity (R := R) f g (p + (0 + 0))
    simpa using hη
  mapComp f g := Envelope.isoOfIso (QEnvelope.isoOfIso (Iso.refl (f ≫ g)))
  mapId a := Envelope.isoOfIso (QEnvelope.isoOfIso (Iso.refl (𝟙 a)))
  mapComp_hom_mem f g := by
    rw [Envelope.mem_parity_iff]
    exact id_mem (f ≫ g)
  mapId_hom_mem a := id_mem (𝟙 a)
  mapComp_naturality_left η g := (TwoEnvelope.twoJ R (QTwoEnvelope R B)).mapComp_naturality_left
    (QTwoEnvelope.J2 η) (QTwoEnvelope.Jm g)
  mapComp_naturality_right f _ _ η :=
    (TwoEnvelope.twoJ R (QTwoEnvelope R B)).mapComp_naturality_right (QTwoEnvelope.Jm f)
      (QTwoEnvelope.J2 η)
  map₂_associator f g h := (TwoEnvelope.twoJ R (QTwoEnvelope R B)).map₂_associator
    (QTwoEnvelope.Jm f) (QTwoEnvelope.Jm g) (QTwoEnvelope.Jm h)
  map₂_leftUnitor f := (TwoEnvelope.twoJ R (QTwoEnvelope R B)).map₂_leftUnitor (QTwoEnvelope.Jm f)
  map₂_rightUnitor f :=
    (TwoEnvelope.twoJ R (QTwoEnvelope R B)).map₂_rightUnitor (QTwoEnvelope.Jm f)

/-- `𝕁 : 𝔄 → 𝔄_{q,π}` is a strict 2-superfunctor. -/
theorem twoJ_isStrict : (twoJ R B).IsStrict where
  map_comp _ _ := rfl
  map_id _ := rfl
  mapComp_eq _ _ := Iso.ext (by simp only [eqToIso.hom, eqToHom_refl]; rfl)
  mapId_eq _ := Iso.ext (by simp only [eqToIso.hom, eqToHom_refl]; rfl)

/-- `𝕁` is the composite of the canonical 2-superfunctors `𝔄 → 𝔄_q → (𝔄_q)_π`. -/
theorem twoJ_eq_comp :
    twoJ R B = (QTwoEnvelope.twoJ R B).comp (TwoEnvelope.twoJ R (QTwoEnvelope R B)) := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    apply Iso.ext
    exact (Category.id_comp _).symm
  · funext a
    apply Iso.ext
    exact (Category.id_comp _).symm

/-- The superfunctor `ℋom_𝔄(λ, μ) → ℋom_{𝔄_{q,π}}(λ, μ)` of `𝕁` is `QPiEnvelope.J`. -/
theorem twoJ_mapFunctor (a b : B) :
    (twoJ R B).mapFunctor a b = QPiEnvelope.J R (a ⟶ b) := rfl

/-- `𝕁` is a graded 2-superfunctor. -/
theorem twoJ_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B] :
    (twoJ R B).IsGraded where
  map₂_mem_degree {a b f g n η} hη := by
    show η ∈ degree (R := R) f g (n + (0 - 0))
    simpa using hη
  mapComp_hom_mem_degree f g := by
    show 𝟙 (f ≫ g) ∈ degree (R := R) _ _ (0 + (0 + 0 - 0))
    simpa using id_mem_degree (R := R) (f ≫ g)
  mapId_hom_mem_degree a := by
    show 𝟙 (𝟙 a) ∈ degree (R := R) _ _ (0 + (0 - 0))
    simpa using id_mem_degree (R := R) (𝟙 a)

variable {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

/-- The restriction `𝕋𝕁 : 𝔄 → 𝔅` of a 2-superfunctor `𝕋 : 𝔄_{q,π} → 𝔅`. -/
def restrict (T : TwoSuperfunctor R (QPiTwoEnvelope R B) C) : TwoSuperfunctor R B C :=
  QTwoEnvelope.restrict (TwoEnvelope.restrict T)

omit [TwoSupercategory R B] [TwoSupercategory R C] in
@[simp] theorem restrict_obj (T : TwoSuperfunctor R (QPiTwoEnvelope R B) C) (a : B) :
    (restrict T).obj a = T.obj ⟨⟨a⟩⟩ := rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem restrict_map (T : TwoSuperfunctor R (QPiTwoEnvelope R B) C) {a b : B} (f : a ⟶ b) :
    (restrict T).map f = T.map (Jm f) := rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem restrict_map₂ (T : TwoSuperfunctor R (QPiTwoEnvelope R B) C) {a b : B} {f g : a ⟶ b}
    (η : f ⟶ g) : (restrict T).map₂ η = T.map₂ (J2 η) := rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem restrict_mapComp (T : TwoSuperfunctor R (QPiTwoEnvelope R B) C) {a b c : B} (f : a ⟶ b)
    (g : b ⟶ c) : (restrict T).mapComp f g = T.mapComp (Jm (R := R) f) (Jm g) := rfl

/-- The restriction `𝕋𝕁` is the composite of `𝕁` and `𝕋`. -/
theorem restrict_eq_comp (T : TwoSuperfunctor R (QPiTwoEnvelope R B) C) :
    restrict T = (twoJ R B).comp T := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    apply Iso.ext
    show (T.mapComp (Jm (R := R) f) (Jm g)).hom = (T.mapComp (Jm f) (Jm g)).hom ≫
      T.map₂ (𝟙 (Jm (R := R) f ≫ Jm g))
    rw [T.map₂_id]
    erw [Category.comp_id]
  · funext a
    apply Iso.ext
    show (T.mapId ⟨⟨a⟩⟩).hom = (T.mapId ⟨⟨a⟩⟩).hom ≫ T.map₂ (𝟙 (𝟙 (⟨⟨a⟩⟩ : QPiTwoEnvelope R B)))
    rw [T.map₂_id]
    erw [Category.comp_id]

omit [TwoSupercategory R C] in
/-- The restriction of a graded 2-superfunctor along `𝕁` is graded. -/
theorem restrict_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] {T : TwoSuperfunctor R (QPiTwoEnvelope R B) C}
    (hT : T.IsGraded) : (restrict T).IsGraded where
  map₂_mem_degree {a b f g n η} hη :=
    hT.map₂_mem_degree (f := Jm f) (g := Jm g) (η := J2 η) (by
      show η ∈ degree (R := R) f g (n + (0 - 0))
      simpa using hη)
  mapComp_hom_mem_degree f g := hT.mapComp_hom_mem_degree (Jm f) (Jm g)
  mapId_hom_mem_degree a := hT.mapId_hom_mem_degree ⟨⟨a⟩⟩

end J

/-! ## Lemma 6.11(i): extension of 2-superfunctors -/

section Extend

open QPiSupercategory

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R C] [∀ a b : C, QPiSupercategory R (a ⟶ b)]

variable (F : TwoSuperfunctor R B C)

/-- **Lemma 6.11(i).** The extension `ℝ̃ : 𝔄_{q,π} → 𝔅` of a 2-superfunctor `ℝ : 𝔄 → 𝔅`: the
extension along the Π-envelope (Lemma 4.7(i)) of the extension along the `Q`-envelope. -/
def extend : TwoSuperfunctor R (QPiTwoEnvelope R B) C :=
  TwoEnvelope.extend (QTwoEnvelope.extend F)

variable {a b c : QPiTwoEnvelope R B}

@[simp] theorem extend_obj (a : QPiTwoEnvelope R B) : (extend F).obj a = F.obj a.as.as := rfl

/-- `ℝ̃(Q^mΠ^aF) = Π^a Q^m (ℝF)`. -/
theorem extend_map (f : a ⟶ b) :
    (extend F).map f = piPow R f.par (qPow R f.obj.shift (F.map f.obj.obj)) := rfl

/-- `ℝ̃(x^{n,b}_{m,a}) = (σ^n ζ^b)⁻¹ ∘ ℝx ∘ (σ^m ζ^a)`, in the diagrammatic order
`ζ^a ≫ σ^m ≫ ℝx ≫ (σ^n)⁻¹ ≫ (ζ^b)⁻¹`. -/
theorem extend_map₂ {f g : a ⟶ b} (η : f ⟶ g) :
    (extend F).map₂ η = (ζPow R f.par _).hom ≫ ((σPow R f.obj.shift (F.map f.obj.obj)).hom ≫
      F.map₂ (toHom η) ≫ (σPow R g.obj.shift (F.map g.obj.obj)).inv) ≫ (ζPow R g.par _).inv :=
  rfl

/-- The coherence map of `ℝ̃`:
`c̃ = (-1)^{ab} (ζ^{a+b})⁻¹ ∘ (σ^{m+n})⁻¹ ∘ c ∘ (σ^n σ^m) ∘ (ζ^b ζ^a)`, in the diagrammatic
order. -/
theorem extendComp_hom (f : a ⟶ b) (g : b ⟶ c) :
    ((extend F).mapComp f g).hom = sign R (f.par * g.par) •
      ((ζPow R f.par _).hom ▷ (extend F).map g ≫
        (QTwoEnvelope.extend F).map f.obj ◁ (ζPow R g.par _).hom ≫
        ((σPow R f.obj.shift (F.map f.obj.obj)).hom ▷ (QTwoEnvelope.extend F).map g.obj ≫
          F.map f.obj.obj ◁ (σPow R g.obj.shift (F.map g.obj.obj)).hom ≫
          (F.mapComp f.obj.obj g.obj.obj).hom ≫
          (σPow R (f.obj.shift + g.obj.shift) (F.map (f.obj.obj ≫ g.obj.obj))).inv) ≫
        (ζPow R (f.par + g.par) _).inv) := rfl

/-- `ĩ = i`. -/
theorem extend_mapId (a : QPiTwoEnvelope R B) : (extend F).mapId a = F.mapId a.as.as := rfl

/-- `ℝ = ℝ̃ 𝕁` on 1-morphisms. -/
theorem extend_map_J {a b : B} (f : a ⟶ b) : (extend F).map (Jm (R := R) f) = F.map f := rfl

/-- `ℝ = ℝ̃ 𝕁` on 2-morphisms. -/
theorem extend_map₂_J {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    (extend F).map₂ (J2 (R := R) η) = F.map₂ η := by
  show 𝟙 _ ≫ (𝟙 _ ≫ F.map₂ η ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp

/-- `ℝ = ℝ̃ 𝕁` on the coherence maps `c`. -/
theorem extendComp_J {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    ((extend F).mapComp (Jm (R := R) f) (Jm g)).hom = (F.mapComp f g).hom :=
  (TwoEnvelope.extendComp_J (QTwoEnvelope.extend F) (a := ⟨⟨a⟩⟩) (b := ⟨⟨b⟩⟩) (c := ⟨⟨c⟩⟩)
    (QTwoEnvelope.Jm f) (QTwoEnvelope.Jm g)).trans
    (QTwoEnvelope.extendComp_J F (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩) f g)

/-- **Lemma 6.11(i).** `ℝ = ℝ̃ 𝕁` as 2-superfunctors. -/
theorem twoJ_comp_extend : (twoJ R B).comp (extend F) = F := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g η
    exact extend_map₂_J F η
  · funext a b c f g
    apply Iso.ext
    show ((extend F).mapComp (Jm (R := R) f) (Jm g)).hom ≫
      (extend F).map₂ (𝟙 (Jm (R := R) f ≫ Jm g)) = _
    rw [(extend F).map₂_id]
    erw [Category.comp_id]
    exact extendComp_J F f g
  · funext a
    apply Iso.ext
    show (F.mapId a).hom ≫ (extend F).map₂ (𝟙 (𝟙 (⟨⟨a⟩⟩ : QPiTwoEnvelope R B))) = _
    rw [(extend F).map₂_id]
    erw [Category.comp_id]

/-- `restrict (extend ℝ) = ℝ`. -/
theorem restrict_extend : restrict (extend F) = F := by
  rw [restrict_eq_comp, twoJ_comp_extend]

/-- **Lemma 6.11(i).** `ℝ̃` is a graded 2-superfunctor when `ℝ` is (and `𝔅` is a graded
2-supercategory). -/
theorem extend_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R C]
    (hF : F.IsGraded) : (extend F).IsGraded where
  map₂_mem_degree {a b f g n η} hη := by
    have hη' : toHom η ∈ degree (R := R) f.obj.obj g.obj.obj (n + (f.obj.shift - g.obj.shift)) :=
      hη
    have := comp_mem_degree (ζPow_hom_mem_degree (R := R) f.par _)
      (comp_mem_degree (σPow_hom_mem_degree (R := R) f.obj.shift _)
        (comp_mem_degree (hF.map₂_mem_degree hη')
          (comp_mem_degree (σPow_inv_mem_degree (R := R) g.obj.shift _)
            (ζPow_inv_mem_degree (R := R) g.par _))))
    rw [extend_map₂]
    simp only [Category.assoc] at this ⊢
    convert this using 2
    ring
  mapComp_hom_mem_degree f g := by
    rw [extendComp_hom]
    refine Submodule.smul_mem _ _ ?_
    have := comp_mem_degree
      (GradedTwoSupercategory.whiskerRight_mem_degree _ (ζPow_hom_mem_degree (R := R) f.par _))
      (comp_mem_degree
        (GradedTwoSupercategory.whiskerLeft_mem_degree _ (ζPow_hom_mem_degree (R := R) g.par _))
        (comp_mem_degree (GradedTwoSupercategory.whiskerRight_mem_degree _
            (σPow_hom_mem_degree (R := R) f.obj.shift _))
          (comp_mem_degree (GradedTwoSupercategory.whiskerLeft_mem_degree _
              (σPow_hom_mem_degree (R := R) g.obj.shift _))
            (comp_mem_degree (hF.mapComp_hom_mem_degree f.obj.obj g.obj.obj)
              (comp_mem_degree
                (σPow_inv_mem_degree (R := R) (f.obj.shift + g.obj.shift) _)
                (ζPow_inv_mem_degree (R := R) (f.par + g.par) _))))))
    simp only [Category.assoc] at this ⊢
    convert this using 2
    ring
  mapId_hom_mem_degree a := hF.mapId_hom_mem_degree a.as.as

end Extend

/-! ## Lemma 6.11(ii): extension of 2-natural transformations -/

section NatTrans

open QPiSupercategory

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R C] [∀ a b : C, QPiSupercategory R (a ⟶ b)]
  {F G H : TwoSuperfunctor R B C}

variable {a b : QPiTwoEnvelope R B}

/-- **Lemma 6.11(ii).** The extension `(X̃, x̃) : ℝ̃ ⇒ 𝕊̃` of a 2-natural transformation
`(X, x) : ℝ ⇒ 𝕊`: `X̃_λ = X_λ` and
`x̃_{Q^mΠ^aF} = (σ^m ζ^a_{𝕊F} X_λ)⁻¹ ∘ x_F ∘ (X_μ σ^m ζ^a_{ℝF})`. -/
def extendTwoNatTrans (θ : TwoNatTrans F G) : TwoNatTrans (extend F) (extend G) :=
  TwoEnvelope.extendTwoNatTrans (QTwoEnvelope.extendTwoNatTrans θ)

@[simp] theorem extendTwoNatTrans_X (θ : TwoNatTrans F G) (a : QPiTwoEnvelope R B) :
    (extendTwoNatTrans θ).X a = θ.X a.as.as := rfl

/-- The formula for `x̃`, in the diagrammatic order
`ζ^a ▷ X_μ ≫ σ^m ▷ X_μ ≫ x_F ≫ X_λ ◁ (σ^m)⁻¹ ≫ X_λ ◁ (ζ^a)⁻¹`. -/
theorem extendTwoNatTrans_x (θ : TwoNatTrans F G) (f : a ⟶ b) :
    (extendTwoNatTrans θ).x f =
      (ζPow R f.par _).hom ▷ θ.X b.as.as ≫
        ((σPow R f.obj.shift (F.map f.obj.obj)).hom ▷ θ.X b.as.as ≫ θ.x f.obj.obj ≫
          θ.X a.as.as ◁ (σPow R f.obj.shift (G.map f.obj.obj)).inv) ≫
        θ.X a.as.as ◁ (ζPow R f.par _).inv := rfl

/-- `x = x̃ 𝕁`. -/
theorem extendTwoNatTrans_x_J (θ : TwoNatTrans F G) {a b : B} (f : a ⟶ b) :
    (extendTwoNatTrans θ).x (Jm (R := R) f) = θ.x f :=
  (TwoEnvelope.extendX_J (a := (⟨⟨a⟩⟩ : QPiTwoEnvelope R B)) (b := ⟨⟨b⟩⟩) _
    (QTwoEnvelope.Jm f)).trans
    (QTwoEnvelope.extendX_J (a := ⟨a⟩) (b := ⟨b⟩) θ f)

/-- The restriction `(Y, y𝕁) : ℝ ⇒ 𝕊` of a 2-natural transformation `(Y, y) : ℝ̃ ⇒ 𝕊̃`. -/
def restrictTwoNatTrans (ψ : TwoNatTrans (extend F) (extend G)) : TwoNatTrans F G :=
  QTwoEnvelope.restrictTwoNatTrans (TwoEnvelope.restrictTwoNatTrans ψ)

@[simp] theorem restrictTwoNatTrans_X (ψ : TwoNatTrans (extend F) (extend G)) (a : B) :
    (restrictTwoNatTrans ψ).X a = ψ.X ⟨⟨a⟩⟩ := rfl

theorem restrictTwoNatTrans_x (ψ : TwoNatTrans (extend F) (extend G)) {a b : B} (f : a ⟶ b) :
    (restrictTwoNatTrans ψ).x f = ψ.x (Jm (R := R) f) := rfl

/-- `(X̃, x̃)` restricts to `(X, x)`. -/
theorem restrictTwoNatTrans_extendTwoNatTrans (θ : TwoNatTrans F G) :
    restrictTwoNatTrans (extendTwoNatTrans θ) = θ := by
  rw [restrictTwoNatTrans, extendTwoNatTrans, TwoEnvelope.restrictTwoNatTrans_extendTwoNatTrans,
    QTwoEnvelope.restrictTwoNatTrans_extendTwoNatTrans]

/-- A 2-natural transformation `ℝ̃ ⇒ 𝕊̃` is the extension of its restriction. -/
theorem extendTwoNatTrans_restrictTwoNatTrans (ψ : TwoNatTrans (extend F) (extend G)) :
    extendTwoNatTrans (restrictTwoNatTrans ψ) = ψ := by
  rw [restrictTwoNatTrans, extendTwoNatTrans, QTwoEnvelope.extendTwoNatTrans_restrictTwoNatTrans,
    TwoEnvelope.extendTwoNatTrans_restrictTwoNatTrans]

/-- **Lemma 6.11(ii), uniqueness.** `(X̃, x̃)` is the unique 2-natural transformation `ℝ̃ ⇒ 𝕊̃`
with `X̃_λ = X_λ` and `x = x̃ 𝕁` (i.e. restricting to `(X, x)` along `𝕁`). -/
theorem extendTwoNatTrans_unique (θ : TwoNatTrans F G) (ψ : TwoNatTrans (extend F) (extend G))
    (h : restrictTwoNatTrans ψ = θ) : ψ = extendTwoNatTrans θ := by
  rw [← h, extendTwoNatTrans_restrictTwoNatTrans]

/-- **Lemma 6.11(ii), uniqueness**, in the paper's form: two 2-natural transformations
`ℝ̃ ⇒ 𝕊̃` with the same 1-morphisms `X̃_λ` and the same restriction `x̃𝕁` are equal. -/
theorem twoNatTrans_ext_of_J (ψ ψ' : TwoNatTrans (extend F) (extend G))
    (hX : ∀ a : B, ψ.X (⟨⟨a⟩⟩ : QPiTwoEnvelope R B) = ψ'.X ⟨⟨a⟩⟩)
    (hx : ∀ {a b : B} (f : a ⟶ b), HEq (ψ.x (Jm (R := R) f)) (ψ'.x (Jm f))) : ψ = ψ' := by
  rw [← extendTwoNatTrans_restrictTwoNatTrans ψ, ← extendTwoNatTrans_restrictTwoNatTrans ψ']
  congr 1
  exact TwoEnvelope.twoNatTrans_ext (funext hX) fun f => hx f

/-- **The analogue of Theorem 4.9**, full faithfulness on 2-natural transformations:
`(X, x) ↦ (X̃, x̃)` is a bijection from 2-natural transformations `ℝ ⇒ 𝕊` to 2-natural
transformations `ℝ̃ ⇒ 𝕊̃`, with inverse the restriction along `𝕁`. -/
def extendTwoNatTransEquiv : TwoNatTrans F G ≃ TwoNatTrans (extend F) (extend G) where
  toFun := extendTwoNatTrans
  invFun := restrictTwoNatTrans
  left_inv := restrictTwoNatTrans_extendTwoNatTrans
  right_inv := extendTwoNatTrans_restrictTwoNatTrans

/-- Functoriality: `1̃ = 1`. -/
theorem extendTwoNatTrans_id :
    extendTwoNatTrans (TwoNatTrans.id F) = TwoNatTrans.id (extend F) := by
  rw [extendTwoNatTrans, QTwoEnvelope.extendTwoNatTrans_id, TwoEnvelope.extendTwoNatTrans_id]
  rfl

/-- Functoriality: `(X', x') ∘ (X, x)` extends to `(X̃', x̃') ∘ (X̃, x̃)`. -/
theorem extendTwoNatTrans_vcomp (θ : TwoNatTrans F G) (θ' : TwoNatTrans G H) :
    extendTwoNatTrans (TwoNatTrans.vcomp θ θ') =
      TwoNatTrans.vcomp (extendTwoNatTrans θ) (extendTwoNatTrans θ') := by
  rw [extendTwoNatTrans, QTwoEnvelope.extendTwoNatTrans_vcomp,
    TwoEnvelope.extendTwoNatTrans_vcomp]
  rfl

/-! ### Graded 2-natural transformations -/

variable [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R C]

omit [∀ a b : B, GradedSupercategory R (a ⟶ b)] in
/-- The extension of a graded 2-natural transformation is graded. -/
theorem extendTwoNatTrans_isGraded {θ : TwoNatTrans F G} (hθ : θ.IsGraded) :
    (extendTwoNatTrans θ).IsGraded := fun {a b} f => by
  have := comp_mem_degree
    (GradedTwoSupercategory.whiskerRight_mem_degree _ (ζPow_hom_mem_degree (R := R) f.par _))
    (comp_mem_degree
      (GradedTwoSupercategory.whiskerRight_mem_degree _
        (σPow_hom_mem_degree (R := R) f.obj.shift (F.map f.obj.obj)))
      (comp_mem_degree (hθ f.obj.obj)
        (comp_mem_degree (GradedTwoSupercategory.whiskerLeft_mem_degree _
            (σPow_inv_mem_degree (R := R) f.obj.shift (G.map f.obj.obj)))
          (GradedTwoSupercategory.whiskerLeft_mem_degree _
            (ζPow_inv_mem_degree (R := R) f.par _)))))
  rw [extendTwoNatTrans_x]
  simp only [Category.assoc] at this ⊢
  convert this using 2
  ring

omit [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R C] in
/-- The restriction of a graded 2-natural transformation is graded. -/
theorem restrictTwoNatTrans_isGraded {ψ : TwoNatTrans (extend F) (extend G)} (hψ : ψ.IsGraded) :
    (restrictTwoNatTrans ψ).IsGraded := fun f => hψ (Jm f)

omit [∀ a b : B, GradedSupercategory R (a ⟶ b)] in
/-- **Lemma 6.11(ii).** `(X̃, x̃)` is graded if and only if `(X, x)` is. -/
theorem extendTwoNatTrans_isGraded_iff (θ : TwoNatTrans F G) :
    (extendTwoNatTrans θ).IsGraded ↔ θ.IsGraded :=
  ⟨fun h => by
    have h' : (restrictTwoNatTrans (extendTwoNatTrans θ)).IsGraded :=
      restrictTwoNatTrans_isGraded h
    rwa [restrictTwoNatTrans_extendTwoNatTrans] at h', extendTwoNatTrans_isGraded⟩

/-- **The analogue of Theorem 4.9** for graded 2-natural transformations: restriction along
`𝕁` is a bijection from graded 2-natural transformations `ℝ̃ ⇒ 𝕊̃` to graded 2-natural
transformations `ℝ ⇒ 𝕊`. -/
def extendGradedTwoNatTransEquiv :
    {θ : TwoNatTrans F G // θ.IsGraded} ≃ {ψ : TwoNatTrans (extend F) (extend G) // ψ.IsGraded} :=
  (extendTwoNatTransEquiv (F := F) (G := G)).subtypeEquiv fun θ =>
    (extendTwoNatTrans_isGraded_iff θ).symm

end NatTrans

/-! ## Supermodifications and the superequivalence `ℋom(ℝ, 𝕊) → ℋom(ℝ̃, 𝕊̃)` -/

section Supermodification

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R C] [∀ a b : C, QPiSupercategory R (a ⟶ b)]
  {F G : TwoSuperfunctor R B C}

/-- The extension `α̃ : (X̃, x̃) ⇛ (Ỹ, ỹ)` of a supermodification `α : (X, x) ⇛ (Y, y)`:
`α̃_λ = α_λ` (the analogue of Remark 4.10). -/
def extendSupermodification {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') :
    extendTwoNatTrans θ ⟶ extendTwoNatTrans θ' :=
  TwoEnvelope.extendSupermodification (QTwoEnvelope.extendSupermodification α)

@[simp] theorem extendSupermodification_app {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ')
    (a : QPiTwoEnvelope R B) : (extendSupermodification α).app a = α.app a.as.as := rfl

/-- `α̃` is homogeneous of parity `p` and degree `n` if and only if `α` is. -/
theorem extendSupermodification_isHomogeneous_iff [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') (p : ZMod 2) (n : ℤ) :
    (extendSupermodification α).IsHomogeneous p n ↔ α.IsHomogeneous p n :=
  ⟨fun h a => h ⟨⟨a⟩⟩, fun h a => h a.as.as⟩

variable (F G) in
/-- The superfunctor `ℋom(ℝ, 𝕊) → ℋom(ℝ̃, 𝕊̃)`, `(X, x) ↦ (X̃, x̃)`, `α ↦ α̃`. -/
@[simps]
def extendHom : TwoNatTrans F G ⥤ TwoNatTrans (extend F) (extend G) where
  obj := extendTwoNatTrans
  map := extendSupermodification
  map_id _ := TwoNatTrans.hom_ext fun _ => rfl
  map_comp _ _ := TwoNatTrans.hom_ext fun _ => rfl

instance : (extendHom F G).Additive where
  map_add := TwoNatTrans.hom_ext fun _ => rfl

instance : (extendHom F G).Linear R where
  map_smul _ _ := TwoNatTrans.hom_ext fun _ => rfl

instance : IsSuperfunctor R (extendHom F G) where
  map_mem hα a := hα a.as.as

instance : (extendHom F G).Faithful where
  map_injective {θ θ'} α β h := TwoNatTrans.hom_ext fun a => by
    have := congrArg (fun γ : extendTwoNatTrans θ ⟶ extendTwoNatTrans θ' => γ.app ⟨⟨a⟩⟩) h
    exact this

instance : (extendHom F G).Full where
  map_surjective {θ θ'} γ := ⟨⟨fun a => γ.app ⟨⟨a⟩⟩, fun {a b} f => by
      have := γ.naturality (Jm (R := R) f)
      simp only [extendHom_obj] at this
      rw [extendTwoNatTrans_x_J, extendTwoNatTrans_x_J] at this
      exact this⟩,
    TwoNatTrans.hom_ext fun _ => rfl⟩

theorem extendHom_evenlyDense : EvenlyDense R (extendHom F G) := fun ψ =>
  ⟨restrictTwoNatTrans ψ, eqToIso (extendTwoNatTrans_restrictTwoNatTrans ψ),
    TwoEnvelope.eqToHom_mem (extendTwoNatTrans_restrictTwoNatTrans ψ)⟩

variable (F G) in
/-- **The analogue of Theorem 4.9.** `(X, x) ↦ (X̃, x̃)`, `α ↦ α̃` is a superequivalence
`ℋom(ℝ, 𝕊) → ℋom(ℝ̃, 𝕊̃)`; it is bijective on objects (`extendTwoNatTransEquiv`) and on
morphisms, and preserves and reflects the parity and degree of supermodifications
(`extendSupermodification_isHomogeneous_iff`). -/
def extendHomSuperequivalence : Superequivalence R (extendHom F G) :=
  Superequivalence.ofFullyFaithful _ extendHom_evenlyDense

end Supermodification

/-! ## Graded `(Q, Π)`-2-supercategories -/

section QPi

open QPiSupercategory QPiTwoSupercategory PiTwoSupercategory

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R C] [GradedTwoSupercategory R C] [QPiTwoSupercategory R C]

/-- **Lemma 6.11(i)** for a graded `(Q, Π)`-2-supercategory `𝔅`: the extension
`ℝ̃ : 𝔄_{q,π} → 𝔅` of a 2-superfunctor `ℝ : 𝔄 → 𝔅`, with `ℝ̃(Q^mΠ^aF) = π^a_{ℝμ} q^m_{ℝμ} (ℝF)`
(in the diagrammatic order `ℝF ≫ q^m ≫ π^a`), `ℝ̃(x^{n,b}_{m,a}) = (σ^nζ^b)⁻¹ ∘ ℝx ∘ σ^mζ^a`,
and the coherence maps of `extendComp_hom`. -/
def extendQPi (F : TwoSuperfunctor R B C) : TwoSuperfunctor R (QPiTwoEnvelope R B) C :=
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) := fun a b => homQPiLeft a b
  extend F

variable (F : TwoSuperfunctor R B C)

@[simp] theorem extendQPi_obj (a : QPiTwoEnvelope R B) : (extendQPi F).obj a = F.obj a.as.as :=
  rfl

/-- `ℝ̃(Q⁰Π⁰F) = ℝF`. -/
theorem extendQPi_map_J {a b : B} (f : a ⟶ b) : (extendQPi F).map (Jm (R := R) f) = F.map f :=
  rfl

/-- `ℝ̃(Q¹Π¹F) = π_{ℝμ} q_{ℝμ} (ℝF)`, i.e. `(ℝF ≫ q_{ℝμ}) ≫ π_{ℝμ}`. -/
theorem extendQPi_map_one_one {a b : B} (f : a ⟶ b) :
    (extendQPi F).map (⟨1, ⟨1, f⟩⟩ : (⟨⟨a⟩⟩ : QPiTwoEnvelope R B) ⟶ ⟨⟨b⟩⟩) =
      (F.map f ≫ QPiTwoSupercategory.q (R := R) (B := C) (F.obj b)) ≫
        PiTwoSupercategory.pi (R := R) (B := C) (F.obj b) := rfl

/-- `ℝ̃(Q⁻¹Π⁰F) = q⁻¹_{ℝμ} (ℝF)`, i.e. `ℝF ≫ q⁻¹_{ℝμ}`. -/
theorem extendQPi_map_neg_one_zero {a b : B} (f : a ⟶ b) :
    (extendQPi F).map (⟨0, ⟨-1, f⟩⟩ : (⟨⟨a⟩⟩ : QPiTwoEnvelope R B) ⟶ ⟨⟨b⟩⟩) =
      F.map f ≫ QPiTwoSupercategory.qinv (R := R) (B := C) (F.obj b) := rfl

/-- `ℝ = ℝ̃ 𝕁` on 2-morphisms. -/
theorem extendQPi_map₂_J {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    (extendQPi F).map₂ (J2 (R := R) η) = F.map₂ η :=
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) := fun a b => homQPiLeft a b
  extend_map₂_J F η

/-- **Lemma 6.11(i).** `ℝ = ℝ̃ 𝕁` as 2-superfunctors. -/
theorem twoJ_comp_extendQPi : (twoJ R B).comp (extendQPi F) = F :=
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) := fun a b => homQPiLeft a b
  twoJ_comp_extend F

/-- **Lemma 6.11(i).** `ℝ̃` is a graded 2-superfunctor when `ℝ` is. -/
theorem extendQPi_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)] (hF : F.IsGraded) :
    (extendQPi F).IsGraded :=
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) := fun a b => homQPiLeft a b
  extend_isGraded F hF

omit [TwoSupercategory R B] in
/-- **Lemma 6.11(i)**, the coherence map of the `Q`-layer in the case `Q¹F`, `Q⁰G`: it is the
paper's rearrangement `c_{G,F} q_ν ∘ (γ_{ℝG})⁻¹ (ℝF)` through the half-braiding `γ` of
Lemma 6.6(ii), i.e. `(ℝF q) ℝG ≅ ℝF (q ℝG) → ℝF (ℝG q) ≅ (ℝF ℝG) q → ℝ(FG) q`; together with
`TwoEnvelope.extendComp_one_zero` and `TwoEnvelope.extendComp_one_one` (the cases with `Π`,
through `β` and `-ξ`) this identifies the coherence maps of `extendComp_hom` with the
description in the proof of Lemma 6.11. -/
theorem extendComp_Q_one_zero {a b c : B} (f₀ : a ⟶ b) (g₀ : b ⟶ c) :
    letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) := fun a b => homQPiLeft a b
    (QTwoEnvelope.extendComp F (QTwoEnvelope.Qm (R := R) f₀) (QTwoEnvelope.Jm g₀)).hom =
      (associator (F.map f₀) (QPiTwoSupercategory.q (R := R) (B := C) (F.obj b))
          (F.map g₀)).hom ≫
        F.map f₀ ◁ (γ (R := R) (F.map g₀)).inv ≫
        (associator (F.map f₀) (F.map g₀) (QPiTwoSupercategory.q (R := R) (B := C) (F.obj c))).inv ≫
        (F.mapComp f₀ g₀).hom ▷ QPiTwoSupercategory.q (R := R) (B := C) (F.obj c) := by
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) := fun a b => homQPiLeft a b
  show (((F.map f₀ ◁ (QPiTwoSupercategory.σ (R := R) (F.obj b)).hom ≫
      (rightUnitor (F.map f₀)).hom) ≫ 𝟙 _) ▷ F.map g₀ ≫ F.map f₀ ◁ 𝟙 (F.map g₀) ≫
      (F.mapComp f₀ g₀).hom ≫ (𝟙 _ ≫ ((rightUnitor (F.map (f₀ ≫ g₀))).inv ≫
        F.map (f₀ ≫ g₀) ◁ (QPiTwoSupercategory.σ (R := R) (F.obj c)).inv))) = _
  rw [whiskerLeft_id (R := R), Category.comp_id, Category.id_comp, Category.id_comp,
    comp_whiskerRight (R := R), whisker_assoc (R := R), ← TwoSupercategory.triangle (R := R),
    QPiTwoSupercategory.γ_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp (R := R)]
  congr 3
  rw [associator_inv_naturality_right_assoc R,
    ← TwoEnvelope.interchange_even_left R (F.mapComp_hom_mem f₀ g₀),
    rightUnitor_inv_naturality_assoc R, rightUnitor_comp_inv R, Category.assoc]

variable {F} {G : TwoSuperfunctor R B C}

/-- **Lemma 6.11(ii)** for a graded `(Q, Π)`-2-supercategory `𝔅`: the extension of a
2-natural transformation. -/
def extendTwoNatTransQPi (θ : TwoNatTrans F G) : TwoNatTrans (extendQPi F) (extendQPi G) :=
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) := fun a b => homQPiLeft a b
  extendTwoNatTrans θ

/-- **Lemma 6.11(ii)** for a graded `(Q, Π)`-2-supercategory `𝔅`: `(X, x) ↦ (X̃, x̃)` is a
bijection from 2-natural transformations `ℝ ⇒ 𝕊` to 2-natural transformations `ℝ̃ ⇒ 𝕊̃`, with
inverse the restriction along `𝕁`. -/
def extendTwoNatTransQPiEquiv : TwoNatTrans F G ≃ TwoNatTrans (extendQPi F) (extendQPi G) :=
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) := fun a b => homQPiLeft a b
  extendTwoNatTransEquiv

theorem extendTwoNatTransQPiEquiv_apply (θ : TwoNatTrans F G) :
    extendTwoNatTransQPiEquiv θ = extendTwoNatTransQPi θ := rfl

/-- The extension of a graded 2-natural transformation is graded. -/
theorem extendTwoNatTransQPi_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    {θ : TwoNatTrans F G} (hθ : θ.IsGraded) : (extendTwoNatTransQPi θ).IsGraded :=
  letI : ∀ a b : C, QPiSupercategory R (a ⟶ b) := fun a b => homQPiLeft a b
  extendTwoNatTrans_isGraded hθ

end QPi

end QPiTwoEnvelope

/-! ## The components of `extendRestrictIso` on the image of `J` -/

namespace QPiEnvelope

variable {R : Type w} [CommRing R] {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear R A]
  [Supercategory R A] [GradedSupercategory R A] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [Linear R D] [Supercategory R D] [GradedSupercategory R D] [QPiSupercategory R D]
  (H : QPiEnvelope R A ⥤ D) [H.Additive] [H.Linear R] [IsGradedSuperfunctor R H]

theorem extendRestrictIso_hom_app_J (X : A) :
    (extendRestrictIso H).hom.app ((J R A).obj X) = 𝟙 _ := by
  simp only [extendRestrictIso, Iso.trans_hom, NatTrans.comp_app, Envelope.extendIso_hom_app]
  erw [Envelope.extendNat_zero_par (X := (QEnvelope.J R A).obj X)]
  simp only [Envelope.extendRestrictIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom]
  simp only [QEnvelope.extendRestrictIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom]
  show (𝟙 _ ≫ H.map (𝟙 _)) ≫ (𝟙 _ ≫ H.map (𝟙 _)) = 𝟙 _
  simp

theorem extendRestrictIso_inv_app_J (X : A) :
    (extendRestrictIso H).inv.app ((J R A).obj X) = 𝟙 _ := by
  have := (extendRestrictIso H).hom_inv_id_app ((J R A).obj X)
  rw [extendRestrictIso_hom_app_J, Category.id_comp] at this
  exact this

end QPiEnvelope

namespace QPiTwoEnvelope

/-! ## The analogue of Theorem 4.9: even density -/

section Density

open QPiSupercategory

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

section XComp

variable {F' G' : TwoSuperfunctor R (QPiTwoEnvelope R B) C} (X : ∀ a, F'.obj a ⟶ G'.obj a)
  (x : ∀ {a b : QPiTwoEnvelope R B} (f : a ⟶ b), F'.map f ≫ X b ⟶ X a ≫ G'.map f)
  (x_mem : ∀ {a b : QPiTwoEnvelope R B} (f : a ⟶ b), x f ∈ parity (R := R) _ _ 0)
  (nat : ∀ {a b : QPiTwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g),
    F'.map₂ η ▷ X b ≫ x g = x f ≫ X a ◁ G'.map₂ η)

/-- The left-hand side of the first coherence diagram of Definition 2.2(iii). -/
def xcompL {a b c : QPiTwoEnvelope R B} (f : a ⟶ b) (g : b ⟶ c) :
    (F'.map f ≫ F'.map g) ≫ X c ⟶ X a ≫ G'.map (f ≫ g) :=
  (F'.mapComp f g).hom ▷ X c ≫ x (f ≫ g)

/-- The right-hand side of the first coherence diagram of Definition 2.2(iii). -/
def xcompR {a b c : QPiTwoEnvelope R B} (f : a ⟶ b) (g : b ⟶ c) :
    (F'.map f ≫ F'.map g) ≫ X c ⟶ X a ≫ G'.map (f ≫ g) :=
  (associator (F'.map f) (F'.map g) (X c)).hom ≫ F'.map f ◁ x g ≫
    (associator (F'.map f) (X b) (G'.map g)).inv ≫ x f ▷ G'.map g ≫
      (associator (X a) (G'.map f) (G'.map g)).hom ≫ X a ◁ (G'.mapComp f g).hom

omit [TwoSupercategory R B] in
include nat in
theorem xcompL_nat₁ {a b c : QPiTwoEnvelope R B} {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) :
    (F'.map₂ u ▷ F'.map g) ▷ X c ≫ xcompL X x f' g = xcompL X x f g ≫ X a ◁ G'.map₂ (u ▷ g) := by
  simp only [xcompL]
  rw [TwoEnvelope.comp_whiskerRight_comp R, F'.mapComp_naturality_left,
    ← TwoEnvelope.comp_whiskerRight_comp R, nat]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
include x_mem nat in
theorem xcompR_nat₁ {a b c : QPiTwoEnvelope R B} {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) :
    (F'.map₂ u ▷ F'.map g) ▷ X c ≫ xcompR X x f' g = xcompR X x f g ≫ X a ◁ G'.map₂ (u ▷ g) := by
  simp only [xcompR]
  rw [associator_naturality_left_assoc R,
    reassoc_of% (TwoEnvelope.interchange_even_right R (F'.map₂ u) (x_mem g)),
    associator_inv_naturality_left_assoc R, TwoEnvelope.comp_whiskerRight_comp R, nat,
    ← TwoEnvelope.comp_whiskerRight_comp R, associator_naturality_middle_assoc R,
    ← whiskerLeft_comp (R := R), G'.mapComp_naturality_left, whiskerLeft_comp (R := R)]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
include nat in
theorem xcompL_nat₂ {a b c : QPiTwoEnvelope R B} (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') :
    (F'.map f ◁ F'.map₂ v) ▷ X c ≫ xcompL X x f g' = xcompL X x f g ≫ X a ◁ G'.map₂ (f ◁ v) := by
  simp only [xcompL]
  rw [TwoEnvelope.comp_whiskerRight_comp R, F'.mapComp_naturality_right,
    ← TwoEnvelope.comp_whiskerRight_comp R, nat]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
include x_mem nat in
theorem xcompR_nat₂ {a b c : QPiTwoEnvelope R B} (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') :
    (F'.map f ◁ F'.map₂ v) ▷ X c ≫ xcompR X x f g' = xcompR X x f g ≫ X a ◁ G'.map₂ (f ◁ v) := by
  simp only [xcompR]
  rw [associator_naturality_middle_assoc R, TwoEnvelope.whiskerLeft_comp_comp R, nat,
    ← TwoEnvelope.whiskerLeft_comp_comp R, associator_inv_naturality_right_assoc R,
    ← reassoc_of% (TwoEnvelope.interchange_even_left R (x_mem f) (G'.map₂ v)),
    associator_naturality_right_assoc R, ← whiskerLeft_comp (R := R),
    G'.mapComp_naturality_right, whiskerLeft_comp (R := R)]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
include x_mem nat in
/-- The first coherence diagram of Definition 2.2(iii) holds for a natural family of even
2-morphisms between 2-superfunctors out of `𝔄_{q,π}` as soon as it holds for 1-morphisms
`Q⁰Π⁰F`, `Q⁰Π⁰G`. -/
theorem xcomp_of_J
    (h : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), xcompL X x (Jm (R := R) f) (Jm g) =
      xcompR X x (Jm (R := R) f) (Jm g))
    {a b c : QPiTwoEnvelope R B} (f : a ⟶ b) (g : b ⟶ c) : xcompL X x f g = xcompR X x f g := by
  have e₁ : Epi ((F'.map₂ (shiftIso f).hom ▷ F'.map g) ▷ X c) :=
    (inferInstance : Epi (whiskerRightIso (R := R) (whiskerRightIso (R := R)
      (F'.map₂Iso (shiftIso f)) _) _).hom)
  refine TwoEnvelope.eq_of_conj_hom _ e₁ _ (xcompL_nat₁ X x nat (shiftIso f).hom g)
    (xcompR_nat₁ X x x_mem nat (shiftIso f).hom g) ?_
  have e₂ : Epi ((F'.map (Jm (R := R) f.obj.obj) ◁ F'.map₂ (shiftIso g).hom) ▷ X c) :=
    (inferInstance : Epi (whiskerRightIso (R := R) (whiskerLeftIso (R := R) _
      (F'.map₂Iso (shiftIso g))) _).hom)
  refine TwoEnvelope.eq_of_conj_hom _ e₂ _ (xcompL_nat₂ X x nat _ (shiftIso g).hom)
    (xcompR_nat₂ X x x_mem nat _ (shiftIso g).hom) ?_
  exact h f.obj.obj g.obj.obj

end XComp

variable [∀ a b : B, GradedSupercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]
  [∀ a b : C, QPiSupercategory R (a ⟶ b)]

variable (T : TwoSuperfunctor R (QPiTwoEnvelope R B) C)

/-- The superfunctor `𝕋 : ℋom_{𝔄_{q,π}}(λ, μ) → ℋom_𝔅(𝕋λ, 𝕋μ)`, as a superfunctor out of the
`(Q, Π)`-envelope `ℋom_𝔄(λ, μ)_{q,π}`. -/
abbrev homFunctor (a b : QPiTwoEnvelope R B) :
    QPiEnvelope R (a.as.as ⟶ b.as.as) ⥤ (T.obj a ⟶ T.obj b) :=
  T.mapFunctor a b

instance (a b : QPiTwoEnvelope R B) : (homFunctor T a b).Additive :=
  inferInstanceAs (T.mapFunctor a b).Additive

instance (a b : QPiTwoEnvelope R B) : (homFunctor T a b).Linear R :=
  inferInstanceAs ((T.mapFunctor a b).Linear R)

instance (a b : QPiTwoEnvelope R B) : IsSuperfunctor R (homFunctor T a b) :=
  inferInstanceAs (IsSuperfunctor R (T.mapFunctor a b))

variable (hT : T.IsGraded)

omit [∀ a b : B, GradedSupercategory R (a ⟶ b)] in
theorem extendRestrict_obj (a : QPiTwoEnvelope R B) : (extend (restrict T)).obj a = T.obj a := rfl

include hT in
/-- The even 2-isomorphism `(𝕋𝕁)~(Q^mΠ^aF) ≅ 𝕋(Q^mΠ^aF)` of degree zero, from Theorem 6.9
applied to the graded superfunctor `𝕋 : ℋom(λ, μ) → ℋom(𝕋λ, 𝕋μ)`. -/
def extendRestrictApp {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (extend (restrict T)).map f ⟶ T.map f :=
  haveI := hT.isGradedSuperfunctor a b
  (QPiEnvelope.extendRestrictIso (homFunctor T a b)).hom.app f

include hT in
theorem extendRestrictApp_mem {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictApp T hT f ∈ parity (R := R) _ _ 0 :=
  haveI := hT.isGradedSuperfunctor a b
  QPiEnvelope.extendRestrictIso_hom_mem (homFunctor T a b) f

include hT in
theorem extendRestrictApp_mem_degree {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictApp T hT f ∈ degree (R := R) _ _ 0 :=
  haveI := hT.isGradedSuperfunctor a b
  QPiEnvelope.extendRestrictIso_hom_mem_degree (homFunctor T a b) f

include hT in
theorem extendRestrictApp_naturality {a b : QPiTwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    (extend (restrict T)).map₂ η ≫ extendRestrictApp T hT g =
      extendRestrictApp T hT f ≫ T.map₂ η :=
  haveI := hT.isGradedSuperfunctor a b
  (QPiEnvelope.extendRestrictIso (homFunctor T a b)).hom.naturality η

include hT in
theorem extendRestrictApp_J {a b : QPiTwoEnvelope R B} (f : a.as.as ⟶ b.as.as) :
    extendRestrictApp T hT (Jm (R := R) f : a ⟶ b) = 𝟙 _ :=
  haveI := hT.isGradedSuperfunctor a b
  QPiEnvelope.extendRestrictIso_hom_app_J (homFunctor T a b) f

include hT in
/-- The components `(𝕋𝕁)~F ≫ 1 ⟶ 1 ≫ 𝕋F` of the 2-natural isomorphism `(𝕋𝕁)~ ⇒ 𝕋`. -/
def extendRestrictX {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (extend (restrict T)).map f ≫ 𝟙 (T.obj b) ⟶ 𝟙 (T.obj a) ≫ T.map f :=
  (rightUnitor _).hom ≫ extendRestrictApp T hT f ≫ (leftUnitor _).inv

include hT in
theorem extendRestrictX_mem {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictX T hT f ∈ parity (R := R) _ _ 0 := by
  have := comp_mem (rightUnitor_hom_mem (R := R) _)
    (comp_mem (extendRestrictApp_mem T hT f) (inv_mem _ (leftUnitor_hom_mem (R := R) _)))
  simpa using this

include hT in
theorem extendRestrictX_mem_degree [GradedTwoSupercategory R C] {a b : QPiTwoEnvelope R B}
    (f : a ⟶ b) : extendRestrictX T hT f ∈ degree (R := R) _ _ 0 := by
  have := comp_mem_degree (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) _)
    (comp_mem_degree (extendRestrictApp_mem_degree T hT f)
      (GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := R) _))
  simpa using this

include hT in
theorem extendRestrictX_naturality {a b : QPiTwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    (extend (restrict T)).map₂ η ▷ 𝟙 (T.obj b) ≫ extendRestrictX T hT g =
      extendRestrictX T hT f ≫ 𝟙 (T.obj a) ◁ T.map₂ η := by
  simp only [extendRestrictX]
  rw [rightUnitor_naturality_assoc R, reassoc_of% (extendRestrictApp_naturality T hT η),
    leftUnitor_inv_naturality R]
  simp only [Category.assoc]

include hT in
/-- **The analogue of Theorem 4.9**, even density: every graded 2-superfunctor
`𝕋 : 𝔄_{q,π} → 𝔅` is isomorphic to the extension `(𝕋𝕁)~` of its restriction, by the 2-natural
transformation with identity 1-morphisms and 2-morphisms the even isomorphisms of degree zero
of Theorem 6.9. -/
def extendRestrictNatTrans : TwoNatTrans (extend (restrict T)) T where
  X a := 𝟙 (T.obj a)
  x f := extendRestrictX T hT f
  x_mem f := extendRestrictX_mem T hT f
  naturality η := extendRestrictX_naturality T hT η
  x_comp f g := xcomp_of_J (F' := extend (restrict T)) (G' := T) (fun a => 𝟙 (T.obj a))
    (fun f => extendRestrictX T hT f) (fun f => extendRestrictX_mem T hT f)
    (fun η => extendRestrictX_naturality T hT η)
    (fun {a b c} f g => by
      have h₁ : ((extend (restrict T)).mapComp (Jm (R := R) f) (Jm g)).hom =
          (T.mapComp (Jm f) (Jm g)).hom :=
        extendComp_J (restrict T) f g
      have h₂ : extendRestrictApp T hT (Jm (R := R) f ≫ Jm g) = 𝟙 _ :=
        extendRestrictApp_J T hT (a := ⟨⟨a⟩⟩) (b := ⟨⟨c⟩⟩) (f ≫ g)
      have h₃ : extendRestrictApp T hT (Jm (R := R) f) = 𝟙 _ :=
        extendRestrictApp_J T hT (a := ⟨⟨a⟩⟩) (b := ⟨⟨b⟩⟩) f
      have h₄ : extendRestrictApp T hT (Jm (R := R) g) = 𝟙 _ :=
        extendRestrictApp_J T hT (a := ⟨⟨b⟩⟩) (b := ⟨⟨c⟩⟩) g
      simp only [xcompL, xcompR, extendRestrictX, h₂, h₃, h₄, Category.id_comp]
      erw [h₁]
      exact TwoEnvelope.unit_coherence R _ _ _) f g
  x_id a := by
    have h : extendRestrictApp T hT (𝟙 a) = 𝟙 _ := extendRestrictApp_J T hT (𝟙 a.as.as)
    show _ ≫ _ ≫ _ ≫ (rightUnitor _).hom ≫ extendRestrictApp T hT (𝟙 a) ≫ (leftUnitor _).inv = _
    rw [h, Category.id_comp, rightUnitor_naturality_assoc R]
    erw [leftUnitor_inv_naturality R]
    rw [unitors_inv_equal R]
    simp only [Iso.hom_inv_id_assoc]
    erw [unitors_inv_equal R (T.obj a), Iso.hom_inv_id_assoc]
    rfl

include hT in
theorem extendRestrictNatTrans_isStrong : (extendRestrictNatTrans T hT).IsStrong :=
  fun {a b} f => by
  show IsIso ((rightUnitor _).hom ≫ extendRestrictApp T hT f ≫ (leftUnitor _).inv)
  have : IsIso (extendRestrictApp T hT f) :=
    haveI := hT.isGradedSuperfunctor a b
    inferInstanceAs (IsIso ((QPiEnvelope.extendRestrictIso (homFunctor T a b)).app f).hom)
  infer_instance

include hT in
theorem extendRestrictNatTrans_isGraded [GradedTwoSupercategory R C] :
    (extendRestrictNatTrans T hT).IsGraded := fun f => extendRestrictX_mem_degree T hT f

include hT in
/-- The inverses `𝕋F ≅ (𝕋𝕁)~F` of the components of `extendRestrictApp`. -/
def extendRestrictAppInv {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    T.map f ⟶ (extend (restrict T)).map f :=
  haveI := hT.isGradedSuperfunctor a b
  (QPiEnvelope.extendRestrictIso (homFunctor T a b)).inv.app f

include hT in
theorem extendRestrictApp_comp_inv {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictApp T hT f ≫ extendRestrictAppInv T hT f = 𝟙 _ :=
  haveI := hT.isGradedSuperfunctor a b
  (QPiEnvelope.extendRestrictIso (homFunctor T a b)).hom_inv_id_app f

include hT in
theorem extendRestrictAppInv_comp {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictAppInv T hT f ≫ extendRestrictApp T hT f = 𝟙 _ :=
  haveI := hT.isGradedSuperfunctor a b
  (QPiEnvelope.extendRestrictIso (homFunctor T a b)).inv_hom_id_app f

include hT in
theorem extendRestrictAppInv_mem {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictAppInv T hT f ∈ parity (R := R) _ _ 0 :=
  haveI := hT.isGradedSuperfunctor a b
  inv_mem ((QPiEnvelope.extendRestrictIso (homFunctor T a b)).app f)
    (QPiEnvelope.extendRestrictIso_hom_mem (homFunctor T a b) f)

include hT in
theorem extendRestrictAppInv_mem_degree {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictAppInv T hT f ∈ degree (R := R) _ _ 0 := by
  haveI := hT.isGradedSuperfunctor a b
  simpa using inv_mem_degree ((QPiEnvelope.extendRestrictIso (homFunctor T a b)).app f)
    (QPiEnvelope.extendRestrictIso_hom_mem_degree (homFunctor T a b) f)

include hT in
theorem extendRestrictAppInv_naturality {a b : QPiTwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    T.map₂ η ≫ extendRestrictAppInv T hT g =
      extendRestrictAppInv T hT f ≫ (extend (restrict T)).map₂ η :=
  haveI := hT.isGradedSuperfunctor a b
  (QPiEnvelope.extendRestrictIso (homFunctor T a b)).inv.naturality η

include hT in
theorem extendRestrictAppInv_J {a b : QPiTwoEnvelope R B} (f : a.as.as ⟶ b.as.as) :
    extendRestrictAppInv T hT (Jm (R := R) f : a ⟶ b) = 𝟙 _ := by
  have := extendRestrictApp_comp_inv T hT (Jm (R := R) f : a ⟶ b)
  rw [extendRestrictApp_J, Category.id_comp] at this
  exact this

include hT in
/-- The components `𝕋F ≫ 1 ⟶ 1 ≫ (𝕋𝕁)~F` of the inverse 2-natural isomorphism. -/
def extendRestrictInvX {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    T.map f ≫ 𝟙 (T.obj b) ⟶ 𝟙 (T.obj a) ≫ (extend (restrict T)).map f :=
  (rightUnitor _).hom ≫ extendRestrictAppInv T hT f ≫ (leftUnitor _).inv

include hT in
theorem extendRestrictInvX_mem {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictInvX T hT f ∈ parity (R := R) _ _ 0 := by
  have := comp_mem (rightUnitor_hom_mem (R := R) _)
    (comp_mem (extendRestrictAppInv_mem T hT f) (inv_mem _ (leftUnitor_hom_mem (R := R) _)))
  simpa using this

include hT in
theorem extendRestrictInvX_mem_degree [GradedTwoSupercategory R C] {a b : QPiTwoEnvelope R B}
    (f : a ⟶ b) : extendRestrictInvX T hT f ∈ degree (R := R) _ _ 0 := by
  have := comp_mem_degree (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) _)
    (comp_mem_degree (extendRestrictAppInv_mem_degree T hT f)
      (GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := R) _))
  simpa using this

include hT in
theorem extendRestrictInvX_naturality {a b : QPiTwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    T.map₂ η ▷ 𝟙 (T.obj b) ≫ extendRestrictInvX T hT g =
      extendRestrictInvX T hT f ≫ 𝟙 (T.obj a) ◁ (extend (restrict T)).map₂ η := by
  simp only [extendRestrictInvX]
  rw [rightUnitor_naturality_assoc R, reassoc_of% (extendRestrictAppInv_naturality T hT η),
    leftUnitor_inv_naturality R]
  simp only [Category.assoc]
  rfl

include hT in
/-- **The analogue of Theorem 4.9**, even density: the inverse 2-natural transformation
`𝕋 ⇒ (𝕋𝕁)~`. -/
def extendRestrictNatTransInv : TwoNatTrans T (extend (restrict T)) where
  X a := 𝟙 (T.obj a)
  x f := extendRestrictInvX T hT f
  x_mem f := extendRestrictInvX_mem T hT f
  naturality η := extendRestrictInvX_naturality T hT η
  x_comp f g := xcomp_of_J (F' := T) (G' := extend (restrict T)) (fun a => 𝟙 (T.obj a))
    (fun f => extendRestrictInvX T hT f) (fun f => extendRestrictInvX_mem T hT f)
    (fun η => extendRestrictInvX_naturality T hT η)
    (fun {a b c} f g => by
      have h₁ : ((extend (restrict T)).mapComp (Jm (R := R) f) (Jm g)).hom =
          (T.mapComp (Jm f) (Jm g)).hom :=
        extendComp_J (restrict T) f g
      have h₂ : extendRestrictAppInv T hT (Jm (R := R) f ≫ Jm g) = 𝟙 _ :=
        extendRestrictAppInv_J T hT (a := ⟨⟨a⟩⟩) (b := ⟨⟨c⟩⟩) (f ≫ g)
      have h₃ : extendRestrictAppInv T hT (Jm (R := R) f) = 𝟙 _ :=
        extendRestrictAppInv_J T hT (a := ⟨⟨a⟩⟩) (b := ⟨⟨b⟩⟩) f
      have h₄ : extendRestrictAppInv T hT (Jm (R := R) g) = 𝟙 _ :=
        extendRestrictAppInv_J T hT (a := ⟨⟨b⟩⟩) (b := ⟨⟨c⟩⟩) g
      simp only [xcompL, xcompR, extendRestrictInvX, h₂, h₃, h₄, Category.id_comp]
      erw [h₁]
      exact TwoEnvelope.unit_coherence R _ _ _) f g
  x_id a := by
    have h : extendRestrictAppInv T hT (𝟙 a) = 𝟙 _ := extendRestrictAppInv_J T hT (𝟙 a.as.as)
    show _ ≫ _ ≫ _ ≫ (rightUnitor _).hom ≫ extendRestrictAppInv T hT (𝟙 a) ≫
      (leftUnitor _).inv = _
    rw [h, Category.id_comp]
    erw [rightUnitor_naturality_assoc R]
    erw [leftUnitor_inv_naturality R]
    rw [unitors_inv_equal R]
    simp only [Iso.hom_inv_id_assoc]
    rfl

include hT in
theorem extendRestrictNatTransInv_isStrong : (extendRestrictNatTransInv T hT).IsStrong :=
  fun {a b} f => by
  show IsIso ((rightUnitor _).hom ≫ extendRestrictAppInv T hT f ≫ (leftUnitor _).inv)
  have : IsIso (extendRestrictAppInv T hT f) :=
    haveI := hT.isGradedSuperfunctor a b
    inferInstanceAs (IsIso ((QPiEnvelope.extendRestrictIso (homFunctor T a b)).app f).inv)
  infer_instance

include hT in
theorem extendRestrictNatTransInv_isGraded [GradedTwoSupercategory R C] :
    (extendRestrictNatTransInv T hT).IsGraded := fun f => extendRestrictInvX_mem_degree T hT f

include hT in
/-- The components of `extendRestrictNatTrans` and `extendRestrictNatTransInv` are mutually
inverse up to the unitors: `x_F ≫ λ ≫ ρ⁻¹ ≫ x'_F = ρ ≫ λ⁻¹`. -/
theorem extendRestrictX_comp_inv {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictX T hT f ≫ (leftUnitor _).hom ≫ (rightUnitor _).inv ≫
        extendRestrictInvX T hT f = (rightUnitor _).hom ≫ (leftUnitor _).inv := by
  simp only [extendRestrictX, extendRestrictInvX, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc]
  rw [reassoc_of% (extendRestrictApp_comp_inv T hT f)]

include hT in
/-- **The analogue of Theorem 4.9.** The composite `(𝕋𝕁)~ ⇒ 𝕋 ⇒ (𝕋𝕁)~` is isomorphic to the
identity in `ℋom((𝕋𝕁)~, (𝕋𝕁)~)`, by the even unitors `1 1 ≅ 1` of degree zero. -/
def extendRestrictCounitIso :
    TwoNatTrans.vcomp (extendRestrictNatTrans T hT) (extendRestrictNatTransInv T hT) ≅
      TwoNatTrans.id (extend (restrict T)) :=
  TwoEnvelope.supermodificationIso (fun a => leftUnitor (𝟙 (T.obj a))) fun f =>
    vcomp_unitors_naturality R _ _ (extendRestrictApp_comp_inv T hT f)

include hT in
/-- **The analogue of Theorem 4.9.** The composite `𝕋 ⇒ (𝕋𝕁)~ ⇒ 𝕋` is isomorphic to the
identity in `ℋom(𝕋, 𝕋)`, by the even unitors `1 1 ≅ 1` of degree zero. -/
def extendRestrictUnitIso :
    TwoNatTrans.vcomp (extendRestrictNatTransInv T hT) (extendRestrictNatTrans T hT) ≅
      TwoNatTrans.id T :=
  TwoEnvelope.supermodificationIso (fun a => leftUnitor (𝟙 (T.obj a))) fun f =>
    vcomp_unitors_naturality R _ _ (extendRestrictAppInv_comp T hT f)

include hT in
theorem extendRestrictCounitIso_hom_isHomogeneous [GradedTwoSupercategory R C] :
    (extendRestrictCounitIso T hT).hom.IsHomogeneous 0 0 := fun _ =>
  ⟨leftUnitor_hom_mem (R := R) _, GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) _⟩

include hT in
theorem extendRestrictUnitIso_hom_isHomogeneous [GradedTwoSupercategory R C] :
    (extendRestrictUnitIso T hT).hom.IsHomogeneous 0 0 := fun _ =>
  ⟨leftUnitor_hom_mem (R := R) _, GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) _⟩

end Density

/-! ## The analogue of Lemma 4.6 -/

section Complete

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B]

/-- **The analogue of Lemma 4.6** (stated after Definition 6.10). The canonical graded
2-superfunctor `𝕁 : 𝔄 → 𝔄_{q,π}` (the identity on objects) induces graded superequivalences on
all morphism supercategories if and only if `𝔄` is `(Q, Π)`-complete. -/
theorem gradedSuperequivalenceJ_iff :
    (∀ a b : B, Nonempty (GradedSuperequivalence R ((twoJ R B).mapFunctor a b))) ↔
      QPiComplete2 (R := R) (B := B) := by
  rw [← J_gradedEvenlyDense_iff]
  exact forall_congr' fun a => forall_congr' fun b =>
    ⟨fun ⟨e⟩ => e.gradedEvenlyDense,
      fun h => ⟨GradedSuperequivalence.ofFullyFaithful (QPiEnvelope.J R (a ⟶ b)) h⟩⟩

end Complete

end QPiTwoEnvelope


end StringDiagrams

end
