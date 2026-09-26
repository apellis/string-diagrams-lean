import StringDiagrams.Super.TwoEnvelope
import StringDiagrams.Super.TwoFunctor
import StringDiagrams.Super.MonoidalUniversal

/-!
# The universal property of the Π-envelope of a 2-supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Lemma 4.7 and Theorem 4.9.

Let `𝔄` be a 2-supercategory and `𝔅` a 2-supercategory whose morphism supercategories carry
Π-supercategory structures (for a Π-2-supercategory `(𝔅, π, ζ)` these are `Π = π_μ -` with
`ζ_F = ζ_μ F`; see `TwoEnvelope.homPi`). All constructions below only use the Π-supercategory
structures of the morphism supercategories of `𝔅`, so they are stated in this generality.

## Lemma 4.7(i)

A 2-superfunctor `ℝ : 𝔄 → 𝔅` extends to a 2-superfunctor `ℝ̃ : 𝔄_π → 𝔅`
(`TwoEnvelope.extend`): `ℝ̃ λ = ℝ λ`, `ℝ̃(Πᵃ F) = πᵃ(ℝ F)` and on 2-morphisms `ℝ̃` is the
extension `Envelope.extend` of Lemma 4.2(i) of the superfunctors
`ℝ : ℋom(λ, μ) → ℋom(ℝλ, ℝμ)`, i.e. (4.5) `ℝ̃(x_a^b) = (ζᵇ)⁻¹ ∘ ℝx ∘ ζᵃ`. Its coherence maps
are `ĩ = i` and

  `c̃_{Πᵇ G, Πᵃ F} = (-1)^{ab} (ζ^{a+b}_{ℝ(GF)})⁻¹ ∘ c_{G,F} ∘ (ζᵇ_{ℝG} ζᵃ_{ℝF})`

(`TwoEnvelope.extendComp`, with the horizontal composite `ζᵇ ζᵃ` of the paper written
`hcomp ζᵃ ζᵇ` in the diagrammatic order). For a Π-2-supercategory this is the paper's
`c̃ = m_{b,a} c_{G,F} ∘ π^b(β^a)⁻¹_{ℝG}(ℝF)`, with `m_{1,1} = -ξ` (see
`TwoEnvelope.extendComp_eq_paper`). The naturality of `c̃` is `extendComp_naturality_left`,
`extendComp_naturality_right`; the coherence axioms of Definition 2.2(ii), which the paper
leaves to the reader, are proved by the argument behind the uniqueness in Lemma 4.2(ii): both
sides are natural in each 1-morphism with respect to the 2-isomorphisms
`(1_F)_0^a : Π⁰F ≅ ΠᵃF`, so they agree once they agree on the 1-morphisms `Π⁰F`, where they
are the axioms for `ℝ`. `ℝ = ℝ̃ 𝕁` holds on objects, 1- and 2-morphisms and coherence maps
(`TwoEnvelope.extend_map_J`, `extend_map₂_J`, `extendComp_J`, `extend_mapId`).

## Lemma 4.7(ii)

A 2-natural transformation `(X, x) : ℝ ⇒ 𝕊` extends to `(X̃, x̃) : ℝ̃ ⇒ 𝕊̃` with `X̃ = X` and
(4.6) `x̃_{ΠᵃF} = (ζᵃ_{𝕊F} X_λ)⁻¹ ∘ x_F ∘ (X_μ ζᵃ_{ℝF})` (`TwoEnvelope.extendTwoNatTrans`), and
it is the unique 2-natural transformation `ℝ̃ ⇒ 𝕊̃` with `X̃ = X` restricting to `x` along `𝕁`
(`TwoEnvelope.extendTwoNatTrans_unique`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace TwoEnvelope

open Envelope

section Helpers

variable {R : Type w} [CommRing R] {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

variable (R)

include R in
@[reassoc]
theorem inv_hom_whiskerRight' {a b c : C} {f g : a ⟶ b} (e : f ≅ g) (h : b ⟶ c) :
    e.inv ▷ h ≫ e.hom ▷ h = 𝟙 (g ≫ h) :=
  TwoSupercategory.inv_hom_whiskerRight R e h

include R in
@[reassoc]
theorem hom_inv_whiskerRight' {a b c : C} {f g : a ⟶ b} (e : f ≅ g) (h : b ⟶ c) :
    e.hom ▷ h ≫ e.inv ▷ h = 𝟙 (f ≫ h) :=
  TwoSupercategory.hom_inv_whiskerRight R e h

include R in
@[reassoc]
theorem whiskerLeft_inv_hom' {a b c : C} (f : a ⟶ b) {g h : b ⟶ c} (e : g ≅ h) :
    f ◁ e.inv ≫ f ◁ e.hom = 𝟙 (f ≫ h) :=
  TwoSupercategory.whiskerLeft_inv_hom R f e

include R in
@[reassoc]
theorem whiskerLeft_hom_inv' {a b c : C} (f : a ⟶ b) {g h : b ⟶ c} (e : g ≅ h) :
    f ◁ e.hom ≫ f ◁ e.inv = 𝟙 (f ≫ g) :=
  TwoSupercategory.whiskerLeft_hom_inv R f e

include R in
theorem whiskerLeft_comp_comp {a b c : C} (f : a ⟶ b) {g h i : b ⟶ c} {j : a ⟶ c} (η : g ⟶ h)
    (θ : h ⟶ i) (κ : f ≫ i ⟶ j) : f ◁ η ≫ f ◁ θ ≫ κ = f ◁ (η ≫ θ) ≫ κ := by
  rw [whiskerLeft_comp (R := R), Category.assoc]

include R in
theorem comp_whiskerRight_comp {a b c : C} {f g h : a ⟶ b} (i : b ⟶ c) {j : a ⟶ c} (η : f ⟶ g)
    (θ : g ⟶ h) (κ : h ≫ i ⟶ j) : η ▷ i ≫ θ ▷ i ≫ κ = (η ≫ θ) ▷ i ≫ κ := by
  rw [comp_whiskerRight (R := R), Category.assoc]

include R in
/-- The interchange law without sign when the left 2-morphism is even and the right one is
arbitrary. -/
theorem interchange_even_left {a b c : C} {f g : a ⟶ b} {h i : b ⟶ c} {η : f ⟶ g}
    (hη : η ∈ parity (R := R) f g 0) (θ : h ⟶ i) : η ▷ h ≫ g ◁ θ = f ◁ θ ≫ η ▷ i := by
  refine Supercategory.induction_on (R := R) θ ?_ (fun q θ hθ => ?_) (fun θ κ hθ hκ => ?_)
  · rw [whiskerLeft_zero R, whiskerLeft_zero R, Limits.comp_zero, Limits.zero_comp]
  · rw [super_interchange hη hθ, koszulSign_zero_left, one_smul]
  · rw [whiskerLeft_add (R := R), whiskerLeft_add (R := R), Preadditive.comp_add,
      Preadditive.add_comp, hθ, hκ]

include R in
/-- The interchange law without sign when the right 2-morphism is even and the left one is
arbitrary. -/
theorem interchange_even_right {a b c : C} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) {θ : h ⟶ i}
    (hθ : θ ∈ parity (R := R) h i 0) : η ▷ h ≫ g ◁ θ = f ◁ θ ≫ η ▷ i := by
  refine Supercategory.induction_on (R := R) η ?_ (fun q η hη => ?_) (fun η κ hη hκ => ?_)
  · rw [zero_whiskerRight R, zero_whiskerRight R, Limits.comp_zero, Limits.zero_comp]
  · rw [super_interchange hη hθ, koszulSign_zero_right, one_smul]
  · rw [add_whiskerRight (R := R), add_whiskerRight (R := R), Preadditive.comp_add,
      Preadditive.add_comp, hη, hκ]

end Helpers

/-! ## Lemma 4.7(i): extension of 2-superfunctors -/

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  [∀ a b : C, PiSupercategory R (a ⟶ b)]

variable (F : TwoSuperfunctor R B C)

/-- The superfunctor `ℋom_{𝔄_π}(λ, μ) → ℋom_𝔅(ℝλ, ℝμ)` of `ℝ̃`: the extension (Lemma 4.2(i))
of `ℝ : ℋom_𝔄(λ, μ) → ℋom_𝔅(ℝλ, ℝμ)`. -/
abbrev extendFunctor (a b : TwoEnvelope R B) :
    (a ⟶ b) ⥤ (F.obj a.as ⟶ F.obj b.as) :=
  Envelope.extend R (F.mapFunctor a.as b.as)

instance (a b : TwoEnvelope R B) : (extendFunctor F a b).Additive :=
  inferInstanceAs (Envelope.extend R (F.mapFunctor a.as b.as)).Additive

instance (a b : TwoEnvelope R B) : (extendFunctor F a b).Linear R :=
  inferInstanceAs ((Envelope.extend R (F.mapFunctor a.as b.as)).Linear R)

instance (a b : TwoEnvelope R B) : IsSuperfunctor R (extendFunctor F a b) :=
  inferInstanceAs (IsSuperfunctor R (Envelope.extend R (F.mapFunctor a.as b.as)))

variable {a b c d : TwoEnvelope R B}

/-- `ζᵃ_{ℝF} : πᵃ(ℝF) ≅ ℝF` for the 1-morphism `Πᵃ F`. -/
abbrev ζF (f : a ⟶ b) : (extendFunctor F a b).obj f ≅ F.map f.obj :=
  ζPow R f.par (F.map f.obj)

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem ζF_hom_mem (f : a ⟶ b) : (ζF F f).hom ∈ parity (R := R) _ _ f.par :=
  ζPow_hom_mem f.par _

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem ζF_inv_mem (f : a ⟶ b) : (ζF F f).inv ∈ parity (R := R) _ _ f.par :=
  ζPow_inv_mem f.par _

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem extendFunctor_map {f g : a ⟶ b} (η : f ⟶ g) :
    (extendFunctor F a b).map η = (ζF F f).hom ≫ F.map₂ (toHom η) ≫ (ζF F g).inv := rfl

/-- The unsigned composite `hcomp ζᵃ ζᵇ ≫ c ≫ (ζ^{a+b})⁻¹` underlying `c̃`. -/
def extendCompAux (f : a ⟶ b) (g : b ⟶ c) :
    (extendFunctor F a b).obj f ≫ (extendFunctor F b c).obj g ⟶
      (extendFunctor F a c).obj (f ≫ g) :=
  (ζF F f).hom ▷ (extendFunctor F b c).obj g ≫ F.map f.obj ◁ (ζF F g).hom ≫
    (F.mapComp f.obj g.obj).hom ≫ (ζF F (f ≫ g)).inv

/-- The inverse of `extendCompAux`. -/
def extendCompAuxInv (f : a ⟶ b) (g : b ⟶ c) :
    (extendFunctor F a c).obj (f ≫ g) ⟶
      (extendFunctor F a b).obj f ≫ (extendFunctor F b c).obj g :=
  (ζF F (f ≫ g)).hom ≫ (F.mapComp f.obj g.obj).inv ≫ F.map f.obj ◁ (ζF F g).inv ≫
    (ζF F f).inv ▷ (extendFunctor F b c).obj g

omit [TwoSupercategory R B] in
theorem extendCompAux_inv (f : a ⟶ b) (g : b ⟶ c) :
    extendCompAux F f g ≫ extendCompAuxInv F f g = 𝟙 _ := by
  simp only [extendCompAux, extendCompAuxInv, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, whiskerLeft_hom_inv'_assoc R, hom_inv_whiskerRight' R]

omit [TwoSupercategory R B] in
theorem extendCompAuxInv_aux (f : a ⟶ b) (g : b ⟶ c) :
    extendCompAuxInv F f g ≫ extendCompAux F f g = 𝟙 _ := by
  simp only [extendCompAux, extendCompAuxInv, Category.assoc, inv_hom_whiskerRight'_assoc R,
    whiskerLeft_inv_hom'_assoc R, Iso.inv_hom_id_assoc, Iso.hom_inv_id]

/-- **Lemma 4.7(i).** The coherence 2-isomorphism
`c̃ = (-1)^{ab} (ζ^{a+b})⁻¹ ∘ c ∘ (ζᵇ ζᵃ) : ℝ̃(Πᵃ F) ≫ ℝ̃(Πᵇ G) ≅ ℝ̃(Π^{a+b}(F ≫ G))`. -/
def extendComp (f : a ⟶ b) (g : b ⟶ c) :
    (extendFunctor F a b).obj f ≫ (extendFunctor F b c).obj g ≅
      (extendFunctor F a c).obj (f ≫ g) where
  hom := sign R (f.par * g.par) • extendCompAux F f g
  inv := sign R (f.par * g.par) • extendCompAuxInv F f g
  hom_inv_id := by
    rw [Linear.smul_comp, Linear.comp_smul, sign_smul_sign_smul, extendCompAux_inv]
  inv_hom_id := by
    rw [Linear.smul_comp, Linear.comp_smul, sign_smul_sign_smul, extendCompAuxInv_aux]

omit [TwoSupercategory R B] in
theorem extendComp_hom (f : a ⟶ b) (g : b ⟶ c) :
    (extendComp F f g).hom = sign R (f.par * g.par) • extendCompAux F f g := rfl

omit [TwoSupercategory R B] in
theorem extendCompAux_mem (f : a ⟶ b) (g : b ⟶ c) :
    extendCompAux F f g ∈ parity (R := R) _ _ 0 := by
  have := comp_mem (whiskerRight_mem ((extendFunctor F b c).obj g) (ζF_hom_mem F f))
    (comp_mem (whiskerLeft_mem (F.map f.obj) (ζF_hom_mem F g))
      (comp_mem (F.mapComp_hom_mem f.obj g.obj) (ζF_inv_mem F (f ≫ g))))
  have e : f.par + (g.par + (0 + (f ≫ g).par)) = 0 := by
    simp only [comp_par]
    generalize f.par = x; generalize g.par = y; revert x y; decide
  rw [e] at this
  exact this

omit [TwoSupercategory R B] in
theorem extendComp_hom_mem (f : a ⟶ b) (g : b ⟶ c) :
    (extendComp F f g).hom ∈ parity (R := R) _ _ 0 :=
  Submodule.smul_mem _ _ (extendCompAux_mem F f g)

theorem extendComp_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) :
    (extendFunctor F a b).map η ▷ (extendFunctor F b c).obj g ≫ (extendComp F f' g).hom =
      (extendComp F f g).hom ≫ (extendFunctor F a c).map (η ▷ g) := by
  refine induction_on' (R := R) η ?_ (fun r η hη => ?_) (fun η θ hη hθ => ?_)
  · rw [Functor.map_zero, zero_whiskerRight R, TwoEnvelope.zero_whiskerRight', Functor.map_zero,
      Limits.zero_comp, Limits.comp_zero]
  · have hi := super_interchange (R := R) (F.map₂_mem hη) (ζF_hom_mem F g)
    rw [extendComp_hom, extendComp_hom, extendFunctor_map, extendFunctor_map,
      toHom_whiskerRight_of_mem hη g, F.map₂_smul]
    simp only [extendCompAux, comp_whiskerRight (R := R), Category.assoc,
      inv_hom_whiskerRight'_assoc R, Iso.inv_hom_id_assoc, Linear.smul_comp, Linear.comp_smul]
    rw [reassoc_of% hi, Linear.smul_comp, Linear.comp_smul, Category.assoc,
      reassoc_of% (F.mapComp_naturality_left _ _), koszulSign_smul (R := R), smul_smul,
      smul_smul, ← sign_add, ← sign_add]
    congr 2
    generalize f.par = x; generalize f'.par = y; generalize g.par = z
    clear hη hi; revert x y z r; decide
  · rw [Functor.map_add, add_whiskerRight (R := R), TwoEnvelope.add_whiskerRight',
      Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, hη, hθ]

theorem extendComp_naturality_right (f : a ⟶ b) {g g' : b ⟶ c} (θ : g ⟶ g') :
    (extendFunctor F a b).obj f ◁ (extendFunctor F b c).map θ ≫ (extendComp F f g').hom =
      (extendComp F f g).hom ≫ (extendFunctor F a c).map (f ◁ θ) := by
  refine induction_on' (R := R) θ ?_ (fun r θ hθ => ?_) (fun η θ hη hθ => ?_)
  · rw [Functor.map_zero, whiskerLeft_zero R, TwoEnvelope.whiskerLeft_zero', Functor.map_zero,
      Limits.zero_comp, Limits.comp_zero]
  · have hw : (ζF F g).hom ≫ F.map₂ (toHom θ) ≫ (ζF F g').inv ∈
        parity (R := R) _ _ (g.par + r + g'.par) := by
      simpa only [Category.assoc] using comp_mem (comp_mem (ζF_hom_mem F g) (F.map₂_mem hθ))
        (ζF_inv_mem F g')
    have hi := super_interchange (R := R) (ζF_hom_mem F f) hw
    have hi' := congrArg (fun t => koszulSign f.par (g.par + r + g'.par) • t) hi
    simp only [koszulSign_smul_smul] at hi'
    rw [extendComp_hom, extendComp_hom, extendFunctor_map, extendFunctor_map,
      toHom_whiskerLeft_of_mem f hθ, F.map₂_smul]
    simp only [extendCompAux, Linear.comp_smul, Linear.smul_comp]
    rw [reassoc_of% hi'.symm]
    simp only [whiskerLeft_comp (R := R), Category.assoc, whiskerLeft_inv_hom'_assoc R,
      Iso.inv_hom_id_assoc, Linear.smul_comp, Linear.comp_smul]
    rw [reassoc_of% (F.mapComp_naturality_right _ _), koszulSign_smul (R := R), smul_smul,
      smul_smul, ← sign_add, ← sign_add]
    congr 2
    generalize f.par = x; generalize g.par = y; generalize g'.par = z
    clear hθ hi hi' hw; revert x y z r; decide
  · rw [Functor.map_add, whiskerLeft_add (R := R), TwoEnvelope.whiskerLeft_add',
      Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, hη, hθ]

/-! ### Values on the 1-morphisms `Π⁰F` -/

omit [TwoSupercategory R B] in
/-- On 1-morphisms `Π⁰F`, `Π⁰G`, the coherence map `c̃` is `c`. -/
theorem extendComp_J (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) :
    (extendComp F (a := a) (b := b) (c := c) ((J R _).obj f) ((J R _).obj g)).hom =
      (F.mapComp f g).hom := by
  show sign R (0 * 0) • (𝟙 (F.map f) ▷ F.map g ≫ F.map f ◁ 𝟙 (F.map g) ≫ (F.mapComp f g).hom ≫
    𝟙 _) = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), mul_zero, sign_zero, one_smul,
    Category.id_comp, Category.id_comp, Category.comp_id]

omit [TwoSupercategory R B] in
theorem extendComp_J_comp_left (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) (h : c.as ⟶ d.as) :
    (extendComp F (a := a) (b := c) (c := d)
      (((J R _).obj f : a ⟶ b) ≫ ((J R _).obj g : b ⟶ c)) ((J R _).obj h)).hom =
      (F.mapComp (f ≫ g) h).hom := by
  show sign R (0 * 0) • (𝟙 (F.map (f ≫ g)) ▷ F.map h ≫ F.map (f ≫ g) ◁ 𝟙 (F.map h) ≫
    (F.mapComp (f ≫ g) h).hom ≫ 𝟙 _) = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), mul_zero, sign_zero, one_smul,
    Category.id_comp, Category.id_comp, Category.comp_id]

omit [TwoSupercategory R B] in
theorem extendComp_J_comp_right (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) (h : c.as ⟶ d.as) :
    (extendComp F (a := a) (b := b) (c := d) ((J R _).obj f)
      (((J R _).obj g : b ⟶ c) ≫ ((J R _).obj h : c ⟶ d))).hom =
      (F.mapComp f (g ≫ h)).hom := by
  show sign R (0 * 0) • (𝟙 (F.map f) ▷ F.map (g ≫ h) ≫ F.map f ◁ 𝟙 (F.map (g ≫ h)) ≫
    (F.mapComp f (g ≫ h)).hom ≫ 𝟙 _) = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), mul_zero, sign_zero, one_smul,
    Category.id_comp, Category.id_comp, Category.comp_id]

omit [TwoSupercategory R B] [TwoSupercategory R C] in
/-- On 2-morphisms between 1-morphisms `Π⁰F`, `ℝ̃` is `ℝ`. -/
theorem extendFunctor_map_J {f g : a.as ⟶ b.as}
    (η : ((J R (a.as ⟶ b.as)).obj f : a ⟶ b) ⟶ (J R (a.as ⟶ b.as)).obj g) :
    (extendFunctor F a b).map η = F.map₂ (toHom η) := by
  show 𝟙 _ ≫ F.map₂ _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-! ### The coherence axioms for `ℝ̃` -/

local notation "F̃" => extendFunctor F

/-- The left-hand side of the hexagon of Definition 2.2(ii) for `ℝ̃`. -/
def assocL (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F̃ a b).obj f ≫ ((F̃ b c).obj g ≫ (F̃ c d).obj h) ⟶ (F̃ a d).obj ((f ≫ g) ≫ h) :=
  (F̃ a b).obj f ◁ (extendComp F g h).hom ≫ (extendComp F f (g ≫ h)).hom ≫
    (F̃ a d).map (associator f g h).inv

/-- The right-hand side of the hexagon of Definition 2.2(ii) for `ℝ̃`. -/
def assocR (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F̃ a b).obj f ≫ ((F̃ b c).obj g ≫ (F̃ c d).obj h) ⟶ (F̃ a d).obj ((f ≫ g) ≫ h) :=
  (associator ((F̃ a b).obj f) ((F̃ b c).obj g) ((F̃ c d).obj h)).inv ≫
    (extendComp F f g).hom ▷ (F̃ c d).obj h ≫ (extendComp F (f ≫ g) h).hom

theorem assocL_nat₁ {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    (F̃ a b).map u ▷ ((F̃ b c).obj g ≫ (F̃ c d).obj h) ≫ assocL F f' g h =
      assocL F f g h ≫ (F̃ a d).map ((u ▷ g) ▷ h) := by
  simp only [assocL]
  rw [← Category.assoc, interchange_even_right R _ (extendComp_hom_mem F g h), Category.assoc,
    reassoc_of% (extendComp_naturality_left F u (g ≫ h)), ← Functor.map_comp,
    associator_inv_naturality_left R, Functor.map_comp]
  simp only [Category.assoc]

theorem assocR_nat₁ {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    (F̃ a b).map u ▷ ((F̃ b c).obj g ≫ (F̃ c d).obj h) ≫ assocR F f' g h =
      assocR F f g h ≫ (F̃ a d).map ((u ▷ g) ▷ h) := by
  simp only [assocR]
  rw [associator_inv_naturality_left_assoc R, comp_whiskerRight_comp R,
    extendComp_naturality_left, ← comp_whiskerRight_comp R, extendComp_naturality_left]
  simp only [Category.assoc]

theorem assocL_nat₂ (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') (h : c ⟶ d) :
    (F̃ a b).obj f ◁ ((F̃ b c).map v ▷ (F̃ c d).obj h) ≫ assocL F f g' h =
      assocL F f g h ≫ (F̃ a d).map ((f ◁ v) ▷ h) := by
  simp only [assocL]
  rw [whiskerLeft_comp_comp R, extendComp_naturality_left, ← whiskerLeft_comp_comp R,
    reassoc_of% (extendComp_naturality_right F f (v ▷ h)),
    ← Functor.map_comp, associator_inv_naturality_middle R, Functor.map_comp]
  simp only [Category.assoc]

theorem assocR_nat₂ (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') (h : c ⟶ d) :
    (F̃ a b).obj f ◁ ((F̃ b c).map v ▷ (F̃ c d).obj h) ≫ assocR F f g' h =
      assocR F f g h ≫ (F̃ a d).map ((f ◁ v) ▷ h) := by
  simp only [assocR]
  rw [associator_inv_naturality_middle_assoc R, comp_whiskerRight_comp R,
    extendComp_naturality_right, ← comp_whiskerRight_comp R, extendComp_naturality_left]
  simp only [Category.assoc]

theorem assocL_nat₃ (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (w : h ⟶ h') :
    (F̃ a b).obj f ◁ (F̃ b c).obj g ◁ (F̃ c d).map w ≫ assocL F f g h' =
      assocL F f g h ≫ (F̃ a d).map ((f ≫ g) ◁ w) := by
  simp only [assocL]
  rw [whiskerLeft_comp_comp R, extendComp_naturality_right, ← whiskerLeft_comp_comp R,
    reassoc_of% (extendComp_naturality_right F f (g ◁ w)), ← Functor.map_comp,
    associator_inv_naturality_right R, Functor.map_comp]
  simp only [Category.assoc]

theorem assocR_nat₃ (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (w : h ⟶ h') :
    (F̃ a b).obj f ◁ (F̃ b c).obj g ◁ (F̃ c d).map w ≫ assocR F f g h' =
      assocR F f g h ≫ (F̃ a d).map ((f ≫ g) ◁ w) := by
  simp only [assocR]
  rw [associator_inv_naturality_right_assoc R,
    ← reassoc_of% (interchange_even_left R (extendComp_hom_mem F f g) ((F̃ c d).map w)),
    extendComp_naturality_right]
  simp only [Category.assoc]

/-- Cancellation of an epimorphism conjugating two pairs of morphisms. -/
theorem eq_of_conj_hom {D : Type*} [Category D] {X X' Y Y' : D} (e : X ⟶ X') (he : Epi e)
    (g : Y ⟶ Y') {φ ψ : X' ⟶ Y'} {φ₀ ψ₀ : X ⟶ Y} (hφ : e ≫ φ = φ₀ ≫ g)
    (hψ : e ≫ ψ = ψ₀ ≫ g) (h : φ₀ = ψ₀) : φ = ψ := by
  rw [← cancel_epi e, hφ, hψ, h]

theorem assocL_eq_assocR (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    assocL F f g h = assocR F f g h := by
  have e₁ : Epi ((F̃ a b).map (shiftIso f).hom ▷ ((F̃ b c).obj g ≫ (F̃ c d).obj h)) :=
    (inferInstance : Epi (whiskerRightIso (R := R) ((F̃ a b).mapIso (shiftIso f)) _).hom)
  refine eq_of_conj_hom _ e₁ _ (assocL_nat₁ F (shiftIso f).hom g h)
    (assocR_nat₁ F (shiftIso f).hom g h) ?_
  have e₂ : Epi ((F̃ a b).obj ((J R _).obj f.obj) ◁
      ((F̃ b c).map (shiftIso g).hom ▷ (F̃ c d).obj h)) :=
    (inferInstance : Epi (whiskerLeftIso (R := R) _ (whiskerRightIso (R := R)
      ((F̃ b c).mapIso (shiftIso g)) ((F̃ c d).obj h))).hom)
  refine eq_of_conj_hom _ e₂ _ (assocL_nat₂ F _ (shiftIso g).hom h)
    (assocR_nat₂ F _ (shiftIso g).hom h) ?_
  have e₃ : Epi ((F̃ a b).obj ((J R _).obj f.obj) ◁ (F̃ b c).obj ((J R _).obj g.obj) ◁
      (F̃ c d).map (shiftIso h).hom) :=
    (inferInstance : Epi (whiskerLeftIso (R := R) _ (whiskerLeftIso (R := R) _
      ((F̃ c d).mapIso (shiftIso h)))).hom)
  refine eq_of_conj_hom _ e₃ _ (assocL_nat₃ F _ _ (shiftIso h).hom)
    (assocR_nat₃ F _ _ (shiftIso h).hom) ?_
  simp only [assocL, assocR]
  rw [extendComp_J, extendComp_J, extendComp_J_comp_left, extendComp_J_comp_right]
  have e : (F̃ a d).map (associator ((J R _).obj f.obj : a ⟶ b) ((J R _).obj g.obj : b ⟶ c)
      ((J R _).obj h.obj : c ⟶ d)).inv = F.map₂ (associator f.obj g.obj h.obj).inv := by
    show 𝟙 _ ≫ F.map₂ _ ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]; rfl
  rw [e]
  exact F.map₂_associator f.obj g.obj h.obj

omit [TwoSupercategory R B] in
theorem extendComp_id_J (f : a.as ⟶ b.as) :
    (extendComp F (𝟙 a) ((J R _).obj f : a ⟶ b)).hom = (F.mapComp (𝟙 a.as) f).hom := by
  show sign R (0 * 0) • (𝟙 (F.map (𝟙 a.as)) ▷ F.map f ≫ F.map (𝟙 a.as) ◁ 𝟙 (F.map f) ≫
    (F.mapComp (𝟙 a.as) f).hom ≫ 𝟙 _) = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), mul_zero, sign_zero, one_smul,
    Category.id_comp, Category.id_comp, Category.comp_id]

omit [TwoSupercategory R B] in
theorem extendComp_J_id (f : a.as ⟶ b.as) :
    (extendComp F ((J R _).obj f : a ⟶ b) (𝟙 b)).hom = (F.mapComp f (𝟙 b.as)).hom := by
  show sign R (0 * 0) • (𝟙 (F.map f) ▷ F.map (𝟙 b.as) ≫ F.map f ◁ 𝟙 (F.map (𝟙 b.as)) ≫
    (F.mapComp f (𝟙 b.as)).hom ≫ 𝟙 _) = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), mul_zero, sign_zero, one_smul,
    Category.id_comp, Category.id_comp, Category.comp_id]

theorem extend_leftUnitor (f : a ⟶ b) :
    (F.mapId a.as).hom ▷ (F̃ a b).obj f ≫ (extendComp F (𝟙 a) f).hom ≫
        (F̃ a b).map (leftUnitor f).hom = (leftUnitor ((F̃ a b).obj f)).hom := by
  have nat : ∀ {f f' : a ⟶ b} (u : f ⟶ f'), 𝟙 _ ◁ (F̃ a b).map u ≫
      ((F.mapId a.as).hom ▷ (F̃ a b).obj f' ≫ (extendComp F (𝟙 a) f').hom ≫
        (F̃ a b).map (leftUnitor f').hom) =
      ((F.mapId a.as).hom ▷ (F̃ a b).obj f ≫ (extendComp F (𝟙 a) f).hom ≫
        (F̃ a b).map (leftUnitor f).hom) ≫ (F̃ a b).map u := by
    intro f f' u
    rw [← reassoc_of% (interchange_even_left R (F.mapId_hom_mem a.as) ((F̃ a b).map u))]
    erw [reassoc_of% (extendComp_naturality_right F (𝟙 a) u)]
    rw [← Functor.map_comp, leftUnitor_naturality R, Functor.map_comp]
    simp only [Category.assoc]
  have e₁ : Epi (𝟙 (F.obj a.as) ◁ (F̃ a b).map (shiftIso f).hom) :=
    (inferInstance : Epi (whiskerLeftIso (R := R) _ ((F̃ a b).mapIso (shiftIso f))).hom)
  refine eq_of_conj_hom _ e₁ _ (nat (shiftIso f).hom) (leftUnitor_naturality R _) ?_
  rw [extendComp_id_J]
  have e : (F̃ a b).map (leftUnitor ((J R _).obj f.obj : a ⟶ b)).hom =
      F.map₂ (leftUnitor f.obj).hom := by
    show 𝟙 _ ≫ F.map₂ _ ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]; rfl
  rw [e]
  exact F.map₂_leftUnitor f.obj

theorem extend_rightUnitor (f : a ⟶ b) :
    (F̃ a b).obj f ◁ (F.mapId b.as).hom ≫ (extendComp F f (𝟙 b)).hom ≫
        (F̃ a b).map (rightUnitor f).hom = (rightUnitor ((F̃ a b).obj f)).hom := by
  have nat : ∀ {f f' : a ⟶ b} (u : f ⟶ f'), (F̃ a b).map u ▷ 𝟙 _ ≫
      ((F̃ a b).obj f' ◁ (F.mapId b.as).hom ≫ (extendComp F f' (𝟙 b)).hom ≫
        (F̃ a b).map (rightUnitor f').hom) =
      ((F̃ a b).obj f ◁ (F.mapId b.as).hom ≫ (extendComp F f (𝟙 b)).hom ≫
        (F̃ a b).map (rightUnitor f).hom) ≫ (F̃ a b).map u := by
    intro f f' u
    rw [reassoc_of% (interchange_even_right R ((F̃ a b).map u) (F.mapId_hom_mem b.as))]
    erw [reassoc_of% (extendComp_naturality_left F u (𝟙 b))]
    rw [← Functor.map_comp, rightUnitor_naturality R, Functor.map_comp]
    simp only [Category.assoc]
  have e₁ : Epi ((F̃ a b).map (shiftIso f).hom ▷ 𝟙 (F.obj b.as)) :=
    (inferInstance : Epi (whiskerRightIso (R := R) ((F̃ a b).mapIso (shiftIso f)) _).hom)
  refine eq_of_conj_hom _ e₁ _ (nat (shiftIso f).hom) (rightUnitor_naturality R _) ?_
  rw [extendComp_J_id]
  have e : (F̃ a b).map (rightUnitor ((J R _).obj f.obj : a ⟶ b)).hom =
      F.map₂ (rightUnitor f.obj).hom := by
    show 𝟙 _ ≫ F.map₂ _ ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]; rfl
  rw [e]
  exact F.map₂_rightUnitor f.obj

/-- **Lemma 4.7(i).** The extension `ℝ̃ : 𝔄_π → 𝔅` of a 2-superfunctor `ℝ : 𝔄 → 𝔅` to the
Π-envelope: `ℝ̃λ = ℝλ`, `ℝ̃(ΠᵃF) = πᵃ(ℝF)`, `ℝ̃(x_a^b) = (ζᵇ)⁻¹ ∘ ℝx ∘ ζᵃ` (4.5), coherence maps
`c̃` (`extendComp`) and `ĩ = i`. -/
def extend : TwoSuperfunctor R (TwoEnvelope R B) C where
  obj a := F.obj a.as
  map {a b} f := (F̃ a b).obj f
  map₂ {a b _ _} η := (F̃ a b).map η
  map₂_id {a b} f := (F̃ a b).map_id f
  map₂_comp {a b _ _ _} η θ := (F̃ a b).map_comp η θ
  map₂_add {a b _ _} _ _ := (F̃ a b).map_add
  map₂_smul {a b _ _} r η := Functor.map_smul (F̃ a b) r η
  map₂_mem {a b _ _ _ _} hη := IsSuperfunctor.map_mem (F := F̃ a b) hη
  mapComp f g := extendComp F f g
  mapId a := F.mapId a.as
  mapComp_hom_mem f g := extendComp_hom_mem F f g
  mapId_hom_mem a := F.mapId_hom_mem a.as
  mapComp_naturality_left η g := extendComp_naturality_left F η g
  mapComp_naturality_right f _ _ θ := extendComp_naturality_right F f θ
  map₂_associator f g h := assocL_eq_assocR F f g h
  map₂_leftUnitor f := extend_leftUnitor F f
  map₂_rightUnitor f := extend_rightUnitor F f

@[simp] theorem extend_obj (a : TwoEnvelope R B) : (extend F).obj a = F.obj a.as := rfl

theorem extend_map (f : a ⟶ b) : (extend F).map f = (F̃ a b).obj f := rfl

theorem extend_map₂ {f g : a ⟶ b} (η : f ⟶ g) : (extend F).map₂ η = (F̃ a b).map η := rfl

/-- `ℝ = ℝ̃ 𝕁` on 1-morphisms. -/
theorem extend_map_J (f : a.as ⟶ b.as) :
    (extend F).map ((J R _).obj f : a ⟶ b) = F.map f := rfl

/-- `ℝ = ℝ̃ 𝕁` on 2-morphisms. -/
theorem extend_map₂_J {f g : a.as ⟶ b.as} (η : f ⟶ g) :
    (extend F).map₂ ((J R (a.as ⟶ b.as)).map η : ((J R _).obj f : a ⟶ b) ⟶ (J R _).obj g) =
      F.map₂ η :=
  extendFunctor_map_J F _

/-- `ℝ = ℝ̃ 𝕁` on the coherence maps `i`. -/
theorem extend_mapId (a : TwoEnvelope R B) : (extend F).mapId a = F.mapId a.as := rfl

end TwoEnvelope

/-! ## Lemma 4.7(ii): extension of 2-natural transformations -/

namespace TwoEnvelope

open Envelope

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  [∀ a b : C, PiSupercategory R (a ⟶ b)]
  {F G : TwoSuperfunctor R B C}

local notation "F̃" => extendFunctor F
local notation "G̃" => extendFunctor G

variable {a b c : TwoEnvelope R B}

/-- Formula (4.6): `x̃_{ΠᵃF} = (ζᵃ_{𝕊F} X_λ)⁻¹ ∘ x_F ∘ (X_μ ζᵃ_{ℝF})`, in the diagrammatic
order `ζᵃ ▷ X_μ ≫ x_F ≫ X_λ ◁ (ζᵃ)⁻¹`. -/
def extendX (θ : TwoNatTrans F G) (f : a ⟶ b) :
    (F̃ a b).obj f ≫ θ.X b.as ⟶ θ.X a.as ≫ (G̃ a b).obj f :=
  (ζF F f).hom ▷ θ.X b.as ≫ θ.x f.obj ≫ θ.X a.as ◁ (ζF G f).inv

omit [TwoSupercategory R B] in
theorem extendX_mem (θ : TwoNatTrans F G) (f : a ⟶ b) :
    extendX θ f ∈ parity (R := R) _ _ 0 := by
  have := comp_mem (whiskerRight_mem (θ.X b.as) (ζF_hom_mem F f))
    (comp_mem (θ.x_mem f.obj) (whiskerLeft_mem (θ.X a.as) (ζF_inv_mem G f)))
  rwa [zero_add, zmod2_add_self] at this

omit [TwoSupercategory R B] in
theorem extendX_naturality (θ : TwoNatTrans F G) {f g : a ⟶ b} (η : f ⟶ g) :
    (F̃ a b).map η ▷ θ.X b.as ≫ extendX θ g = extendX θ f ≫ θ.X a.as ◁ (G̃ a b).map η := by
  simp only [extendX, extendFunctor_map, comp_whiskerRight (R := R), whiskerLeft_comp (R := R),
    Category.assoc, inv_hom_whiskerRight'_assoc R, whiskerLeft_inv_hom'_assoc R]
  rw [reassoc_of% (θ.naturality (toHom η))]

omit [TwoSupercategory R B] in
theorem extendX_J (θ : TwoNatTrans F G) (f : a.as ⟶ b.as) :
    extendX θ ((J R _).obj f : a ⟶ b) = θ.x f := by
  show 𝟙 (F.map f) ▷ θ.X b.as ≫ θ.x f ≫ θ.X a.as ◁ 𝟙 (G.map f) = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp, Category.comp_id]

omit [TwoSupercategory R B] in
theorem extendX_J_comp (θ : TwoNatTrans F G) (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) :
    extendX θ (((J R _).obj f : a ⟶ b) ≫ ((J R _).obj g : b ⟶ c)) = θ.x (f ≫ g) := by
  show 𝟙 (F.map (f ≫ g)) ▷ θ.X c.as ≫ θ.x (f ≫ g) ≫ θ.X a.as ◁ 𝟙 (G.map (f ≫ g)) = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp, Category.comp_id]

section Comp

variable (θ : TwoNatTrans F G)

/-- The left-hand side of the first coherence diagram of Definition 2.2(iii) for `(X̃, x̃)`. -/
def compL (f : a ⟶ b) (g : b ⟶ c) :
    ((F̃ a b).obj f ≫ (F̃ b c).obj g) ≫ θ.X c.as ⟶ θ.X a.as ≫ (G̃ a c).obj (f ≫ g) :=
  (extendComp F f g).hom ▷ θ.X c.as ≫ extendX θ (f ≫ g)

/-- The right-hand side of the first coherence diagram of Definition 2.2(iii) for
`(X̃, x̃)`. -/
def compR (f : a ⟶ b) (g : b ⟶ c) :
    ((F̃ a b).obj f ≫ (F̃ b c).obj g) ≫ θ.X c.as ⟶ θ.X a.as ≫ (G̃ a c).obj (f ≫ g) :=
  (associator ((F̃ a b).obj f) ((F̃ b c).obj g) (θ.X c.as)).hom ≫
    (F̃ a b).obj f ◁ extendX θ g ≫ (associator ((F̃ a b).obj f) (θ.X b.as) ((G̃ b c).obj g)).inv ≫
      extendX θ f ▷ (G̃ b c).obj g ≫
        (associator (θ.X a.as) ((G̃ a b).obj f) ((G̃ b c).obj g)).hom ≫
          θ.X a.as ◁ (extendComp G f g).hom

theorem compL_nat₁ {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) :
    ((F̃ a b).map u ▷ (F̃ b c).obj g) ▷ θ.X c.as ≫ compL θ f' g =
      compL θ f g ≫ θ.X a.as ◁ (G̃ a c).map (u ▷ g) := by
  simp only [compL]
  rw [comp_whiskerRight_comp R, extendComp_naturality_left, ← comp_whiskerRight_comp R,
    extendX_naturality]
  simp only [Category.assoc]

theorem compR_nat₁ {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) :
    ((F̃ a b).map u ▷ (F̃ b c).obj g) ▷ θ.X c.as ≫ compR θ f' g =
      compR θ f g ≫ θ.X a.as ◁ (G̃ a c).map (u ▷ g) := by
  simp only [compR]
  rw [associator_naturality_left_assoc R,
    reassoc_of% (interchange_even_right R ((F̃ a b).map u) (extendX_mem θ g)),
    associator_inv_naturality_left_assoc R, comp_whiskerRight_comp R, extendX_naturality,
    ← comp_whiskerRight_comp R, associator_naturality_middle_assoc R,
    ← whiskerLeft_comp (R := R), extendComp_naturality_left, whiskerLeft_comp (R := R)]
  simp only [Category.assoc]

theorem compL_nat₂ (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') :
    ((F̃ a b).obj f ◁ (F̃ b c).map v) ▷ θ.X c.as ≫ compL θ f g' =
      compL θ f g ≫ θ.X a.as ◁ (G̃ a c).map (f ◁ v) := by
  simp only [compL]
  rw [comp_whiskerRight_comp R, extendComp_naturality_right, ← comp_whiskerRight_comp R,
    extendX_naturality]
  simp only [Category.assoc]

theorem compR_nat₂ (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') :
    ((F̃ a b).obj f ◁ (F̃ b c).map v) ▷ θ.X c.as ≫ compR θ f g' =
      compR θ f g ≫ θ.X a.as ◁ (G̃ a c).map (f ◁ v) := by
  simp only [compR]
  rw [associator_naturality_middle_assoc R, whiskerLeft_comp_comp R, extendX_naturality,
    ← whiskerLeft_comp_comp R, associator_inv_naturality_right_assoc R,
    ← reassoc_of% (interchange_even_left R (extendX_mem θ f) ((G̃ b c).map v)),
    associator_naturality_right_assoc R, ← whiskerLeft_comp (R := R),
    extendComp_naturality_right, whiskerLeft_comp (R := R)]
  simp only [Category.assoc]

theorem compL_eq_compR (f : a ⟶ b) (g : b ⟶ c) : compL θ f g = compR θ f g := by
  have e₁ : Epi (((F̃ a b).map (shiftIso f).hom ▷ (F̃ b c).obj g) ▷ θ.X c.as) :=
    (inferInstance : Epi (whiskerRightIso (R := R) (whiskerRightIso (R := R)
      ((F̃ a b).mapIso (shiftIso f)) _) _).hom)
  refine eq_of_conj_hom _ e₁ _ (compL_nat₁ θ (shiftIso f).hom g)
    (compR_nat₁ θ (shiftIso f).hom g) ?_
  have e₂ : Epi (((F̃ a b).obj ((J R _).obj f.obj) ◁ (F̃ b c).map (shiftIso g).hom) ▷
      θ.X c.as) :=
    (inferInstance : Epi (whiskerRightIso (R := R) (whiskerLeftIso (R := R) _
      ((F̃ b c).mapIso (shiftIso g))) _).hom)
  refine eq_of_conj_hom _ e₂ _ (compL_nat₂ θ _ (shiftIso g).hom)
    (compR_nat₂ θ _ (shiftIso g).hom) ?_
  simp only [compL, compR]
  rw [extendComp_J, extendComp_J, extendX_J, extendX_J, extendX_J_comp]
  exact θ.x_comp f.obj g.obj

end Comp

/-- **Lemma 4.7(ii).** The extension `(X̃, x̃) : ℝ̃ ⇒ 𝕊̃` of a 2-natural transformation
`(X, x) : ℝ ⇒ 𝕊`: `X̃_λ = X_λ` and `x̃` given by (4.6) (`extendX`). -/
def extendTwoNatTrans (θ : TwoNatTrans F G) : TwoNatTrans (extend F) (extend G) where
  X a := θ.X a.as
  x f := extendX θ f
  x_mem f := extendX_mem θ f
  naturality η := extendX_naturality θ η
  x_comp f g := compL_eq_compR θ f g
  x_id a := by
    have e : extendX θ (𝟙 a) = θ.x (𝟙 a.as) := extendX_J θ (𝟙 a.as)
    show _ ≫ _ ≫ _ ≫ extendX θ (𝟙 a) = _
    rw [e]
    exact θ.x_id a.as

@[simp] theorem extendTwoNatTrans_X (θ : TwoNatTrans F G) (a : TwoEnvelope R B) :
    (extendTwoNatTrans θ).X a = θ.X a.as := rfl

theorem extendTwoNatTrans_x (θ : TwoNatTrans F G) (f : a ⟶ b) :
    (extendTwoNatTrans θ).x f = extendX θ f := rfl

/-- `x = x̃ 𝕁`. -/
theorem extendTwoNatTrans_x_J (θ : TwoNatTrans F G) (f : a.as ⟶ b.as) :
    (extendTwoNatTrans θ).x ((J R _).obj f : a ⟶ b) = θ.x f :=
  extendX_J θ f

omit [TwoSupercategory R B] [TwoSupercategory R C] [∀ a b : C, PiSupercategory R (a ⟶ b)] in
/-- Two 2-natural transformations with the same 1-morphisms and the same 2-morphisms are
equal. -/
theorem twoNatTrans_ext {F' G' : TwoSuperfunctor R B C} {θ θ' : TwoNatTrans F' G'}
    (hX : θ.X = θ'.X) (hx : ∀ {a b : B} (f : a ⟶ b), HEq (θ.x f) (θ'.x f)) : θ = θ' := by
  obtain ⟨X, x, _, _, _, _⟩ := θ
  obtain ⟨X', x', _, _, _, _⟩ := θ'
  dsimp only at hX hx
  subst hX
  have : @x = @x' := by
    funext a b f
    exact eq_of_heq (hx f)
  subst this
  rfl

/-- The restriction `(Y, y𝕁) : ℝ ⇒ 𝕊` of a 2-natural transformation `(Y, y) : ℝ̃ ⇒ 𝕊̃`. -/
def restrictTwoNatTrans (ψ : TwoNatTrans (extend F) (extend G)) : TwoNatTrans F G where
  X a := ψ.X ⟨a⟩
  x {a b} f := ψ.x ((J R (a ⟶ b)).obj f : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩)
  x_mem {a b} f := ψ.x_mem ((J R (a ⟶ b)).obj f : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩)
  naturality {a b f g} η := by
    have := ψ.naturality ((J R (a ⟶ b)).map η : ((J R (a ⟶ b)).obj f : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩) ⟶ _)
    rwa [extend_map₂_J, extend_map₂_J] at this
  x_comp {a b c} f g := by
    have := ψ.x_comp ((J R (a ⟶ b)).obj f : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩)
      ((J R (b ⟶ c)).obj g : (⟨b⟩ : TwoEnvelope R B) ⟶ ⟨c⟩)
    erw [extendComp_J, extendComp_J] at this
    exact this
  x_id a := ψ.x_id ⟨a⟩

@[simp] theorem restrictTwoNatTrans_X (ψ : TwoNatTrans (extend F) (extend G)) (a : B) :
    (restrictTwoNatTrans ψ).X a = ψ.X ⟨a⟩ := rfl

theorem restrictTwoNatTrans_x (ψ : TwoNatTrans (extend F) (extend G)) {a b : B} (f : a ⟶ b) :
    (restrictTwoNatTrans ψ).x f =
      ψ.x ((J R (a ⟶ b)).obj f : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩) := rfl

/-- `(X̃, x̃)` restricts to `(X, x)`. -/
theorem restrictTwoNatTrans_extendTwoNatTrans (θ : TwoNatTrans F G) :
    restrictTwoNatTrans (extendTwoNatTrans θ) = θ :=
  twoNatTrans_ext rfl fun {a b} f =>
    heq_of_eq (extendX_J (a := (⟨a⟩ : TwoEnvelope R B)) (b := ⟨b⟩) θ f)

/-- A 2-natural transformation `ℝ̃ ⇒ 𝕊̃` is the extension of its restriction. -/
theorem extendTwoNatTrans_restrictTwoNatTrans (ψ : TwoNatTrans (extend F) (extend G)) :
    extendTwoNatTrans (restrictTwoNatTrans ψ) = ψ := by
  refine twoNatTrans_ext rfl fun {a b} f => heq_of_eq ?_
  have h := ψ.naturality (shiftIso f).inv
  have e₁ : (extend F).map₂ (shiftIso f).inv = (ζF F f).hom := by
    show (ζF F f).hom ≫ F.map₂ (𝟙 f.obj) ≫ 𝟙 _ = _
    rw [F.map₂_id, Category.comp_id, Category.comp_id]
  have e₂ : (extend G).map₂ (shiftIso f).inv = (ζF G f).hom := by
    show (ζF G f).hom ≫ G.map₂ (𝟙 f.obj) ≫ 𝟙 _ = _
    rw [G.map₂_id, Category.comp_id, Category.comp_id]
  rw [e₁, e₂] at h
  show (ζF F f).hom ▷ ψ.X b ≫ ψ.x ((J R _).obj f.obj) ≫ ψ.X a ◁ (ζF G f).inv = ψ.x f
  rw [reassoc_of% h, whiskerLeft_hom_inv' R, Category.comp_id]

/-- **Lemma 4.7(ii), uniqueness.** `(X̃, x̃)` is the unique 2-natural transformation
`ℝ̃ ⇒ 𝕊̃` with `X̃_λ = X_λ` and `x = x̃ 𝕁`. -/
theorem extendTwoNatTrans_unique (θ : TwoNatTrans F G) (ψ : TwoNatTrans (extend F) (extend G))
    (h : restrictTwoNatTrans ψ = θ) : ψ = extendTwoNatTrans θ := by
  rw [← h, extendTwoNatTrans_restrictTwoNatTrans]

/-- **Theorem 4.9**, full faithfulness on 2-natural transformations: `(X, x) ↦ (X̃, x̃)` is a
bijection from 2-natural transformations `ℝ ⇒ 𝕊` to 2-natural transformations `ℝ̃ ⇒ 𝕊̃`, with
inverse the restriction along `𝕁`. -/
def extendTwoNatTransEquiv : TwoNatTrans F G ≃ TwoNatTrans (extend F) (extend G) where
  toFun := extendTwoNatTrans
  invFun := restrictTwoNatTrans
  left_inv := restrictTwoNatTrans_extendTwoNatTrans
  right_inv := extendTwoNatTrans_restrictTwoNatTrans

/-! ## Remark 4.10 and Theorem 4.9 on morphism supercategories -/

theorem extend_naturality_of_mem {θ θ' : TwoNatTrans F G} {p : ZMod 2}
    (α : ∀ a : B, θ.X a ⟶ θ'.X a) (hα : ∀ a, α a ∈ parity (R := R) _ _ p)
    (nat : ∀ {a b : B} (f : a ⟶ b), θ.x f ≫ α a ▷ G.map f = F.map f ◁ α b ≫ θ'.x f)
    {a b : TwoEnvelope R B} (f : a ⟶ b) :
    (extendTwoNatTrans θ).x f ≫ α a.as ▷ (extend G).map f =
      (extend F).map f ◁ α b.as ≫ (extendTwoNatTrans θ').x f := by
  simp only [extendTwoNatTrans_x, extendX, extend_map, Category.assoc]
  have h₁ := super_interchange (R := R) (hα a.as) (ζF_inv_mem G f)
  have h₂ := super_interchange (R := R) (ζF_hom_mem F f) (hα b.as)
  rw [← koszulSign_smul_smul p f.par (θ.X a.as ◁ _ ≫ _), ← h₁, Linear.comp_smul,
    Linear.comp_smul, reassoc_of% (nat f.obj), ← Category.assoc ((ζF F f).hom ▷ _),
    h₂, Linear.smul_comp, smul_smul, koszulSign_comm, koszulSign_mul_self, one_smul]
  simp only [Category.assoc]

theorem extend_naturality {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') {a b : TwoEnvelope R B}
    (f : a ⟶ b) :
    (extendTwoNatTrans θ).x f ≫ α.app a.as ▷ (extend G).map f =
      (extend F).map f ◁ α.app b.as ≫ (extendTwoNatTrans θ').x f := by
  have h := fun p => extend_naturality_of_mem (TwoNatTrans.projHom p α).app
    (fun a => proj_mem (R := R) p (α.app a)) (TwoNatTrans.projHom p α).naturality f
  have e : ∀ a : B, α.app a = (TwoNatTrans.projHom 0 α).app a + (TwoNatTrans.projHom 1 α).app a :=
    fun a => (proj_add_proj (R := R) (α.app a)).symm
  rw [e, e, add_whiskerRight (R := R), whiskerLeft_add (R := R), Preadditive.comp_add,
    Preadditive.add_comp, h 0, h 1]

/-- **Remark 4.10.** The extension `α̃ : (X̃, x̃) ⇛ (Ỹ, ỹ)` of a supermodification
`α : (X, x) ⇛ (Y, y)`: `α̃_λ = α_λ`. -/
def extendSupermodification {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') :
    extendTwoNatTrans θ ⟶ extendTwoNatTrans θ' where
  app a := α.app a.as
  naturality f := extend_naturality α f

@[simp] theorem extendSupermodification_app {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ')
    (a : TwoEnvelope R B) : (extendSupermodification α).app a = α.app a.as := rfl

variable (F G) in
/-- **Theorem 4.9 / Remark 4.10.** The superfunctor
`ℋom(ℝ, 𝕊) → ℋom(ℝ̃, 𝕊̃)`, `(X, x) ↦ (X̃, x̃)`, `α ↦ α̃`. -/
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
  map_mem hα a := hα a.as

instance : (extendHom F G).Faithful where
  map_injective {θ θ'} α β h := TwoNatTrans.hom_ext fun a => by
    have := congrArg (fun γ : extendTwoNatTrans θ ⟶ extendTwoNatTrans θ' => γ.app ⟨a⟩) h
    exact this

instance : (extendHom F G).Full where
  map_surjective {θ θ'} γ := ⟨⟨fun a => γ.app ⟨a⟩, fun {a b} f => by
      have := γ.naturality ((J R (a ⟶ b)).obj f : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩)
      have h₁ : (extendTwoNatTrans θ).x
          ((J R (a ⟶ b)).obj f : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩) = θ.x f :=
        extendX_J (a := (⟨a⟩ : TwoEnvelope R B)) (b := ⟨b⟩) θ f
      have h₂ : (extendTwoNatTrans θ').x
          ((J R (a ⟶ b)).obj f : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩) = θ'.x f :=
        extendX_J (a := (⟨a⟩ : TwoEnvelope R B)) (b := ⟨b⟩) θ' f
      simp only [extendHom_obj] at this
      rw [h₁, h₂] at this
      exact this⟩,
    TwoNatTrans.hom_ext fun _ => rfl⟩

omit [TwoSupercategory R B] [∀ a b : C, PiSupercategory R (a ⟶ b)] in
theorem eqToHom_mem {F' G' : TwoSuperfunctor R (TwoEnvelope R B) C} {θ θ' : TwoNatTrans F' G'}
    (h : θ = θ') : (eqToIso h).hom ∈ parity (R := R) θ θ' 0 := by
  subst h; exact id_mem _

theorem extendHom_evenlyDense : EvenlyDense R (extendHom F G) := fun ψ =>
  ⟨restrictTwoNatTrans ψ, eqToIso (extendTwoNatTrans_restrictTwoNatTrans ψ),
    eqToHom_mem (extendTwoNatTrans_restrictTwoNatTrans ψ)⟩

variable (F G) in
/-- **Theorem 4.9 / Remark 4.10.** `(X, x) ↦ (X̃, x̃)`, `α ↦ α̃` is a superequivalence
`ℋom(ℝ, 𝕊) → ℋom(ℝ̃, 𝕊̃)`; it is bijective on objects (`extendTwoNatTransEquiv`) and on
morphisms. -/
def extendHomSuperequivalence : Superequivalence R (extendHom F G) :=
  Superequivalence.ofFullyFaithful _ extendHom_evenlyDense

end TwoEnvelope

/-! ## The canonical 2-superfunctor `𝕁` and restriction along it -/

namespace TwoEnvelope

open Envelope

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- The 1-morphism `Π⁰F` of `𝔄_π`. -/
def Jm {a b : B} (f : a ⟶ b) : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩ := Envelope.mk 0 f

/-- The 2-morphism `x_0^0 : Π⁰F ⇒ Π⁰G` of `𝔄_π`. -/
def J2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : Jm (R := R) f ⟶ Jm g := Envelope.ofHom η

omit [TwoSupercategory R B] in
theorem Jm_eq {a b : B} (f : a ⟶ b) : Jm (R := R) f = (J R (a ⟶ b)).obj f := rfl

omit [TwoSupercategory R B] in
theorem J2_eq {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : J2 (R := R) η = (J R (a ⟶ b)).map η := rfl

omit [TwoSupercategory R B] in
theorem J2_whiskerRight {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    J2 (R := R) η ▷ Jm h = J2 (η ▷ h) :=
  hom_ext (TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl)

omit [TwoSupercategory R B] in
theorem J2_whiskerLeft {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    Jm (R := R) f ◁ J2 η = J2 (f ◁ η) :=
  hom_ext (TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl _)

variable (R B) in
/-- The canonical strict 2-superfunctor `𝕁 : 𝔄 → 𝔄_π` (after Lemma 4.5): the identity on
objects, `F ↦ Π⁰F`, `x ↦ x_0^0`, with identity coherence maps. -/
def twoJ : TwoSuperfunctor R B (TwoEnvelope R B) where
  obj a := ⟨a⟩
  map f := Jm f
  map₂ η := J2 η
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  map₂_add _ _ := rfl
  map₂_smul _ _ := rfl
  map₂_mem {a b _ _ _ _} hη := IsSuperfunctor.map_mem (F := J R (a ⟶ b)) hη
  mapComp f g := isoOfIso (Iso.refl (f ≫ g))
  mapId a := isoOfIso (Iso.refl (𝟙 a))
  mapComp_hom_mem f g := by
    rw [mem_parity_iff]
    exact id_mem (f ≫ g)
  mapId_hom_mem a := id_mem (𝟙 a)
  mapComp_naturality_left η g := by
    rw [J2_whiskerRight]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  mapComp_naturality_right f _ _ η := by
    rw [J2_whiskerLeft]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  map₂_associator f g h := by
    apply hom_ext
    rw [toHom_comp, toHom_comp, toHom_comp, toHom_comp,
      TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl,
      TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
    show f ◁ 𝟙 (g ≫ h) ≫ 𝟙 _ ≫ (associator f g h).inv = (associator f g h).inv ≫ 𝟙 (f ≫ g) ▷ h ≫ 𝟙 _
    rw [whiskerLeft_id (R := R), id_whiskerRight (R := R)]
    simp
  map₂_leftUnitor f := by
    apply hom_ext
    rw [toHom_comp, toHom_comp, TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
    show 𝟙 (𝟙 _) ▷ f ≫ 𝟙 _ ≫ (leftUnitor f).hom = (leftUnitor f).hom
    rw [id_whiskerRight (R := R)]
    simp
  map₂_rightUnitor f := by
    apply hom_ext
    rw [toHom_comp, toHom_comp, TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
    show f ◁ 𝟙 (𝟙 _) ≫ 𝟙 _ ≫ (rightUnitor f).hom = (rightUnitor f).hom
    rw [whiskerLeft_id (R := R)]
    simp

variable {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

/-- The restriction `𝕋𝕁 : 𝔄 → 𝔅` of a 2-superfunctor `𝕋 : 𝔄_π → 𝔅`. -/
def restrict (T : TwoSuperfunctor R (TwoEnvelope R B) C) : TwoSuperfunctor R B C where
  obj a := T.obj ⟨a⟩
  map f := T.map (Jm f)
  map₂ η := T.map₂ (J2 η)
  map₂_id f := T.map₂_id (Jm f)
  map₂_comp η θ := T.map₂_comp (J2 η) (J2 θ)
  map₂_add η θ := T.map₂_add (J2 η) (J2 θ)
  map₂_smul r η := T.map₂_smul r (J2 η)
  map₂_mem {a b _ _ _ _} hη := T.map₂_mem (IsSuperfunctor.map_mem (F := J R (a ⟶ b)) hη)
  mapComp f g := T.mapComp (Jm f) (Jm g)
  mapId a := T.mapId ⟨a⟩
  mapComp_hom_mem f g := T.mapComp_hom_mem (Jm f) (Jm g)
  mapId_hom_mem a := T.mapId_hom_mem ⟨a⟩
  mapComp_naturality_left η g := by
    have := T.mapComp_naturality_left (J2 (R := R) η) (Jm g)
    rw [J2_whiskerRight] at this
    exact this
  mapComp_naturality_right f _ _ η := by
    have := T.mapComp_naturality_right (Jm (R := R) f) (J2 η)
    rw [J2_whiskerLeft] at this
    exact this
  map₂_associator f g h := T.map₂_associator (Jm f) (Jm g) (Jm h)
  map₂_leftUnitor f := T.map₂_leftUnitor (Jm f)
  map₂_rightUnitor f := T.map₂_rightUnitor (Jm f)

variable [∀ a b : C, PiSupercategory R (a ⟶ b)]

section XComp

variable {F' G' : TwoSuperfunctor R (TwoEnvelope R B) C} (X : ∀ a, F'.obj a ⟶ G'.obj a)
  (x : ∀ {a b : TwoEnvelope R B} (f : a ⟶ b), F'.map f ≫ X b ⟶ X a ≫ G'.map f)
  (x_mem : ∀ {a b : TwoEnvelope R B} (f : a ⟶ b), x f ∈ parity (R := R) _ _ 0)
  (nat : ∀ {a b : TwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g),
    F'.map₂ η ▷ X b ≫ x g = x f ≫ X a ◁ G'.map₂ η)

/-- The left-hand side of the first coherence diagram of Definition 2.2(iii). -/
def xcompL {a b c : TwoEnvelope R B} (f : a ⟶ b) (g : b ⟶ c) :
    (F'.map f ≫ F'.map g) ≫ X c ⟶ X a ≫ G'.map (f ≫ g) :=
  (F'.mapComp f g).hom ▷ X c ≫ x (f ≫ g)

/-- The right-hand side of the first coherence diagram of Definition 2.2(iii). -/
def xcompR {a b c : TwoEnvelope R B} (f : a ⟶ b) (g : b ⟶ c) :
    (F'.map f ≫ F'.map g) ≫ X c ⟶ X a ≫ G'.map (f ≫ g) :=
  (associator (F'.map f) (F'.map g) (X c)).hom ≫ F'.map f ◁ x g ≫
    (associator (F'.map f) (X b) (G'.map g)).inv ≫ x f ▷ G'.map g ≫
      (associator (X a) (G'.map f) (G'.map g)).hom ≫ X a ◁ (G'.mapComp f g).hom

omit [TwoSupercategory R B] [∀ a b : C, PiSupercategory R (a ⟶ b)] in
include nat in
theorem xcompL_nat₁ {a b c : TwoEnvelope R B} {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) :
    (F'.map₂ u ▷ F'.map g) ▷ X c ≫ xcompL X x f' g = xcompL X x f g ≫ X a ◁ G'.map₂ (u ▷ g) := by
  simp only [xcompL]
  rw [comp_whiskerRight_comp R, F'.mapComp_naturality_left, ← comp_whiskerRight_comp R, nat]
  simp only [Category.assoc]

omit [TwoSupercategory R B] [∀ a b : C, PiSupercategory R (a ⟶ b)] in
include x_mem nat in
theorem xcompR_nat₁ {a b c : TwoEnvelope R B} {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) :
    (F'.map₂ u ▷ F'.map g) ▷ X c ≫ xcompR X x f' g = xcompR X x f g ≫ X a ◁ G'.map₂ (u ▷ g) := by
  simp only [xcompR]
  rw [associator_naturality_left_assoc R,
    reassoc_of% (interchange_even_right R (F'.map₂ u) (x_mem g)),
    associator_inv_naturality_left_assoc R, comp_whiskerRight_comp R, nat,
    ← comp_whiskerRight_comp R, associator_naturality_middle_assoc R,
    ← whiskerLeft_comp (R := R), G'.mapComp_naturality_left, whiskerLeft_comp (R := R)]
  simp only [Category.assoc]

omit [TwoSupercategory R B] [∀ a b : C, PiSupercategory R (a ⟶ b)] in
include nat in
theorem xcompL_nat₂ {a b c : TwoEnvelope R B} (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') :
    (F'.map f ◁ F'.map₂ v) ▷ X c ≫ xcompL X x f g' = xcompL X x f g ≫ X a ◁ G'.map₂ (f ◁ v) := by
  simp only [xcompL]
  rw [comp_whiskerRight_comp R, F'.mapComp_naturality_right, ← comp_whiskerRight_comp R, nat]
  simp only [Category.assoc]

omit [TwoSupercategory R B] [∀ a b : C, PiSupercategory R (a ⟶ b)] in
include x_mem nat in
theorem xcompR_nat₂ {a b c : TwoEnvelope R B} (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') :
    (F'.map f ◁ F'.map₂ v) ▷ X c ≫ xcompR X x f g' = xcompR X x f g ≫ X a ◁ G'.map₂ (f ◁ v) := by
  simp only [xcompR]
  rw [associator_naturality_middle_assoc R, whiskerLeft_comp_comp R, nat,
    ← whiskerLeft_comp_comp R, associator_inv_naturality_right_assoc R,
    ← reassoc_of% (interchange_even_left R (x_mem f) (G'.map₂ v)),
    associator_naturality_right_assoc R, ← whiskerLeft_comp (R := R),
    G'.mapComp_naturality_right, whiskerLeft_comp (R := R)]
  simp only [Category.assoc]

omit [TwoSupercategory R B] [∀ a b : C, PiSupercategory R (a ⟶ b)] in
include x_mem nat in
/-- The first coherence diagram of Definition 2.2(iii) holds for a natural family of even
2-morphisms between 2-superfunctors out of `𝔄_π` as soon as it holds for 1-morphisms `Π⁰F`,
`Π⁰G`. -/
theorem xcomp_of_J
    (h : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), xcompL X x (Jm (R := R) f) (Jm g) =
      xcompR X x (Jm (R := R) f) (Jm g))
    {a b c : TwoEnvelope R B} (f : a ⟶ b) (g : b ⟶ c) : xcompL X x f g = xcompR X x f g := by
  have e₁ : Epi ((F'.map₂ (shiftIso f).hom ▷ F'.map g) ▷ X c) :=
    (inferInstance : Epi (whiskerRightIso (R := R) (whiskerRightIso (R := R)
      (F'.map₂Iso (shiftIso f)) _) _).hom)
  refine eq_of_conj_hom _ e₁ _ (xcompL_nat₁ X x nat (shiftIso f).hom g)
    (xcompR_nat₁ X x x_mem nat (shiftIso f).hom g) ?_
  have e₂ : Epi ((F'.map ((J R _).obj f.obj) ◁ F'.map₂ (shiftIso g).hom) ▷ X c) :=
    (inferInstance : Epi (whiskerRightIso (R := R) (whiskerLeftIso (R := R) _
      (F'.map₂Iso (shiftIso g))) _).hom)
  refine eq_of_conj_hom _ e₂ _ (xcompL_nat₂ X x nat _ (shiftIso g).hom)
    (xcompR_nat₂ X x x_mem nat _ (shiftIso g).hom) ?_
  exact h f.obj g.obj

end XComp

/-! ## Theorem 4.9, even density -/

omit [TwoSupercategory R B] [∀ a b : C, PiSupercategory R (a ⟶ b)] in
variable (R) in
include R in
/-- The coherence of the identity 2-natural transformation, with a 2-morphism `φ` attached. -/
theorem unit_coherence {a b c : C} (f : a ⟶ b) (g : b ⟶ c) {h : a ⟶ c} (φ : f ≫ g ⟶ h) :
    φ ▷ 𝟙 c ≫ (rightUnitor h).hom ≫ (leftUnitor h).inv =
      (associator f g (𝟙 c)).hom ≫ f ◁ ((rightUnitor g).hom ≫ (leftUnitor g).inv) ≫
        (associator f (𝟙 b) g).inv ≫ ((rightUnitor f).hom ≫ (leftUnitor f).inv) ▷ g ≫
          (associator (𝟙 a) f g).hom ≫ 𝟙 a ◁ φ := by
  have tri : (associator f (𝟙 b) g).inv ≫ (rightUnitor f).hom ▷ g = f ◁ (leftUnitor g).hom := by
    rw [← TwoSupercategory.triangle (R := R), Iso.inv_hom_id_assoc]
  rw [rightUnitor_naturality_assoc R, leftUnitor_inv_naturality R, whiskerLeft_comp (R := R),
    comp_whiskerRight (R := R)]
  simp only [Category.assoc]
  rw [reassoc_of% tri, whiskerLeft_inv_hom'_assoc R, ← Category.assoc ((leftUnitor f).inv ▷ g),
    ← leftUnitor_comp_inv R f g, ← Category.assoc (associator f g (𝟙 c)).hom,
    ← rightUnitor_comp R f g]

variable (T : TwoSuperfunctor R (TwoEnvelope R B) C)

variable (T : TwoSuperfunctor R (TwoEnvelope R B) C)

theorem extendRestrict_obj (a : TwoEnvelope R B) : (extend (restrict T)).obj a = T.obj a := rfl

/-- The superfunctor `𝕋 : ℋom_{𝔄_π}(λ, μ) → ℋom_𝔅(𝕋λ, 𝕋μ)`, as a superfunctor out of the
Π-envelope `ℋom_𝔄(λ, μ)_π`. -/
abbrev homFunctor (a b : TwoEnvelope R B) : Envelope R (a.as ⟶ b.as) ⥤ (T.obj a ⟶ T.obj b) :=
  T.mapFunctor a b

instance (a b : TwoEnvelope R B) : (homFunctor T a b).Additive :=
  inferInstanceAs (T.mapFunctor a b).Additive

instance (a b : TwoEnvelope R B) : (homFunctor T a b).Linear R :=
  inferInstanceAs ((T.mapFunctor a b).Linear R)

instance (a b : TwoEnvelope R B) : IsSuperfunctor R (homFunctor T a b) :=
  inferInstanceAs (IsSuperfunctor R (T.mapFunctor a b))

/-- The even 2-isomorphism `(𝕋𝕁)~(ΠᵃF) ≅ 𝕋(ΠᵃF)` of Theorem 4.3 applied to the superfunctor
`𝕋 : ℋom(λ, μ) → ℋom(𝕋λ, 𝕋μ)`. -/
def extendRestrictApp {a b : TwoEnvelope R B} (f : a ⟶ b) :
    (extend (restrict T)).map f ⟶ T.map f :=
  (extendRestrictIso (homFunctor T a b)).hom.app f

theorem extendRestrictApp_mem {a b : TwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictApp T f ∈ parity (R := R) _ _ 0 :=
  extendRestrictIso_hom_mem (homFunctor T a b) f

theorem extendRestrictApp_naturality {a b : TwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    (extend (restrict T)).map₂ η ≫ extendRestrictApp T g = extendRestrictApp T f ≫ T.map₂ η :=
  (extendRestrictIso (homFunctor T a b)).hom.naturality η

theorem extendRestrictApp_J {a b : TwoEnvelope R B} (f : a.as ⟶ b.as) :
    extendRestrictApp T ((J R (a.as ⟶ b.as)).obj f : a ⟶ b) = 𝟙 _ :=
  extendRestrictIso_hom_app_J (H := homFunctor T a b) f

/-- The components `(𝕋𝕁)~F ≫ 1 ⟶ 1 ≫ 𝕋F` of the 2-natural isomorphism `(𝕋𝕁)~ ⇒ 𝕋`. -/
def extendRestrictX {a b : TwoEnvelope R B} (f : a ⟶ b) :
    (extend (restrict T)).map f ≫ 𝟙 (T.obj b) ⟶ 𝟙 (T.obj a) ≫ T.map f :=
  (rightUnitor _).hom ≫ extendRestrictApp T f ≫ (leftUnitor _).inv

theorem extendRestrictX_mem {a b : TwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictX T f ∈ parity (R := R) _ _ 0 := by
  have := comp_mem (rightUnitor_hom_mem (R := R) _)
    (comp_mem (extendRestrictApp_mem T f) (inv_mem _ (leftUnitor_hom_mem (R := R) _)))
  simpa using this

theorem extendRestrictX_naturality {a b : TwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    (extend (restrict T)).map₂ η ▷ 𝟙 (T.obj b) ≫ extendRestrictX T g =
      extendRestrictX T f ≫ 𝟙 (T.obj a) ◁ T.map₂ η := by
  simp only [extendRestrictX]
  rw [rightUnitor_naturality_assoc R, reassoc_of% (extendRestrictApp_naturality T η),
    leftUnitor_inv_naturality R]
  simp only [Category.assoc]

/-- **Theorem 4.9**, even density: every 2-superfunctor `𝕋 : 𝔄_π → 𝔅` is isomorphic to the
extension `(𝕋𝕁)~` of its restriction, by the 2-natural transformation with identity
1-morphisms and 2-morphisms the even isomorphisms of Theorem 4.3. -/
def extendRestrictNatTrans : TwoNatTrans (extend (restrict T)) T where
  X a := 𝟙 (T.obj a)
  x f := extendRestrictX T f
  x_mem f := extendRestrictX_mem T f
  naturality η := extendRestrictX_naturality T η
  x_comp f g := xcomp_of_J (F' := extend (restrict T)) (G' := T) (fun a => 𝟙 (T.obj a)) (fun f => extendRestrictX T f)
    (fun f => extendRestrictX_mem T f) (fun η => extendRestrictX_naturality T η)
    (fun {a b c} f g => by
      have h₁ : (extendComp (restrict T) (Jm (R := R) f) (Jm g)).hom =
          (T.mapComp (Jm f) (Jm g)).hom :=
        extendComp_J (restrict T) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩) f g
      have h₂ : extendRestrictApp T (Jm (R := R) f ≫ Jm g) = 𝟙 _ :=
        extendRestrictApp_J T (a := ⟨a⟩) (b := ⟨c⟩) (f ≫ g)
      have h₃ : extendRestrictApp T (Jm (R := R) f) = 𝟙 _ :=
        extendRestrictApp_J T (a := ⟨a⟩) (b := ⟨b⟩) f
      have h₄ : extendRestrictApp T (Jm (R := R) g) = 𝟙 _ :=
        extendRestrictApp_J T (a := ⟨b⟩) (b := ⟨c⟩) g
      simp only [xcompL, xcompR, extendRestrictX, h₂, h₃, h₄, Category.id_comp]
      erw [h₁]
      exact unit_coherence R _ _ _) f g
  x_id a := by
    have h : extendRestrictApp T (𝟙 a) = 𝟙 _ := extendRestrictApp_J T (𝟙 a.as)
    show _ ≫ _ ≫ _ ≫ (rightUnitor _).hom ≫ extendRestrictApp T (𝟙 a) ≫ (leftUnitor _).inv = _
    rw [h, Category.id_comp, rightUnitor_naturality_assoc R]
    erw [leftUnitor_inv_naturality R]
    rw [unitors_inv_equal R]
    simp only [Iso.hom_inv_id_assoc]
    erw [unitors_inv_equal R (T.obj a), Iso.hom_inv_id_assoc]
    rfl

theorem extendRestrictNatTrans_isStrong : (extendRestrictNatTrans T).IsStrong := fun f => by
  show IsIso ((rightUnitor _).hom ≫ extendRestrictApp T f ≫ (leftUnitor _).inv)
  have : IsIso (extendRestrictApp T f) :=
    inferInstanceAs (IsIso ((extendRestrictIso (homFunctor T _ _)).app f).hom)
  infer_instance

/-- The inverses `𝕋F ≅ (𝕋𝕁)~F` of the components of `extendRestrictApp`. -/
def extendRestrictAppInv {a b : TwoEnvelope R B} (f : a ⟶ b) :
    T.map f ⟶ (extend (restrict T)).map f :=
  (extendRestrictIso (homFunctor T a b)).inv.app f

theorem extendRestrictAppInv_J {a b : TwoEnvelope R B} (f : a.as ⟶ b.as) :
    extendRestrictAppInv T ((J R (a.as ⟶ b.as)).obj f : a ⟶ b) = 𝟙 _ :=
  extendRestrictIso_inv_app_J (H := homFunctor T a b) f

/-- The components `𝕋F ≫ 1 ⟶ 1 ≫ (𝕋𝕁)~F` of the inverse 2-natural isomorphism. -/
def extendRestrictInvX {a b : TwoEnvelope R B} (f : a ⟶ b) :
    T.map f ≫ 𝟙 (T.obj b) ⟶ 𝟙 (T.obj a) ≫ (extend (restrict T)).map f :=
  (rightUnitor _).hom ≫ extendRestrictAppInv T f ≫ (leftUnitor _).inv

theorem extendRestrictInvX_mem {a b : TwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictInvX T f ∈ parity (R := R) _ _ 0 := by
  have := comp_mem (rightUnitor_hom_mem (R := R) _)
    (comp_mem (extendRestrictIso_inv_mem (H := homFunctor T a b) f)
      (inv_mem _ (leftUnitor_hom_mem (R := R) _)))
  simpa using this

theorem extendRestrictInvX_naturality {a b : TwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    T.map₂ η ▷ 𝟙 (T.obj b) ≫ extendRestrictInvX T g =
      extendRestrictInvX T f ≫ 𝟙 (T.obj a) ◁ (extend (restrict T)).map₂ η := by
  simp only [extendRestrictInvX, extendRestrictAppInv]
  rw [rightUnitor_naturality_assoc R]
  erw [reassoc_of% ((extendRestrictIso (homFunctor T a b)).inv.naturality η)]
  erw [leftUnitor_inv_naturality R]
  simp only [Category.assoc]
  rfl

/-- **Theorem 4.9**, even density: the inverse 2-natural transformation `𝕋 ⇒ (𝕋𝕁)~`. -/
def extendRestrictNatTransInv : TwoNatTrans T (extend (restrict T)) where
  X a := 𝟙 (T.obj a)
  x f := extendRestrictInvX T f
  x_mem f := extendRestrictInvX_mem T f
  naturality η := extendRestrictInvX_naturality T η
  x_comp f g := xcomp_of_J (F' := T) (G' := extend (restrict T)) (fun a => 𝟙 (T.obj a))
    (fun f => extendRestrictInvX T f)
    (fun f => extendRestrictInvX_mem T f) (fun η => extendRestrictInvX_naturality T η)
    (fun {a b c} f g => by
      have h₁ : (extendComp (restrict T) (Jm (R := R) f) (Jm g)).hom =
          (T.mapComp (Jm f) (Jm g)).hom :=
        extendComp_J (restrict T) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩) f g
      have h₂ : extendRestrictAppInv T (Jm (R := R) f ≫ Jm g) = 𝟙 _ :=
        extendRestrictAppInv_J T (a := ⟨a⟩) (b := ⟨c⟩) (f ≫ g)
      have h₃ : extendRestrictAppInv T (Jm (R := R) f) = 𝟙 _ :=
        extendRestrictAppInv_J T (a := ⟨a⟩) (b := ⟨b⟩) f
      have h₄ : extendRestrictAppInv T (Jm (R := R) g) = 𝟙 _ :=
        extendRestrictAppInv_J T (a := ⟨b⟩) (b := ⟨c⟩) g
      simp only [xcompL, xcompR, extendRestrictInvX, h₂, h₃, h₄, Category.id_comp]
      erw [h₁]
      exact unit_coherence R _ _ _) f g
  x_id a := by
    have h : extendRestrictAppInv T (𝟙 a) = 𝟙 _ := extendRestrictAppInv_J T (𝟙 a.as)
    show _ ≫ _ ≫ _ ≫ (rightUnitor _).hom ≫ extendRestrictAppInv T (𝟙 a) ≫ (leftUnitor _).inv = _
    rw [h, Category.id_comp]
    erw [rightUnitor_naturality_assoc R]
    erw [leftUnitor_inv_naturality R]
    rw [unitors_inv_equal R]
    simp only [Iso.hom_inv_id_assoc]
    rfl

theorem extendRestrictNatTransInv_isStrong : (extendRestrictNatTransInv T).IsStrong := fun f => by
  show IsIso ((rightUnitor _).hom ≫ extendRestrictAppInv T f ≫ (leftUnitor _).inv)
  have : IsIso (extendRestrictAppInv T f) :=
    inferInstanceAs (IsIso ((extendRestrictIso (homFunctor T _ _)).app f).inv)
  infer_instance

/-- The components of `extendRestrictNatTrans` and `extendRestrictNatTransInv` are mutually
inverse up to the unitors: `x_F ≫ λ ≫ ρ⁻¹ ≫ x'_F = ρ ≫ λ⁻¹`. -/
theorem extendRestrictX_comp_inv {a b : TwoEnvelope R B} (f : a ⟶ b) :
    extendRestrictX T f ≫ (leftUnitor _).hom ≫ (rightUnitor _).inv ≫ extendRestrictInvX T f =
      (rightUnitor _).hom ≫ (leftUnitor _).inv := by
  simp only [extendRestrictX, extendRestrictInvX, extendRestrictApp, extendRestrictAppInv,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [← NatTrans.comp_app_assoc, Iso.hom_inv_id, NatTrans.id_app, Category.id_comp]

end TwoEnvelope

end StringDiagrams

end
