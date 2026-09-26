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
(4.6) `x̃_{ΠᵃF} = (ζᵃ_{𝕊F} X_λ)⁻¹ ∘ x_F ∘ (X_μ ζᵃ_{ℝF})` (`TwoEnvelope.extendNatTrans`), and
it is the unique 2-natural transformation `ℝ̃ ⇒ 𝕊̃` with `X̃ = X` restricting to `x` along `𝕁`
(`TwoEnvelope.extendNatTrans_unique`).
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

end TwoEnvelope

end StringDiagrams

end
