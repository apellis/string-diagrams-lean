import StringDiagrams.Super.GradedTwoEnvelope
import StringDiagrams.Super.TwoEnvelopeEquivalence

/-!
# The universal property of the `Q`-envelope of a 2-supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Lemma 6.11: the `Q`-part of the extension of 2-superfunctors and 2-natural transformations
along the canonical `𝕁 : 𝔄 → 𝔄_{q,π}`.

The `(Q, Π)`-envelope of Definition 6.10 is built in `StringDiagrams.Super.GradedTwoEnvelope`
as the Π-envelope `TwoEnvelope R (QTwoEnvelope R 𝔄)` of the `Q`-envelope `QTwoEnvelope R 𝔄`
(1-morphisms `Q^m F`, 2-morphisms those of `𝔄`, horizontal composition without signs). This
file is the analogue of `StringDiagrams.Super.TwoEnvelopeUniversal` for the `Q`-envelope; the
extension along the `(Q, Π)`-envelope (Lemma 6.11 itself) is obtained in
`StringDiagrams.Super.GradedTwoEnvelopeUniversal` by composing it with the extension along
the Π-envelope of Lemma 4.7.

Let `𝔄` be a 2-supercategory and `𝔅` a 2-supercategory whose morphism supercategories carry
graded `(Q, Π)`-supercategory structures (for a graded `(Q, Π)`-2-supercategory these are
`Q = q_μ -`, `Π = π_μ -`; see `QPiTwoSupercategory.homQPiLeft` in
`StringDiagrams.Super.GradedTwoEnvelopeUniversal`). Only the functors `Q^m` and the
isomorphisms `σ^m : Q^m ⇒ I` of the morphism supercategories of `𝔅` are used.

* `QTwoEnvelope.twoJ`: the canonical strict 2-superfunctor `𝕁 : 𝔄 → 𝔄_q`, `F ↦ Q⁰F`.
* `QTwoEnvelope.extend`: the extension `ℝ^q : 𝔄_q → 𝔅` of a 2-superfunctor `ℝ : 𝔄 → 𝔅`:
  `ℝ^q(Q^m F) = Q^m(ℝF)`, `ℝ^q(x^n_m) = (σ^n)⁻¹ ∘ ℝx ∘ σ^m`, with coherence maps `i` and
  `c^q_{Q^nG, Q^mF} = (σ^{m+n})⁻¹ ∘ c_{G,F} ∘ (σ^n σ^m)` (`QTwoEnvelope.extendComp`; the
  collapsing of powers of `q` in the proof of Lemma 6.11). All 2-morphisms involved other
  than `ℝx` are even, so no signs occur. `ℝ = ℝ^q 𝕁` (`QTwoEnvelope.twoJ_comp_extend`).
* `QTwoEnvelope.extendTwoNatTrans`: the extension `(X, x^q)` of a 2-natural transformation,
  `x^q_{Q^mF} = (σ^m_{𝕊F} X_λ)⁻¹ ∘ x_F ∘ (X_μ σ^m_{ℝF})`, its uniqueness
  (`QTwoEnvelope.extendTwoNatTrans_unique`), the bijection with 2-natural transformations
  `ℝ ⇒ 𝕊` (`QTwoEnvelope.extendTwoNatTransEquiv`), functoriality
  (`QTwoEnvelope.extendTwoNatTrans_id`, `QTwoEnvelope.extendTwoNatTrans_vcomp`), and the
  superequivalence `ℋom(ℝ, 𝕊) → ℋom(ℝ^q, 𝕊^q)` on supermodifications
  (`QTwoEnvelope.extendHomSuperequivalence`).

The coherence axioms are proved as in `StringDiagrams.Super.TwoEnvelopeUniversal`: both
sides are natural with respect to the even 2-isomorphisms `(1_F)^m_0 : Q⁰F ≅ Q^mF`, so they
agree once they agree on the 1-morphisms `Q⁰F`, where they are the axioms for `ℝ`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace QTwoEnvelope

open QEnvelope

section Struct

variable {R : Type w} {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]

variable {a b c d : QTwoEnvelope R B}

@[simp] theorem comp_shift (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).shift = f.shift + g.shift := rfl

@[simp] theorem comp_obj (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).obj = f.obj ≫ g.obj := rfl

@[simp] theorem id_shift (a : QTwoEnvelope R B) : (𝟙 a : a ⟶ a).shift = 0 := rfl

@[simp] theorem id_obj (a : QTwoEnvelope R B) : (𝟙 a : a ⟶ a).obj = 𝟙 a.as := rfl

theorem toHom_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    toHom (f ◁ η) = f.obj ◁ toHom η := rfl

theorem toHom_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    toHom (η ▷ h) = toHom η ▷ h.obj := rfl

@[simp] theorem toHom_associator_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    toHom (associator f g h).hom = (associator f.obj g.obj h.obj).hom := rfl

@[simp] theorem toHom_associator_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    toHom (associator f g h).inv = (associator f.obj g.obj h.obj).inv := rfl

@[simp] theorem toHom_leftUnitor_hom (f : a ⟶ b) :
    toHom (leftUnitor f).hom = (leftUnitor f.obj).hom := rfl

@[simp] theorem toHom_leftUnitor_inv (f : a ⟶ b) :
    toHom (leftUnitor f).inv = (leftUnitor f.obj).inv := rfl

@[simp] theorem toHom_rightUnitor_hom (f : a ⟶ b) :
    toHom (rightUnitor f).hom = (rightUnitor f.obj).hom := rfl

@[simp] theorem toHom_rightUnitor_inv (f : a ⟶ b) :
    toHom (rightUnitor f).inv = (rightUnitor f.obj).inv := rfl

/-- The 1-morphism `Q⁰F` of `𝔄_q`. -/
def Jm {a b : B} (f : a ⟶ b) : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩ := ⟨0, f⟩

/-- The 1-morphism `Q¹F` of `𝔄_q`. -/
def Qm {a b : B} (f : a ⟶ b) : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩ := ⟨1, f⟩

/-- The 2-morphism `x^0_0 : Q⁰F ⇒ Q⁰G` of `𝔄_q`. -/
def J2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : Jm (R := R) f ⟶ Jm g := QEnvelope.ofHom η

theorem Jm_eq {a b : B} (f : a ⟶ b) : Jm (R := R) f = (J R (a ⟶ b)).obj f := rfl

theorem J2_eq {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : J2 (R := R) η = (J R (a ⟶ b)).map η := rfl

theorem J2_whiskerRight {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    J2 (R := R) η ▷ Jm h = J2 (η ▷ h) := rfl

theorem J2_whiskerLeft {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    Jm (R := R) f ◁ J2 η = J2 (f ◁ η) := rfl

variable [CommRing R] [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

variable (R B) in
/-- The canonical strict 2-superfunctor `𝕁 : 𝔄 → 𝔄_q`: the identity on objects, `F ↦ Q⁰F`,
`x ↦ x^0_0`, with identity coherence maps. -/
def twoJ : TwoSuperfunctor R B (QTwoEnvelope R B) where
  obj a := ⟨a⟩
  map f := Jm f
  map₂ η := J2 η
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  map₂_add _ _ := rfl
  map₂_smul _ _ := rfl
  map₂_mem hη := hη
  mapComp f g := isoOfIso (Iso.refl (f ≫ g))
  mapId a := isoOfIso (Iso.refl (𝟙 a))
  mapComp_hom_mem f g := id_mem (f ≫ g)
  mapId_hom_mem a := id_mem (𝟙 a)
  mapComp_naturality_left η g :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  mapComp_naturality_right f _ _ η :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  map₂_associator f g h := by
    apply hom_ext
    show f ◁ 𝟙 (g ≫ h) ≫ 𝟙 _ ≫ (associator f g h).inv =
      (associator f g h).inv ≫ 𝟙 (f ≫ g) ▷ h ≫ 𝟙 _
    rw [whiskerLeft_id (R := R), id_whiskerRight (R := R)]
    simp
  map₂_leftUnitor f := by
    apply hom_ext
    show 𝟙 (𝟙 _) ▷ f ≫ 𝟙 _ ≫ (leftUnitor f).hom = (leftUnitor f).hom
    rw [id_whiskerRight (R := R)]
    simp
  map₂_rightUnitor f := by
    apply hom_ext
    show f ◁ 𝟙 (𝟙 _) ≫ 𝟙 _ ≫ (rightUnitor f).hom = (rightUnitor f).hom
    rw [whiskerLeft_id (R := R)]
    simp

/-- `𝕁 : 𝔄 → 𝔄_q` is a strict 2-superfunctor. -/
theorem twoJ_isStrict : (twoJ R B).IsStrict where
  map_comp _ _ := rfl
  map_id _ := rfl
  mapComp_eq _ _ := Iso.ext rfl
  mapId_eq _ := Iso.ext rfl

variable {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

/-- The restriction `𝕋𝕁 : 𝔄 → 𝔅` of a 2-superfunctor `𝕋 : 𝔄_q → 𝔅`. -/
def restrict (T : TwoSuperfunctor R (QTwoEnvelope R B) C) : TwoSuperfunctor R B C where
  obj a := T.obj ⟨a⟩
  map f := T.map (Jm f)
  map₂ η := T.map₂ (J2 η)
  map₂_id f := T.map₂_id (Jm f)
  map₂_comp η θ := T.map₂_comp (J2 η) (J2 θ)
  map₂_add η θ := T.map₂_add (J2 η) (J2 θ)
  map₂_smul r η := T.map₂_smul r (J2 η)
  map₂_mem hη := T.map₂_mem hη
  mapComp f g := T.mapComp (Jm f) (Jm g)
  mapId a := T.mapId ⟨a⟩
  mapComp_hom_mem f g := T.mapComp_hom_mem (Jm f) (Jm g)
  mapId_hom_mem a := T.mapId_hom_mem ⟨a⟩
  mapComp_naturality_left η g := T.mapComp_naturality_left (J2 (R := R) η) (Jm g)
  mapComp_naturality_right f _ _ η := T.mapComp_naturality_right (Jm (R := R) f) (J2 η)
  map₂_associator f g h := T.map₂_associator (Jm f) (Jm g) (Jm h)
  map₂_leftUnitor f := T.map₂_leftUnitor (Jm f)
  map₂_rightUnitor f := T.map₂_rightUnitor (Jm f)

/-- The restriction `𝕋𝕁` is the composite of `𝕁` and `𝕋`. -/
theorem restrict_eq_comp (T : TwoSuperfunctor R (QTwoEnvelope R B) C) :
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
    show (T.mapId ⟨a⟩).hom = (T.mapId ⟨a⟩).hom ≫ T.map₂ (𝟙 (𝟙 (⟨a⟩ : QTwoEnvelope R B)))
    rw [T.map₂_id]
    erw [Category.comp_id]

end Struct

/-! ## The extension of 2-superfunctors -/

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

/-- The superfunctor `ℋom_{𝔄_q}(λ, μ) → ℋom_𝔅(ℝλ, ℝμ)` of `ℝ^q`: the extension
`QEnvelope.extend` of `ℝ : ℋom_𝔄(λ, μ) → ℋom_𝔅(ℝλ, ℝμ)`. -/
abbrev extendFunctor (a b : QTwoEnvelope R B) :
    (a ⟶ b) ⥤ (F.obj a.as ⟶ F.obj b.as) :=
  QEnvelope.extend R (F.mapFunctor a.as b.as)

instance (a b : QTwoEnvelope R B) : (extendFunctor F a b).Additive :=
  inferInstanceAs (QEnvelope.extend R (F.mapFunctor a.as b.as)).Additive

instance (a b : QTwoEnvelope R B) : (extendFunctor F a b).Linear R :=
  inferInstanceAs ((QEnvelope.extend R (F.mapFunctor a.as b.as)).Linear R)

variable {a b c d : QTwoEnvelope R B}

/-- `σ^m_{ℝF} : Q^m(ℝF) ≅ ℝF` for the 1-morphism `Q^m F`. -/
abbrev σF (f : a ⟶ b) : (extendFunctor F a b).obj f ≅ F.map f.obj :=
  σPow R f.shift (F.map f.obj)

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem σF_hom_mem (f : a ⟶ b) : (σF F f).hom ∈ parity (R := R) _ _ 0 :=
  σPow_hom_mem f.shift _

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem σF_inv_mem (f : a ⟶ b) : (σF F f).inv ∈ parity (R := R) _ _ 0 :=
  σPow_inv_mem f.shift _

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem extendFunctor_map {f g : a ⟶ b} (η : f ⟶ g) :
    (extendFunctor F a b).map η = (σF F f).hom ≫ F.map₂ (toHom η) ≫ (σF F g).inv := rfl

instance (a b : QTwoEnvelope R B) : IsSuperfunctor R (extendFunctor F a b) where
  map_mem {f g p η} hη := by
    have := comp_mem (comp_mem (σF_hom_mem F f) (F.map₂_mem (f := f.obj) (g := g.obj) hη))
      (σF_inv_mem F g)
    rw [extendFunctor_map]
    simpa using this

/-- The coherence 2-morphism `(σ^{m+n})⁻¹ ∘ c ∘ (σ^n σ^m)` of `ℝ^q`. -/
def extendCompAux (f : a ⟶ b) (g : b ⟶ c) :
    (extendFunctor F a b).obj f ≫ (extendFunctor F b c).obj g ⟶
      (extendFunctor F a c).obj (f ≫ g) :=
  (σF F f).hom ▷ (extendFunctor F b c).obj g ≫ F.map f.obj ◁ (σF F g).hom ≫
    (F.mapComp f.obj g.obj).hom ≫ (σF F (f ≫ g)).inv

/-- The inverse of `extendCompAux`. -/
def extendCompAuxInv (f : a ⟶ b) (g : b ⟶ c) :
    (extendFunctor F a c).obj (f ≫ g) ⟶
      (extendFunctor F a b).obj f ≫ (extendFunctor F b c).obj g :=
  (σF F (f ≫ g)).hom ≫ (F.mapComp f.obj g.obj).inv ≫ F.map f.obj ◁ (σF F g).inv ≫
    (σF F f).inv ▷ (extendFunctor F b c).obj g

omit [TwoSupercategory R B] in
theorem extendCompAux_inv (f : a ⟶ b) (g : b ⟶ c) :
    extendCompAux F f g ≫ extendCompAuxInv F f g = 𝟙 _ := by
  simp only [extendCompAux, extendCompAuxInv, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, TwoEnvelope.whiskerLeft_hom_inv'_assoc R,
    TwoEnvelope.hom_inv_whiskerRight' R]

omit [TwoSupercategory R B] in
theorem extendCompAuxInv_aux (f : a ⟶ b) (g : b ⟶ c) :
    extendCompAuxInv F f g ≫ extendCompAux F f g = 𝟙 _ := by
  simp only [extendCompAux, extendCompAuxInv, Category.assoc,
    TwoEnvelope.inv_hom_whiskerRight'_assoc R, TwoEnvelope.whiskerLeft_inv_hom'_assoc R,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id]

/-- The coherence 2-isomorphism
`c^q_{Q^nG, Q^mF} = (σ^{m+n})⁻¹ ∘ c ∘ (σ^n σ^m) : ℝ^q(Q^m F) ≫ ℝ^q(Q^n G) ≅ ℝ^q(Q^{m+n}(F ≫ G))`
of `ℝ^q` (the collapsing of powers of `q` in the proof of Lemma 6.11). -/
def extendComp (f : a ⟶ b) (g : b ⟶ c) :
    (extendFunctor F a b).obj f ≫ (extendFunctor F b c).obj g ≅
      (extendFunctor F a c).obj (f ≫ g) where
  hom := extendCompAux F f g
  inv := extendCompAuxInv F f g
  hom_inv_id := extendCompAux_inv F f g
  inv_hom_id := extendCompAuxInv_aux F f g

omit [TwoSupercategory R B] in
theorem extendComp_hom (f : a ⟶ b) (g : b ⟶ c) :
    (extendComp F f g).hom = (σF F f).hom ▷ (extendFunctor F b c).obj g ≫
      F.map f.obj ◁ (σF F g).hom ≫ (F.mapComp f.obj g.obj).hom ≫ (σF F (f ≫ g)).inv := rfl

omit [TwoSupercategory R B] in
theorem extendComp_hom_mem (f : a ⟶ b) (g : b ⟶ c) :
    (extendComp F f g).hom ∈ parity (R := R) _ _ 0 := by
  have := comp_mem (whiskerRight_mem ((extendFunctor F b c).obj g) (σF_hom_mem F f))
    (comp_mem (whiskerLeft_mem (F.map f.obj) (σF_hom_mem F g))
      (comp_mem (F.mapComp_hom_mem f.obj g.obj) (σF_inv_mem F (f ≫ g))))
  rw [extendComp_hom]
  simpa using this

omit [TwoSupercategory R B] in
theorem extendComp_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) :
    (extendFunctor F a b).map η ▷ (extendFunctor F b c).obj g ≫ (extendComp F f' g).hom =
      (extendComp F f g).hom ≫ (extendFunctor F a c).map (η ▷ g) := by
  rw [extendComp_hom, extendComp_hom, extendFunctor_map, extendFunctor_map, toHom_whiskerRight]
  simp only [comp_whiskerRight (R := R), Category.assoc,
    TwoEnvelope.inv_hom_whiskerRight'_assoc R, Iso.inv_hom_id_assoc]
  rw [reassoc_of% (TwoEnvelope.interchange_even_right R (F.map₂ (toHom η)) (σF_hom_mem F g)),
    F.mapComp_naturality_left_assoc]

omit [TwoSupercategory R B] in
theorem extendComp_naturality_right (f : a ⟶ b) {g g' : b ⟶ c} (θ : g ⟶ g') :
    (extendFunctor F a b).obj f ◁ (extendFunctor F b c).map θ ≫ (extendComp F f g').hom =
      (extendComp F f g).hom ≫ (extendFunctor F a c).map (f ◁ θ) := by
  rw [extendComp_hom, extendComp_hom, extendFunctor_map, extendFunctor_map, toHom_whiskerLeft,
    ← reassoc_of% (TwoEnvelope.interchange_even_left R (σF_hom_mem F f)
      ((σF F g).hom ≫ F.map₂ (toHom θ) ≫ (σF F g').inv))]
  simp only [whiskerLeft_comp (R := R), Category.assoc,
    TwoEnvelope.whiskerLeft_inv_hom'_assoc R, Iso.inv_hom_id_assoc]
  rw [F.mapComp_naturality_right_assoc]

/-! ### Values on the 1-morphisms `Q⁰F` -/

omit [TwoSupercategory R B] in
/-- On 1-morphisms `Q⁰F`, `Q⁰G`, the coherence map `c^q` is `c`. -/
theorem extendComp_J (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) :
    (extendComp F (a := a) (b := b) (c := c) ((J R _).obj f) ((J R _).obj g)).hom =
      (F.mapComp f g).hom := by
  show 𝟙 (F.map f) ▷ F.map g ≫ F.map f ◁ 𝟙 (F.map g) ≫ (F.mapComp f g).hom ≫ 𝟙 _ = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp, Category.id_comp,
    Category.comp_id]

omit [TwoSupercategory R B] in
theorem extendComp_J_comp_left (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) (h : c.as ⟶ d.as) :
    (extendComp F (a := a) (b := c) (c := d)
      (((J R _).obj f : a ⟶ b) ≫ ((J R _).obj g : b ⟶ c)) ((J R _).obj h)).hom =
      (F.mapComp (f ≫ g) h).hom := by
  show 𝟙 (F.map (f ≫ g)) ▷ F.map h ≫ F.map (f ≫ g) ◁ 𝟙 (F.map h) ≫
    (F.mapComp (f ≫ g) h).hom ≫ 𝟙 _ = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp, Category.id_comp,
    Category.comp_id]

omit [TwoSupercategory R B] in
theorem extendComp_J_comp_right (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) (h : c.as ⟶ d.as) :
    (extendComp F (a := a) (b := b) (c := d) ((J R _).obj f)
      (((J R _).obj g : b ⟶ c) ≫ ((J R _).obj h : c ⟶ d))).hom =
      (F.mapComp f (g ≫ h)).hom := by
  show 𝟙 (F.map f) ▷ F.map (g ≫ h) ≫ F.map f ◁ 𝟙 (F.map (g ≫ h)) ≫
    (F.mapComp f (g ≫ h)).hom ≫ 𝟙 _ = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp, Category.id_comp,
    Category.comp_id]

omit [TwoSupercategory R B] [TwoSupercategory R C] in
/-- On 2-morphisms between 1-morphisms `Q⁰F`, `ℝ^q` is `ℝ`. -/
theorem extendFunctor_map_J {f g : a.as ⟶ b.as}
    (η : ((J R (a.as ⟶ b.as)).obj f : a ⟶ b) ⟶ (J R (a.as ⟶ b.as)).obj g) :
    (extendFunctor F a b).map η = F.map₂ (toHom η) := by
  show 𝟙 _ ≫ F.map₂ _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-! ### The coherence axioms for `ℝ^q` -/

local notation "F̃" => extendFunctor F

/-- The left-hand side of the hexagon of Definition 2.2(ii) for `ℝ^q`. -/
def assocL (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F̃ a b).obj f ≫ ((F̃ b c).obj g ≫ (F̃ c d).obj h) ⟶ (F̃ a d).obj ((f ≫ g) ≫ h) :=
  (F̃ a b).obj f ◁ (extendComp F g h).hom ≫ (extendComp F f (g ≫ h)).hom ≫
    (F̃ a d).map (associator f g h).inv

/-- The right-hand side of the hexagon of Definition 2.2(ii) for `ℝ^q`. -/
def assocR (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F̃ a b).obj f ≫ ((F̃ b c).obj g ≫ (F̃ c d).obj h) ⟶ (F̃ a d).obj ((f ≫ g) ≫ h) :=
  (associator ((F̃ a b).obj f) ((F̃ b c).obj g) ((F̃ c d).obj h)).inv ≫
    (extendComp F f g).hom ▷ (F̃ c d).obj h ≫ (extendComp F (f ≫ g) h).hom

theorem assocL_nat₁ {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    (F̃ a b).map u ▷ ((F̃ b c).obj g ≫ (F̃ c d).obj h) ≫ assocL F f' g h =
      assocL F f g h ≫ (F̃ a d).map ((u ▷ g) ▷ h) := by
  simp only [assocL]
  rw [← Category.assoc, TwoEnvelope.interchange_even_right R _ (extendComp_hom_mem F g h),
    Category.assoc, reassoc_of% (extendComp_naturality_left F u (g ≫ h)), ← Functor.map_comp,
    associator_inv_naturality_left R, Functor.map_comp]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
theorem assocR_nat₁ {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    (F̃ a b).map u ▷ ((F̃ b c).obj g ≫ (F̃ c d).obj h) ≫ assocR F f' g h =
      assocR F f g h ≫ (F̃ a d).map ((u ▷ g) ▷ h) := by
  simp only [assocR]
  rw [associator_inv_naturality_left_assoc R, TwoEnvelope.comp_whiskerRight_comp R,
    extendComp_naturality_left, ← TwoEnvelope.comp_whiskerRight_comp R,
    extendComp_naturality_left]
  simp only [Category.assoc]

theorem assocL_nat₂ (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') (h : c ⟶ d) :
    (F̃ a b).obj f ◁ ((F̃ b c).map v ▷ (F̃ c d).obj h) ≫ assocL F f g' h =
      assocL F f g h ≫ (F̃ a d).map ((f ◁ v) ▷ h) := by
  simp only [assocL]
  rw [TwoEnvelope.whiskerLeft_comp_comp R, extendComp_naturality_left,
    ← TwoEnvelope.whiskerLeft_comp_comp R, reassoc_of% (extendComp_naturality_right F f (v ▷ h)),
    ← Functor.map_comp, associator_inv_naturality_middle R, Functor.map_comp]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
theorem assocR_nat₂ (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') (h : c ⟶ d) :
    (F̃ a b).obj f ◁ ((F̃ b c).map v ▷ (F̃ c d).obj h) ≫ assocR F f g' h =
      assocR F f g h ≫ (F̃ a d).map ((f ◁ v) ▷ h) := by
  simp only [assocR]
  rw [associator_inv_naturality_middle_assoc R, TwoEnvelope.comp_whiskerRight_comp R,
    extendComp_naturality_right, ← TwoEnvelope.comp_whiskerRight_comp R,
    extendComp_naturality_left]
  simp only [Category.assoc]

theorem assocL_nat₃ (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (w : h ⟶ h') :
    (F̃ a b).obj f ◁ (F̃ b c).obj g ◁ (F̃ c d).map w ≫ assocL F f g h' =
      assocL F f g h ≫ (F̃ a d).map ((f ≫ g) ◁ w) := by
  simp only [assocL]
  rw [TwoEnvelope.whiskerLeft_comp_comp R, extendComp_naturality_right,
    ← TwoEnvelope.whiskerLeft_comp_comp R,
    reassoc_of% (extendComp_naturality_right F f (g ◁ w)), ← Functor.map_comp,
    associator_inv_naturality_right R, Functor.map_comp]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
theorem assocR_nat₃ (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (w : h ⟶ h') :
    (F̃ a b).obj f ◁ (F̃ b c).obj g ◁ (F̃ c d).map w ≫ assocR F f g h' =
      assocR F f g h ≫ (F̃ a d).map ((f ≫ g) ◁ w) := by
  simp only [assocR]
  rw [associator_inv_naturality_right_assoc R,
    ← reassoc_of% (TwoEnvelope.interchange_even_left R (extendComp_hom_mem F f g)
      ((F̃ c d).map w)),
    extendComp_naturality_right]
  simp only [Category.assoc]

theorem assocL_eq_assocR (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    assocL F f g h = assocR F f g h := by
  have e₁ : Epi ((F̃ a b).map (shiftIso f).hom ▷ ((F̃ b c).obj g ≫ (F̃ c d).obj h)) :=
    (inferInstance : Epi (whiskerRightIso (R := R) ((F̃ a b).mapIso (shiftIso f)) _).hom)
  refine TwoEnvelope.eq_of_conj_hom _ e₁ _ (assocL_nat₁ F (shiftIso f).hom g h)
    (assocR_nat₁ F (shiftIso f).hom g h) ?_
  have e₂ : Epi ((F̃ a b).obj ((J R _).obj f.obj) ◁
      ((F̃ b c).map (shiftIso g).hom ▷ (F̃ c d).obj h)) :=
    (inferInstance : Epi (whiskerLeftIso (R := R) _ (whiskerRightIso (R := R)
      ((F̃ b c).mapIso (shiftIso g)) ((F̃ c d).obj h))).hom)
  refine TwoEnvelope.eq_of_conj_hom _ e₂ _ (assocL_nat₂ F _ (shiftIso g).hom h)
    (assocR_nat₂ F _ (shiftIso g).hom h) ?_
  have e₃ : Epi ((F̃ a b).obj ((J R _).obj f.obj) ◁ (F̃ b c).obj ((J R _).obj g.obj) ◁
      (F̃ c d).map (shiftIso h).hom) :=
    (inferInstance : Epi (whiskerLeftIso (R := R) _ (whiskerLeftIso (R := R) _
      ((F̃ c d).mapIso (shiftIso h)))).hom)
  refine TwoEnvelope.eq_of_conj_hom _ e₃ _ (assocL_nat₃ F _ _ (shiftIso h).hom)
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
  show 𝟙 (F.map (𝟙 a.as)) ▷ F.map f ≫ F.map (𝟙 a.as) ◁ 𝟙 (F.map f) ≫
    (F.mapComp (𝟙 a.as) f).hom ≫ 𝟙 _ = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp, Category.id_comp,
    Category.comp_id]

omit [TwoSupercategory R B] in
theorem extendComp_J_id (f : a.as ⟶ b.as) :
    (extendComp F ((J R _).obj f : a ⟶ b) (𝟙 b)).hom = (F.mapComp f (𝟙 b.as)).hom := by
  show 𝟙 (F.map f) ▷ F.map (𝟙 b.as) ≫ F.map f ◁ 𝟙 (F.map (𝟙 b.as)) ≫
    (F.mapComp f (𝟙 b.as)).hom ≫ 𝟙 _ = _
  rw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp, Category.id_comp,
    Category.comp_id]

theorem extend_leftUnitor (f : a ⟶ b) :
    (F.mapId a.as).hom ▷ (F̃ a b).obj f ≫ (extendComp F (𝟙 a) f).hom ≫
        (F̃ a b).map (leftUnitor f).hom = (leftUnitor ((F̃ a b).obj f)).hom := by
  have nat : ∀ {f f' : a ⟶ b} (u : f ⟶ f'), 𝟙 _ ◁ (F̃ a b).map u ≫
      ((F.mapId a.as).hom ▷ (F̃ a b).obj f' ≫ (extendComp F (𝟙 a) f').hom ≫
        (F̃ a b).map (leftUnitor f').hom) =
      ((F.mapId a.as).hom ▷ (F̃ a b).obj f ≫ (extendComp F (𝟙 a) f).hom ≫
        (F̃ a b).map (leftUnitor f).hom) ≫ (F̃ a b).map u := by
    intro f f' u
    rw [← reassoc_of% (TwoEnvelope.interchange_even_left R (F.mapId_hom_mem a.as)
      ((F̃ a b).map u))]
    erw [reassoc_of% (extendComp_naturality_right F (𝟙 a) u)]
    rw [← Functor.map_comp, leftUnitor_naturality R, Functor.map_comp]
    simp only [Category.assoc]
  have e₁ : Epi (𝟙 (F.obj a.as) ◁ (F̃ a b).map (shiftIso f).hom) :=
    (inferInstance : Epi (whiskerLeftIso (R := R) _ ((F̃ a b).mapIso (shiftIso f))).hom)
  refine TwoEnvelope.eq_of_conj_hom _ e₁ _ (nat (shiftIso f).hom) (leftUnitor_naturality R _) ?_
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
    rw [reassoc_of% (TwoEnvelope.interchange_even_right R ((F̃ a b).map u)
      (F.mapId_hom_mem b.as))]
    erw [reassoc_of% (extendComp_naturality_left F u (𝟙 b))]
    rw [← Functor.map_comp, rightUnitor_naturality R, Functor.map_comp]
    simp only [Category.assoc]
  have e₁ : Epi ((F̃ a b).map (shiftIso f).hom ▷ 𝟙 (F.obj b.as)) :=
    (inferInstance : Epi (whiskerRightIso (R := R) ((F̃ a b).mapIso (shiftIso f)) _).hom)
  refine TwoEnvelope.eq_of_conj_hom _ e₁ _ (nat (shiftIso f).hom) (rightUnitor_naturality R _) ?_
  rw [extendComp_J_id]
  have e : (F̃ a b).map (rightUnitor ((J R _).obj f.obj : a ⟶ b)).hom =
      F.map₂ (rightUnitor f.obj).hom := by
    show 𝟙 _ ≫ F.map₂ _ ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]; rfl
  rw [e]
  exact F.map₂_rightUnitor f.obj

/-- The extension `ℝ^q : 𝔄_q → 𝔅` of a 2-superfunctor `ℝ : 𝔄 → 𝔅` to the `Q`-envelope:
`ℝ^q λ = ℝλ`, `ℝ^q(Q^mF) = Q^m(ℝF)`, `ℝ^q(x^n_m) = (σ^n)⁻¹ ∘ ℝx ∘ σ^m`, coherence maps
`c^q` (`extendComp`) and `i`. -/
def extend : TwoSuperfunctor R (QTwoEnvelope R B) C where
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

@[simp] theorem extend_obj (a : QTwoEnvelope R B) : (extend F).obj a = F.obj a.as := rfl

theorem extend_map (f : a ⟶ b) : (extend F).map f = (F̃ a b).obj f := rfl

theorem extend_map₂ {f g : a ⟶ b} (η : f ⟶ g) : (extend F).map₂ η = (F̃ a b).map η := rfl

/-- `ℝ = ℝ^q 𝕁` on 1-morphisms. -/
theorem extend_map_J (f : a.as ⟶ b.as) :
    (extend F).map ((J R _).obj f : a ⟶ b) = F.map f := rfl

/-- `ℝ = ℝ^q 𝕁` on 2-morphisms. -/
theorem extend_map₂_J {f g : a.as ⟶ b.as} (η : f ⟶ g) :
    (extend F).map₂ ((J R (a.as ⟶ b.as)).map η : ((J R _).obj f : a ⟶ b) ⟶ (J R _).obj g) =
      F.map₂ η :=
  extendFunctor_map_J F _

/-- `ℝ = ℝ^q 𝕁` on the coherence maps `i`. -/
theorem extend_mapId (a : QTwoEnvelope R B) : (extend F).mapId a = F.mapId a.as := rfl

/-- `ℝ = ℝ^q 𝕁` as 2-superfunctors. -/
theorem twoJ_comp_extend : (twoJ R B).comp (extend F) = F := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g η
    show 𝟙 _ ≫ F.map₂ η ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
  · funext a b c f g
    apply Iso.ext
    show (extendComp F (Jm (R := R) f) (Jm g)).hom ≫
      (extend F).map₂ (𝟙 (Jm (R := R) f ≫ Jm g)) = _
    rw [(extend F).map₂_id]
    erw [Category.comp_id]
    exact extendComp_J F (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩) f g
  · funext a
    apply Iso.ext
    show (F.mapId a).hom ≫ (extend F).map₂ (𝟙 (𝟙 (⟨a⟩ : QTwoEnvelope R B))) = _
    rw [(extend F).map₂_id]
    erw [Category.comp_id]

/-- `restrict (extend ℝ) = ℝ`. -/
theorem restrict_extend : restrict (extend F) = F := by
  rw [restrict_eq_comp, twoJ_comp_extend]

end QTwoEnvelope

/-! ## The extension of 2-natural transformations -/

namespace QTwoEnvelope

open QEnvelope QPiSupercategory

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R C] [∀ a b : C, QPiSupercategory R (a ⟶ b)]
  {F G : TwoSuperfunctor R B C}

local notation "F̃" => extendFunctor F
local notation "G̃" => extendFunctor G

variable {a b c : QTwoEnvelope R B}

/-- The 2-morphisms `x^q_{Q^mF} = (σ^m_{𝕊F} X_λ)⁻¹ ∘ x_F ∘ (X_μ σ^m_{ℝF})`, in the diagrammatic
order `σ^m ▷ X_μ ≫ x_F ≫ X_λ ◁ (σ^m)⁻¹`. -/
def extendX (θ : TwoNatTrans F G) (f : a ⟶ b) :
    (F̃ a b).obj f ≫ θ.X b.as ⟶ θ.X a.as ≫ (G̃ a b).obj f :=
  (σF F f).hom ▷ θ.X b.as ≫ θ.x f.obj ≫ θ.X a.as ◁ (σF G f).inv

omit [TwoSupercategory R B] in
theorem extendX_mem (θ : TwoNatTrans F G) (f : a ⟶ b) :
    extendX θ f ∈ parity (R := R) _ _ 0 := by
  have := comp_mem (whiskerRight_mem (θ.X b.as) (σF_hom_mem F f))
    (comp_mem (θ.x_mem f.obj) (whiskerLeft_mem (θ.X a.as) (σF_inv_mem G f)))
  simpa using this

omit [TwoSupercategory R B] in
theorem extendX_naturality (θ : TwoNatTrans F G) {f g : a ⟶ b} (η : f ⟶ g) :
    (F̃ a b).map η ▷ θ.X b.as ≫ extendX θ g = extendX θ f ≫ θ.X a.as ◁ (G̃ a b).map η := by
  simp only [extendX, extendFunctor_map, comp_whiskerRight (R := R), whiskerLeft_comp (R := R),
    Category.assoc, TwoEnvelope.inv_hom_whiskerRight'_assoc R,
    TwoEnvelope.whiskerLeft_inv_hom'_assoc R]
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

/-- The left-hand side of the first coherence diagram of Definition 2.2(iii) for
`(X, x^q)`. -/
def compL (f : a ⟶ b) (g : b ⟶ c) :
    ((F̃ a b).obj f ≫ (F̃ b c).obj g) ≫ θ.X c.as ⟶ θ.X a.as ≫ (G̃ a c).obj (f ≫ g) :=
  (extendComp F f g).hom ▷ θ.X c.as ≫ extendX θ (f ≫ g)

/-- The right-hand side of the first coherence diagram of Definition 2.2(iii) for
`(X, x^q)`. -/
def compR (f : a ⟶ b) (g : b ⟶ c) :
    ((F̃ a b).obj f ≫ (F̃ b c).obj g) ≫ θ.X c.as ⟶ θ.X a.as ≫ (G̃ a c).obj (f ≫ g) :=
  (associator ((F̃ a b).obj f) ((F̃ b c).obj g) (θ.X c.as)).hom ≫
    (F̃ a b).obj f ◁ extendX θ g ≫ (associator ((F̃ a b).obj f) (θ.X b.as) ((G̃ b c).obj g)).inv ≫
      extendX θ f ▷ (G̃ b c).obj g ≫
        (associator (θ.X a.as) ((G̃ a b).obj f) ((G̃ b c).obj g)).hom ≫
          θ.X a.as ◁ (extendComp G f g).hom

omit [TwoSupercategory R B] in
theorem compL_nat₁ {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) :
    ((F̃ a b).map u ▷ (F̃ b c).obj g) ▷ θ.X c.as ≫ compL θ f' g =
      compL θ f g ≫ θ.X a.as ◁ (G̃ a c).map (u ▷ g) := by
  simp only [compL]
  rw [TwoEnvelope.comp_whiskerRight_comp R, extendComp_naturality_left,
    ← TwoEnvelope.comp_whiskerRight_comp R, extendX_naturality]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
theorem compR_nat₁ {f f' : a ⟶ b} (u : f ⟶ f') (g : b ⟶ c) :
    ((F̃ a b).map u ▷ (F̃ b c).obj g) ▷ θ.X c.as ≫ compR θ f' g =
      compR θ f g ≫ θ.X a.as ◁ (G̃ a c).map (u ▷ g) := by
  simp only [compR]
  rw [associator_naturality_left_assoc R,
    reassoc_of% (TwoEnvelope.interchange_even_right R ((F̃ a b).map u) (extendX_mem θ g)),
    associator_inv_naturality_left_assoc R, TwoEnvelope.comp_whiskerRight_comp R,
    extendX_naturality, ← TwoEnvelope.comp_whiskerRight_comp R,
    associator_naturality_middle_assoc R, ← whiskerLeft_comp (R := R),
    extendComp_naturality_left, whiskerLeft_comp (R := R)]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
theorem compL_nat₂ (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') :
    ((F̃ a b).obj f ◁ (F̃ b c).map v) ▷ θ.X c.as ≫ compL θ f g' =
      compL θ f g ≫ θ.X a.as ◁ (G̃ a c).map (f ◁ v) := by
  simp only [compL]
  rw [TwoEnvelope.comp_whiskerRight_comp R, extendComp_naturality_right,
    ← TwoEnvelope.comp_whiskerRight_comp R, extendX_naturality]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
theorem compR_nat₂ (f : a ⟶ b) {g g' : b ⟶ c} (v : g ⟶ g') :
    ((F̃ a b).obj f ◁ (F̃ b c).map v) ▷ θ.X c.as ≫ compR θ f g' =
      compR θ f g ≫ θ.X a.as ◁ (G̃ a c).map (f ◁ v) := by
  simp only [compR]
  rw [associator_naturality_middle_assoc R, TwoEnvelope.whiskerLeft_comp_comp R,
    extendX_naturality, ← TwoEnvelope.whiskerLeft_comp_comp R,
    associator_inv_naturality_right_assoc R,
    ← reassoc_of% (TwoEnvelope.interchange_even_left R (extendX_mem θ f) ((G̃ b c).map v)),
    associator_naturality_right_assoc R, ← whiskerLeft_comp (R := R),
    extendComp_naturality_right, whiskerLeft_comp (R := R)]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
theorem compL_eq_compR (f : a ⟶ b) (g : b ⟶ c) : compL θ f g = compR θ f g := by
  have e₁ : Epi (((F̃ a b).map (shiftIso f).hom ▷ (F̃ b c).obj g) ▷ θ.X c.as) :=
    (inferInstance : Epi (whiskerRightIso (R := R) (whiskerRightIso (R := R)
      ((F̃ a b).mapIso (shiftIso f)) _) _).hom)
  refine TwoEnvelope.eq_of_conj_hom _ e₁ _ (compL_nat₁ θ (shiftIso f).hom g)
    (compR_nat₁ θ (shiftIso f).hom g) ?_
  have e₂ : Epi (((F̃ a b).obj ((J R _).obj f.obj) ◁ (F̃ b c).map (shiftIso g).hom) ▷
      θ.X c.as) :=
    (inferInstance : Epi (whiskerRightIso (R := R) (whiskerLeftIso (R := R) _
      ((F̃ b c).mapIso (shiftIso g))) _).hom)
  refine TwoEnvelope.eq_of_conj_hom _ e₂ _ (compL_nat₂ θ _ (shiftIso g).hom)
    (compR_nat₂ θ _ (shiftIso g).hom) ?_
  simp only [compL, compR]
  rw [extendComp_J, extendComp_J, extendX_J, extendX_J, extendX_J_comp]
  exact θ.x_comp f.obj g.obj

end Comp

/-- The extension `(X, x^q) : ℝ^q ⇒ 𝕊^q` of a 2-natural transformation `(X, x) : ℝ ⇒ 𝕊`. -/
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

@[simp] theorem extendTwoNatTrans_X (θ : TwoNatTrans F G) (a : QTwoEnvelope R B) :
    (extendTwoNatTrans θ).X a = θ.X a.as := rfl

theorem extendTwoNatTrans_x (θ : TwoNatTrans F G) (f : a ⟶ b) :
    (extendTwoNatTrans θ).x f = extendX θ f := rfl

/-- `x = x^q 𝕁`. -/
theorem extendTwoNatTrans_x_J (θ : TwoNatTrans F G) (f : a.as ⟶ b.as) :
    (extendTwoNatTrans θ).x ((J R _).obj f : a ⟶ b) = θ.x f :=
  extendX_J θ f

/-- The restriction `(Y, y𝕁) : ℝ ⇒ 𝕊` of a 2-natural transformation `(Y, y) : ℝ^q ⇒ 𝕊^q`. -/
def restrictTwoNatTrans (ψ : TwoNatTrans (extend F) (extend G)) : TwoNatTrans F G where
  X a := ψ.X ⟨a⟩
  x {a b} f := ψ.x ((J R (a ⟶ b)).obj f : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩)
  x_mem {a b} f := ψ.x_mem ((J R (a ⟶ b)).obj f : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩)
  naturality {a b f g} η := by
    have := ψ.naturality ((J R (a ⟶ b)).map η :
      ((J R (a ⟶ b)).obj f : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩) ⟶ _)
    rwa [extend_map₂_J, extend_map₂_J] at this
  x_comp {a b c} f g := by
    have := ψ.x_comp ((J R (a ⟶ b)).obj f : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩)
      ((J R (b ⟶ c)).obj g : (⟨b⟩ : QTwoEnvelope R B) ⟶ ⟨c⟩)
    erw [extendComp_J, extendComp_J] at this
    exact this
  x_id a := ψ.x_id ⟨a⟩

@[simp] theorem restrictTwoNatTrans_X (ψ : TwoNatTrans (extend F) (extend G)) (a : B) :
    (restrictTwoNatTrans ψ).X a = ψ.X ⟨a⟩ := rfl

theorem restrictTwoNatTrans_x (ψ : TwoNatTrans (extend F) (extend G)) {a b : B} (f : a ⟶ b) :
    (restrictTwoNatTrans ψ).x f =
      ψ.x ((J R (a ⟶ b)).obj f : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩) := rfl

/-- `(X, x^q)` restricts to `(X, x)`. -/
theorem restrictTwoNatTrans_extendTwoNatTrans (θ : TwoNatTrans F G) :
    restrictTwoNatTrans (extendTwoNatTrans θ) = θ :=
  TwoEnvelope.twoNatTrans_ext rfl fun {a b} f =>
    heq_of_eq (extendX_J (a := (⟨a⟩ : QTwoEnvelope R B)) (b := ⟨b⟩) θ f)

/-- A 2-natural transformation `ℝ^q ⇒ 𝕊^q` is the extension of its restriction. -/
theorem extendTwoNatTrans_restrictTwoNatTrans (ψ : TwoNatTrans (extend F) (extend G)) :
    extendTwoNatTrans (restrictTwoNatTrans ψ) = ψ := by
  refine TwoEnvelope.twoNatTrans_ext rfl fun {a b} f => heq_of_eq ?_
  have h := ψ.naturality (shiftIso f).inv
  have e₁ : (extend F).map₂ (shiftIso f).inv = (σF F f).hom := by
    show (σF F f).hom ≫ F.map₂ (𝟙 f.obj) ≫ 𝟙 _ = _
    rw [F.map₂_id, Category.comp_id, Category.comp_id]
  have e₂ : (extend G).map₂ (shiftIso f).inv = (σF G f).hom := by
    show (σF G f).hom ≫ G.map₂ (𝟙 f.obj) ≫ 𝟙 _ = _
    rw [G.map₂_id, Category.comp_id, Category.comp_id]
  rw [e₁, e₂] at h
  show (σF F f).hom ▷ ψ.X b ≫ ψ.x ((J R _).obj f.obj) ≫ ψ.X a ◁ (σF G f).inv = ψ.x f
  rw [reassoc_of% h, TwoEnvelope.whiskerLeft_hom_inv' R, Category.comp_id]

/-- **Uniqueness.** `(X, x^q)` is the unique 2-natural transformation `ℝ^q ⇒ 𝕊^q` with
1-morphisms `X_λ` and `x = x^q 𝕁`. -/
theorem extendTwoNatTrans_unique (θ : TwoNatTrans F G) (ψ : TwoNatTrans (extend F) (extend G))
    (h : restrictTwoNatTrans ψ = θ) : ψ = extendTwoNatTrans θ := by
  rw [← h, extendTwoNatTrans_restrictTwoNatTrans]

/-- `(X, x) ↦ (X, x^q)` is a bijection from 2-natural transformations `ℝ ⇒ 𝕊` to 2-natural
transformations `ℝ^q ⇒ 𝕊^q`, with inverse the restriction along `𝕁`. -/
def extendTwoNatTransEquiv : TwoNatTrans F G ≃ TwoNatTrans (extend F) (extend G) where
  toFun := extendTwoNatTrans
  invFun := restrictTwoNatTrans
  left_inv := restrictTwoNatTrans_extendTwoNatTrans
  right_inv := extendTwoNatTrans_restrictTwoNatTrans

/-! ### Functoriality -/

/-- `1^q = 1`. -/
theorem extendTwoNatTrans_id :
    extendTwoNatTrans (TwoNatTrans.id F) = TwoNatTrans.id (extend F) := by
  rw [← extendTwoNatTrans_restrictTwoNatTrans (TwoNatTrans.id (extend F))]
  congr 1

/-- `(X', x') ∘ (X, x)` extends to `(X', x'^q) ∘ (X, x^q)`. -/
theorem extendTwoNatTrans_vcomp {H : TwoSuperfunctor R B C} (θ : TwoNatTrans F G)
    (θ' : TwoNatTrans G H) :
    extendTwoNatTrans (TwoNatTrans.vcomp θ θ') =
      TwoNatTrans.vcomp (extendTwoNatTrans θ) (extendTwoNatTrans θ') := by
  rw [← extendTwoNatTrans_restrictTwoNatTrans
    (TwoNatTrans.vcomp (extendTwoNatTrans θ) (extendTwoNatTrans θ'))]
  congr 1
  refine TwoEnvelope.twoNatTrans_ext rfl fun {a b} f => heq_of_eq ?_
  rw [restrictTwoNatTrans_x, TwoNatTrans.vcomp_x, TwoNatTrans.vcomp_x]
  have h₁ : (extendTwoNatTrans θ).x
      ((J R (a ⟶ b)).obj f : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩) = θ.x f :=
    extendX_J (a := (⟨a⟩ : QTwoEnvelope R B)) (b := ⟨b⟩) θ f
  have h₂ : (extendTwoNatTrans θ').x
      ((J R (a ⟶ b)).obj f : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩) = θ'.x f :=
    extendX_J (a := (⟨a⟩ : QTwoEnvelope R B)) (b := ⟨b⟩) θ' f
  rw [h₁, h₂]
  rfl

/-! ### Supermodifications -/

theorem extend_naturality {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') (f : a ⟶ b) :
    (extendTwoNatTrans θ).x f ≫ α.app a.as ▷ (extend G).map f =
      (extend F).map f ◁ α.app b.as ≫ (extendTwoNatTrans θ').x f := by
  simp only [extendTwoNatTrans_x, extendX, extend_map, Category.assoc]
  rw [← TwoEnvelope.interchange_even_right R (α.app a.as) (σF_inv_mem G f),
    reassoc_of% (α.naturality f.obj), ← Category.assoc ((σF F f).hom ▷ _),
    TwoEnvelope.interchange_even_left R (σF_hom_mem F f) (α.app b.as)]
  simp only [Category.assoc]

/-- The extension `α^q : (X, x^q) ⇛ (Y, y^q)` of a supermodification `α : (X, x) ⇛ (Y, y)`:
`α^q_λ = α_λ`. -/
def extendSupermodification {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') :
    extendTwoNatTrans θ ⟶ extendTwoNatTrans θ' where
  app a := α.app a.as
  naturality f := extend_naturality α f

@[simp] theorem extendSupermodification_app {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ')
    (a : QTwoEnvelope R B) : (extendSupermodification α).app a = α.app a.as := rfl

variable (F G) in
/-- The superfunctor `ℋom(ℝ, 𝕊) → ℋom(ℝ^q, 𝕊^q)`, `(X, x) ↦ (X, x^q)`, `α ↦ α^q`. -/
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
      have := γ.naturality ((J R (a ⟶ b)).obj f : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩)
      have h₁ : (extendTwoNatTrans θ).x
          ((J R (a ⟶ b)).obj f : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩) = θ.x f :=
        extendX_J (a := (⟨a⟩ : QTwoEnvelope R B)) (b := ⟨b⟩) θ f
      have h₂ : (extendTwoNatTrans θ').x
          ((J R (a ⟶ b)).obj f : (⟨a⟩ : QTwoEnvelope R B) ⟶ ⟨b⟩) = θ'.x f :=
        extendX_J (a := (⟨a⟩ : QTwoEnvelope R B)) (b := ⟨b⟩) θ' f
      simp only [extendHom_obj] at this
      rw [h₁, h₂] at this
      exact this⟩,
    TwoNatTrans.hom_ext fun _ => rfl⟩

omit [TwoSupercategory R B] [∀ a b : C, QPiSupercategory R (a ⟶ b)]
  [∀ a b : C, GradedSupercategory R (a ⟶ b)] in
theorem eqToHom_mem {F' G' : TwoSuperfunctor R (QTwoEnvelope R B) C} {θ θ' : TwoNatTrans F' G'}
    (h : θ = θ') : (eqToIso h).hom ∈ parity (R := R) θ θ' 0 := by
  subst h; exact id_mem _

theorem extendHom_evenlyDense : EvenlyDense R (extendHom F G) := fun ψ =>
  ⟨restrictTwoNatTrans ψ, eqToIso (extendTwoNatTrans_restrictTwoNatTrans ψ),
    eqToHom_mem (extendTwoNatTrans_restrictTwoNatTrans ψ)⟩

variable (F G) in
/-- `(X, x) ↦ (X, x^q)`, `α ↦ α^q` is a superequivalence `ℋom(ℝ, 𝕊) → ℋom(ℝ^q, 𝕊^q)`; it is
bijective on objects (`extendTwoNatTransEquiv`) and on morphisms. -/
def extendHomSuperequivalence : Superequivalence R (extendHom F G) :=
  Superequivalence.ofFullyFaithful _ extendHom_evenlyDense

end QTwoEnvelope

end StringDiagrams

end
