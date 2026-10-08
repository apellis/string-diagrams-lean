import StringDiagrams.Super.QPiTwoSCatDUnit
import StringDiagrams.Super.QAssociatedTwoNat

/-!
# The §6 analogue of Lemma 5.4: `𝕋` is an isomorphism, natural in graded 2-superfunctors

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6: after
Definition 6.14 the paper leaves the analogues of Lemma 5.4 and Theorem 5.5 to the reader. The
analogue of Lemma 5.4 is that `𝔻 : (Q, Π)-2-Cat → (Q, Π)-2-GSCat` and
`𝔼 : (Q, Π)-2-GSCat → (Q, Π)-2-Cat` are mutually inverse equivalences of categories. Here:

* `𝕋_𝔅 : 𝔻(𝔼 𝔅) → 𝔅` (`QAssociated2.T`) is graded (`QAssociated2.T_isGraded`) and an
  isomorphism in `(Q, Π)-2-GSCat`: its inverse is the graded 2-superfunctor `QAssociated2.Tinv`,
  the identity on objects and 1-morphisms and the inverse of `𝕋_𝔅` on 2-morphisms, with identity
  coherence maps (`QAssociated2.T_comp_Tinv`, `QAssociated2.Tinv_comp_T`, `QPiTwoGSCat.TIso`).
* `𝕋` is natural, as an equality of 2-superfunctors `𝔻(𝔼 ℝ) ≫ 𝕋_𝔅' = 𝕋_𝔅 ≫ ℝ`
  (`QAssociated2.mapQ_comp_T`).

With `𝔼 ∘ 𝔻 = I` (`QPiTwoCat.unitNatIso`, `StringDiagrams.Super.QPiTwoSCatDUnit`) this is the
mathematical content of the equivalence `(Q, Π)-2-Cat ≌ (Q, Π)-2-GSCat`. Not yet done: the
natural isomorphism `𝔼 ⋙ 𝔻 ≅ 𝟭` of functors between the bundled categories (and hence the bundled
`Equivalence`); its naturality square is `QAssociated2.mapQ_comp_T`, but identifying the
bundled `𝔻(𝔼 ℝ)` with `QPiTwoFunctor.mapQ` of `𝔼 ℝ` by definitional unfolding is too slow to
elaborate.

`(Q, Π)`-2-functors are those of `StringDiagrams.Super.QPiTwoSCat` (with the compatibility axiom
recorded in the README, as for erratum 4 to Definition 6.12).
-/
noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace QAssociated2

section T

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B] [QPiTwoSupercategory R B]

attribute [local instance] QPiTwoSupercategory.centralShift

/-- `𝕋_𝔅` is a graded 2-superfunctor. -/
theorem T_isGraded : (T R B).IsGraded where
  map₂_mem_degree hx := T_map₂_mem_degree hx
  mapComp_hom_mem_degree _ _ := id_mem_degree _
  mapId_hom_mem_degree _ := id_mem_degree _

theorem T_map₂_injective {a b : QAssociated2 R (GUnderlying2 R B)} {f g : a ⟶ b} {x y : f ⟶ g}
    (h : (T R B).map₂ x = (T R B).map₂ y) : x = y :=
  (T_map₂_bijective f g).1 h

instance (a b : QAssociated2 R (GUnderlying2 R B)) : ((T R B).mapFunctor a b).Faithful where
  map_injective h := T_map₂_injective h

instance (a b : QAssociated2 R (GUnderlying2 R B)) :
    IsGradedSuperfunctor R ((T R B).mapFunctor a b) :=
  T_isGraded.isGradedSuperfunctor a b

/-! ### `𝕋` on whiskerings and coherence maps -/

theorem T_map₂_whiskerLeft {a b c : QAssociated2 R (GUnderlying2 R B)} (f : a ⟶ b) {g h : b ⟶ c}
    (η : g ⟶ h) : (T R B).map₂ (f ◁ η) = (T R B).map f ◁ (T R B).map₂ η :=
  ((Category.id_comp _).symm.trans ((T R B).mapComp_naturality_right f η).symm).trans
    (Category.comp_id _)

theorem T_map₂_whiskerRight {a b c : QAssociated2 R (GUnderlying2 R B)} {f g : a ⟶ b}
    (η : f ⟶ g) (h : b ⟶ c) : (T R B).map₂ (η ▷ h) = (T R B).map₂ η ▷ (T R B).map h :=
  ((Category.id_comp _).symm.trans ((T R B).mapComp_naturality_left η h).symm).trans
    (Category.comp_id _)

theorem T_map₂_associator_inv {a b c d : QAssociated2 R (GUnderlying2 R B)} (f : a ⟶ b)
    (g : b ⟶ c) (h : c ⟶ d) :
    (T R B).map₂ (associator f g h).inv =
      (associator ((T R B).map f) ((T R B).map g) ((T R B).map h)).inv := by
  have := (T R B).map₂_associator f g h
  erw [whiskerLeft_id (R := R), id_whiskerRight (R := R), Category.id_comp, Category.id_comp,
    Category.comp_id] at this
  erw [Category.comp_id] at this
  exact this

theorem T_map₂_leftUnitor_hom {a b : QAssociated2 R (GUnderlying2 R B)} (f : a ⟶ b) :
    (T R B).map₂ (leftUnitor f).hom = (leftUnitor ((T R B).map f)).hom := by
  have := (T R B).map₂_leftUnitor f
  erw [id_whiskerRight (R := R), Category.id_comp, Category.id_comp] at this
  exact this

theorem T_map₂_rightUnitor_hom {a b : QAssociated2 R (GUnderlying2 R B)} (f : a ⟶ b) :
    (T R B).map₂ (rightUnitor f).hom = (rightUnitor ((T R B).map f)).hom := by
  have := (T R B).map₂_rightUnitor f
  erw [whiskerLeft_id (R := R), Category.id_comp, Category.id_comp] at this
  exact this

/-! ### The inverse of `𝕋` -/

/-- An object of `𝔻(𝔼 𝔅)`, from an object of `𝔅`. -/
abbrev mkO (a : B) : QAssociated2 R (GUnderlying2 R B) := ⟨⟨⟨⟨a⟩⟩⟩⟩

/-- A 1-morphism of `𝔻(𝔼 𝔅)`, from a 1-morphism of `𝔅`. -/
abbrev mkM {a b : B} (f : a ⟶ b) : mkO (R := R) a ⟶ mkO b := ⟨⟨⟨⟨f⟩⟩⟩⟩

variable (R B) in
/-- The inverse of `𝕋_𝔅` on 2-morphisms. -/
def tinv₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : mkM (R := R) f ⟶ mkM g :=
  ((T_map₂_bijective (R := R) (B := B) (mkM f) (mkM g)).2 η).choose

theorem T_map₂_tinv₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : (T R B).map₂ (tinv₂ R B η) = η :=
  ((T_map₂_bijective (R := R) (B := B) (mkM f) (mkM g)).2 η).choose_spec

theorem tinv₂_T_map₂ {a b : B} {f g : a ⟶ b} (x : mkM (R := R) f ⟶ mkM g) :
    tinv₂ R B ((T R B).map₂ x) = x :=
  (T_map₂_bijective (R := R) (B := B) (mkM f) (mkM g)).1 (T_map₂_tinv₂ ((T R B).map₂ x))

theorem tinv₂_mem {a b : B} {f g : a ⟶ b} {η : f ⟶ g} {p : ZMod 2}
    (hη : η ∈ parity (R := R) f g p) : tinv₂ R B η ∈ parity (R := R) _ _ p :=
  mem_of_map_mem ((T R B).mapFunctor (mkO a) (mkO b)) (by
    change (T R B).map₂ (tinv₂ R B η) ∈ _
    rw [T_map₂_tinv₂]
    exact hη)

theorem tinv₂_mem_degree {a b : B} {f g : a ⟶ b} {η : f ⟶ g} {n : ℤ}
    (hη : η ∈ degree (R := R) f g n) : tinv₂ R B η ∈ degree (R := R) _ _ n :=
  mem_degree_of_map_mem ((T R B).mapFunctor (mkO a) (mkO b)) (by
    change (T R B).map₂ (tinv₂ R B η) ∈ _
    rw [T_map₂_tinv₂]
    exact hη)

variable (R B) in
/-- **The §6 analogue of Lemma 5.4.** The inverse `𝕋_𝔅⁻¹ : 𝔅 → 𝔻(𝔼 𝔅)` of `𝕋_𝔅`: the identity on
objects and 1-morphisms, the inverse of `𝕋_𝔅` on 2-morphisms, with identity coherence maps. -/
@[simps obj map map₂]
def Tinv : TwoSuperfunctor R B (QAssociated2 R (GUnderlying2 R B)) where
  obj a := ⟨⟨⟨⟨a⟩⟩⟩⟩
  map f := ⟨⟨⟨⟨f⟩⟩⟩⟩
  map₂ η := tinv₂ R B η
  map₂_id f := T_map₂_injective ((T_map₂_tinv₂ _).trans ((T R B).map₂_id (mkM f)).symm)
  map₂_comp η θ := T_map₂_injective ((T_map₂_tinv₂ _).trans (by
    rw [(T R B).map₂_comp, T_map₂_tinv₂, T_map₂_tinv₂]
    rfl))
  map₂_add η θ := T_map₂_injective ((T_map₂_tinv₂ _).trans (by
    rw [(T R B).map₂_add, T_map₂_tinv₂, T_map₂_tinv₂]
    rfl))
  map₂_smul r η := T_map₂_injective ((T_map₂_tinv₂ _).trans (by
    rw [(T R B).map₂_smul, T_map₂_tinv₂]
    rfl))
  map₂_mem hη := tinv₂_mem hη
  mapComp f g := Iso.refl _
  mapId a := Iso.refl _
  mapComp_hom_mem _ _ := id_mem _
  mapId_hom_mem _ := id_mem _
  mapComp_naturality_left {a b c f f'} η g := T_map₂_injective (by
    rw [(T R B).map₂_comp, (T R B).map₂_comp, T_map₂_whiskerRight, T_map₂_tinv₂, T_map₂_tinv₂]
    erw [(T R B).map₂_id, (T R B).map₂_id, Category.comp_id, Category.id_comp]
    rfl)
  mapComp_naturality_right {a b c} f g g' η := T_map₂_injective (by
    rw [(T R B).map₂_comp, (T R B).map₂_comp, T_map₂_whiskerLeft, T_map₂_tinv₂, T_map₂_tinv₂]
    erw [(T R B).map₂_id, (T R B).map₂_id, Category.comp_id, Category.id_comp]
    rfl)
  map₂_associator f g h := T_map₂_injective (by
    simp only [(T R B).map₂_comp, T_map₂_whiskerLeft, T_map₂_whiskerRight, T_map₂_tinv₂,
      T_map₂_associator_inv, Iso.refl_hom, (T R B).map₂_id]
    erw [whiskerLeft_id (R := R), id_whiskerRight (R := R), Category.comp_id, Category.id_comp,
      Category.comp_id, Category.id_comp]
    rfl)
  map₂_leftUnitor f := T_map₂_injective (by
    simp only [(T R B).map₂_comp, T_map₂_whiskerRight, T_map₂_tinv₂, T_map₂_leftUnitor_hom,
      Iso.refl_hom, (T R B).map₂_id]
    erw [id_whiskerRight (R := R), Category.id_comp, Category.id_comp]
    rfl)
  map₂_rightUnitor f := T_map₂_injective (by
    simp only [(T R B).map₂_comp, T_map₂_whiskerLeft, T_map₂_tinv₂, T_map₂_rightUnitor_hom,
      Iso.refl_hom, (T R B).map₂_id]
    erw [whiskerLeft_id (R := R), Category.id_comp, Category.id_comp]
    rfl)

/-- `𝕋_𝔅⁻¹` is a graded 2-superfunctor. -/
theorem Tinv_isGraded : (Tinv R B).IsGraded where
  map₂_mem_degree hx := tinv₂_mem_degree hx
  mapComp_hom_mem_degree _ _ := id_mem_degree _
  mapId_hom_mem_degree _ := id_mem_degree _

/-- `𝕋_𝔅⁻¹ ∘ 𝕋_𝔅 = 𝕀`. -/
theorem T_comp_Tinv : (T R B).comp (Tinv R B) = TwoSuperfunctor.id R _ := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    obtain ⟨⟨⟨⟨a⟩⟩⟩⟩ := a
    obtain ⟨⟨⟨⟨b⟩⟩⟩⟩ := b
    obtain ⟨⟨⟨⟨f⟩⟩⟩⟩ := f
    obtain ⟨⟨⟨⟨g⟩⟩⟩⟩ := g
    exact tinv₂_T_map₂ x
  · funext a b c f g
    obtain ⟨⟨⟨⟨a⟩⟩⟩⟩ := a
    obtain ⟨⟨⟨⟨b⟩⟩⟩⟩ := b
    obtain ⟨⟨⟨⟨c⟩⟩⟩⟩ := c
    obtain ⟨⟨⟨⟨f⟩⟩⟩⟩ := f
    obtain ⟨⟨⟨⟨g⟩⟩⟩⟩ := g
    apply Iso.ext
    exact (Category.id_comp _).trans ((Tinv R B).map₂_id _)
  · funext a
    obtain ⟨⟨⟨⟨a⟩⟩⟩⟩ := a
    apply Iso.ext
    exact (Category.id_comp _).trans ((Tinv R B).map₂_id _)

/-- `𝕋_𝔅 ∘ 𝕋_𝔅⁻¹ = 𝕀`. -/
theorem Tinv_comp_T : (Tinv R B).comp (T R B) = TwoSuperfunctor.id R B := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    exact T_map₂_tinv₂ x
  · funext a b c f g
    apply Iso.ext
    exact (Category.id_comp _).trans ((T R B).map₂_id _)
  · funext a
    apply Iso.ext
    exact (Category.id_comp _).trans ((T R B).map₂_id _)

end T

/-! ### Naturality of `𝕋` -/

section Naturality

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B] [QPiTwoSupercategory R B]
  {B' : Type u₂} [BicategoryStruct.{w₂, v₂} B']
  [∀ a b : B', Preadditive (a ⟶ b)] [∀ a b : B', Linear R (a ⟶ b)]
  [∀ a b : B', Supercategory R (a ⟶ b)] [∀ a b : B', GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B'] [GradedTwoSupercategory R B'] [QPiTwoSupercategory R B']

attribute [local instance] QPiTwoSupercategory.centralShift

/-- **Naturality of `𝕋`**, as an equality of 2-superfunctors: `𝕋_𝔅' ∘ 𝔻(𝔼 ℝ) = ℝ ∘ 𝕋_𝔅`. -/
theorem mapQ_comp_T (G : TwoSuperfunctor R B B') (hG : G.IsGraded) :
    ((G.toQPiTwoFunctor hG).mapQ).comp (T R B') = (T R B).comp G := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    exact T_map₂_mapQ G hG x
  · funext a b c f g
    apply Iso.ext
    exact (Category.id_comp _).trans ((T_map₂_mapQ_mapComp G hG f g).trans
      ((Category.comp_id _).symm.trans (congrArg _ (G.map₂_id _).symm)))
  · funext a
    apply Iso.ext
    exact (Category.id_comp _).trans ((T_map₂_mapQ_mapId G hG a).trans
      ((Category.comp_id _).symm.trans (congrArg _ (G.map₂_id _).symm)))

end Naturality

end QAssociated2

namespace QPiTwoGSCat

variable {R : Type w} [CommRing R]

/-- `𝕋_𝔅` as a morphism of `(Q, Π)-2-GSCat`. -/
def THom (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    QPiTwoGSCat.of R (QAssociated2 R (GUnderlying2 R B)) ⟶ B :=
  ⟨QAssociated2.T R B, QAssociated2.T_isGraded⟩

/-- `𝕋_𝔅⁻¹` as a morphism of `(Q, Π)-2-GSCat`. -/
def TinvHom (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    B ⟶ QPiTwoGSCat.of R (QAssociated2 R (GUnderlying2 R B)) :=
  ⟨QAssociated2.Tinv R B, QAssociated2.Tinv_isGraded⟩

theorem THom_comp_TinvHom (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) : THom B ≫ TinvHom B = 𝟙 _ := by
  apply Subtype.ext
  rw [QPiTwoGSCat.comp_val, QPiTwoGSCat.id_val]
  exact QAssociated2.T_comp_Tinv

theorem TinvHom_comp_THom (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) : TinvHom B ≫ THom B = 𝟙 B := by
  apply Subtype.ext
  rw [QPiTwoGSCat.comp_val, QPiTwoGSCat.id_val]
  exact QAssociated2.Tinv_comp_T

/-- **The §6 analogue of Lemma 5.4.** `𝕋_𝔅 : 𝔻(𝔼 𝔅) ≅ 𝔅` is an isomorphism in
`(Q, Π)-2-GSCat`. -/
def TIso (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    QPiTwoGSCat.of R (QAssociated2 R (GUnderlying2 R B)) ≅ B where
  hom := THom B
  inv := TinvHom B
  hom_inv_id := THom_comp_TinvHom B
  inv_hom_id := TinvHom_comp_THom B

end QPiTwoGSCat

end StringDiagrams
