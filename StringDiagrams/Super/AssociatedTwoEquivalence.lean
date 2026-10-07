import StringDiagrams.Super.QPiTwoSCatD

/-!
# Lemma 5.4 as an equivalence of categories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Lemma 5.4:
the functors `D₂ : Π-2-Cat → Π-2-SCat` and `E₂ : Π-2-SCat → Π-2-Cat` are mutually inverse
equivalences of categories.

* `𝕋_𝔄 : D₂(E₂ 𝔄) → 𝔄` (`Associated2.T`) is an isomorphism in `Π-2-SCat`: its inverse is the
  2-superfunctor `Associated2.Tinv`, the identity on objects and 1-morphisms,
  `h ↦ (h₀, ζ_μ G⁻¹ ∘ h₁)` on 2-morphisms, with identity coherence maps
  (`Associated2.T_comp_Tinv`, `Associated2.Tinv_comp_T`, `Associated2.TIso`).
* `𝕋` is natural, as an equality of 2-superfunctors `D₂(E₂ ℝ) ≫ 𝕋_𝔄' = 𝕋_𝔄 ≫ ℝ`
  (`Associated2.mapTwo_comp_T`), hence a natural isomorphism `E₂ ⋙ D₂ ≅ 𝟭`
  (`PiTwoSCat.counitNatIso`).
* With `E₂ ∘ D₂ = I` (`PiTwoCat.unitNatIso`), this gives the equivalence of categories
  `Π-2-Cat ≌ Π-2-SCat` (`PiTwoCat.equivalence`).

The paper's `𝕋` is the corrected one of the errata to (5.5) (see the README); the statement of
Lemma 5.4 is as printed.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace Associated2

section T

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A] [PiTwoSupercategory R A]

/-! ### `𝕋` on whiskerings and coherence maps -/

theorem T_map₂_whiskerLeft {a b c : Associated2 R (Underlying2 R A)} (f : a ⟶ b) {g h : b ⟶ c}
    (η : g ⟶ h) : (T R A).map₂ (f ◁ η) = (T R A).map f ◁ (T R A).map₂ η :=
  ((Category.id_comp _).symm.trans ((T R A).mapComp_naturality_right f η).symm).trans
    (Category.comp_id _)

theorem T_map₂_whiskerRight {a b c : Associated2 R (Underlying2 R A)} {f g : a ⟶ b} (η : f ⟶ g)
    (h : b ⟶ c) : (T R A).map₂ (η ▷ h) = (T R A).map₂ η ▷ (T R A).map h :=
  ((Category.id_comp _).symm.trans ((T R A).mapComp_naturality_left η h).symm).trans
    (Category.comp_id _)

theorem T_map₂_associator_inv {a b c d : Associated2 R (Underlying2 R A)} (f : a ⟶ b)
    (g : b ⟶ c) (h : c ⟶ d) :
    (T R A).map₂ (associator f g h).inv =
      (associator ((T R A).map f) ((T R A).map g) ((T R A).map h)).inv := by
  have := (T R A).map₂_associator f g h
  erw [whiskerLeft_id (R := R), id_whiskerRight (R := R), Category.id_comp, Category.id_comp,
    Category.comp_id] at this
  erw [Category.comp_id] at this
  exact this

theorem T_map₂_associator_hom {a b c d : Associated2 R (Underlying2 R A)} (f : a ⟶ b)
    (g : b ⟶ c) (h : c ⟶ d) :
    (T R A).map₂ (associator f g h).hom =
      (associator ((T R A).map f) ((T R A).map g) ((T R A).map h)).hom := by
  have e : (T R A).map₂ (associator f g h).hom ≫ (T R A).map₂ (associator f g h).inv = 𝟙 _ := by
    rw [← (T R A).map₂_comp, Iso.hom_inv_id, (T R A).map₂_id]
  rw [T_map₂_associator_inv] at e
  exact (Iso.comp_inv_eq_id _).1 e

theorem T_map₂_leftUnitor_hom {a b : Associated2 R (Underlying2 R A)} (f : a ⟶ b) :
    (T R A).map₂ (leftUnitor f).hom = (leftUnitor ((T R A).map f)).hom := by
  have := (T R A).map₂_leftUnitor f
  erw [id_whiskerRight (R := R), Category.id_comp, Category.id_comp] at this
  exact this

theorem T_map₂_rightUnitor_hom {a b : Associated2 R (Underlying2 R A)} (f : a ⟶ b) :
    (T R A).map₂ (rightUnitor f).hom = (rightUnitor ((T R A).map f)).hom := by
  have := (T R A).map₂_rightUnitor f
  erw [whiskerLeft_id (R := R), Category.id_comp, Category.id_comp] at this
  exact this

/-! ### The inverse of `𝕋` -/

theorem Tinv₂_mem {a b : Associated2 R (Underlying2 R A)} {f g : a ⟶ b}
    {h : f.obj.obj ⟶ g.obj.obj} {p : ZMod 2} (hh : h ∈ parity (R := R) _ _ p) :
    Tinv₂ R A h ∈ parity (R := R) f g p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [mem_parity_zero']
    apply Subtype.ext
    show proj R 1 h ≫ _ = 0
    rw [proj_of_mem_ne hh (by decide)]
    exact Limits.zero_comp
  · rw [mem_parity_one']
    apply Subtype.ext
    exact proj_of_mem_ne hh (by decide)

variable (R A) in
/-- **Lemma 5.4.** The inverse `𝕋_𝔄⁻¹ : 𝔄 → (E₂ 𝔄)^` of `𝕋_𝔄`: the identity on objects and
1-morphisms, `h ↦ (h₀, ζ_μ G⁻¹ ∘ h₁)` on 2-morphisms, with identity coherence maps. -/
@[simps]
def Tinv : TwoSuperfunctor R A (Associated2 R (Underlying2 R A)) where
  obj a := ⟨⟨a⟩⟩
  map f := ⟨⟨f⟩⟩
  map₂ η := Tinv₂ R A η
  map₂_id f := T_map₂_injective (by rw [T_map₂_Tinv₂, (T R A).map₂_id]; rfl)
  map₂_comp η θ := T_map₂_injective (by
    rw [(T R A).map₂_comp, T_map₂_Tinv₂, T_map₂_Tinv₂, T_map₂_Tinv₂]
    rfl)
  map₂_add η θ := T_map₂_injective (by
    rw [(T R A).map₂_add, T_map₂_Tinv₂, T_map₂_Tinv₂, T_map₂_Tinv₂]
    rfl)
  map₂_smul r η := T_map₂_injective (by
    rw [(T R A).map₂_smul, T_map₂_Tinv₂, T_map₂_Tinv₂]
    rfl)
  map₂_mem hη := Tinv₂_mem hη
  mapComp f g := Iso.refl _
  mapId a := Iso.refl _
  mapComp_hom_mem _ _ := id_mem _
  mapId_hom_mem _ := id_mem _
  mapComp_naturality_left {a b c f f'} η g := T_map₂_injective (by
    rw [(T R A).map₂_comp, (T R A).map₂_comp, T_map₂_whiskerRight, T_map₂_Tinv₂, T_map₂_Tinv₂]
    erw [(T R A).map₂_id, (T R A).map₂_id, Category.comp_id, Category.id_comp]
    rfl)
  mapComp_naturality_right {a b c} f g g' η := T_map₂_injective (by
    rw [(T R A).map₂_comp, (T R A).map₂_comp, T_map₂_whiskerLeft, T_map₂_Tinv₂, T_map₂_Tinv₂]
    erw [(T R A).map₂_id, (T R A).map₂_id, Category.comp_id, Category.id_comp]
    rfl)
  map₂_associator f g h := T_map₂_injective (by
    simp only [T_map₂_Tinv₂, T_map₂_associator_inv, Iso.refl_hom, whiskerLeft_id (R := R),
      id_whiskerRight (R := R), Category.comp_id, Category.id_comp]
    rfl)
  map₂_leftUnitor f := T_map₂_injective (by
    simp only [T_map₂_Tinv₂, T_map₂_leftUnitor_hom, Iso.refl_hom, id_whiskerRight (R := R),
      Category.id_comp]
    rfl)
  map₂_rightUnitor f := T_map₂_injective (by
    simp only [T_map₂_Tinv₂, T_map₂_rightUnitor_hom, Iso.refl_hom, whiskerLeft_id (R := R),
      Category.id_comp]
    rfl)

theorem Tinv₂_T_map₂ {a b : Associated2 R (Underlying2 R A)} {f g : a ⟶ b} (x : f ⟶ g) :
    Tinv₂ R A ((T R A).map₂ x) = x :=
  T_map₂_injective (T_map₂_Tinv₂ _)

/-- **Lemma 5.4.** `𝕋_𝔄⁻¹ ∘ 𝕋_𝔄 = 𝕀`. -/
theorem T_comp_Tinv : (T R A).comp (Tinv R A) = TwoSuperfunctor.id R _ := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    exact Tinv₂_T_map₂ x
  · funext a b c f g
    apply Iso.ext
    change 𝟙 _ ≫ Tinv₂ R A (𝟙 _) = 𝟙 _
    rw [Category.id_comp]
    exact (Tinv R A).map₂_id _
  · funext a
    apply Iso.ext
    change 𝟙 _ ≫ Tinv₂ R A (𝟙 _) = 𝟙 _
    rw [Category.id_comp]
    exact (Tinv R A).map₂_id _

/-- **Lemma 5.4.** `𝕋_𝔄 ∘ 𝕋_𝔄⁻¹ = 𝕀`. -/
theorem Tinv_comp_T : (Tinv R A).comp (T R A) = TwoSuperfunctor.id R A := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    exact T_map₂_Tinv₂ (f := (Tinv R A).map f) (g := (Tinv R A).map g) x
  · funext a b c f g
    apply Iso.ext
    exact (Category.id_comp _).trans ((T R A).map₂_id _)
  · funext a
    apply Iso.ext
    exact (Category.id_comp _).trans ((T R A).map₂_id _)

end T

/-! ### Naturality of `𝕋` -/

section Naturality

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A] [PiTwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [TwoSupercategory R A'] [PiTwoSupercategory R A']

/-- **Lemma 5.4, naturality of `𝕋`**, as an equality of 2-superfunctors:
`𝕋_𝔄' ∘ (E₂ ℝ)^ = ℝ ∘ 𝕋_𝔄`. -/
theorem mapTwo_comp_T (G : TwoSuperfunctor R A A') :
    (G.toPiTwoFunctor.mapTwo).comp (T R A') = (T R A).comp G := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    exact T_map₂_mapTwo G x
  · funext a b c f g
    apply Iso.ext
    change 𝟙 _ ≫ (T R A').map₂ ((G.toPiTwoFunctor.mapTwo).mapComp f g).hom =
      (G.mapComp f.obj.obj g.obj.obj).hom ≫ G.map₂ (𝟙 _)
    rw [Category.id_comp, T_map₂_mapTwo_mapComp, G.map₂_id, Category.comp_id]
  · funext a
    apply Iso.ext
    change 𝟙 _ ≫ (T R A').map₂ ((G.toPiTwoFunctor.mapTwo).mapId a).hom =
      (G.mapId a.obj.obj).hom ≫ G.map₂ (𝟙 _)
    rw [Category.id_comp, T_map₂_mapTwo_mapId, G.map₂_id, Category.comp_id]

end Naturality

end Associated2

namespace PiTwoSCat

variable {R : Type w} [CommRing R]

/-- **Lemma 5.4.** `𝕋_𝔄 : D₂(E₂ 𝔄) ≅ 𝔄` is an isomorphism in `Π-2-SCat`. -/
@[simps]
def TIso (A : PiTwoSCat.{w, w₁, v₁, u₁} R) :
    (toPiTwoCat ⋙ PiTwoCat.toPiTwoSCat).obj A ≅ A where
  hom := Associated2.T R A
  inv := Associated2.Tinv R A
  hom_inv_id := Associated2.T_comp_Tinv
  inv_hom_id := Associated2.Tinv_comp_T

/-- **Lemma 5.4, `D₂ ∘ E₂ ≅ I`**, as a natural isomorphism `E₂ ⋙ D₂ ≅ 𝟭` of endofunctors of
`Π-2-SCat`, with components `𝕋`. -/
def counitNatIso :
    toPiTwoCat ⋙ PiTwoCat.toPiTwoSCat ≅ 𝟭 (PiTwoSCat.{w, w₁, v₁, u₁} R) :=
  NatIso.ofComponents TIso fun {_ _} G => Associated2.mapTwo_comp_T G

end PiTwoSCat

namespace PiTwoCat

variable {R : Type w} [CommRing R]

/-- **Brundan–Ellis, Lemma 5.4.** `D₂ : Π-2-Cat → Π-2-SCat` and `E₂ : Π-2-SCat → Π-2-Cat` are
mutually inverse equivalences of categories, with unit `E₂ ∘ D₂ = I` (`PiTwoCat.unitNatIso`)
and counit `𝕋 : D₂ ∘ E₂ ≅ I` (`PiTwoSCat.counitNatIso`). -/
def equivalence : PiTwoCat.{w, w₁, v₁, u₁} R ≌ PiTwoSCat.{w, w₁, v₁, u₁} R :=
  CategoryTheory.Equivalence.mk toPiTwoSCat PiTwoSCat.toPiTwoCat unitNatIso PiTwoSCat.counitNatIso

instance : (toPiTwoSCat : PiTwoCat.{w, w₁, v₁, u₁} R ⥤ _).IsEquivalence :=
  equivalence.isEquivalence_functor

instance : (PiTwoSCat.toPiTwoCat : PiTwoSCat.{w, w₁, v₁, u₁} R ⥤ _).IsEquivalence :=
  equivalence.isEquivalence_inverse

end PiTwoCat

end StringDiagrams
