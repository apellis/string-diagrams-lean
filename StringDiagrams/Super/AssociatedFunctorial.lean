import StringDiagrams.Super.Associated
import StringDiagrams.Super.PiTwo

/-!
# The strict Π-2-functors `𝔼₁`, `𝔻₁` and Theorem 5.3

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (5.3) and
Theorem 5.3: the functors `E₁ : Π-SCat → Π-Cat` and `D₁ : Π-Cat → Π-SCat` of (5.1)–(5.2)
(`StringDiagrams.Super.Underlying`, `StringDiagrams.Super.Associated`) upgrade to strict
Π-2-functors `𝔼₁ : Π-𝔖ℭ𝔞𝔱 → Π-ℭ𝔞𝔱` and `𝔻₁ : Π-ℭ𝔞𝔱 → Π-𝔖ℭ𝔞𝔱` (on underlying 2-categories),
and `T : 𝔻₁ ∘ 𝔼₁ ≅ 𝕀` is a Π-2-natural isomorphism.

The strict 2-categories `Π-ℭ𝔞𝔱` and `Π-𝔖ℭ𝔞𝔱` themselves are not packaged as Lean bicategories
here (see `StringDiagrams.Super.SCat` for `Π-𝔖ℭ𝔞𝔱`); as for Lemma 5.1, we state the content of
Theorem 5.3 directly:

* `𝔼₁` on 2-morphisms is `Underlying.natTrans` (Corollary 3.3(iii)); it preserves identities,
  vertical composition and whiskering (`Underlying.natTrans_id`, `Underlying.natTrans_comp`,
  `Underlying.natTrans_whiskerLeft`, `Underlying.natTrans_whiskerRight`), and is strict as a
  Π-2-functor: `β` and `ξ` of the Π-2-category `Π-ℭ𝔞𝔱` at `𝔼₁` of a superfunctor (resp.
  Π-supercategory) are `𝔼₁` of the `β` and `ξ` of Lemma 3.2 (`Underlying.piFunctor_β_hom_app_val`,
  `Underlying.ξ_hom_app_val`, both by definition).
* `𝔻₁` on 2-morphisms is `Associated.mapNatTrans` ((5.3)); it preserves identities, vertical
  composition and whiskering (`mapNatTrans_id`, `mapNatTrans_comp`, `mapNatTrans_whiskerLeft`,
  `mapNatTrans_whiskerRight`), and is strict as a Π-2-functor: `𝔻₁ Π = Π̂` (`pi_eq_map_pi`),
  `ξ̂ = 𝔻₁ ξ` (`Associated.ξ_hom`) and `β_{F̂} = 𝔻₁ β_F` (`β_map`; this uses the corrected sign
  of `StringDiagrams.Super.Associated`).
* `𝔼₁ ∘ 𝔻₁ = 𝕀` on 2-morphisms (`natTrans_mapNatTrans`).
* `T` is a Π-2-natural isomorphism with identity components `t_F` (`T_naturality`): it is
  natural in 2-morphisms, `x T_A = T_B (x̲)^` (`T_map_mapNatTrans`), and satisfies the coherence
  axiom of Definition 5.2(iii), i.e. `β_{T_A} = 1` (`β_T`).

Together with Lemma 5.1 (`StringDiagrams.Super.Associated`) this is the content of the second
bullet of Theorem 1.9 (the functor (2) of (1.5) is an equivalence) and of its 2-categorical
strengthening, Theorem 5.3.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ w₃ w₄ w₅ w₆

/-! ## `𝔼₁` on 2-morphisms -/

namespace Underlying

variable {R : Type w} [CommRing R]
  {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [Supercategory R E]

variable {F G H : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F] [G.Additive]
  [G.Linear R] [IsSuperfunctor R G] [H.Additive] [H.Linear R] [IsSuperfunctor R H]

/-- `𝔼₁` preserves identity 2-morphisms. -/
theorem natTrans_id :
    natTrans (isSupernatural_id (R := R) (F := F)) = 𝟙 (map (R := R) F) := by
  ext X; rfl

/-- `𝔼₁` preserves vertical composition. -/
theorem natTrans_comp {x : ∀ X, F.obj X ⟶ G.obj X} {y : ∀ X, G.obj X ⟶ H.obj X}
    (hx : IsSupernatural R 0 x) (hy : IsSupernatural R 0 y) :
    natTrans (by simpa using hx.comp hy) = natTrans hx ≫ natTrans hy := by
  ext X; rfl

/-- `𝔼₁` preserves whiskering on the left. -/
theorem natTrans_whiskerLeft (K : E ⥤ C) [K.Additive] [K.Linear R] [IsSuperfunctor R K]
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R 0 x) :
    natTrans (F := K ⋙ F) (G := K ⋙ G) (hx.whiskerLeft K) =
      whiskerLeft (map (R := R) K) (natTrans hx) := by
  ext X; rfl

/-- `𝔼₁` preserves whiskering on the right. -/
theorem natTrans_whiskerRight (K : D ⥤ E) [K.Additive] [K.Linear R] [IsSuperfunctor R K]
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R 0 x) :
    natTrans (F := F ⋙ K) (G := G ⋙ K) (hx.whiskerRight K) =
      whiskerRight (natTrans hx) (map (R := R) K) := by
  ext X; rfl

end Underlying

/-! ## `𝔼₁` is a strict Π-2-functor -/

namespace PiSCat

variable {R : Type w} [CommRing R] {A B : PiSCat.{w, w₂, w₁} R}

/-- **Theorem 5.3, `𝔼₁` is strict on `β`.** The isomorphism `β` of the Π-2-category `Π-ℭ𝔞𝔱` at
the Π-functor `𝔼₁ F = (F̲, β_F)` is `𝔼₁` of the isomorphism `β_F` of Lemma 3.2 in
`Π-𝔖ℭ𝔞𝔱`. -/
theorem underlying_piFunctor_β (F : A ⟶ B) (X : A.carrier) :
    ((Underlying.piFunctor (R := R) F.toFunctor).β.hom.app ⟨X⟩).1 =
      (PiTwoSupercategory.β (R := R) F).hom.app 0 X := by
  rw [β_app_zero]; rfl

/-- **Theorem 5.3, `𝔼₁` is strict on `ξ`.** The isomorphism `ξ` of the Π-category `𝔼₁ A` is
`𝔼₁` of the isomorphism `ξ_A` of Lemma 3.2 in `Π-𝔖ℭ𝔞𝔱`. -/
theorem underlying_ξ (A : PiSCat.{w, w₂, w₁} R) (X : A.carrier) :
    ((PiCategory.ξ (R := R) (C := Underlying R A.carrier)).hom.app ⟨X⟩).1 =
      (PiTwoSupercategory.ξ (R := R) A).hom.app 0 X := by
  rw [ξ_app_zero]; rfl

end PiSCat

/-! ## `𝔻₁` on 2-morphisms -/

namespace Associated

section Map

variable {R : Type w} [CommRing R]
  {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [PiCategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [PiCategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [PiCategory R E]

variable {F G H : C ⥤ D} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R] [H.Additive]
  [H.Linear R] {hF : PiFunctor R F} {hG : PiFunctor R G} {hH : PiFunctor R H}

/-- **Brundan–Ellis, (5.3).** `𝔻₁` on 2-morphisms: the even supernatural transformation
`ŷ : F̂ ⇒ Ĝ`, `ŷ_λ := (y_λ, 0)`, of a Π-natural transformation `y`. -/
@[simps]
def mapNatTrans {y : F ⟶ G} (hy : PiFunctor.IsPiNatural R hF hG y) : map hF ⟶ map hG where
  app X := homMk (y.app X.obj) 0
  naturality _ _ f := (isSupernatural_mapNatTrans hy).naturality_zero f

theorem mapNatTrans_isSupernatural {y : F ⟶ G} (hy : PiFunctor.IsPiNatural R hF hG y) :
    IsSupernatural R 0 (F := map hF) (G := map hG) (mapNatTrans hy).app :=
  isSupernatural_mapNatTrans hy

/-- `𝔻₁` preserves identity 2-morphisms. -/
theorem mapNatTrans_id : mapNatTrans (PiFunctor.isPiNatural_id hF) = 𝟙 (map hF) := by
  ext X <;> simp

/-- `𝔻₁` preserves vertical composition. -/
theorem mapNatTrans_comp {x : F ⟶ G} {y : G ⟶ H} (hx : PiFunctor.IsPiNatural R hF hG x)
    (hy : PiFunctor.IsPiNatural R hG hH y) :
    mapNatTrans (hx.comp hy) = mapNatTrans hx ≫ mapNatTrans hy := by
  ext X <;> simp

omit [F.Additive] [F.Linear R] [G.Additive] [G.Linear R] in
/-- Whiskering a Π-natural transformation by a Π-functor on the left. -/
theorem isPiNatural_whiskerLeft {K : E ⥤ C} [K.Additive] (hK : PiFunctor R K) {y : F ⟶ G}
    (hy : PiFunctor.IsPiNatural R hF hG y) :
    PiFunctor.IsPiNatural R (hK.comp hF) (hK.comp hG) (whiskerLeft K y) := fun X => by
  simp only [PiFunctor.comp_β, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, whiskerLeft_app, Functor.comp_obj, Category.assoc]
  rw [y.naturality, reassoc_of% (hy (K.obj X))]

omit [F.Additive] [F.Linear R] [G.Additive] [G.Linear R] in
/-- Whiskering a Π-natural transformation by a Π-functor on the right. -/
theorem isPiNatural_whiskerRight {K : D ⥤ E} [K.Additive] (hK : PiFunctor R K) {y : F ⟶ G}
    (hy : PiFunctor.IsPiNatural R hF hG y) :
    PiFunctor.IsPiNatural R (hF.comp hK) (hG.comp hK) (whiskerRight y K) := fun X => by
  simp only [PiFunctor.comp_β, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, whiskerRight_app, Functor.comp_obj, Category.assoc, ← K.map_comp,
    hy X]
  rw [K.map_comp, reassoc_of% (hK.β.hom.naturality (y.app X))]

/-- `𝔻₁` preserves whiskering on the left (with `𝔻₁(K F) = 𝔻₁ K ⋙ 𝔻₁ F`, `map_comp`). -/
theorem mapNatTrans_whiskerLeft {K : E ⥤ C} [K.Additive] [K.Linear R] (hK : PiFunctor R K)
    {y : F ⟶ G} (hy : PiFunctor.IsPiNatural R hF hG y) (X : Associated R E) :
    (mapNatTrans (isPiNatural_whiskerLeft hK hy)).app X =
      (mapNatTrans hy).app ((map hK).obj X) := rfl

/-- `𝔻₁` preserves whiskering on the right. -/
theorem mapNatTrans_whiskerRight {K : D ⥤ E} [K.Additive] [K.Linear R] (hK : PiFunctor R K)
    {y : F ⟶ G} (hy : PiFunctor.IsPiNatural R hF hG y) (X : Associated R C) :
    (mapNatTrans (isPiNatural_whiskerRight hK hy)).app X =
      (map hK).map ((mapNatTrans hy).app X) := by
  ext <;> simp

/-- **Theorem 5.3, `𝔼₁ ∘ 𝔻₁ = 𝕀` on 2-morphisms.** `𝔼₁(𝔻₁ y)` is `y` under the identification
`unit` of Lemma 5.1. -/
theorem natTrans_mapNatTrans {y : F ⟶ G} (hy : PiFunctor.IsPiNatural R hF hG y) (X : C) :
    (Underlying.natTrans (F := map hF) (G := map hG) (mapNatTrans_isSupernatural hy)).app
      ⟨⟨X⟩⟩ = (unit R D).map (y.app X) := rfl

/-- **Theorem 5.3, `𝔻₁ Π = Π̂`.** The Π-supercategory structure of `Â` is `𝔻₁` of `(Π, β_Π = -1)`:
`𝔻₁` is a strict Π-2-functor on the 1-morphisms `π`. -/
theorem pi_eq_map_pi :
    PiSupercategory.pi (R := R) (C := Associated R C) = map (PiFunctor.pi (R := R) (C := C)) :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    ext
    · simp [pi_map_fst]
    · simp [pi_map_snd]

omit [PiCategory R D] [F.Additive] [F.Linear R] [G.Additive] [G.Linear R] [H.Additive]
  [H.Linear R] in
theorem ζ_inv (X : Associated R C) :
    (PiSupercategory.ζ (R := R) X).inv =
      homMk (X := X) (Y := ⟨(PiCategory.pi (R := R)).obj X.obj⟩) 0
        (-(PiCategory.ξApp (R := R) X.obj).inv) := rfl

omit [F.Linear R] in
/-- **Theorem 5.3, `𝔻₁ β_F = β_{F̂}`.** The isomorphism `β_{F̂} = -ζ F̂ ζ⁻¹` of Corollary 3.3(ii)
for the superfunctor `F̂ = 𝔻₁(F, β_F)` is `β_F`, viewed as an even morphism. This uses the
corrected sign of the composition of odd morphisms in `Â`. -/
theorem β_map (X : Associated R C) :
    (PiSupercategory.β R (map hF) X).hom =
      homMk (X := ⟨(PiCategory.pi (R := R)).obj (F.obj X.obj)⟩)
        (Y := ⟨F.obj ((PiCategory.pi (R := R)).obj X.obj)⟩) (hF.β.hom.app X.obj) 0 := by
  have hc := hF.comm X.obj
  have n := (PiCategory.ξ (R := R) (C := D)).hom.naturality (hF.β.hom.app X.obj)
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at n
  rw [PiSupercategory.β_hom]
  ext
  · simp only [comp_fst, map_map, homMk_fst, homMk_snd, ζ_hom, ζ_inv, Limits.zero_comp,
      Functor.map_neg, Preadditive.neg_comp, zero_sub, neg_neg, Category.id_comp, pi_obj,
      Functor.map_comp, Category.assoc]
    have h1 : F.map ((PiCategory.ξ (R := R)).inv.app X.obj) ≫
        hF.β.inv.app ((PiCategory.pi (R := R)).obj X.obj) =
        (PiCategory.ξ (R := R)).inv.app (F.obj X.obj) ≫
          (PiCategory.pi (R := R)).map (hF.β.hom.app X.obj) := by
      rw [← cancel_epi ((PiCategory.ξ (R := R)).hom.app (F.obj X.obj)), reassoc_of% hc]
      simp
    rw [PiCategory.ξApp_inv, ← Functor.map_comp_assoc, h1, Functor.map_comp, Category.assoc,
      PiCategory.ξApp_hom]
    erw [n]
    rw [← Category.assoc, PiCategory.ξ_pi, ← Functor.map_comp, Iso.inv_hom_id_app]
    simp
  · simp [ζ_hom, ζ_inv]

end Map

/-! ## `T` is a Π-2-natural isomorphism -/

section T

variable {R : Type w} [CommRing R]
  {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [PiSupercategory R A]
  {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [PiSupercategory R B]

@[simp] theorem T_map_homMk {X Y : Associated R (Underlying R A)} (f : X.obj ⟶ Y.obj) :
    (T R A).map (homMk f 0) = f.1 := by
  simp [T_map]

/-- **Theorem 5.3, naturality of `t`.** For an even supernatural transformation `x : F ⇒ G`
between superfunctors of Π-supercategories, `x T_A = T_B (x̲)^`. -/
theorem T_map_mapNatTrans {F G : A ⥤ B} [F.Additive] [F.Linear R] [IsSuperfunctor R F]
    [G.Additive] [G.Linear R] [IsSuperfunctor R G] {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R 0 x) (X : Associated R (Underlying R A)) :
    (T R B).map ((mapNatTrans (Underlying.isPiNatural hx)).app X) = x X.obj.obj := by
  simp [mapNatTrans]
  rfl

/-- **Theorem 5.3, the coherence axiom of Definition 5.2(iii) for `(T, t)`.** The isomorphism
`β_{T_A} = -ζ_A T_A ζ⁻¹` of Corollary 3.3(ii) for the superfunctor `T_A` is the identity. -/
theorem β_T (X : Associated R (Underlying R A)) :
    (PiSupercategory.β R (T R A) X).hom = 𝟙 _ := by
  have h : (T R A).map (PiSupercategory.ζ (R := R) X).inv =
      (PiSupercategory.ζ (R := R) X.obj.obj).inv := by
    rw [← cancel_epi (PiSupercategory.ζ (R := R) X.obj.obj).hom, Iso.hom_inv_id, ← T_map_ζ,
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  rw [PiSupercategory.β_hom, h]
  exact Iso.hom_inv_id _

end T

end Associated

end StringDiagrams

end
