import StringDiagrams.Super.PiCatE1
import StringDiagrams.Super.AssociatedTwoWhitehead
import StringDiagrams.Super.TwoSuperequivalenceComp

/-!
# Corollary 5.6: `Π-𝔖ℭ𝔞𝔱` and `Π-ℭ𝔞𝔱̂` are 2-superequivalent

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Corollary 5.6: the 2-supercategories `Π-𝔖ℭ𝔞𝔱` (`PiSCat R`, `StringDiagrams.Super.PiTwo`) and
`Π-ℭ𝔞𝔱̂ = D₂(Π-ℭ𝔞𝔱)` (`Associated2 R (PiCat R)`, the associated 2-supercategory (5.5) of the
Π-2-category `Π-ℭ𝔞𝔱` of `StringDiagrams.Super.PiCatBicategory`) are 2-superequivalent.

The proof is the paper's: `E₁ : E₂(Π-𝔖ℭ𝔞𝔱) → Π-ℭ𝔞𝔱` is a Π-2-functor which is a local
equivalence (`StringDiagrams.Super.PiCatE1`, Theorem 5.3), so `D₂ E₁ : D₂(E₂(Π-𝔖ℭ𝔞𝔱)) → Π-ℭ𝔞𝔱̂`
is a local 2-superequivalence (`PiCat.D₂E₁_isLocalTwoSuperequivalence`):

* on morphism supercategories it is `D₁` of the Π-equivalences `Hom(A, B) → Hom(E₁A, E₁B)`,
  and `D₁` of a full, faithful, essentially surjective Π-functor is a superequivalence
  (`Associated.mapSuperequivalence`);
* every Π-category `C` is isomorphic to `E₁(D₁ C)` (`PiCat.unitIsoApp`, Lemma 5.1), which gives
  a superequivalence `E₁(D₁ C) → C` in `Π-ℭ𝔞𝔱̂`.

Composing with the 2-superequivalence `𝕋 : D₂(E₂(Π-𝔖ℭ𝔞𝔱)) → Π-𝔖ℭ𝔞𝔱` of Lemma 5.4 / Theorem 5.5
(`Associated2.T_isTwoSuperequivalence`) gives `PiCat.twoSuperequivalent_piSCat_associated2`.

## The statement

Corollary 5.6 is printed as "the 2-supercategories `Π-2-𝔖ℭ𝔞𝔱` and `Π-2-ℭ𝔞𝔱̂` are
2-superequivalent". Neither of these is a 2-supercategory as printed (`Π-2-𝔖ℭ𝔞𝔱` is the strict
2-category of Π-2-supercategories, and `Π-2-ℭ𝔞𝔱` carries no Π-2-category structure to apply
`D₂` to), and the printed proof concerns `E₁ : E₂(Π-𝔖ℭ𝔞𝔱) → Π-ℭ𝔞𝔱` of Theorem 5.3, `D₂` of it, and
Theorem 5.5 applied to `Π-𝔖ℭ𝔞𝔱`. We formalize the statement that this proof establishes: the
2-supercategories `Π-𝔖ℭ𝔞𝔱` (Π-supercategories, superfunctors, supernatural transformations) and
`Π-ℭ𝔞𝔱̂ = D₂(Π-ℭ𝔞𝔱)` are 2-superequivalent.

Universes: for `R : Type w`, both sides consist of Π-(super)categories with objects in
`Type u` and morphisms in `Type v` (`PiSCat.{w, v, u} R`, `PiCat.{w, v, u} R`); their
1-morphisms and 2-morphisms live in `Type (max u v)`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ w₃ w₄ v u

variable {R : Type w} [CommRing R]

/-! ## `D₁` of a Π-equivalence is a superequivalence -/

namespace Associated

variable {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [PiCategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [PiCategory R D]
  {F : C ⥤ D} [F.Additive] [F.Linear R] (hF : PiFunctor R F)

set_option backward.isDefEq.respectTransparency false in
instance map_faithful [F.Faithful] : (map hF).Faithful where
  map_injective {X Y f g} h := by
    have h1 : F.map f.1 = F.map g.1 := congrArg (fun k : (map hF).obj X ⟶ (map hF).obj Y => k.1) h
    have h2 : F.map f.2 ≫ hF.β.inv.app Y.obj = F.map g.2 ≫ hF.β.inv.app Y.obj :=
      congrArg (fun k : (map hF).obj X ⟶ (map hF).obj Y => k.2) h
    exact hom_ext (F.map_injective h1) (F.map_injective ((cancel_mono _).1 h2))

set_option backward.isDefEq.respectTransparency false in
instance map_full [F.Full] : (map hF).Full where
  map_surjective {X Y} g := ⟨homMk (F.preimage g.1) (F.preimage (g.2 ≫ hF.β.hom.app Y.obj)), by
    ext
    · simp
    · simp only [map_map, homMk_fst, homMk_snd, Functor.map_preimage, Category.assoc,
        Iso.hom_inv_id_app]
      exact Category.comp_id _⟩

omit [F.Linear R] in
/-- `D₁` of an essentially surjective Π-functor is evenly dense. -/
theorem map_evenlyDense [F.EssSurj] : EvenlyDense R (map hF) := fun Y =>
  ⟨⟨F.objPreimage Y.obj⟩, evenIso (F.objObjPreimageIso Y.obj), mem_parity_zero.2 rfl⟩

/-- `D₁` of a full, faithful and essentially surjective Π-functor is a superequivalence. -/
def mapSuperequivalence [F.Full] [F.Faithful] [F.EssSurj] : Superequivalence R (map hF) :=
  Superequivalence.ofFullyFaithful _ (map_evenlyDense hF)

end Associated

/-! ## `D₂ E₁` is a local 2-superequivalence -/

namespace PiCat

variable (R) in
/-- **Proof of Corollary 5.6.** The 2-superfunctor `D₂ E₁ : D₂(E₂(Π-𝔖ℭ𝔞𝔱)) → Π-ℭ𝔞𝔱̂`. -/
abbrev D₂E₁ :
    TwoSuperfunctor R (Associated2 R (Underlying2 R (PiSCat.{w, v, u} R)))
      (Associated2 R (PiCat.{w, v, u} R)) :=
  (PiSCat.E₁PiTwoFunctor R).mapTwo

/-- A Π-category `C` is superequivalent in `Π-ℭ𝔞𝔱̂` to `E₁(D₁ C)`, via the isomorphism
`C ≅ E₁(D₁ C)` of Lemma 5.1. -/
theorem superequivalent_E₁_D₁ (C : Associated2 R (PiCat.{w, v, u} R)) :
    TwoSupercategory.Superequivalent R ((D₂E₁ R).obj ⟨⟨D₁.obj C.obj⟩⟩) C :=
  ⟨⟨(unitIsoApp C.obj).inv⟩, ⟨(unitIsoApp C.obj).hom⟩,
    Associated.evenIso (eqToIso (unitIsoApp C.obj).inv_hom_id),
    Associated.evenIso (eqToIso (unitIsoApp C.obj).hom_inv_id),
    Associated.mem_parity_zero.2 rfl, Associated.mem_parity_zero.2 rfl⟩

/-- **Proof of Corollary 5.6.** `D₂ E₁ : D₂(E₂(Π-𝔖ℭ𝔞𝔱)) → Π-ℭ𝔞𝔱̂` is a 2-superequivalence in the
second formulation of Definition 2.2: `D₁` of the Π-equivalences of morphism categories of
Theorem 5.3 on morphism supercategories, and essentially surjective up to superequivalence. -/
theorem D₂E₁_isLocalTwoSuperequivalence :
    (D₂E₁.{w, v, u} R).IsLocalTwoSuperequivalence where
  hom a b := ⟨Associated.mapSuperequivalence ((PiSCat.E₁PiTwoFunctor R).homPi R a.obj b.obj)⟩
  essSurj C := ⟨⟨⟨D₁.obj C.obj⟩⟩, superequivalent_E₁_D₁ C⟩

/-- **Brundan–Ellis, Corollary 5.6.** The 2-supercategories `Π-𝔖ℭ𝔞𝔱` and
`Π-ℭ𝔞𝔱̂ = D₂(Π-ℭ𝔞𝔱)` are 2-superequivalent (first formulation of Definition 2.2). -/
theorem twoSuperequivalent_piSCat_associated2 :
    TwoSuperfunctor.TwoSuperequivalent R (PiSCat.{w, v, u} R)
      (Associated2 R (PiCat.{w, v, u} R)) :=
  (Associated2.twoSuperequivalent_associated2_underlying2 R (PiSCat.{w, v, u} R)).symm.trans
    ⟨D₂E₁ R, D₂E₁_isLocalTwoSuperequivalence.isTwoSuperequivalence⟩

end PiCat

end StringDiagrams

end
