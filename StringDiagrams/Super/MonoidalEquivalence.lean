import StringDiagrams.Super.Monoidal
import StringDiagrams.Super.Supernatural

/-!
# Monoidal superequivalences

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, the
paragraph after Definition 1.4: monoidal supercategories `A` and `B` are *monoidally
superequivalent* if there are monoidal superfunctors `F : A → B` and `G : B → A` such that
`G ∘ F` and `F ∘ G` are isomorphic to the identities via monoidal natural transformations.

## Main definitions

* `MonoidalSuperfunctor.comp`: the composite of monoidal superfunctors, with coherence maps
  `c_{GF} = G(c_F) ∘ c_G` and `i_{GF} = G(i_F) ∘ i_G`.
* `MonoidalNatTrans.vcomp`: vertical composition of monoidal natural transformations.
* `MonoidalNatIso`: a monoidal natural transformation with a monoidal inverse;
  `MonoidalNatIso.ofNatIso` (the inverse of an invertible monoidal natural transformation is
  monoidal).
* `MonoidalSuperequivalence R C D`: monoidal superfunctors `F : C → D`, `G : D → C` and
  monoidal natural isomorphisms `1 ≅ G ∘ F`, `F ∘ G ≅ 1`.
* `MonoidalSuperequivalence.superequivalence`: the underlying superfunctor of a monoidal
  superequivalence is a superequivalence of the underlying supercategories
  (`Supercategory.Superequivalence`, Definition 1.1(iv)).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {R : Type w} [CommRing R]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [Supercategory R C]
  [MonoidalCategoryStruct C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [MonoidalCategoryStruct D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear R E] [Supercategory R E]
  [MonoidalCategoryStruct E]

/-! ## Composition of monoidal superfunctors -/

namespace MonoidalSuperfunctor

variable [MonoidalSupercategory R E]

attribute [reassoc] μ_natural_left μ_natural_right associativity

/-- The composite of monoidal superfunctors `F : C → D` and `G : D → E`: the superfunctor
`G ∘ F` (in Lean `F ⋙ G`) with coherence maps `c_{X,Y} = G(c_F) ∘ (c_G)_{FX,FY}` and
`i = G(i_F) ∘ i_G`. -/
@[simps]
def comp {F : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F] {G : D ⥤ E} [G.Additive]
    [G.Linear R] [IsSuperfunctor R G] (cF : MonoidalSuperfunctor R F)
    (cG : MonoidalSuperfunctor R G) : MonoidalSuperfunctor R (F ⋙ G) where
  μIso X Y := cG.μIso (F.obj X) (F.obj Y) ≪≫ G.mapIso (cF.μIso X Y)
  εIso := cG.εIso ≪≫ G.mapIso cF.εIso
  μ_mem X Y := by
    simpa using comp_mem (cG.μ_mem (F.obj X) (F.obj Y)) (map_mem G (cF.μ_mem X Y))
  ε_mem := by simpa using comp_mem cG.ε_mem (map_mem G cF.ε_mem)
  μ_natural_left f X' := by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc]
    rw [cG.μ_natural_left_assoc, ← G.map_comp, ← G.map_comp, cF.μ_natural_left]
  μ_natural_right X' f := by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc]
    rw [cG.μ_natural_right_assoc, ← G.map_comp, ← G.map_comp, cF.μ_natural_right]
  associativity X Y Z := by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
      MonoidalSupercategory.comp_whiskerRight (R := R),
      MonoidalSupercategory.whiskerLeft_comp (R := R), Category.assoc]
    rw [cG.μ_natural_left_assoc, ← G.map_comp, ← G.map_comp, cF.associativity, G.map_comp,
      G.map_comp, cG.associativity_assoc, ← cG.μ_natural_right_assoc]
  left_unitality X := by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
      MonoidalSupercategory.comp_whiskerRight (R := R), Category.assoc]
    rw [cG.left_unitality, cG.μ_natural_left_assoc, ← G.map_comp, ← G.map_comp,
      ← cF.left_unitality]
  right_unitality X := by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
      MonoidalSupercategory.whiskerLeft_comp (R := R), Category.assoc]
    rw [cG.right_unitality, cG.μ_natural_right_assoc, ← G.map_comp, ← G.map_comp,
      ← cF.right_unitality]

end MonoidalSuperfunctor

/-! ## Monoidal natural transformations -/

namespace MonoidalNatTrans

variable [MonoidalSupercategory R D]
  {F G H : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F] [G.Additive] [G.Linear R]
  [IsSuperfunctor R G] [H.Additive] [H.Linear R] [IsSuperfunctor R H]
  {cF : MonoidalSuperfunctor R F} {cG : MonoidalSuperfunctor R G} {cH : MonoidalSuperfunctor R H}

omit [MonoidalSupercategory R D] in
/-- Two monoidal natural transformations are equal if their underlying natural
transformations are. -/
theorem ext' {x y : MonoidalNatTrans R cF cG} (h : x.toNatTrans = y.toNatTrans) : x = y := by
  cases x; cases y; subst h; rfl

/-- Vertical composition of monoidal natural transformations. -/
@[simps]
def vcomp (x : MonoidalNatTrans R cF cG) (y : MonoidalNatTrans R cG cH) :
    MonoidalNatTrans R cF cH where
  toNatTrans := x.toNatTrans ≫ y.toNatTrans
  app_mem X := by simpa using comp_mem (x.app_mem X) (y.app_mem X)
  tensor X Y := by
    simp only [NatTrans.comp_app]
    rw [← Category.assoc, x.tensor, Category.assoc,
      y.tensor, ← Category.assoc,
      MonoidalSupercategory.tensorHom_comp_tensorHom _ _ _ _ (y.app_mem X) (x.app_mem Y),
      koszulSign_zero_left, one_smul]
  unit := by rw [NatTrans.comp_app, ← Category.assoc, x.unit, y.unit]

end MonoidalNatTrans

variable (R) in
/-- A monoidal natural isomorphism: monoidal natural transformations `F ⇒ G` and `G ⇒ F`
which are mutually inverse. -/
structure MonoidalNatIso [MonoidalSupercategory R D] {F G : C ⥤ D} [F.Additive] [F.Linear R]
    [IsSuperfunctor R F] [G.Additive] [G.Linear R] [IsSuperfunctor R G]
    (cF : MonoidalSuperfunctor R F) (cG : MonoidalSuperfunctor R G) where
  /-- The forward monoidal natural transformation. -/
  hom : MonoidalNatTrans R cF cG
  /-- The inverse monoidal natural transformation. -/
  inv : MonoidalNatTrans R cG cF
  hom_inv_id : hom.toNatTrans ≫ inv.toNatTrans = 𝟙 F
  inv_hom_id : inv.toNatTrans ≫ hom.toNatTrans = 𝟙 G

namespace MonoidalNatIso

variable [MonoidalSupercategory R D]
  {F G : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F] [G.Additive] [G.Linear R]
  [IsSuperfunctor R G] {cF : MonoidalSuperfunctor R F} {cG : MonoidalSuperfunctor R G}

/-- The underlying natural isomorphism. -/
@[simps]
def toNatIso (e : MonoidalNatIso R cF cG) : F ≅ G where
  hom := e.hom.toNatTrans
  inv := e.inv.toNatTrans
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- The inverse of an invertible monoidal natural transformation is monoidal. -/
def ofNatIso (x : MonoidalNatTrans R cF cG) (e : F ≅ G) (h : e.hom = x.toNatTrans) :
    MonoidalNatIso R cF cG where
  hom := x
  inv :=
    { toNatTrans := e.inv
      app_mem X := inv_mem (e.app X) (by simpa [h] using x.app_mem X)
      tensor X Y := by
        have hX : e.inv.app X ∈ parity (R := R) _ _ 0 :=
          inv_mem (e.app X) (by simpa [h] using x.app_mem X)
        have hX' : e.hom.app X ∈ parity (R := R) _ _ 0 := by simpa [h] using x.app_mem X
        have hY : e.inv.app Y ∈ parity (R := R) _ _ 0 :=
          inv_mem (e.app Y) (by simpa [h] using x.app_mem Y)
        have ht := x.tensor X Y
        rw [← h] at ht
        have hinv : (e.inv.app X ⊗ e.inv.app Y) ≫ (e.hom.app X ⊗ e.hom.app Y) = 𝟙 _ := by
          rw [MonoidalSupercategory.tensorHom_comp_tensorHom _ _ _ _ hX' hY,
            koszulSign_zero_left, one_smul, Iso.inv_hom_id_app, Iso.inv_hom_id_app,
            MonoidalSupercategory.tensor_id R]
        rw [← cancel_mono (e.hom.app (X ⊗ Y)), Category.assoc, Iso.inv_hom_id_app,
          Category.comp_id, Category.assoc, ht, ← Category.assoc, hinv, Category.id_comp]
      unit := by
        rw [← cancel_mono (e.hom.app (𝟙_ C)), Category.assoc, Iso.inv_hom_id_app,
          Category.comp_id, h, x.unit] }
  hom_inv_id := by change x.toNatTrans ≫ e.inv = 𝟙 F; rw [← h, Iso.hom_inv_id]
  inv_hom_id := by change e.inv ≫ x.toNatTrans = 𝟙 G; rw [← h, Iso.inv_hom_id]

@[simp] theorem ofNatIso_hom (x : MonoidalNatTrans R cF cG) (e : F ≅ G) (h : e.hom = x.toNatTrans) :
    (ofNatIso x e h).hom = x := rfl

@[simp] theorem ofNatIso_inv_toNatTrans (x : MonoidalNatTrans R cF cG) (e : F ≅ G)
    (h : e.hom = x.toNatTrans) : (ofNatIso x e h).inv.toNatTrans = e.inv := rfl

end MonoidalNatIso

/-! ## Monoidal superequivalences -/

variable (R C D) in
/-- A monoidal superequivalence between monoidal supercategories `C` and `D` (Brundan–Ellis,
the paragraph after Definition 1.4): monoidal superfunctors `F : C → D` and `G : D → C` such
that `G ∘ F` and `F ∘ G` are isomorphic to the identities via monoidal natural
transformations. -/
structure MonoidalSuperequivalence [MonoidalSupercategory R C] [MonoidalSupercategory R D] where
  /-- The superfunctor `F : C → D`. -/
  functor : C ⥤ D
  [functor_additive : functor.Additive]
  [functor_linear : functor.Linear R]
  [functor_isSuperfunctor : IsSuperfunctor R functor]
  /-- The monoidal structure of `F`. -/
  functorMonoidal : MonoidalSuperfunctor R functor
  /-- The superfunctor `G : D → C`. -/
  inverse : D ⥤ C
  [inverse_additive : inverse.Additive]
  [inverse_linear : inverse.Linear R]
  [inverse_isSuperfunctor : IsSuperfunctor R inverse]
  /-- The monoidal structure of `G`. -/
  inverseMonoidal : MonoidalSuperfunctor R inverse
  /-- The monoidal natural isomorphism `1 ≅ G ∘ F`. -/
  unitIso : MonoidalNatIso R (MonoidalSuperfunctor.id (R := R) (C := C))
    (functorMonoidal.comp inverseMonoidal)
  /-- The monoidal natural isomorphism `F ∘ G ≅ 1`. -/
  counitIso : MonoidalNatIso R (inverseMonoidal.comp functorMonoidal)
    (MonoidalSuperfunctor.id (R := R) (C := D))

attribute [instance] MonoidalSuperequivalence.functor_additive
  MonoidalSuperequivalence.functor_linear MonoidalSuperequivalence.functor_isSuperfunctor
  MonoidalSuperequivalence.inverse_additive MonoidalSuperequivalence.inverse_linear
  MonoidalSuperequivalence.inverse_isSuperfunctor

namespace MonoidalSuperequivalence

variable [MonoidalSupercategory R C] [MonoidalSupercategory R D]

/-- The superfunctor of a monoidal superequivalence is a superequivalence of the underlying
supercategories (Definition 1.1(iv)): the unit and counit are even since monoidal natural
transformations are even. -/
def superequivalence (e : MonoidalSuperequivalence R C D) : Superequivalence R e.functor where
  inverse := e.inverse
  unitIso := e.unitIso.toNatIso
  counitIso := e.counitIso.toNatIso
  unitIso_mem X := e.unitIso.hom.app_mem X
  counitIso_mem Y := e.counitIso.hom.app_mem Y

end MonoidalSuperequivalence

end StringDiagrams

end
