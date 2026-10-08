import StringDiagrams.Super.QAssociated
import StringDiagrams.Super.PiCatBicategory

/-!
# The strict 2-category `(Q, Π)-ℭ𝔄𝔗`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, after
Definition 6.12: the 2-category `(Q, Π)-ℭ𝔄𝔗` of `(Q, Π)`-categories, `(Q, Π)`-functors and
`(Q, Π)`-natural transformations (with the `(Q, Π)`-functors of `StringDiagrams.QPiFunctor`,
which include the compatibility of `γ_F` and `β`; erratum 4 to §6 in the README).

* `QPiCat R`: bundled `(Q, Π)`-categories; `QPiCat.Hom`: bundled linear `(Q, Π)`-functors.
* `QPiCat.instCategory`: the category of `(Q, Π)`-categories and `(Q, Π)`-functors.
* `QPiCat.instBicategory`: the bicategory with `(Q, Π)`-natural transformations
  (`QPiCat.qpiNat`) as 2-morphisms and identity coherence isomorphisms; it is strict
  (`QPiCat.instStrict`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u

variable {R : Type w} [CommRing R]

namespace QPiFunctor

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [QPiCategory R C]
  {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D] [QPiCategory R D]

/-- Two `(Q, Π)`-functor structures on a functor with the same `β` and `γ` are equal. -/
theorem ext {F : C ⥤ D} {hF hG : QPiFunctor R F}
    (hβ : ∀ X, hF.β.hom.app X = hG.β.hom.app X) (hγ : ∀ X, hF.γ.hom.app X = hG.γ.hom.app X) :
    hF = hG := by
  obtain ⟨⟨hF', γF⟩, cF⟩ := hF
  obtain ⟨⟨hG', γG⟩, cG⟩ := hG
  have e1 : hF' = hG' := PiFunctor.ext hβ
  subst e1
  have e2 : γF = γG := Iso.ext (NatTrans.ext (funext hγ))
  subst e2
  rfl

end QPiFunctor

/-! ## The category `(Q, Π)-Cat` -/

variable (R) in
/-- A `(Q, Π)`-category over `R` (Brundan–Ellis, Definition 6.12(i)), bundled. -/
structure QPiCat where
  /-- The objects. -/
  carrier : Type u
  [str : Category.{v} carrier]
  [preadditive : Preadditive carrier]
  [linear : Linear R carrier]
  [qpi : QPiCategory R carrier]

namespace QPiCat

attribute [instance] str preadditive linear qpi

instance : CoeSort (QPiCat.{w, v, u} R) (Type u) := ⟨QPiCat.carrier⟩

variable (R) in
/-- The bundled `(Q, Π)`-category of a `(Q, Π)`-category. -/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [QPiCategory R C] :
    QPiCat.{w, v, u} R :=
  ⟨C⟩

/-- A morphism of `(Q, Π)-Cat`: a linear `(Q, Π)`-functor (Definition 6.12(ii)). -/
structure Hom (A B : QPiCat.{w, v, u} R) where
  /-- The underlying functor. -/
  toFunctor : A ⥤ B
  [additive : toFunctor.Additive]
  [linear : toFunctor.Linear R]
  /-- The `(Q, Π)`-functor structure `β`, `γ`. -/
  qpiFunctor : QPiFunctor R toFunctor

attribute [instance] Hom.additive Hom.linear

/-- Two `(Q, Π)`-functors with the same underlying functor, `β` and `γ` are equal. -/
theorem Hom.ext {A B : QPiCat.{w, v, u} R} {F G : Hom A B} (h : F.toFunctor = G.toFunctor)
    (hβ : ∀ X, HEq (F.qpiFunctor.β.hom.app X) (G.qpiFunctor.β.hom.app X))
    (hγ : ∀ X, HEq (F.qpiFunctor.γ.hom.app X) (G.qpiFunctor.γ.hom.app X)) : F = G := by
  cases F
  cases G
  dsimp only at h hβ hγ
  subst h
  congr
  exact QPiFunctor.ext (fun X => eq_of_heq (hβ X)) fun X => eq_of_heq (hγ X)

/-- The category `(Q, Π)-Cat` of `(Q, Π)`-categories and `(Q, Π)`-functors. -/
instance instCategory : Category (QPiCat.{w, v, u} R) where
  Hom := Hom
  id A := ⟨𝟭 A, QPiFunctor.id R A⟩
  comp F G := ⟨F.toFunctor ⋙ G.toFunctor, F.qpiFunctor.comp G.qpiFunctor⟩
  id_comp F := Hom.ext rfl (fun X => heq_of_eq (by simp))
    fun X => heq_of_eq (by simp)
  comp_id F := Hom.ext rfl (fun X => heq_of_eq (by simp))
    fun X => heq_of_eq (by simp)
  assoc F G H := Hom.ext rfl (fun X => heq_of_eq (by simp))
    fun X => heq_of_eq (by simp)

variable {A B E : QPiCat.{w, v, u} R}

theorem hom_def : (A ⟶ B) = Hom A B := rfl

@[simp] theorem id_toFunctor : (𝟙 A : A ⟶ A).toFunctor = 𝟭 A := rfl

@[simp] theorem comp_toFunctor (F : A ⟶ B) (G : B ⟶ E) :
    (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

@[simp] theorem id_qpiFunctor : (𝟙 A : A ⟶ A).qpiFunctor = QPiFunctor.id R A := rfl

@[simp] theorem comp_qpiFunctor (F : A ⟶ B) (G : B ⟶ E) :
    (F ≫ G).qpiFunctor = F.qpiFunctor.comp G.qpiFunctor := rfl

/-! ## `(Q, Π)`-natural transformations as 2-morphisms -/

variable (F G : A ⟶ B) in
/-- The `R`-submodule of `(Q, Π)`-natural transformations (Definition 6.12(iii)). -/
def qpiNat : Submodule R (F.toFunctor ⟶ G.toFunctor) where
  carrier := {x | QPiFunctor.IsQPiNatural R F.qpiFunctor G.qpiFunctor x}
  add_mem' {x y} hx hy := ⟨(PiCat.piNat (A := PiCat.of R A) (B := PiCat.of R B)
      ⟨F.toFunctor, F.qpiFunctor.toPiFunctor⟩ ⟨G.toFunctor, G.qpiFunctor.toPiFunctor⟩).add_mem
      hx.1 hy.1, fun X => by
    rw [NatTrans.app_add, NatTrans.app_add, Preadditive.comp_add, Functor.map_add,
      Preadditive.add_comp, hx.2 X, hy.2 X]⟩
  zero_mem' := ⟨(PiCat.piNat (A := PiCat.of R A) (B := PiCat.of R B)
      ⟨F.toFunctor, F.qpiFunctor.toPiFunctor⟩ ⟨G.toFunctor, G.qpiFunctor.toPiFunctor⟩).zero_mem,
    fun X => by simp⟩
  smul_mem' r x hx := ⟨(PiCat.piNat (A := PiCat.of R A) (B := PiCat.of R B)
      ⟨F.toFunctor, F.qpiFunctor.toPiFunctor⟩ ⟨G.toFunctor, G.qpiFunctor.toPiFunctor⟩).smul_mem r
      hx.1, fun X => by
    rw [NatTrans.app_smul, NatTrans.app_smul, Linear.comp_smul, Functor.map_smul,
      Linear.smul_comp, hx.2 X]⟩

/-- The category of `(Q, Π)`-functors `A → B` and `(Q, Π)`-natural transformations. -/
instance homCategory (A B : QPiCat.{w, v, u} R) : Category (A ⟶ B) where
  Hom F G := qpiNat F G
  id F := ⟨𝟙 F.toFunctor, QPiFunctor.isQPiNatural_id _⟩
  comp x y := ⟨x.1 ≫ y.1, QPiFunctor.IsQPiNatural.comp x.2 y.2⟩
  id_comp x := Subtype.ext (Category.id_comp x.1)
  comp_id x := Subtype.ext (Category.comp_id x.1)
  assoc x y z := Subtype.ext (Category.assoc x.1 y.1 z.1)

variable {F G H K : A ⟶ B}

/-- The natural transformation underlying a 2-morphism of `(Q, Π)-ℭ𝔄𝔗`. -/
abbrev Hom₂.natTrans (x : F ⟶ G) : F.toFunctor ⟶ G.toFunctor := Subtype.val (p := fun y =>
  y ∈ qpiNat F G) x

theorem Hom₂.isQPiNatural (x : F ⟶ G) :
    QPiFunctor.IsQPiNatural R F.qpiFunctor G.qpiFunctor (Hom₂.natTrans x) :=
  Subtype.property (p := fun y => y ∈ qpiNat F G) x

/-- A 2-morphism of `(Q, Π)-ℭ𝔄𝔗` from a `(Q, Π)`-natural transformation. -/
abbrev hom₂Mk (x : F.toFunctor ⟶ G.toFunctor)
    (hx : QPiFunctor.IsQPiNatural R F.qpiFunctor G.qpiFunctor x) : F ⟶ G := ⟨x, hx⟩

@[simp] theorem hom₂Mk_natTrans (x : F.toFunctor ⟶ G.toFunctor)
    (hx : QPiFunctor.IsQPiNatural R F.qpiFunctor G.qpiFunctor x) :
    Hom₂.natTrans (hom₂Mk x hx) = x := rfl

@[simp] theorem id₂_natTrans (F : A ⟶ B) : Hom₂.natTrans (𝟙 F) = 𝟙 F.toFunctor := rfl

@[simp] theorem comp₂_natTrans (x : F ⟶ G) (y : G ⟶ H) :
    Hom₂.natTrans (x ≫ y) = Hom₂.natTrans x ≫ Hom₂.natTrans y := rfl

@[ext] theorem hom₂_ext {x y : F ⟶ G}
    (h : ∀ X, (Hom₂.natTrans x).app X = (Hom₂.natTrans y).app X) : x = y :=
  Subtype.ext (NatTrans.ext (funext h))

theorem id₂_natTrans_app (F : A ⟶ B) (X : A) :
    (Hom₂.natTrans (𝟙 F)).app X = 𝟙 _ := rfl

theorem comp₂_natTrans_app (x : F ⟶ G) (y : G ⟶ H) (X : A) :
    (Hom₂.natTrans (x ≫ y)).app X = (Hom₂.natTrans x).app X ≫ (Hom₂.natTrans y).app X := rfl

/-- A `(Q, Π)`-natural isomorphism of `(Q, Π)`-functors. -/
@[simps]
def iso₂Mk (e : F.toFunctor ≅ G.toFunctor)
    (he : QPiFunctor.IsQPiNatural R F.qpiFunctor G.qpiFunctor e.hom) : F ≅ G where
  hom := hom₂Mk e.hom he
  inv := hom₂Mk e.inv ⟨PiFunctor.IsPiNatural.inv he.1, fun X => by
    rw [← cancel_epi ((QPiCategory.Q (R := R)).map (e.hom.app X)), ← reassoc_of% (he.2 X),
      ← Functor.map_comp_assoc]
    simp⟩
  hom_inv_id := Subtype.ext e.hom_inv_id
  inv_hom_id := Subtype.ext e.inv_hom_id

@[simp] theorem iso₂Mk_hom_natTrans_app (e : F.toFunctor ≅ G.toFunctor)
    (he : QPiFunctor.IsQPiNatural R F.qpiFunctor G.qpiFunctor e.hom) (X : A) :
    (Hom₂.natTrans (iso₂Mk e he).hom).app X = e.hom.app X := rfl

@[simp] theorem iso₂Mk_inv_natTrans_app (e : F.toFunctor ≅ G.toFunctor)
    (he : QPiFunctor.IsQPiNatural R F.qpiFunctor G.qpiFunctor e.hom) (X : A) :
    (Hom₂.natTrans (iso₂Mk e he).inv).app X = e.inv.app X := rfl

/-! ## The bicategory `(Q, Π)-ℭ𝔄𝔗` -/

/-- Whiskering on the left by a `(Q, Π)`-functor. -/
def whiskerLeft₂ (F : A ⟶ B) {G H : B ⟶ E} (y : G ⟶ H) : F ≫ G ⟶ F ≫ H :=
  hom₂Mk (Functor.whiskerLeft F.toFunctor (Hom₂.natTrans y))
    (QAssociated.isQPiNatural_whiskerLeft F.qpiFunctor (Hom₂.isQPiNatural y))

/-- Whiskering on the right by a `(Q, Π)`-functor. -/
def whiskerRight₂ {F G : A ⟶ B} (x : F ⟶ G) (H : B ⟶ E) : F ≫ H ⟶ G ≫ H :=
  hom₂Mk (Functor.whiskerRight (Hom₂.natTrans x) H.toFunctor)
    (QAssociated.isQPiNatural_whiskerRight H.qpiFunctor (Hom₂.isQPiNatural x))

theorem associator_isQPiNatural {A B E E' : QPiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ E)
    (H : E ⟶ E') :
    QPiFunctor.IsQPiNatural R ((F ≫ G) ≫ H).qpiFunctor (F ≫ G ≫ H).qpiFunctor
      (Functor.associator F.toFunctor G.toFunctor H.toFunctor).hom :=
  ⟨fun X => by simp, fun X => by simp⟩

theorem leftUnitor_isQPiNatural (F : A ⟶ B) :
    QPiFunctor.IsQPiNatural R (𝟙 A ≫ F).qpiFunctor F.qpiFunctor
      (Functor.leftUnitor F.toFunctor).hom :=
  ⟨fun X => by simp, fun X => by simp⟩

theorem rightUnitor_isQPiNatural (F : A ⟶ B) :
    QPiFunctor.IsQPiNatural R (F ≫ 𝟙 B).qpiFunctor F.qpiFunctor
      (Functor.rightUnitor F.toFunctor).hom :=
  ⟨fun X => by simp, fun X => by simp⟩

/-- **Brundan–Ellis, after Definition 6.12.** The bicategory `(Q, Π)-ℭ𝔄𝔗` of
`(Q, Π)`-categories, `(Q, Π)`-functors and `(Q, Π)`-natural transformations, with the category
structure of `(Q, Π)-Cat` on 1-morphisms. -/
instance instBicategory : Bicategory.{max u v, max u v} (QPiCat.{w, v, u} R) where
  toCategoryStruct := inferInstance
  homCategory A B := homCategory A B
  whiskerLeft F _ _ y := whiskerLeft₂ F y
  whiskerRight x H := whiskerRight₂ x H
  associator F G H := iso₂Mk (Functor.associator F.toFunctor G.toFunctor H.toFunctor)
    (associator_isQPiNatural F G H)
  leftUnitor F := iso₂Mk (Functor.leftUnitor F.toFunctor) (leftUnitor_isQPiNatural F)
  rightUnitor F := iso₂Mk (Functor.rightUnitor F.toFunctor) (rightUnitor_isQPiNatural F)
  whiskerLeft_id F G := hom₂_ext fun X => rfl
  whiskerLeft_comp F _ _ _ x y := hom₂_ext fun X => rfl
  id_whiskerLeft x := hom₂_ext fun X => by simp [whiskerLeft₂]
  comp_whiskerLeft F G _ _ x := hom₂_ext fun X => by simp [whiskerLeft₂]
  id_whiskerRight F G := hom₂_ext fun X => by simp [whiskerRight₂]
  comp_whiskerRight x y H := hom₂_ext fun X => by simp [whiskerRight₂]
  whiskerRight_id x := hom₂_ext fun X => by simp [whiskerRight₂]
  whiskerRight_comp x G H := hom₂_ext fun X => by simp [whiskerRight₂]
  whisker_assoc F _ _ y H := hom₂_ext fun X => by simp [whiskerLeft₂, whiskerRight₂]
  whisker_exchange x y := hom₂_ext fun X => by simp [whiskerLeft₂, whiskerRight₂]
  pentagon F G H K := hom₂_ext fun X => by simp [whiskerLeft₂, whiskerRight₂]
  triangle F G := hom₂_ext fun X => by simp [whiskerLeft₂, whiskerRight₂]

@[simp] theorem whiskerLeft_natTrans_app (F : A ⟶ B) {G H : B ⟶ E} (y : G ⟶ H) (X : A) :
    (Hom₂.natTrans (F ◁ y)).app X = (Hom₂.natTrans y).app (F.toFunctor.obj X) := rfl

@[simp] theorem whiskerRight_natTrans_app {F G : A ⟶ B} (x : F ⟶ G) (H : B ⟶ E) (X : A) :
    (Hom₂.natTrans (x ▷ H)).app X = H.toFunctor.map ((Hom₂.natTrans x).app X) := rfl

@[simp] theorem associator_hom_natTrans_app {E' : QPiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ E)
    (H : E ⟶ E') (X : A) :
    (Hom₂.natTrans (Bicategory.associator F G H).hom).app X = 𝟙 _ := rfl

@[simp] theorem associator_inv_natTrans_app {E' : QPiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ E)
    (H : E ⟶ E') (X : A) :
    (Hom₂.natTrans (Bicategory.associator F G H).inv).app X = 𝟙 _ := rfl

@[simp] theorem leftUnitor_hom_natTrans_app (F : A ⟶ B) (X : A) :
    (Hom₂.natTrans (Bicategory.leftUnitor F).hom).app X = 𝟙 _ := rfl

@[simp] theorem leftUnitor_inv_natTrans_app (F : A ⟶ B) (X : A) :
    (Hom₂.natTrans (Bicategory.leftUnitor F).inv).app X = 𝟙 _ := rfl

@[simp] theorem rightUnitor_hom_natTrans_app (F : A ⟶ B) (X : A) :
    (Hom₂.natTrans (Bicategory.rightUnitor F).hom).app X = 𝟙 _ := rfl

@[simp] theorem rightUnitor_inv_natTrans_app (F : A ⟶ B) (X : A) :
    (Hom₂.natTrans (Bicategory.rightUnitor F).inv).app X = 𝟙 _ := rfl

theorem eqToHom_natTrans_app {F G : A ⟶ B} (h : F = G) (X : A) :
    (Hom₂.natTrans (eqToHom h)).app X = eqToHom (by rw [h]) := by
  subst h
  rfl

/-- `(Q, Π)-ℭ𝔄𝔗` is a strict bicategory. -/
instance instStrict : Bicategory.Strict (QPiCat.{w, v, u} R) where
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc
  leftUnitor_eqToIso F := Iso.ext (hom₂_ext fun X => by
    rw [eqToIso.hom, eqToHom_natTrans_app, eqToHom_refl]; rfl)
  rightUnitor_eqToIso F := Iso.ext (hom₂_ext fun X => by
    rw [eqToIso.hom, eqToHom_natTrans_app, eqToHom_refl]; rfl)
  associator_eqToIso F G H := Iso.ext (hom₂_ext fun X => by
    rw [eqToIso.hom, eqToHom_natTrans_app, eqToHom_refl]; rfl)

end QPiCat

end StringDiagrams

end
