import StringDiagrams.Super.GradedSub
import StringDiagrams.Super.SCat
import StringDiagrams.Super.GradedTwo
import StringDiagrams.Super.QPi

/-!
# The strict graded 2-supercategories `𝔊𝔖ℭ𝔞𝔱` and `(Q, Π)-𝔊𝔖ℭ𝔞𝔱`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6: the
graded supercategory `ℋom(A, B)` of graded superfunctors and graded supernatural
transformations (the last example after Definition 6.1), the strict graded 2-supercategory
`𝔊𝔖ℭ𝔞𝔱` of graded supercategories, graded superfunctors and graded supernatural transformations
(the basic example after Definition 6.2), and the graded `(Q, Π)`-2-supercategory
`(Q, Π)-𝔊𝔖ℭ𝔞𝔱` of graded `(Q, Π)`-supercategories, graded superfunctors and graded supernatural
transformations (the example after Definition 6.5).

* `GradedSuperfunctor R A B`: a graded superfunctor (Definition 6.1), bundled.
* `GradedHom R A B`: the graded supercategory `ℋom(A, B)`. Its morphisms `F ⟶ G` are the
  graded supernatural transformations, i.e. the elements of `⨁ₙ Hom(F, G)ₙ` where `Hom(F, G)ₙ`
  is the superspace of supernatural transformations homogeneous of degree `n`
  (`GradedSuperfunctor.degNat`); it is the graded subcategory (`GradedSubcategory`) of the
  supercategory `Superfunctor R A B` of Example 1.2(iv) determined by these
  (`GradedSuperfunctor.family`). The morphisms of degree `n` are those whose parity components
  are homogeneous supernatural transformations of degree `n` in the sense of Definition 6.1
  (`GradedHom.mem_degree_iff`); `GradedHom.ofHomogeneous` and `GradedHom.isoOfHomogeneous`
  produce morphisms and isomorphisms from homogeneous ones.
* `GSCat R`: graded supercategories, bundled, with the structure of a strict graded
  2-supercategory (`GSCat.instTwoSupercategory`, `GSCat.instGradedTwoSupercategory`,
  `GSCat.instStrict`): the morphism supercategories are the `GradedHom R A B`, horizontal
  composition is composition of graded superfunctors and the whiskerings of supernatural
  transformations, as in `SCat R`.
* `QPiGSCat R`: graded `(Q, Π)`-supercategories, bundled, with the same 1- and 2-morphisms,
  a strict graded 2-supercategory, and a graded `(Q, Π)`-2-supercategory
  (`QPiGSCat.instQPiTwoSupercategory`) with `q_A := Q_A`, `q_A⁻¹ := Q_A⁻¹`, `π_A := Π_A`, and
  `σ_A`, `σ̄_A`, `ζ_A` the given supernatural isomorphisms (even of degree `-1`, even of
  degree `1`, odd of degree `0`).

The monoidal structure `⊠` on the category `GSCat` of graded supercategories and graded
superfunctors is not formalized (nor is `⊠` on `SCat`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe w u₁ v₁ u₂ v₂ u₃ v₃ v u

variable {R : Type w} [CommRing R]

/-! ## Graded superfunctors and the graded supercategory `ℋom(A, B)` -/

section GradedHom

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [GradedSupercategory R A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B]
  {C : Type u₃} [Category.{v₃} C] [Preadditive C] [Linear R C] [Supercategory R C]
  [GradedSupercategory R C]

variable (R A B) in
/-- A graded superfunctor (Brundan–Ellis, Definition 6.1), bundled: a superfunctor preserving
degrees. -/
structure GradedSuperfunctor extends Superfunctor R A B where
  [isGraded : IsGradedSuperfunctor R toFunctor]

namespace GradedSuperfunctor

attribute [instance] isGraded

/-- The object part of a graded superfunctor. -/
abbrev obj (F : GradedSuperfunctor R A B) (X : A) : B := F.toFunctor.obj X

/-- The morphism part of a graded superfunctor. -/
abbrev map (F : GradedSuperfunctor R A B) {X Y : A} (f : X ⟶ Y) : F.obj X ⟶ F.obj Y :=
  F.toFunctor.map f

variable (R A) in
/-- The identity graded superfunctor. -/
def id : GradedSuperfunctor R A A where
  toSuperfunctor := Superfunctor.id R A
  isGraded := inferInstanceAs (IsGradedSuperfunctor R (𝟭 A))

/-- The composite `F ⋙ G` of graded superfunctors (the paper's `G F`). -/
def comp (F : GradedSuperfunctor R A B) (G : GradedSuperfunctor R B C) :
    GradedSuperfunctor R A C where
  toSuperfunctor := F.toSuperfunctor.comp G.toSuperfunctor
  isGraded := inferInstanceAs (IsGradedSuperfunctor R (F.toFunctor ⋙ G.toFunctor))

@[simp] theorem id_toSuperfunctor : (id R A).toSuperfunctor = Superfunctor.id R A := rfl

@[simp] theorem comp_toSuperfunctor (F : GradedSuperfunctor R A B) (G : GradedSuperfunctor R B C) :
    (F.comp G).toSuperfunctor = F.toSuperfunctor.comp G.toSuperfunctor := rfl

/-- The supernatural transformations homogeneous of degree `n` (Brundan–Ellis, Definition
6.1): those whose components (of either parity) have degree `n`. -/
def degNat (F G : GradedSuperfunctor R A B) (n : ℤ) :
    Submodule R (F.toSuperfunctor ⟶ G.toSuperfunctor) where
  carrier := {x | ∀ (p : ZMod 2) (X : A), x.app p X ∈ degree (R := R) (F.obj X) (G.obj X) n}
  add_mem' {x y} hx hy p X := by
    rw [Superfunctor.add_app]; exact Submodule.add_mem _ (hx p X) (hy p X)
  zero_mem' p X := by rw [Superfunctor.zero_app]; exact Submodule.zero_mem _
  smul_mem' r x hx p X := by
    rw [Superfunctor.smul_app]; exact Submodule.smul_mem _ _ (hx p X)

theorem mem_degNat_iff {F G : GradedSuperfunctor R A B} {n : ℤ}
    {x : F.toSuperfunctor ⟶ G.toSuperfunctor} :
    x ∈ degNat F G n ↔ ∀ (p : ZMod 2) (X : A), x.app p X ∈ degree (R := R) (F.obj X) (G.obj X) n :=
  Iff.rfl

/-- Evaluation of the component of parity `p` at `X`, as a linear map. -/
def evalNat (F G : GradedSuperfunctor R A B) (p : ZMod 2) (X : A) :
    (F.toSuperfunctor ⟶ G.toSuperfunctor) →ₗ[R] (F.obj X ⟶ G.obj X) where
  toFun x := x.app p X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem iSupIndep_degNat (F G : GradedSuperfunctor R A B) : iSupIndep (degNat F G) := by
  refine iSupIndep_of_eval (degNat F G) (A := ZMod 2 × A) (N := fun pX => F.obj pX.2 ⟶ G.obj pX.2)
    (fun pX => evalNat F G pX.1 pX.2) (fun pX n => degree (R := R) (F.obj pX.2) (G.obj pX.2) n)
    (fun pX => (isInternal_degree (R := R) _ _).submodule_iSupIndep) ?_ ?_
  · rintro ⟨p, X⟩ n x ⟨y, hy, rfl⟩
    exact hy p X
  · intro x hx
    exact Superfunctor.hom_ext fun p X => hx (p, X)

theorem whiskerLeft_mem_degNat (F : GradedSuperfunctor R A B) {G K : GradedSuperfunctor R B C}
    {n : ℤ} {y : G.toSuperfunctor ⟶ K.toSuperfunctor} (hy : y ∈ degNat G K n) :
    Superfunctor.whiskerLeft F.toSuperfunctor y ∈ degNat (F.comp G) (F.comp K) n :=
  fun p X => hy p (F.obj X)

theorem whiskerRight_mem_degNat {F H : GradedSuperfunctor R A B} {n : ℤ}
    {x : F.toSuperfunctor ⟶ H.toSuperfunctor} (hx : x ∈ degNat F H n)
    (G : GradedSuperfunctor R B C) :
    Superfunctor.whiskerRight x G.toSuperfunctor ∈ degNat (F.comp G) (H.comp G) n :=
  fun p X => map_mem_degree G.toFunctor (hx p X)

variable (R A B) in
/-- The graded hom family defining `ℋom(A, B)`: the supernatural transformations homogeneous
of each degree. -/
def family : GradedHomFamily R (Superfunctor R A B) (GradedSuperfunctor R A B) where
  obj := toSuperfunctor
  deg := degNat
  proj_mem {F G n x} p hx q X := by
    rw [Superfunctor.proj_app]
    split_ifs with h
    · subst h; exact hx q X
    · exact Submodule.zero_mem _
  id_mem F p X := by
    change (if p = 0 then 𝟙 (F.obj X) else 0) ∈ _
    split_ifs
    · exact id_mem_degree _
    · exact Submodule.zero_mem _
  comp_mem {F G H m n x y} hx hy r X := by
    rw [Superfunctor.comp_app]
    exact Submodule.add_mem _ (comp_mem_degree (hx 0 X) (hy r X))
      (comp_mem_degree (hx 1 X) (hy _ X))
  indep := iSupIndep_degNat

theorem whiskerLeft_mem_hom (F : GradedSuperfunctor R A B) {G K : GradedSuperfunctor R B C}
    {y : G.toSuperfunctor ⟶ K.toSuperfunctor} (hy : y ∈ (family R B C).hom G K) :
    Superfunctor.whiskerLeft F.toSuperfunctor y ∈ (family R A C).hom (F.comp G) (F.comp K) := by
  refine (family R B C).hom_induction hy
    (fun n y hy => (family R A C).mem_hom_of_mem (whiskerLeft_mem_degNat F hy)) ?_ ?_
  · rw [show Superfunctor.whiskerLeft F.toSuperfunctor (0 : G.toSuperfunctor ⟶ K.toSuperfunctor) = 0
      from Superfunctor.hom_ext fun _ _ => rfl]
    exact Submodule.zero_mem _
  · intro y z hy hz
    rw [Superfunctor.whiskerLeft_add]; exact Submodule.add_mem _ hy hz

theorem whiskerRight_mem_hom {F H : GradedSuperfunctor R A B}
    {x : F.toSuperfunctor ⟶ H.toSuperfunctor} (hx : x ∈ (family R A B).hom F H)
    (G : GradedSuperfunctor R B C) :
    Superfunctor.whiskerRight x G.toSuperfunctor ∈ (family R A C).hom (F.comp G) (H.comp G) := by
  refine (family R A B).hom_induction hx
    (fun n x hx => (family R A C).mem_hom_of_mem (whiskerRight_mem_degNat hx G)) ?_ ?_
  · rw [show Superfunctor.whiskerRight (0 : F.toSuperfunctor ⟶ H.toSuperfunctor) G.toSuperfunctor = 0
      from Superfunctor.hom_ext fun _ _ => G.toFunctor.map_zero _ _]
    exact Submodule.zero_mem _
  · intro x z hx hz
    rw [Superfunctor.add_whiskerRight]; exact Submodule.add_mem _ hx hz

end GradedSuperfunctor

variable (R A B) in
/-- **Brundan–Ellis, §6 (after Definition 6.1).** The graded supercategory `ℋom(A, B)` of
graded superfunctors `A → B` and graded supernatural transformations. -/
abbrev GradedHom := GradedSubcategory (GradedSuperfunctor.family R A B)

namespace GradedHom

open GradedSuperfunctor GradedSubcategory

/-- A graded superfunctor, as an object of `ℋom(A, B)`. -/
abbrev of (F : GradedSuperfunctor R A B) : GradedHom R A B := ⟨F⟩

/-- The morphisms of degree `n` of `ℋom(A, B)` are the supernatural transformations whose
parity components are homogeneous supernatural transformations of degree `n`
(Definition 6.1). -/
theorem mem_degree_iff {F G : GradedHom R A B} {n : ℤ} {x : F ⟶ G} :
    x ∈ degree (R := R) F G n ↔ ∀ p : ZMod 2, IsGradedSupernatural R p n (x.1.app p) :=
  ⟨fun h p => ⟨x.1.isSupernatural p, h p⟩, fun h p X => (h p).mem_degree X⟩

theorem mem_parity_iff {F G : GradedHom R A B} {p : ZMod 2} {x : F ⟶ G} :
    x ∈ parity (R := R) F G p ↔ x.1.app (p + 1) = 0 :=
  Iff.rfl

/-- A supernatural transformation homogeneous of parity `p` and degree `n`, as a morphism of
`ℋom(A, B)`. -/
def ofHomogeneous {F G : GradedHom R A B} {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.as.obj X ⟶ G.as.obj X} (hx : IsGradedSupernatural R p n x) : F ⟶ G :=
  homMk hx.toIsSupernatural.toSuperNatTrans fun q X => by
    change (if q = p then x X else 0) ∈ _
    split_ifs
    · exact hx.mem_degree X
    · exact Submodule.zero_mem _

@[simp] theorem ofHomogeneous_app {F G : GradedHom R A B} {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.as.obj X ⟶ G.as.obj X} (hx : IsGradedSupernatural R p n x) (q : ZMod 2) (X : A) :
    (ofHomogeneous hx).1.app q X = if q = p then x X else 0 := rfl

theorem ofHomogeneous_mem {F G : GradedHom R A B} {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.as.obj X ⟶ G.as.obj X} (hx : IsGradedSupernatural R p n x) :
    ofHomogeneous hx ∈ parity (R := R) F G p :=
  Superfunctor.IsSupernatural.toSuperNatTrans_mem hx.toIsSupernatural

theorem ofHomogeneous_mem_degree {F G : GradedHom R A B} {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.as.obj X ⟶ G.as.obj X} (hx : IsGradedSupernatural R p n x) :
    ofHomogeneous hx ∈ degree (R := R) F G n :=
  homMk_mem_degree _ _

/-- A homogeneous supernatural isomorphism, as an isomorphism of `ℋom(A, B)`. -/
def isoOfHomogeneous {F G : GradedHom R A B} {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.as.obj X ≅ G.as.obj X} (hx : IsGradedSupernatural R p n fun X => (x X).hom)
    (hx' : IsGradedSupernatural R p (-n) fun X => (x X).inv) : F ≅ G where
  hom := ofHomogeneous hx
  inv := ofHomogeneous hx'
  hom_inv_id := Subtype.ext (Superfunctor.hom_ext_parity
    (fun X => by rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)
    (fun X => by rcases parity_eq_zero_or_one p with rfl | rfl <;> simp))
  inv_hom_id := Subtype.ext (Superfunctor.hom_ext_parity
    (fun X => by rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)
    (fun X => by rcases parity_eq_zero_or_one p with rfl | rfl <;> simp))

@[simp] theorem isoOfHomogeneous_hom {F G : GradedHom R A B} {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.as.obj X ≅ G.as.obj X} (hx : IsGradedSupernatural R p n fun X => (x X).hom)
    (hx' : IsGradedSupernatural R p (-n) fun X => (x X).inv) :
    (isoOfHomogeneous hx hx').hom = ofHomogeneous hx := rfl

@[simp] theorem isoOfHomogeneous_inv {F G : GradedHom R A B} {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.as.obj X ≅ G.as.obj X} (hx : IsGradedSupernatural R p n fun X => (x X).hom)
    (hx' : IsGradedSupernatural R p (-n) fun X => (x X).inv) :
    (isoOfHomogeneous hx hx').inv = ofHomogeneous hx' := rfl

end GradedHom

end GradedHom

/-! ## The strict graded 2-supercategory `𝔊𝔖ℭ𝔞𝔱` -/

variable (R) in
/-- A graded supercategory over `R` (Brundan–Ellis, Definition 6.1), bundled. -/
structure GSCat extends SCat.{w, v, u} R where
  [graded : GradedSupercategory R carrier]

namespace GSCat

attribute [instance] graded

instance : CoeSort (GSCat.{w, v, u} R) (Type u) := ⟨fun A => A.carrier⟩

variable (R) in
/-- The bundled graded supercategory of a graded supercategory. -/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C]
    [GradedSupercategory R C] : GSCat.{w, v, u} R :=
  ⟨SCat.of R C⟩

open BicategoryStruct GradedSuperfunctor

/-- The horizontal composition data of `𝔊𝔖ℭ𝔞𝔱`: graded superfunctors, graded supernatural
transformations, their whiskerings, and identity coherence maps. -/
instance instBicategoryStruct : BicategoryStruct.{max u v, max u v} (GSCat.{w, v, u} R) where
  Hom A B := GradedHom R A B
  id A := ⟨GradedSuperfunctor.id R A⟩
  comp F G := ⟨F.as.comp G.as⟩
  homCategory _ _ := inferInstance
  whiskerLeft F _ _ y := ⟨Superfunctor.whiskerLeft F.as.toSuperfunctor y.1, whiskerLeft_mem_hom F.as y.2⟩
  whiskerRight x G := ⟨Superfunctor.whiskerRight x.1 G.as.toSuperfunctor, whiskerRight_mem_hom x.2 G.as⟩
  associator _ _ _ := Iso.refl _
  leftUnitor _ := Iso.refl _
  rightUnitor _ := Iso.refl _

instance (A B : GSCat.{w, v, u} R) : Preadditive (A ⟶ B) :=
  inferInstanceAs (Preadditive (GradedHom R A B))

instance (A B : GSCat.{w, v, u} R) : Linear R (A ⟶ B) :=
  inferInstanceAs (Linear R (GradedHom R A B))

instance (A B : GSCat.{w, v, u} R) : Supercategory R (A ⟶ B) :=
  inferInstanceAs (Supercategory R (GradedHom R A B))

instance (A B : GSCat.{w, v, u} R) : GradedSupercategory R (A ⟶ B) :=
  inferInstanceAs (GradedSupercategory R (GradedHom R A B))

theorem hom_def (A B : GSCat.{w, v, u} R) : (A ⟶ B) = GradedHom R A B := rfl

@[simp] theorem whiskerLeft_val {A B C : GSCat.{w, v, u} R} (F : A ⟶ B) {G K : B ⟶ C}
    (y : G ⟶ K) : (F ◁ y).1 = Superfunctor.whiskerLeft F.as.toSuperfunctor y.1 := rfl

@[simp] theorem whiskerRight_val {A B C : GSCat.{w, v, u} R} {F H : A ⟶ B} (x : F ⟶ H)
    (G : B ⟶ C) : (x ▷ G).1 = Superfunctor.whiskerRight x.1 G.as.toSuperfunctor := rfl

@[simp] theorem associator_hom {A B C D : GSCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).hom = 𝟙 (F ≫ G ≫ H) := rfl

@[simp] theorem associator_inv {A B C D : GSCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C)
    (H : C ⟶ D) : (associator F G H).inv = 𝟙 (F ≫ G ≫ H) := rfl

@[simp] theorem leftUnitor_hom {A B : GSCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).hom = 𝟙 F := rfl

@[simp] theorem leftUnitor_inv {A B : GSCat.{w, v, u} R} (F : A ⟶ B) :
    (leftUnitor F).inv = 𝟙 F := rfl

@[simp] theorem rightUnitor_hom {A B : GSCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).hom = 𝟙 F := rfl

@[simp] theorem rightUnitor_inv {A B : GSCat.{w, v, u} R} (F : A ⟶ B) :
    (rightUnitor F).inv = 𝟙 F := rfl

/-- **Brundan–Ellis, §6 (after Definition 6.2).** Graded supercategories, graded superfunctors
and graded supernatural transformations form a 2-supercategory `𝔊𝔖ℭ𝔞𝔱`. -/
instance instTwoSupercategory : TwoSupercategory R (GSCat.{w, v, u} R) where
  whiskerLeft_id F G := Subtype.ext
    (TwoSupercategory.whiskerLeft_id (R := R) (B := SCat R) F.as.toSuperfunctor G.as.toSuperfunctor)
  whiskerLeft_comp F _ _ _ y z := Subtype.ext
    (TwoSupercategory.whiskerLeft_comp (R := R) (B := SCat R) F.as.toSuperfunctor y.1 z.1)
  id_whiskerLeft y := Subtype.ext (TwoSupercategory.id_whiskerLeft (R := R) (B := SCat R) y.1)
  comp_whiskerLeft F G _ _ y := Subtype.ext
    (TwoSupercategory.comp_whiskerLeft (R := R) (B := SCat R) F.as.toSuperfunctor
      G.as.toSuperfunctor y.1)
  id_whiskerRight F G := Subtype.ext
    (TwoSupercategory.id_whiskerRight (R := R) (B := SCat R) F.as.toSuperfunctor G.as.toSuperfunctor)
  comp_whiskerRight x z G := Subtype.ext
    (TwoSupercategory.comp_whiskerRight (R := R) (B := SCat R) x.1 z.1 G.as.toSuperfunctor)
  whiskerRight_id x := Subtype.ext (TwoSupercategory.whiskerRight_id (R := R) (B := SCat R) x.1)
  whiskerRight_comp x G H := Subtype.ext
    (TwoSupercategory.whiskerRight_comp (R := R) (B := SCat R) x.1 G.as.toSuperfunctor
      H.as.toSuperfunctor)
  whisker_assoc F _ _ y H := Subtype.ext
    (TwoSupercategory.whisker_assoc (R := R) (B := SCat R) F.as.toSuperfunctor y.1
      H.as.toSuperfunctor)
  pentagon F G H K := Subtype.ext
    (TwoSupercategory.pentagon (R := R) (B := SCat R) F.as.toSuperfunctor G.as.toSuperfunctor
      H.as.toSuperfunctor K.as.toSuperfunctor)
  triangle F G := Subtype.ext
    (TwoSupercategory.triangle (R := R) (B := SCat R) F.as.toSuperfunctor G.as.toSuperfunctor)
  whiskerLeft_add F _ _ y z := Subtype.ext
    (TwoSupercategory.whiskerLeft_add (R := R) (B := SCat R) F.as.toSuperfunctor y.1 z.1)
  add_whiskerRight x z G := Subtype.ext
    (TwoSupercategory.add_whiskerRight (R := R) (B := SCat R) x.1 z.1 G.as.toSuperfunctor)
  whiskerLeft_smul F _ _ r y := Subtype.ext
    (TwoSupercategory.whiskerLeft_smul (B := SCat R) F.as.toSuperfunctor r y.1)
  smul_whiskerRight r x G := Subtype.ext
    (TwoSupercategory.smul_whiskerRight (B := SCat R) r x.1 G.as.toSuperfunctor)
  whiskerLeft_mem F _ _ _ _ hy :=
    TwoSupercategory.whiskerLeft_mem (R := R) (B := SCat R) F.as.toSuperfunctor hy
  whiskerRight_mem G hx :=
    TwoSupercategory.whiskerRight_mem (R := R) (B := SCat R) G.as.toSuperfunctor hx
  super_interchange hx hy := Subtype.ext
    (TwoSupercategory.super_interchange (R := R) (B := SCat R) hx hy)
  associator_hom_mem _ _ _ := id_mem _
  leftUnitor_hom_mem _ := id_mem _
  rightUnitor_hom_mem _ := id_mem _

/-- **Brundan–Ellis, §6 (after Definition 6.2).** `𝔊𝔖ℭ𝔞𝔱` is a graded 2-supercategory: the
whiskerings preserve degrees. -/
instance instGradedTwoSupercategory : GradedTwoSupercategory R (GSCat.{w, v, u} R) where
  whiskerLeft_mem_degree F _ _ _ _ hη := whiskerLeft_mem_degNat F.as hη
  whiskerRight_mem_degree h hη := whiskerRight_mem_degNat hη h.as
  associator_hom_mem_degree _ _ _ := id_mem_degree _
  leftUnitor_hom_mem_degree _ := id_mem_degree _
  rightUnitor_hom_mem_degree _ := id_mem_degree _

/-- **Brundan–Ellis, Definition 6.2.** `𝔊𝔖ℭ𝔞𝔱` is a strict graded 2-supercategory. -/
instance instStrict : BicategoryStruct.Strict (GSCat.{w, v, u} R) where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

end GSCat

/-! ## The graded (Q, Π)-2-supercategory `(Q, Π)-𝔊𝔖ℭ𝔞𝔱` -/

variable (R) in
/-- A graded `(Q, Π)`-supercategory over `R` (Brundan–Ellis, Definition 6.4), bundled. -/
structure QPiGSCat extends GSCat.{w, v, u} R where
  [qpi : QPiSupercategory R carrier]

namespace QPiGSCat

attribute [instance] qpi

instance : CoeSort (QPiGSCat.{w, v, u} R) (Type u) := ⟨fun A => A.carrier⟩

variable (R) in
/-- The bundled graded `(Q, Π)`-supercategory of a graded `(Q, Π)`-supercategory. -/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C]
    [GradedSupercategory R C] [QPiSupercategory R C] : QPiGSCat.{w, v, u} R :=
  ⟨GSCat.of R C⟩

open BicategoryStruct

/-- The data of the 2-supercategory `(Q, Π)-𝔊𝔖ℭ𝔞𝔱`: that of `𝔊𝔖ℭ𝔞𝔱` on the underlying graded
supercategories. -/
instance instBicategoryStruct : BicategoryStruct.{max u v, max u v} (QPiGSCat.{w, v, u} R) where
  Hom A B := A.toGSCat ⟶ B.toGSCat
  id A := 𝟙 A.toGSCat
  comp F G := F ≫ G
  homCategory A B := inferInstanceAs (Category (A.toGSCat ⟶ B.toGSCat))
  whiskerLeft F _ _ y := F ◁ y
  whiskerRight x G := x ▷ G
  associator F G H := associator (B := GSCat R) F G H
  leftUnitor F := leftUnitor (B := GSCat R) F
  rightUnitor F := rightUnitor (B := GSCat R) F

instance (A B : QPiGSCat.{w, v, u} R) : Preadditive (A ⟶ B) :=
  inferInstanceAs (Preadditive (A.toGSCat ⟶ B.toGSCat))

instance (A B : QPiGSCat.{w, v, u} R) : Linear R (A ⟶ B) :=
  inferInstanceAs (Linear R (A.toGSCat ⟶ B.toGSCat))

instance (A B : QPiGSCat.{w, v, u} R) : Supercategory R (A ⟶ B) :=
  inferInstanceAs (Supercategory R (A.toGSCat ⟶ B.toGSCat))

instance (A B : QPiGSCat.{w, v, u} R) : GradedSupercategory R (A ⟶ B) :=
  inferInstanceAs (GradedSupercategory R (A.toGSCat ⟶ B.toGSCat))

theorem hom_def (A B : QPiGSCat.{w, v, u} R) : (A ⟶ B) = GradedHom R A B := rfl

/-- **Brundan–Ellis, §6 (after Definition 6.5).** Graded `(Q, Π)`-supercategories, graded
superfunctors and graded supernatural transformations form a 2-supercategory
`(Q, Π)-𝔊𝔖ℭ𝔞𝔱`. -/
instance instTwoSupercategory : TwoSupercategory R (QPiGSCat.{w, v, u} R) where
  whiskerLeft_id F G := TwoSupercategory.whiskerLeft_id (R := R) (B := GSCat R) F G
  whiskerLeft_comp F _ _ _ y z := TwoSupercategory.whiskerLeft_comp (R := R) (B := GSCat R) F y z
  id_whiskerLeft y := TwoSupercategory.id_whiskerLeft (R := R) (B := GSCat R) y
  comp_whiskerLeft F G _ _ y := TwoSupercategory.comp_whiskerLeft (R := R) (B := GSCat R) F G y
  id_whiskerRight F G := TwoSupercategory.id_whiskerRight (R := R) (B := GSCat R) F G
  comp_whiskerRight x z G := TwoSupercategory.comp_whiskerRight (R := R) (B := GSCat R) x z G
  whiskerRight_id x := TwoSupercategory.whiskerRight_id (R := R) (B := GSCat R) x
  whiskerRight_comp x G H := TwoSupercategory.whiskerRight_comp (R := R) (B := GSCat R) x G H
  whisker_assoc F _ _ y H := TwoSupercategory.whisker_assoc (R := R) (B := GSCat R) F y H
  pentagon F G H K := TwoSupercategory.pentagon (R := R) (B := GSCat R) F G H K
  triangle F G := TwoSupercategory.triangle (R := R) (B := GSCat R) F G
  whiskerLeft_add F _ _ y z := TwoSupercategory.whiskerLeft_add (R := R) (B := GSCat R) F y z
  add_whiskerRight x z G := TwoSupercategory.add_whiskerRight (R := R) (B := GSCat R) x z G
  whiskerLeft_smul F _ _ r y := TwoSupercategory.whiskerLeft_smul (B := GSCat R) F r y
  smul_whiskerRight r x G := TwoSupercategory.smul_whiskerRight (B := GSCat R) r x G
  whiskerLeft_mem F _ _ _ _ hy := TwoSupercategory.whiskerLeft_mem (B := GSCat R) F hy
  whiskerRight_mem G hx := TwoSupercategory.whiskerRight_mem (B := GSCat R) G hx
  super_interchange hx hy := TwoSupercategory.super_interchange (B := GSCat R) hx hy
  associator_hom_mem F G H := TwoSupercategory.associator_hom_mem (B := GSCat R) F G H
  leftUnitor_hom_mem F := TwoSupercategory.leftUnitor_hom_mem (B := GSCat R) F
  rightUnitor_hom_mem F := TwoSupercategory.rightUnitor_hom_mem (B := GSCat R) F

/-- `(Q, Π)-𝔊𝔖ℭ𝔞𝔱` is a graded 2-supercategory. -/
instance instGradedTwoSupercategory : GradedTwoSupercategory R (QPiGSCat.{w, v, u} R) where
  whiskerLeft_mem_degree F _ _ _ _ hη :=
    GradedTwoSupercategory.whiskerLeft_mem_degree (R := R) (B := GSCat R) F hη
  whiskerRight_mem_degree h hη :=
    GradedTwoSupercategory.whiskerRight_mem_degree (R := R) (B := GSCat R) h hη
  associator_hom_mem_degree F G H :=
    GradedTwoSupercategory.associator_hom_mem_degree (R := R) (B := GSCat R) F G H
  leftUnitor_hom_mem_degree F :=
    GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) (B := GSCat R) F
  rightUnitor_hom_mem_degree F :=
    GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) (B := GSCat R) F

/-- `(Q, Π)-𝔊𝔖ℭ𝔞𝔱` is a strict 2-supercategory. -/
instance instStrict : BicategoryStruct.Strict (QPiGSCat.{w, v, u} R) where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

/-! ### The (Q, Π)-2-structure -/

open GradedHom QPiSupercategory PiSupercategory

/-- `Π_A`, as a 1-morphism of `(Q, Π)-𝔊𝔖ℭ𝔞𝔱`. -/
def piHom (A : QPiGSCat.{w, v, u} R) : A ⟶ A := ⟨⟨⟨PiSupercategory.pi (R := R) (C := A)⟩⟩⟩

/-- `Q_A`, as a 1-morphism of `(Q, Π)-𝔊𝔖ℭ𝔞𝔱`. -/
def qHom (A : QPiGSCat.{w, v, u} R) : A ⟶ A := ⟨⟨⟨QPiSupercategory.Q (R := R) (C := A)⟩⟩⟩

/-- `Q_A⁻¹`, as a 1-morphism of `(Q, Π)-𝔊𝔖ℭ𝔞𝔱`. -/
def qinvHom (A : QPiGSCat.{w, v, u} R) : A ⟶ A := ⟨⟨⟨QPiSupercategory.Qinv (R := R) (C := A)⟩⟩⟩

section Iso

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C]
  [GradedSupercategory R C] [QPiSupercategory R C]

theorem ζ_inv_isSupernatural :
    IsSupernatural R 1 (F := 𝟭 C) (G := PiSupercategory.pi (R := R)) fun X =>
      (PiSupercategory.ζ (R := R) X).inv :=
  IsSupernatural.of_twist (fun X => ζ_inv_mem X) fun {X Y} f => by
    rw [pi_map_eq, twist_twist, Iso.inv_hom_id_assoc]; rfl

theorem σ_inv_isSupernatural :
    IsSupernatural R 0 (F := 𝟭 C) (G := QPiSupercategory.Q (R := R)) fun X =>
      (QPiSupercategory.σ (R := R) X).inv :=
  IsSupernatural.of_twist (fun X => σ_inv_mem X) fun {X Y} f => by
    rw [twist_zero, Q_map_eq, Iso.inv_hom_id_assoc]; rfl

theorem σbar_inv_isSupernatural :
    IsSupernatural R 0 (F := 𝟭 C) (G := QPiSupercategory.Qinv (R := R)) fun X =>
      (QPiSupercategory.σbar (R := R) X).inv :=
  IsSupernatural.of_twist (fun X => σbar_inv_mem X) fun {X Y} f => by
    rw [twist_zero, Qinv_map_eq, Iso.inv_hom_id_assoc]; rfl

end Iso

variable (A : QPiGSCat.{w, v, u} R)

theorem ζ_hom_isGradedSupernatural :
    IsGradedSupernatural R 1 0 (F := PiSupercategory.pi (R := R) (C := A)) (G := 𝟭 A) fun X =>
      (PiSupercategory.ζ (R := R) X).hom :=
  ⟨PiSupercategory.ζ_isSupernatural, fun X => ζ_hom_mem_degree X⟩

theorem ζ_inv_isGradedSupernatural :
    IsGradedSupernatural R 1 (-0) (F := 𝟭 A) (G := PiSupercategory.pi (R := R)) fun X =>
      (PiSupercategory.ζ (R := R) X).inv :=
  ⟨ζ_inv_isSupernatural, fun X => by rw [neg_zero]; exact ζ_inv_mem_degree X⟩

theorem σ_hom_isGradedSupernatural :
    IsGradedSupernatural R 0 (-1) (F := QPiSupercategory.Q (R := R) (C := A)) (G := 𝟭 A) fun X =>
      (QPiSupercategory.σ (R := R) X).hom :=
  ⟨QPiSupercategory.σ_isSupernatural, fun X => σ_hom_mem_degree X⟩

theorem σ_inv_isGradedSupernatural :
    IsGradedSupernatural R 0 (-(-1)) (F := 𝟭 A) (G := QPiSupercategory.Q (R := R)) fun X =>
      (QPiSupercategory.σ (R := R) X).inv :=
  ⟨σ_inv_isSupernatural, fun X => by rw [neg_neg]; exact σ_inv_mem_degree X⟩

theorem σbar_hom_isGradedSupernatural :
    IsGradedSupernatural R 0 1 (F := QPiSupercategory.Qinv (R := R) (C := A)) (G := 𝟭 A) fun X =>
      (QPiSupercategory.σbar (R := R) X).hom :=
  ⟨QPiSupercategory.σbar_isSupernatural, fun X => σbar_hom_mem_degree X⟩

theorem σbar_inv_isGradedSupernatural :
    IsGradedSupernatural R 0 (-1) (F := 𝟭 A) (G := QPiSupercategory.Qinv (R := R)) fun X =>
      (QPiSupercategory.σbar (R := R) X).inv :=
  ⟨σbar_inv_isSupernatural, fun X => σbar_inv_mem_degree X⟩

/-- The odd supernatural isomorphism `ζ_A : Π_A ⇒ I_A` of degree `0`, as a 2-isomorphism. -/
def ζHom : piHom A ≅ 𝟙 A :=
  isoOfHomogeneous (x := fun X => PiSupercategory.ζ (R := R) (C := A) X)
    (ζ_hom_isGradedSupernatural A) (ζ_inv_isGradedSupernatural A)

/-- The even supernatural isomorphism `σ_A : Q_A ⇒ I_A` of degree `-1`, as a 2-isomorphism. -/
def σHom : qHom A ≅ 𝟙 A :=
  isoOfHomogeneous (x := fun X => QPiSupercategory.σ (R := R) (C := A) X)
    (σ_hom_isGradedSupernatural A) (σ_inv_isGradedSupernatural A)

/-- The even supernatural isomorphism `σ̄_A : Q_A⁻¹ ⇒ I_A` of degree `1`, as a 2-isomorphism. -/
def σbarHom : qinvHom A ≅ 𝟙 A :=
  isoOfHomogeneous (x := fun X => QPiSupercategory.σbar (R := R) (C := A) X)
    (σbar_hom_isGradedSupernatural A) (σbar_inv_isGradedSupernatural A)

/-- `(Q, Π)-𝔊𝔖ℭ𝔞𝔱` is a Π-2-supercategory with `π_A := Π_A` and `ζ_A` the given odd
supernatural isomorphism. -/
instance instPiTwoSupercategory : PiTwoSupercategory R (QPiGSCat.{w, v, u} R) where
  pi := piHom
  ζ := ζHom
  ζ_hom_mem A := ofHomogeneous_mem (ζ_hom_isGradedSupernatural A)

/-- **Brundan–Ellis, §6 (after Definition 6.5).** `(Q, Π)-𝔊𝔖ℭ𝔞𝔱` is a graded
`(Q, Π)`-2-supercategory, with `q_A := Q_A`, `q_A⁻¹ := Q_A⁻¹`, `π_A := Π_A` and `σ_A`, `σ̄_A`,
`ζ_A` the given supernatural isomorphisms. -/
instance instQPiTwoSupercategory : QPiTwoSupercategory R (QPiGSCat.{w, v, u} R) where
  pi := piHom
  ζ := ζHom
  ζ_hom_mem A := ofHomogeneous_mem (ζ_hom_isGradedSupernatural A)
  ζ_hom_mem_degree A := ofHomogeneous_mem_degree (ζ_hom_isGradedSupernatural A)
  q := qHom
  qinv := qinvHom
  σ := σHom
  σbar := σbarHom
  σ_hom_mem A := ofHomogeneous_mem (σ_hom_isGradedSupernatural A)
  σ_hom_mem_degree A := ofHomogeneous_mem_degree (σ_hom_isGradedSupernatural A)
  σbar_hom_mem A := ofHomogeneous_mem (σbar_hom_isGradedSupernatural A)
  σbar_hom_mem_degree A := ofHomogeneous_mem_degree (σbar_hom_isGradedSupernatural A)

@[simp] theorem ζ_hom_app_one (A : QPiGSCat.{w, v, u} R) (X : A) :
    (PiTwoSupercategory.ζ (R := R) A).hom.1.app 1 X = (PiSupercategory.ζ (R := R) X).hom := rfl

@[simp] theorem σ_hom_app_zero (A : QPiGSCat.{w, v, u} R) (X : A) :
    (QPiTwoSupercategory.σ (R := R) A).hom.1.app 0 X = (QPiSupercategory.σ (R := R) X).hom := rfl

@[simp] theorem σbar_hom_app_zero (A : QPiGSCat.{w, v, u} R) (X : A) :
    (QPiTwoSupercategory.σbar (R := R) A).hom.1.app 0 X =
      (QPiSupercategory.σbar (R := R) X).hom := rfl

end QPiGSCat

end StringDiagrams

end
