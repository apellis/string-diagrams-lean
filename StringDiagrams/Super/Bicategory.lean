import StringDiagrams.Super.Monoidal
import Mathlib.CategoryTheory.Bicategory.Strict

/-!
# 2-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definitions 2.1 and 2.2.

A *2-supercategory* (Definition 2.2(i)) has objects, a supercategory `Hom(λ, μ)` of
1-morphisms and 2-morphisms for each pair of objects, identity 1-morphisms, horizontal
composition superfunctors `T : Hom(μ, ν) ⊠ Hom(λ, μ) → Hom(λ, ν)`, and even supernatural
isomorphisms `a`, `l`, `r` satisfying the pentagon and triangle axioms. A *strict
2-supercategory* (Definition 2.1) is a category enriched in the monoidal category `SCat` of
supercategories with the product `⊠`; as the paper notes after Definition 2.2, this is the
same as a 2-supercategory whose coherence maps are identities.

Because of the sign in the composition of `⊠`, horizontal composition satisfies the *super
interchange law* `(vu) ∘ (yx) = (-1)^{|u||y|} (v ∘ y)(u ∘ x)` rather than the ordinary one,
so a 2-supercategory is not a bicategory. Mathlib's `Bicategory` has the ordinary interchange
law as its axiom `whisker_exchange`, and Mathlib has no separate class of bicategory data.

## Design

* `BicategoryStruct B`: the data fields of Mathlib's `Bicategory` (category structure on
  1-morphisms, hom categories, whiskerings, associator and unitors), without axioms.
  `bicategoryStructOfBicategory` extracts it from a Mathlib bicategory.
* `TwoSupercategory R B`: a `Prop` class of axioms, for hom categories that are `R`-linear
  supercategories: all axioms of Mathlib's `Bicategory` except `whisker_exchange`, which is
  replaced by the super interchange law for homogeneous 2-morphisms
  `η ▷ h ≫ g ◁ θ = (-1)^{|η||θ|} • (f ◁ θ ≫ η ▷ i)` (for `η : f ⟶ g`, `θ : h ⟶ i`); together
  with linearity and evenness of the whiskerings and evenness of the coherence maps. This is
  Definition 2.2(i) unpacked, exactly as `MonoidalSupercategory` unpacks Definition 1.4(i):
  the superfunctor `T` is determined by the whiskerings, its functoriality on `⊠` is the
  functoriality of the whiskerings plus the super interchange law, and the naturality of the
  even coherence maps is Mathlib's axioms `comp_whiskerLeft`, `whisker_assoc`,
  `whiskerRight_comp`, `id_whiskerLeft`, `whiskerRight_id`.
* `BicategoryStruct.Strict B`: the coherence maps are identities (as Mathlib's
  `Bicategory.Strict`). A strict 2-supercategory (Definition 2.1) is a `TwoSupercategory`
  with `BicategoryStruct.Strict`.

The notations `f ◁ η`, `η ▷ h` for the whiskerings are scoped in `BicategoryStruct`.

## Conventions

With 1-morphisms composed in diagrammatic order (`F ≫ G` is the paper's `GF`), the paper's
horizontal composite `yx : GF ⇒ KH` of `x : F ⇒ H` and `y : G ⇒ K` is
`TwoSupercategory.hcomp x y = x ▷ G ≫ H ◁ y` (the paper's `yH ∘ Gx`), which is also Mathlib's
`Bicategory.hcomp` convention. The axiom `super_interchange` is the paper's
`yH ∘ Gx = (-1)^{|x||y|} Kx ∘ yF`, and the super interchange law of Section 2 is
`TwoSupercategory.hcomp_comp_hcomp`.

## Main definitions and results

* `BicategoryStruct`, `TwoSupercategory` (Definition 2.2(i)), `BicategoryStruct.Strict`
  (Definition 2.1 with `TwoSupercategory`).
* `TwoSupercategory.hcomp_comp_hcomp`: the super interchange law.
* `TwoSupercategory.toBicategory`: a 2-supercategory without odd 2-morphisms is a bicategory
  in the sense of Mathlib, with the same data.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w v u w₁

/-- The data of a bicategory: the data fields of Mathlib's `Bicategory`, without its axioms. -/
class BicategoryStruct (B : Type u) extends CategoryStruct.{v} B where
  /-- The category structure on the collection of 1-morphisms. -/
  homCategory : ∀ a b : B, Category.{w} (a ⟶ b) := by infer_instance
  /-- Left whiskering. -/
  whiskerLeft {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) : f ≫ g ⟶ f ≫ h
  /-- Right whiskering. -/
  whiskerRight {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : f ≫ h ⟶ g ≫ h
  /-- The associator. -/
  associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (f ≫ g) ≫ h ≅ f ≫ g ≫ h
  /-- The left unitor. -/
  leftUnitor {a b : B} (f : a ⟶ b) : 𝟙 a ≫ f ≅ f
  /-- The right unitor. -/
  rightUnitor {a b : B} (f : a ⟶ b) : f ≫ 𝟙 b ≅ f

attribute [instance] BicategoryStruct.homCategory

namespace BicategoryStruct

@[inherit_doc] scoped infixr:81 " ◁ " => BicategoryStruct.whiskerLeft
@[inherit_doc] scoped infixl:81 " ▷ " => BicategoryStruct.whiskerRight

end BicategoryStruct

open BicategoryStruct

/-- The data of a bicategory in the sense of Mathlib. -/
@[reducible]
def bicategoryStructOfBicategory (B : Type u) [Bicategory.{w, v} B] :
    BicategoryStruct.{w, v} B where
  homCategory := Bicategory.homCategory
  whiskerLeft := Bicategory.whiskerLeft
  whiskerRight := Bicategory.whiskerRight
  associator := Bicategory.associator
  leftUnitor := Bicategory.leftUnitor
  rightUnitor := Bicategory.rightUnitor

section Defs

variable (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]

/-- A 2-supercategory (Brundan–Ellis, Definition 2.2(i)), in unpacked form: the axioms of
Mathlib's `Bicategory` other than `whisker_exchange`, the super interchange law for
homogeneous 2-morphisms, linearity and evenness of the whiskerings, and evenness of the
coherence maps. See the module documentation. -/
class TwoSupercategory : Prop where
  whiskerLeft_id {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : f ◁ 𝟙 g = 𝟙 (f ≫ g)
  whiskerLeft_comp {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i) :
    f ◁ (η ≫ θ) = f ◁ η ≫ f ◁ θ
  id_whiskerLeft {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    𝟙 a ◁ η = (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv
  comp_whiskerLeft {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    (f ≫ g) ◁ η = (associator f g h).hom ≫ f ◁ g ◁ η ≫ (associator f g h').inv
  id_whiskerRight {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : 𝟙 f ▷ g = 𝟙 (f ≫ g)
  comp_whiskerRight {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c) :
    (η ≫ θ) ▷ i = η ▷ i ≫ θ ▷ i
  whiskerRight_id {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝟙 b = (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv
  whiskerRight_comp {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ (g ≫ h) = (associator f g h).inv ≫ η ▷ g ▷ h ≫ (associator f' g h).hom
  whisker_assoc {a b c d : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    (f ◁ η) ▷ h = (associator f g h).hom ≫ f ◁ (η ▷ h) ≫ (associator f g' h).inv
  pentagon {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (associator f g h).hom ▷ i ≫ (associator f (g ≫ h) i).hom ≫ f ◁ (associator g h i).hom =
      (associator (f ≫ g) h i).hom ≫ (associator f g (h ≫ i)).hom
  triangle {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (associator f (𝟙 b) g).hom ≫ f ◁ (leftUnitor g).hom = (rightUnitor f).hom ▷ g
  whiskerLeft_add {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h) :
    f ◁ (η + θ) = f ◁ η + f ◁ θ
  add_whiskerRight {a b c : B} {f g : a ⟶ b} (η θ : f ⟶ g) (h : b ⟶ c) :
    (η + θ) ▷ h = η ▷ h + θ ▷ h
  whiskerLeft_smul {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (r : R) (η : g ⟶ h) :
    f ◁ (r • η) = r • (f ◁ η)
  smul_whiskerRight {a b c : B} {f g : a ⟶ b} (r : R) (η : f ⟶ g) (h : b ⟶ c) :
    (r • η) ▷ h = r • (η ▷ h)
  whiskerLeft_mem {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} {p : ZMod 2} {η : g ⟶ h} :
    η ∈ parity (R := R) g h p → f ◁ η ∈ parity (R := R) (f ≫ g) (f ≫ h) p
  whiskerRight_mem {a b c : B} {f g : a ⟶ b} {p : ZMod 2} {η : f ⟶ g} (h : b ⟶ c) :
    η ∈ parity (R := R) f g p → η ▷ h ∈ parity (R := R) (f ≫ h) (g ≫ h) p
  /-- The super interchange law, in whiskering form. -/
  super_interchange {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} {p q : ZMod 2} {η : f ⟶ g}
    {θ : h ⟶ i} : η ∈ parity (R := R) f g p → θ ∈ parity (R := R) h i q →
      η ▷ h ≫ g ◁ θ = koszulSign p q • (f ◁ θ ≫ η ▷ i)
  associator_hom_mem {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).hom ∈ parity (R := R) ((f ≫ g) ≫ h) (f ≫ g ≫ h) 0
  leftUnitor_hom_mem {a b : B} (f : a ⟶ b) : (leftUnitor f).hom ∈ parity (R := R) (𝟙 a ≫ f) f 0
  rightUnitor_hom_mem {a b : B} (f : a ⟶ b) :
    (rightUnitor f).hom ∈ parity (R := R) (f ≫ 𝟙 b) f 0

/-- The coherence maps of bicategory data are identities (as in Mathlib's
`Bicategory.Strict`). A strict 2-supercategory (Brundan–Ellis, Definition 2.1) is a
`TwoSupercategory` whose data is strict. -/
class BicategoryStruct.Strict : Prop where
  id_comp : ∀ {a b : B} (f : a ⟶ b), 𝟙 a ≫ f = f
  comp_id : ∀ {a b : B} (f : a ⟶ b), f ≫ 𝟙 b = f
  assoc : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), (f ≫ g) ≫ h = f ≫ g ≫ h
  leftUnitor_eqToIso : ∀ {a b : B} (f : a ⟶ b), leftUnitor f = eqToIso (id_comp f)
  rightUnitor_eqToIso : ∀ {a b : B} (f : a ⟶ b), rightUnitor f = eqToIso (comp_id f)
  associator_eqToIso : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    associator f g h = eqToIso (assoc f g h)

end Defs

namespace TwoSupercategory

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- Horizontal composition: for `x : f ⟶ g` and `y : h ⟶ i`, the paper's `yx = yg ∘ hx`. -/
def hcomp {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (x : f ⟶ g) (y : h ⟶ i) : f ≫ h ⟶ g ≫ i :=
  x ▷ h ≫ g ◁ y

theorem hcomp_mem {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} {p q : ZMod 2} {x : f ⟶ g}
    {y : h ⟶ i} (hx : x ∈ parity (R := R) f g p) (hy : y ∈ parity (R := R) h i q) :
    hcomp x y ∈ parity (R := R) (f ≫ h) (g ≫ i) (p + q) :=
  comp_mem (whiskerRight_mem h hx) (whiskerLeft_mem g hy)

/-- The other expression of the horizontal composite: `yx = (-1)^{|x||y|} iy ∘ xf`. -/
theorem hcomp_eq {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} {p q : ZMod 2} {x : f ⟶ g}
    {y : h ⟶ i} (hx : x ∈ parity (R := R) f g p) (hy : y ∈ parity (R := R) h i q) :
    hcomp x y = koszulSign p q • (f ◁ y ≫ x ▷ i) :=
  super_interchange hx hy

/-- **The super interchange law** in a 2-supercategory (Brundan–Ellis, Section 2):
`(vu) ∘ (yx) = (-1)^{|u||y|} (v ∘ y)(u ∘ x)`. -/
theorem hcomp_comp_hcomp {a b c : B} {f g k : a ⟶ b} {h i l : b ⟶ c} {pu py : ZMod 2}
    (x : f ⟶ g) (u : g ⟶ k) (y : h ⟶ i) (v : i ⟶ l) (hu : u ∈ parity (R := R) g k pu)
    (hy : y ∈ parity (R := R) h i py) :
    hcomp x y ≫ hcomp u v = koszulSign pu py • hcomp (x ≫ u) (y ≫ v) := by
  simp only [hcomp, Category.assoc]
  rw [← Category.assoc (g ◁ y), ← koszulSign_smul_smul pu py (g ◁ y ≫ u ▷ i),
    ← super_interchange hu hy, Linear.smul_comp, Linear.comp_smul,
    comp_whiskerRight (R := R), whiskerLeft_comp (R := R)]
  simp only [Category.assoc]

/-! ## 2-supercategories without odd 2-morphisms -/

variable (R B) in
/-- There are no odd 2-morphisms. -/
def NoOdd : Prop := ∀ (a b : B) (f g : a ⟶ b), parity (R := R) f g 1 = ⊥

omit [TwoSupercategory R B] in
theorem mem_parity_zero_of_noOdd (hB : NoOdd R B) {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    η ∈ parity (R := R) f g 0 :=
  MonoidalSupercategory.mem_parity_zero_of_noOdd (C := a ⟶ b) (hB a b) η

theorem whisker_exchange_of_noOdd (hB : NoOdd R B) {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c}
    (η : f ⟶ g) (θ : h ⟶ i) : f ◁ θ ≫ η ▷ i = η ▷ h ≫ g ◁ θ := by
  rw [super_interchange (mem_parity_zero_of_noOdd hB η) (mem_parity_zero_of_noOdd hB θ),
    koszulSign_zero_left, one_smul]

variable (R) in
/-- A 2-supercategory without odd 2-morphisms is a bicategory in the sense of Mathlib, with
the same data. -/
@[reducible]
def toBicategory (hB : NoOdd R B) : Bicategory.{w, v} B where
  homCategory := BicategoryStruct.homCategory
  whiskerLeft := BicategoryStruct.whiskerLeft
  whiskerRight := BicategoryStruct.whiskerRight
  associator := BicategoryStruct.associator
  leftUnitor := BicategoryStruct.leftUnitor
  rightUnitor := BicategoryStruct.rightUnitor
  whiskerLeft_id := whiskerLeft_id (R := R)
  whiskerLeft_comp := whiskerLeft_comp (R := R)
  id_whiskerLeft := id_whiskerLeft (R := R)
  comp_whiskerLeft := comp_whiskerLeft (R := R)
  id_whiskerRight := id_whiskerRight (R := R)
  comp_whiskerRight := comp_whiskerRight (R := R)
  whiskerRight_id := whiskerRight_id (R := R)
  whiskerRight_comp := whiskerRight_comp (R := R)
  whisker_assoc := whisker_assoc (R := R)
  whisker_exchange := whisker_exchange_of_noOdd hB
  pentagon := pentagon (R := R)
  triangle := triangle (R := R)

/-- A strict 2-supercategory without odd 2-morphisms is a strict bicategory. -/
theorem toBicategory_strict [BicategoryStruct.Strict B] (hB : NoOdd R B) :
    letI := toBicategory R hB
    Bicategory.Strict B :=
  letI := toBicategory R hB
  { id_comp := BicategoryStruct.Strict.id_comp
    comp_id := BicategoryStruct.Strict.comp_id
    assoc := BicategoryStruct.Strict.assoc
    leftUnitor_eqToIso := BicategoryStruct.Strict.leftUnitor_eqToIso
    rightUnitor_eqToIso := BicategoryStruct.Strict.rightUnitor_eqToIso
    associator_eqToIso := BicategoryStruct.Strict.associator_eqToIso }

end TwoSupercategory

end StringDiagrams

end
