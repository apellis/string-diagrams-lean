import StringDiagrams.Super.Functor
import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Monoidal supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.4.

A monoidal supercategory is a supercategory `A` with a superfunctor `- ⊗ - : A ⊠ A → A`, a
unit object and even supernatural isomorphisms `a`, `l`, `r` satisfying the pentagon and
triangle axioms. In `A ⊠ A` composition carries the sign `(f ⊗ g) ∘ (h ⊗ k) =
(-1)^{|g||h|} (f ∘ h) ⊗ (g ∘ k)`; consequently the tensor product of morphisms satisfies
the *super interchange law* (1.1), and a monoidal supercategory is not a monoidal category in
the usual sense. Mathlib's `MonoidalCategory` contains the ordinary interchange law (through
its axiom `tensor_comp`), so it cannot be used when there are odd morphisms.

## The unpacked definition

We use Mathlib's data class `MonoidalCategoryStruct` (tensor product of objects, left and
right whiskering, tensor product of morphisms, unit, associator and unitors) and a `Prop`
class `MonoidalSupercategory R C` of axioms, which is Definition 1.4(i) unpacked:

* A superfunctor `⊗ : A ⊠ A → A` is determined by its restrictions to the morphisms
  `f ⊗ 1_Y` and `1_X ⊗ g` (the whiskerings `f ▷ Y`, `X ◁ g`), since
  `f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)` in `A ⊠ A`. That `⊗` is a functor on `A ⊠ A` amounts to:
  each whiskering is a functor (`whiskerLeft_id`, `whiskerLeft_comp`, `id_whiskerRight`,
  `comp_whiskerRight`), and the two whiskerings commute up to the Koszul sign
  (`super_interchange`: `(f ▷ Y) ≫ (X' ◁ g) = (-1)^{|f||g|} • ((X ◁ g) ≫ (f ▷ Y'))` for
  homogeneous `f`, `g`), which is the composition rule of `A ⊠ A` for
  `(1 ⊗ g) ∘ (f ⊗ 1)`. That `⊗` is `SVec`-enriched amounts to: each whiskering is
  `R`-linear and preserves parities.
* That `a`, `l`, `r` are even supernatural isomorphisms amounts to: their components are even
  (`associator_hom_mem`, `leftUnitor_hom_mem`, `rightUnitor_hom_mem`) and they are natural
  (Mathlib's axioms `associator_naturality`, `leftUnitor_naturality`,
  `rightUnitor_naturality`; no sign appears since they are even).
* The coherence axioms are Mathlib's `pentagon` and `triangle`.

Thus `MonoidalSupercategory` consists of all the axioms of Mathlib's `MonoidalCategory` except
`tensor_comp` (equivalently, except the interchange law `whisker_exchange`, from which Mathlib
derives it), together with: functoriality of the whiskerings (which Mathlib derives from
`tensor_comp`), the super interchange law, linearity and evenness of the whiskerings, and
evenness of the coherence maps. The redundant axiom `tensor_id` is a theorem here.

## Conventions for the tensor product of morphisms

Mathlib's `tensorHom f g` is `f ▷ X₂ ≫ Y₁ ◁ g` (axiom `tensorHom_def`, kept here so that the
purely even case is literally Mathlib's). The paper's `f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)` is
`X₁ ◁ g ≫ f ▷ Y₂`, which we call `MonoidalSupercategory.superTensorHom f g`; for homogeneous
`f`, `g` the two differ by the sign `(-1)^{|f||g|}` (`tensorHom_eq_superTensorHom`). The
super interchange law (1.1) is `superTensorHom_comp_superTensorHom`; its form for Mathlib's
`tensorHom` is `tensorHom_comp_tensorHom`.

## Main definitions and results

* `MonoidalSupercategory R C` (Definition 1.4(i)); `MonoidalSupercategory.IsStrict` (strict
  monoidal supercategories).
* `superTensorHom_comp_superTensorHom`: the super interchange law (1.1).
* `MonoidalSupercategory.toMonoidalCategory`, `MonoidalSupercategory.ofMonoidalCategory`: for
  a supercategory without odd morphisms, monoidal supercategory structures are the same as
  Mathlib monoidal structures with linear tensor product.
* `MonoidalSuperfunctor` (Definition 1.4(ii)), `MonoidalSuperfunctor.id`;
  `MonoidalNatTrans` (Definition 1.4(iii)), `MonoidalNatTrans.id`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe w v u v₂ u₂

variable (R : Type w) [CommRing R] (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
  [Supercategory R C]

/-- A monoidal supercategory (Brundan–Ellis, Definition 1.4(i)), in unpacked form: the axioms
of Mathlib's `MonoidalCategory` other than `tensor_comp`, functoriality of the whiskerings,
the super interchange law for homogeneous morphisms, linearity and evenness of the
whiskerings, and evenness of the coherence maps. See the module documentation. -/
class MonoidalSupercategory [MonoidalCategoryStruct C] : Prop where
  tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f ⊗ g = f ▷ X₂ ≫ Y₁ ◁ g
  whiskerLeft_id (X Y : C) : X ◁ 𝟙 Y = 𝟙 (X ⊗ Y)
  id_whiskerRight (X Y : C) : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)
  whiskerLeft_comp (X : C) {Y Z W : C} (f : Y ⟶ Z) (g : Z ⟶ W) :
    X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g
  comp_whiskerRight {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (W : C) :
    (f ≫ g) ▷ W = f ▷ W ≫ g ▷ W
  whiskerLeft_add (X : C) {Y Z : C} (f g : Y ⟶ Z) : X ◁ (f + g) = X ◁ f + X ◁ g
  add_whiskerRight {X Y : C} (f g : X ⟶ Y) (Z : C) : (f + g) ▷ Z = f ▷ Z + g ▷ Z
  whiskerLeft_smul (X : C) {Y Z : C} (r : R) (f : Y ⟶ Z) : X ◁ (r • f) = r • (X ◁ f)
  smul_whiskerRight {X Y : C} (r : R) (f : X ⟶ Y) (Z : C) : (r • f) ▷ Z = r • (f ▷ Z)
  whiskerLeft_mem (X : C) {Y Z : C} {p : ZMod 2} {f : Y ⟶ Z} :
    f ∈ parity (R := R) Y Z p → X ◁ f ∈ parity (R := R) (X ⊗ Y) (X ⊗ Z) p
  whiskerRight_mem {X Y : C} {p : ZMod 2} {f : X ⟶ Y} (Z : C) :
    f ∈ parity (R := R) X Y p → f ▷ Z ∈ parity (R := R) (X ⊗ Z) (Y ⊗ Z) p
  /-- The super interchange law, in whiskering form. -/
  super_interchange {X X' Y Y' : C} {p q : ZMod 2} {f : X ⟶ X'} {g : Y ⟶ Y'} :
    f ∈ parity (R := R) X X' p → g ∈ parity (R := R) Y Y' q →
      f ▷ Y ≫ X' ◁ g = koszulSign p q • (X ◁ g ≫ f ▷ Y')
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ (f₂ ⊗ f₃))
  leftUnitor_naturality {X Y : C} (f : X ⟶ Y) :
    𝟙_ C ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f
  rightUnitor_naturality {X Y : C} (f : X ⟶ Y) :
    f ▷ 𝟙_ C ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f
  pentagon (W X Y Z : C) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom
  triangle (X Y : C) : (α_ X (𝟙_ C) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y
  associator_hom_mem (X Y Z : C) :
    (α_ X Y Z).hom ∈ parity (R := R) ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)) 0
  leftUnitor_hom_mem (X : C) : (λ_ X).hom ∈ parity (R := R) (𝟙_ C ⊗ X) X 0
  rightUnitor_hom_mem (X : C) : (ρ_ X).hom ∈ parity (R := R) (X ⊗ 𝟙_ C) X 0

/-- A monoidal structure is strict if its associators and unitors are identities, i.e.
`eqToIso`s of equalities of objects. -/
class MonoidalSupercategory.IsStrict [MonoidalCategoryStruct C] : Prop where
  tensor_assoc (X Y Z : C) : (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)
  unit_tensor (X : C) : 𝟙_ C ⊗ X = X
  tensor_unit (X : C) : X ⊗ 𝟙_ C = X
  associator_eq (X Y Z : C) : α_ X Y Z = eqToIso (tensor_assoc X Y Z)
  leftUnitor_eq (X : C) : λ_ X = eqToIso (unit_tensor X)
  rightUnitor_eq (X : C) : ρ_ X = eqToIso (tensor_unit X)

namespace MonoidalSupercategory

variable {R C} [MonoidalCategoryStruct C] [MonoidalSupercategory R C]

/-! ## Linearity of whiskering -/

section Linear

variable (R)
include R

theorem whiskerLeft_zero (X : C) {Y Z : C} : X ◁ (0 : Y ⟶ Z) = 0 := by
  have h := whiskerLeft_add (R := R) X (0 : Y ⟶ Z) 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem zero_whiskerRight {X Y : C} (Z : C) : (0 : X ⟶ Y) ▷ Z = 0 := by
  have h := add_whiskerRight (R := R) (0 : X ⟶ Y) 0 Z
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem whiskerLeft_neg (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ (-f) = -(X ◁ f) := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← whiskerLeft_add (R := R), neg_add_cancel, whiskerLeft_zero R]

theorem neg_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) : (-f) ▷ Z = -(f ▷ Z) := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← add_whiskerRight (R := R), neg_add_cancel, zero_whiskerRight R]

theorem whiskerLeft_zsmul (X : C) {Y Z : C} (n : ℤ) (f : Y ⟶ Z) : X ◁ (n • f) = n • (X ◁ f) := by
  induction n using Int.induction_on with
  | hz => simp [whiskerLeft_zero R]
  | hp n ih => simp only [add_smul, one_smul, whiskerLeft_add (R := R), ih]
  | hn n ih =>
    rw [sub_smul, sub_smul, sub_eq_add_neg, sub_eq_add_neg, one_smul, one_smul,
      whiskerLeft_add (R := R), ih, whiskerLeft_neg R]

theorem zsmul_whiskerRight {X Y : C} (n : ℤ) (f : X ⟶ Y) (Z : C) : (n • f) ▷ Z = n • (f ▷ Z) := by
  induction n using Int.induction_on with
  | hz => simp [zero_whiskerRight R]
  | hp n ih => simp only [add_smul, one_smul, add_whiskerRight (R := R), ih]
  | hn n ih =>
    rw [sub_smul, sub_smul, sub_eq_add_neg, sub_eq_add_neg, one_smul, one_smul,
      add_whiskerRight (R := R), ih, neg_whiskerRight R]

end Linear

variable (R) in
include R in
theorem tensor_id (X Y : C) : 𝟙 X ⊗ 𝟙 Y = 𝟙 (X ⊗ Y) := by
  rw [tensorHom_def (R := R), id_whiskerRight (R := R), whiskerLeft_id (R := R),
    Category.comp_id]

/-! ## The super interchange law -/

/-- The paper's tensor product of morphisms `f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)`, i.e. `g` is applied
first: `X₁ ◁ g ≫ f ▷ Y₂`. -/
def superTensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : X₁ ⊗ X₂ ⟶ Y₁ ⊗ Y₂ :=
  X₁ ◁ g ≫ f ▷ Y₂

/-- The tensor product of homogeneous morphisms is homogeneous, with parities adding. -/
theorem superTensorHom_mem {X₁ Y₁ X₂ Y₂ : C} {p q : ZMod 2} {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂}
    (hf : f ∈ parity (R := R) X₁ Y₁ p) (hg : g ∈ parity (R := R) X₂ Y₂ q) :
    superTensorHom f g ∈ parity (R := R) (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (p + q) := by
  rw [add_comm]
  exact comp_mem (whiskerLeft_mem X₁ hg) (whiskerRight_mem Y₂ hf)

theorem tensorHom_mem {X₁ Y₁ X₂ Y₂ : C} {p q : ZMod 2} {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂}
    (hf : f ∈ parity (R := R) X₁ Y₁ p) (hg : g ∈ parity (R := R) X₂ Y₂ q) :
    f ⊗ g ∈ parity (R := R) (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (p + q) := by
  rw [tensorHom_def (R := R)]
  exact comp_mem (whiskerRight_mem X₂ hf) (whiskerLeft_mem Y₁ hg)

/-- Mathlib's `tensorHom` and the paper's tensor product differ by the Koszul sign. -/
theorem tensorHom_eq_superTensorHom {X₁ Y₁ X₂ Y₂ : C} {p q : ZMod 2} {f : X₁ ⟶ Y₁}
    {g : X₂ ⟶ Y₂} (hf : f ∈ parity (R := R) X₁ Y₁ p) (hg : g ∈ parity (R := R) X₂ Y₂ q) :
    f ⊗ g = koszulSign p q • superTensorHom f g := by
  rw [tensorHom_def (R := R), super_interchange hf hg, superTensorHom]

/-- **The super interchange law** (Brundan–Ellis (1.1)): for homogeneous morphisms,
`(f ⊗ g) ∘ (h ⊗ k) = (-1)^{|g||h|} (f ∘ h) ⊗ (g ∘ k)`, for the paper's tensor product. -/
theorem superTensorHom_comp_superTensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {pg ph : ZMod 2}
    (h : X₁ ⟶ Y₁) (k : X₂ ⟶ Y₂) (f : Y₁ ⟶ Z₁) (g : Y₂ ⟶ Z₂)
    (hh : h ∈ parity (R := R) X₁ Y₁ ph) (hg : g ∈ parity (R := R) Y₂ Z₂ pg) :
    superTensorHom h k ≫ superTensorHom f g =
      koszulSign pg ph • superTensorHom (h ≫ f) (k ≫ g) := by
  simp only [superTensorHom, Category.assoc]
  rw [← Category.assoc (h ▷ Y₂), super_interchange hh hg, Linear.smul_comp,
    Linear.comp_smul, koszulSign_comm, whiskerLeft_comp (R := R), comp_whiskerRight (R := R)]
  simp only [Category.assoc]

/-- The super interchange law for Mathlib's `tensorHom`:
`(h ⊗ k) ≫ (f ⊗ g) = (-1)^{|f||k|} (h ≫ f) ⊗ (k ≫ g)`. -/
theorem tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {pf pk : ZMod 2}
    (h : X₁ ⟶ Y₁) (k : X₂ ⟶ Y₂) (f : Y₁ ⟶ Z₁) (g : Y₂ ⟶ Z₂)
    (hf : f ∈ parity (R := R) Y₁ Z₁ pf) (hk : k ∈ parity (R := R) X₂ Y₂ pk) :
    (h ⊗ k) ≫ (f ⊗ g) = koszulSign pf pk • ((h ≫ f) ⊗ (k ≫ g)) := by
  simp only [tensorHom_def (R := R), Category.assoc]
  rw [← Category.assoc (Y₁ ◁ k), ← koszulSign_smul_smul pf pk (Y₁ ◁ k ≫ f ▷ Y₂),
    ← super_interchange hf hk, Linear.smul_comp, Linear.comp_smul, whiskerLeft_comp (R := R),
    comp_whiskerRight (R := R)]
  simp only [Category.assoc]

/-- The interchange law without sign when one of the morphisms is even. -/
theorem interchange_of_even_left {X X' Y Y' : C} {q : ZMod 2} {f : X ⟶ X'} {g : Y ⟶ Y'}
    (hf : f ∈ parity (R := R) X X' 0) (hg : g ∈ parity (R := R) Y Y' q) :
    f ▷ Y ≫ X' ◁ g = X ◁ g ≫ f ▷ Y' := by
  rw [super_interchange hf hg, koszulSign_zero_left, one_smul]

theorem interchange_of_even_right {X X' Y Y' : C} {p : ZMod 2} {f : X ⟶ X'} {g : Y ⟶ Y'}
    (hf : f ∈ parity (R := R) X X' p) (hg : g ∈ parity (R := R) Y Y' 0) :
    f ▷ Y ≫ X' ◁ g = X ◁ g ≫ f ▷ Y' := by
  rw [super_interchange hf hg, koszulSign_zero_right, one_smul]

/-- Odd morphisms anti-commute past each other. -/
theorem interchange_of_odd {X X' Y Y' : C} {f : X ⟶ X'} {g : Y ⟶ Y'}
    (hf : f ∈ parity (R := R) X X' 1) (hg : g ∈ parity (R := R) Y Y' 1) :
    f ▷ Y ≫ X' ◁ g = -(X ◁ g ≫ f ▷ Y') := by
  rw [super_interchange hf hg, koszulSign_one_one, neg_one_smul]

/-! ## Supercategories without odd morphisms -/

section Even

variable (R C) in
/-- A supercategory has no odd morphisms. -/
def NoOdd : Prop := ∀ X Y : C, parity (R := R) X Y 1 = ⊥

omit [MonoidalCategoryStruct C] [MonoidalSupercategory R C] in
/-- Without odd morphisms, every morphism is even. -/
theorem mem_parity_zero_of_noOdd (h : NoOdd R C) {X Y : C} (f : X ⟶ Y) :
    f ∈ parity (R := R) X Y 0 := by
  have hf : f ∈ ⨆ q, parity (R := R) X Y q := by
    rw [(isInternal (R := R) X Y).submodule_iSup_eq_top]; exact Submodule.mem_top
  refine (iSup_le fun q => ?_ : ⨆ q, parity (R := R) X Y q ≤ parity (R := R) X Y 0) hf
  rcases parity_eq_zero_or_one q with rfl | rfl
  · exact le_rfl
  · rw [h X Y]; exact bot_le

omit [MonoidalCategoryStruct C] [MonoidalSupercategory R C] in
theorem eq_zero_of_noOdd (h : NoOdd R C) {X Y : C} {f : X ⟶ Y}
    (hf : f ∈ parity (R := R) X Y 1) : f = 0 := by
  rw [h X Y] at hf; exact (Submodule.mem_bot R).mp hf

/-- Without odd morphisms, the interchange law holds for all morphisms. -/
theorem whisker_exchange_of_noOdd (h : NoOdd R C) {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    X ◁ g ≫ f ▷ Y' = f ▷ Y ≫ X' ◁ g :=
  (interchange_of_even_left (mem_parity_zero_of_noOdd h f) (mem_parity_zero_of_noOdd h g)).symm

variable (R) in
/-- A monoidal supercategory without odd morphisms is a monoidal category in the sense of
Mathlib, with the same data. -/
@[reducible]
def toMonoidalCategory (h : NoOdd R C) : MonoidalCategory C where
  tensorHom_def f g := tensorHom_def (R := R) f g
  tensor_id := tensor_id R
  tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ := by
    simp only [tensorHom_def (R := R), whiskerLeft_comp (R := R), comp_whiskerRight (R := R),
      Category.assoc]
    rw [← Category.assoc (g₁ ▷ X₂), ← whisker_exchange_of_noOdd h g₁ f₂]
    simp only [Category.assoc]
  whiskerLeft_id := whiskerLeft_id (R := R)
  id_whiskerRight := id_whiskerRight (R := R)
  associator_naturality := associator_naturality (R := R)
  leftUnitor_naturality := leftUnitor_naturality (R := R)
  rightUnitor_naturality := rightUnitor_naturality (R := R)
  pentagon := pentagon (R := R)
  triangle := triangle (R := R)

theorem toMonoidalPreadditive (h : NoOdd R C) :
    letI := toMonoidalCategory R h
    MonoidalPreadditive C :=
  letI := toMonoidalCategory R h
  { whiskerLeft_zero := whiskerLeft_zero R _
    zero_whiskerRight := zero_whiskerRight R _
    whiskerLeft_add := whiskerLeft_add (R := R) _
    add_whiskerRight f g := add_whiskerRight (R := R) f g _ }

theorem toMonoidalLinear (h : NoOdd R C) :
    letI := toMonoidalCategory R h
    letI := toMonoidalPreadditive h
    MonoidalLinear R C :=
  letI := toMonoidalCategory R h
  letI := toMonoidalPreadditive h
  { whiskerLeft_smul := whiskerLeft_smul
    smul_whiskerRight r _ _ f X := smul_whiskerRight r f X }

end Even

end MonoidalSupercategory

section OfMonoidal

variable {R C}

/-- A monoidal `R`-linear category in the sense of Mathlib, on a supercategory without odd
morphisms, is a monoidal supercategory. -/
theorem MonoidalSupercategory.ofMonoidalCategory [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear R C] (h : MonoidalSupercategory.NoOdd R C) : MonoidalSupercategory R C where
  tensorHom_def := MonoidalCategory.tensorHom_def
  whiskerLeft_id := MonoidalCategory.whiskerLeft_id
  id_whiskerRight := MonoidalCategory.id_whiskerRight
  whiskerLeft_comp := MonoidalCategory.whiskerLeft_comp
  comp_whiskerRight := MonoidalCategory.comp_whiskerRight
  whiskerLeft_add _ _ _ f g := MonoidalPreadditive.whiskerLeft_add f g
  add_whiskerRight f g _ := MonoidalPreadditive.add_whiskerRight f g
  whiskerLeft_smul := MonoidalLinear.whiskerLeft_smul
  smul_whiskerRight r f Z := MonoidalLinear.smul_whiskerRight r f Z
  whiskerLeft_mem X Y Z p f hf := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact MonoidalSupercategory.mem_parity_zero_of_noOdd h _
    · rw [MonoidalSupercategory.eq_zero_of_noOdd h hf, MonoidalPreadditive.whiskerLeft_zero]
      exact Submodule.zero_mem _
  whiskerRight_mem {X Y p f} Z hf := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact MonoidalSupercategory.mem_parity_zero_of_noOdd h _
    · rw [MonoidalSupercategory.eq_zero_of_noOdd h hf, MonoidalPreadditive.zero_whiskerRight]
      exact Submodule.zero_mem _
  super_interchange {X X' Y Y' p q f g} hf hg := by
    rcases koszulSign_eq_one_or p q with hs | ⟨rfl, rfl⟩
    · rw [hs, one_smul, whisker_exchange]
    · rw [MonoidalSupercategory.eq_zero_of_noOdd h hf]
      simp
  associator_naturality := MonoidalCategory.associator_naturality
  leftUnitor_naturality := MonoidalCategory.leftUnitor_naturality
  rightUnitor_naturality := MonoidalCategory.rightUnitor_naturality
  pentagon := MonoidalCategory.pentagon
  triangle := MonoidalCategory.triangle
  associator_hom_mem _ _ _ := MonoidalSupercategory.mem_parity_zero_of_noOdd h _
  leftUnitor_hom_mem _ := MonoidalSupercategory.mem_parity_zero_of_noOdd h _
  rightUnitor_hom_mem _ := MonoidalSupercategory.mem_parity_zero_of_noOdd h _

end OfMonoidal

/-! ## Monoidal superfunctors and monoidal natural transformations -/

section Functor

variable {R C} {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [MonoidalCategoryStruct C] [MonoidalCategoryStruct D]

variable (R) in
/-- A (strong) monoidal superfunctor (Brundan–Ellis, Definition 1.4(ii)): a superfunctor `F`
with an even supernatural isomorphism `c : (F -) ⊗ (F -) ≅ F (- ⊗ -)` (here `μIso`) and an
even isomorphism `i : 1 ≅ F 1` (here `εIso`), satisfying the associativity and unitality
axioms of a monoidal functor. Since `c` is even, its naturality carries no sign; as a natural
transformation between superfunctors on `A ⊠ A` it amounts to naturality in each variable
separately (`μ_natural_left`, `μ_natural_right`). The axioms mirror those of Mathlib's
`Functor.LaxMonoidal`. -/
structure MonoidalSuperfunctor (F : C ⥤ D) [F.Additive] [F.Linear R] [IsSuperfunctor R F] where
  /-- The coherence isomorphism `c_{X,Y} : F X ⊗ F Y ≅ F (X ⊗ Y)`. -/
  μIso : ∀ X Y : C, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)
  /-- The coherence isomorphism `i : 1 ≅ F 1`. -/
  εIso : 𝟙_ D ≅ F.obj (𝟙_ C)
  μ_mem : ∀ X Y : C, (μIso X Y).hom ∈ parity (R := R) _ _ 0
  ε_mem : εIso.hom ∈ parity (R := R) _ _ 0
  μ_natural_left : ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
    F.map f ▷ F.obj X' ≫ (μIso Y X').hom = (μIso X X').hom ≫ F.map (f ▷ X')
  μ_natural_right : ∀ {X Y : C} (X' : C) (f : X ⟶ Y),
    F.obj X' ◁ F.map f ≫ (μIso X' Y).hom = (μIso X' X).hom ≫ F.map (X' ◁ f)
  associativity : ∀ X Y Z : C,
    (μIso X Y).hom ▷ F.obj Z ≫ (μIso (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μIso Y Z).hom ≫
        (μIso X (Y ⊗ Z)).hom
  left_unitality : ∀ X : C,
    (λ_ (F.obj X)).hom = εIso.hom ▷ F.obj X ≫ (μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom
  right_unitality : ∀ X : C,
    (ρ_ (F.obj X)).hom = F.obj X ◁ εIso.hom ≫ (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom

namespace MonoidalSuperfunctor

variable [MonoidalSupercategory R C]

/-- The identity functor is a monoidal superfunctor. -/
def id : MonoidalSuperfunctor R (𝟭 C) where
  μIso X Y := Iso.refl _
  εIso := Iso.refl _
  μ_mem _ _ := id_mem _
  ε_mem := id_mem _
  μ_natural_left _ _ := by simp
  μ_natural_right _ _ := by simp
  associativity X Y Z := by
    simp [MonoidalSupercategory.id_whiskerRight (R := R),
      MonoidalSupercategory.whiskerLeft_id (R := R)]
  left_unitality X := by simp [MonoidalSupercategory.id_whiskerRight (R := R)]
  right_unitality X := by simp [MonoidalSupercategory.whiskerLeft_id (R := R)]

end MonoidalSuperfunctor

variable (R) in
/-- A monoidal natural transformation (Brundan–Ellis, Definition 1.4(iii)) between monoidal
superfunctors: an even supernatural transformation `x : F ⇒ G` (a natural transformation with
even components) with `x_{X ⊗ Y} ∘ c_F = c_G ∘ (x_X ⊗ x_Y)` and `x_1 ∘ i_F = i_G`. Since `x` is
even, the two conventions for the tensor product of `x_X` and `x_Y` agree. (There are no
monoidal supernatural transformations of odd parity.) -/
structure MonoidalNatTrans {F G : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F]
    [G.Additive] [G.Linear R] [IsSuperfunctor R G] (cF : MonoidalSuperfunctor R F)
    (cG : MonoidalSuperfunctor R G) where
  /-- The underlying natural transformation. -/
  toNatTrans : F ⟶ G
  app_mem : ∀ X, toNatTrans.app X ∈ parity (R := R) (F.obj X) (G.obj X) 0
  tensor : ∀ X Y : C, (cF.μIso X Y).hom ≫ toNatTrans.app (X ⊗ Y) =
    (toNatTrans.app X ⊗ toNatTrans.app Y) ≫ (cG.μIso X Y).hom
  unit : cF.εIso.hom ≫ toNatTrans.app (𝟙_ C) = cG.εIso.hom

namespace MonoidalNatTrans

variable [MonoidalSupercategory R D]

/-- The identity monoidal natural transformation. -/
def id {F : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F]
    (cF : MonoidalSuperfunctor R F) : MonoidalNatTrans R cF cF where
  toNatTrans := 𝟙 F
  app_mem X := id_mem _
  tensor X Y := by
    simp [MonoidalSupercategory.tensor_id R]
  unit := by simp

/-- The underlying even supernatural transformation. -/
def toSuperNatTrans {F G : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F]
    [G.Additive] [G.Linear R] [IsSuperfunctor R G] {cF : MonoidalSuperfunctor R F}
    {cG : MonoidalSuperfunctor R G} (x : MonoidalNatTrans R cF cG) : SuperNatTrans R F G :=
  SuperNatTrans.ofNatTrans x.toNatTrans x.app_mem

end MonoidalNatTrans

end Functor

end StringDiagrams

end
