import StringDiagrams.Super.Underlying
import StringDiagrams.Super.MonoidalEnvelope
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Monoidal Π-supercategories and monoidal Π-categories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definitions 1.12, 1.14 and 1.16.

## The underlying monoidal category

For a monoidal supercategory `A`, the underlying category `A̲` of even morphisms
(Definition 1.1(v)) is a monoidal category in the sense of Mathlib
(`Underlying.instMonoidalCategory`): on even morphisms the super interchange law is the
ordinary one. We use it to transport Mathlib's coherence lemmas (which only involve even
coherence maps) back to `A` (`MonoidalSupercategory.unitors_equal`,
`MonoidalSupercategory.leftUnitor_tensor`, …).

## Monoidal Π-supercategories (Definition 1.12)

A monoidal Π-supercategory is a monoidal supercategory with an object `π` and an odd
isomorphism `ζ : π ≅ 1` (`StringDiagrams.MonoidalPiSupercategory`). We prove:

* it is a Π-supercategory with `Π := π ⊗ -` and `ζ_λ := l_λ ∘ (ζ ⊗ 1_λ)`
  (`MonoidalPiSupercategory.toPiSupercategory`);
* the even isomorphisms `β_λ := (1_λ ⊗ ζ⁻¹) ∘ r_λ⁻¹ ∘ l_λ ∘ (ζ ⊗ 1_λ) : π ⊗ λ ≅ λ ⊗ π` are
  natural (`β_naturality`), satisfy (1.6) (`β_unit`) and (1.7) (`β_tensor`), so that
  `(π, β)` is an object of the Drinfeld center of `A̲` (`MonoidalPiSupercategory.halfBraiding`),
  and `β_π = -1` (`β_pi`);
* the even isomorphism `ξ := (l_1 = r_1) ∘ (ζ ⊗ ζ) : π ⊗ π ≅ 1` (`ξ_hom_eq`) satisfies (1.8)
  (`ξ_comm`).

## Monoidal Π-categories (Definition 1.14)

`StringDiagrams.MonoidalPiCategory`: a monoidal category with an object `π` of the Drinfeld
center (Mathlib's `HalfBraiding`) with `β_π = -1` and an isomorphism `ξ : π ⊗ π ≅ 1`
satisfying (1.8). The underlying monoidal category of a monoidal Π-supercategory is a monoidal
Π-category (`MonoidalPiSupercategory.toMonoidalPiCategory`): the object part of the functor (2)
of (1.9). A monoidal superfunctor `F` between monoidal Π-supercategories gives a monoidal
Π-functor between the underlying monoidal Π-categories, with `j := (F ζ_A)⁻¹ ∘ i ∘ ζ_B`
(`MonoidalSuperfunctor.toMonoidalPiFunctor`): the functor (2) on morphisms.

## Not formalized

Theorem 1.15 (the monoidal analogue of Theorem 1.9): neither the universal property of the
monoidal Π-envelope (extension of monoidal superfunctors along `J`) nor the inverse functor
`Π-Mon → Π-SMon` (a monoidal structure on the associated Π-supercategory of a monoidal
Π-category) is formalized here.

The Π-envelope of a monoidal supercategory is a monoidal Π-supercategory
(`Envelope.instMonoidalPiSupercategory`, Definition 1.16).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe w w₁ w₂ w₃ w₄

/-! ## The underlying monoidal category -/

namespace Underlying

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]

/-- The monoidal structure of the underlying category. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Underlying R C) where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  whiskerLeft X _ _ f := ⟨X.obj ◁ f.1, MonoidalSupercategory.whiskerLeft_mem _ f.2⟩
  whiskerRight f Y := ⟨f.1 ▷ Y.obj, MonoidalSupercategory.whiskerRight_mem _ f.2⟩
  tensorHom f g := ⟨f.1 ⊗ g.1, by simpa using MonoidalSupercategory.tensorHom_mem f.2 g.2⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z := isoMk (α_ X.obj Y.obj Z.obj)
    (MonoidalSupercategory.associator_hom_mem _ _ _)
  leftUnitor X := isoMk (λ_ X.obj) (MonoidalSupercategory.leftUnitor_hom_mem _)
  rightUnitor X := isoMk (ρ_ X.obj) (MonoidalSupercategory.rightUnitor_hom_mem _)

@[simp] theorem tensorObj_obj (X Y : Underlying R C) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

@[simp] theorem tensorUnit_obj : (𝟙_ (Underlying R C)).obj = 𝟙_ C := rfl

@[simp] theorem whiskerLeft_val (X : Underlying R C) {Y Y' : Underlying R C} (f : Y ⟶ Y') :
    (X ◁ f).1 = X.obj ◁ f.1 := rfl

@[simp] theorem whiskerRight_val {X X' : Underlying R C} (f : X ⟶ X') (Y : Underlying R C) :
    (f ▷ Y).1 = f.1 ▷ Y.obj := rfl

@[simp] theorem tensorHom_val {X X' Y Y' : Underlying R C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ g).1 = f.1 ⊗ g.1 := rfl

@[simp] theorem associator_hom_val (X Y Z : Underlying R C) :
    (α_ X Y Z).hom.1 = (α_ X.obj Y.obj Z.obj).hom := rfl

@[simp] theorem associator_inv_val (X Y Z : Underlying R C) :
    (α_ X Y Z).inv.1 = (α_ X.obj Y.obj Z.obj).inv := rfl

@[simp] theorem leftUnitor_hom_val (X : Underlying R C) : (λ_ X).hom.1 = (λ_ X.obj).hom := rfl

@[simp] theorem leftUnitor_inv_val (X : Underlying R C) : (λ_ X).inv.1 = (λ_ X.obj).inv := rfl

@[simp] theorem rightUnitor_hom_val (X : Underlying R C) : (ρ_ X).hom.1 = (ρ_ X.obj).hom := rfl

@[simp] theorem rightUnitor_inv_val (X : Underlying R C) : (ρ_ X).inv.1 = (ρ_ X.obj).inv := rfl

/-- The underlying category of a monoidal supercategory is a monoidal category: on even
morphisms the super interchange law is the ordinary interchange law. -/
instance instMonoidalCategory : MonoidalCategory (Underlying R C) where
  tensorHom_def f g := Subtype.ext (MonoidalSupercategory.tensorHom_def (R := R) f.1 g.1)
  tensor_id X Y := Subtype.ext (MonoidalSupercategory.tensor_id R X.obj Y.obj)
  tensor_comp f₁ f₂ g₁ g₂ := Subtype.ext (by
    simp only [comp_val, tensorHom_val]
    rw [MonoidalSupercategory.tensorHom_comp_tensorHom _ _ _ _ g₁.2 f₂.2, koszulSign_zero_left,
      one_smul])
  whiskerLeft_id X Y := Subtype.ext (MonoidalSupercategory.whiskerLeft_id (R := R) _ _)
  id_whiskerRight X Y := Subtype.ext (MonoidalSupercategory.id_whiskerRight (R := R) _ _)
  associator_naturality f₁ f₂ f₃ :=
    Subtype.ext (MonoidalSupercategory.associator_naturality (R := R) f₁.1 f₂.1 f₃.1)
  leftUnitor_naturality f := Subtype.ext (MonoidalSupercategory.leftUnitor_naturality (R := R) f.1)
  rightUnitor_naturality f :=
    Subtype.ext (MonoidalSupercategory.rightUnitor_naturality (R := R) f.1)
  pentagon W X Y Z := Subtype.ext (MonoidalSupercategory.pentagon (R := R) _ _ _ _)
  triangle X Y := Subtype.ext (MonoidalSupercategory.triangle (R := R) _ _)

instance instMonoidalPreadditive : MonoidalPreadditive (Underlying R C) where
  whiskerLeft_zero := Subtype.ext (MonoidalSupercategory.whiskerLeft_zero R _)
  zero_whiskerRight := Subtype.ext (MonoidalSupercategory.zero_whiskerRight R _)
  whiskerLeft_add f g := Subtype.ext (MonoidalSupercategory.whiskerLeft_add (R := R) _ f.1 g.1)
  add_whiskerRight f g := Subtype.ext (MonoidalSupercategory.add_whiskerRight (R := R) f.1 g.1 _)

instance instMonoidalLinear : MonoidalLinear R (Underlying R C) where
  whiskerLeft_smul X _ _ r f := Subtype.ext (MonoidalSupercategory.whiskerLeft_smul X.obj r f.1)
  smul_whiskerRight r _ _ f X := Subtype.ext (MonoidalSupercategory.smul_whiskerRight r f.1 X.obj)

end Underlying

/-! ## Coherence lemmas for monoidal supercategories -/

namespace MonoidalSupercategory

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]

variable (R) in
include R in
theorem unitors_equal : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
  congrArg Subtype.val (MonoidalCategory.unitors_equal (C := Underlying R C))

variable (R) in
include R in
theorem leftUnitor_tensor (X Y : C) :
    (λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ▷ Y :=
  congrArg Subtype.val (MonoidalCategory.leftUnitor_tensor (C := Underlying R C) ⟨X⟩ ⟨Y⟩)

variable (R) in
include R in
@[reassoc]
theorem rightUnitor_tensor_inv (X Y : C) :
    (ρ_ (X ⊗ Y)).inv = X ◁ (ρ_ Y).inv ≫ (α_ X Y (𝟙_ C)).inv :=
  congrArg Subtype.val (MonoidalCategory.rightUnitor_tensor_inv (C := Underlying R C) ⟨X⟩ ⟨Y⟩)

variable (R) in
include R in
@[reassoc]
theorem rightUnitor_inv_naturality {X Y : C} (f : X ⟶ Y) :
    (ρ_ X).inv ≫ f ▷ 𝟙_ C = f ≫ (ρ_ Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← rightUnitor_naturality (R := R), Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

variable (R) in
include R in
@[reassoc]
theorem associator_inv_naturality_right (X Y : C) {Z Z' : C} (h : Z ⟶ Z') :
    X ◁ (Y ◁ h) ≫ (α_ X Y Z').inv = (α_ X Y Z).inv ≫ (X ⊗ Y) ◁ h := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← associator_naturality_right R, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end MonoidalSupercategory

/-! ## Monoidal Π-supercategories -/

variable (R : Type w) [CommRing R] (C : Type w₁) [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]

/-- A monoidal Π-supercategory (Brundan–Ellis, Definition 1.12): a monoidal supercategory with
an object `π` and an odd isomorphism `ζ : π ≅ 1`. -/
class MonoidalPiSupercategory where
  /-- The object `π`. -/
  pi : C
  /-- The odd isomorphism `ζ : π ≅ 1`. -/
  ζ : pi ≅ 𝟙_ C
  ζ_hom_mem : ζ.hom ∈ parity (R := R) pi (𝟙_ C) 1

namespace MonoidalPiSupercategory

variable {R C} [MonoidalPiSupercategory R C]

local notation "𝛑" => MonoidalPiSupercategory.pi (R := R) (C := C)
local notation "𝛇" => MonoidalPiSupercategory.ζ (R := R) (C := C)

omit [MonoidalSupercategory R C] in
theorem ζ_inv_mem : (𝛇).inv ∈ parity (R := R) (𝟙_ C) 𝛑 1 := inv_mem _ (ζ_hom_mem (R := R) (C := C))

/-- The functor `π ⊗ - : C ⥤ C`. -/
@[simps]
def leftFunctor : C ⥤ C where
  obj X := 𝛑 ⊗ X
  map f := 𝛑 ◁ f
  map_id _ := MonoidalSupercategory.whiskerLeft_id (R := R) _ _
  map_comp f g := MonoidalSupercategory.whiskerLeft_comp (R := R) _ f g

instance : (leftFunctor (R := R) (C := C)).Additive where
  map_add := MonoidalSupercategory.whiskerLeft_add (R := R) _ _ _

instance : (leftFunctor (R := R) (C := C)).Linear R where
  map_smul f r := MonoidalSupercategory.whiskerLeft_smul _ r f

instance : IsSuperfunctor R (leftFunctor (R := R) (C := C)) where
  map_mem hf := MonoidalSupercategory.whiskerLeft_mem _ hf

/-- The odd isomorphism `ζ_λ := l_λ ∘ (ζ ⊗ 1_λ) : π ⊗ λ ≅ λ`. -/
def ζL (X : C) : 𝛑 ⊗ X ≅ X where
  hom := (𝛇).hom ▷ X ≫ (λ_ X).hom
  inv := (λ_ X).inv ≫ (𝛇).inv ▷ X
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← MonoidalSupercategory.comp_whiskerRight (R := R),
      Iso.hom_inv_id, MonoidalSupercategory.id_whiskerRight (R := R)]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc ((𝛇).inv ▷ X),
      ← MonoidalSupercategory.comp_whiskerRight (R := R), Iso.inv_hom_id,
      MonoidalSupercategory.id_whiskerRight (R := R), Category.id_comp, Iso.inv_hom_id]

/-- The odd isomorphism `r_λ ∘ (1_λ ⊗ ζ) : λ ⊗ π ≅ λ`. -/
def ζR (X : C) : X ⊗ 𝛑 ≅ X where
  hom := X ◁ (𝛇).hom ≫ (ρ_ X).hom
  inv := (ρ_ X).inv ≫ X ◁ (𝛇).inv
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← MonoidalSupercategory.whiskerLeft_comp (R := R),
      Iso.hom_inv_id, MonoidalSupercategory.whiskerLeft_id (R := R)]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc (X ◁ (𝛇).inv),
      ← MonoidalSupercategory.whiskerLeft_comp (R := R), Iso.inv_hom_id,
      MonoidalSupercategory.whiskerLeft_id (R := R), Category.id_comp, Iso.inv_hom_id]

theorem ζL_hom_mem (X : C) : (ζL (R := R) X).hom ∈ parity (R := R) (𝛑 ⊗ X) X 1 := by
  simpa using comp_mem (MonoidalSupercategory.whiskerRight_mem X (ζ_hom_mem (R := R) (C := C)))
    (MonoidalSupercategory.leftUnitor_hom_mem (R := R) X)

theorem ζR_hom_mem (X : C) : (ζR (R := R) X).hom ∈ parity (R := R) (X ⊗ 𝛑) X 1 := by
  simpa using comp_mem (MonoidalSupercategory.whiskerLeft_mem X (ζ_hom_mem (R := R) (C := C)))
    (MonoidalSupercategory.rightUnitor_hom_mem (R := R) X)

/-- Supernaturality of `ζL`: `ζ_μ ∘ (1_π ⊗ f) = (-1)^{|f|} f ∘ ζ_λ`. -/
theorem ζL_naturality {X Y : C} {q : ZMod 2} {f : X ⟶ Y} (hf : f ∈ parity (R := R) X Y q) :
    𝛑 ◁ f ≫ (ζL (R := R) Y).hom = sign R q • ((ζL (R := R) X).hom ≫ f) := by
  have h := MonoidalSupercategory.super_interchange (ζ_hom_mem (R := R) (C := C)) hf
  rw [koszulSign_smul (R := R), one_mul] at h
  have h' : 𝛑 ◁ f ≫ (𝛇).hom ▷ Y = sign R q • ((𝛇).hom ▷ X ≫ 𝟙_ C ◁ f) := by
    rw [h, sign_smul_sign_smul]
  simp only [ζL, ← Category.assoc, h', Linear.smul_comp]
  rw [Category.assoc, MonoidalSupercategory.leftUnitor_naturality (R := R), Category.assoc]

/-- Supernaturality of `ζR`: `ζ_μ ∘ (f ⊗ 1_π) = (-1)^{|f|} f ∘ ζ_λ`. -/
theorem ζR_naturality {X Y : C} {q : ZMod 2} {f : X ⟶ Y} (hf : f ∈ parity (R := R) X Y q) :
    f ▷ 𝛑 ≫ (ζR (R := R) Y).hom = sign R q • ((ζR (R := R) X).hom ≫ f) := by
  have h := MonoidalSupercategory.super_interchange hf (ζ_hom_mem (R := R) (C := C))
  rw [koszulSign_smul (R := R), mul_one] at h
  simp only [ζR, ← Category.assoc, h, Linear.smul_comp]
  rw [Category.assoc, MonoidalSupercategory.rightUnitor_naturality (R := R), Category.assoc]

variable (R C) in
/-- **Brundan–Ellis, after Definition 1.12.** A monoidal Π-supercategory is a Π-supercategory
with `Π := π ⊗ -` and `ζ_λ := l_λ ∘ (ζ ⊗ 1_λ)`. -/
def toPiSupercategory : PiSupercategory R C where
  pi := leftFunctor (R := R)
  ζ := ζL (R := R)
  ζ_isSupernatural :=
    { mem := ζL_hom_mem
      naturality := fun hf => by
        rw [one_mul]
        exact ζL_naturality hf }

/-! ### The half-braiding `β` -/

/-- The even isomorphism `β_λ : π ⊗ λ ≅ λ ⊗ π`,
`β_λ = (1_λ ⊗ ζ⁻¹) ∘ r_λ⁻¹ ∘ l_λ ∘ (ζ ⊗ 1_λ)` (Brundan–Ellis, after Definition 1.12). -/
def β (X : C) : 𝛑 ⊗ X ≅ X ⊗ 𝛑 := ζL (R := R) X ≪≫ (ζR (R := R) X).symm

theorem β_hom (X : C) :
    (β (R := R) X).hom = (𝛇).hom ▷ X ≫ (λ_ X).hom ≫ (ρ_ X).inv ≫ X ◁ (𝛇).inv := by
  simp [β, ζL, ζR]

theorem β_hom_mem (X : C) : (β (R := R) X).hom ∈ parity (R := R) (𝛑 ⊗ X) (X ⊗ 𝛑) 0 := by
  have := comp_mem (ζL_hom_mem (R := R) X) (inv_mem _ (ζR_hom_mem (R := R) X))
  simpa [β] using this

/-- `β` is natural (an even supernatural isomorphism `π ⊗ - ⇒ - ⊗ π`). -/
theorem β_naturality {X Y : C} (f : X ⟶ Y) :
    𝛑 ◁ f ≫ (β (R := R) Y).hom = (β (R := R) X).hom ≫ f ▷ 𝛑 := by
  refine induction_on (R := R) f ?_ (fun q f hf => ?_) (fun f g hf hg => ?_)
  · rw [MonoidalSupercategory.whiskerLeft_zero R, MonoidalSupercategory.zero_whiskerRight R,
      Limits.zero_comp, Limits.comp_zero]
  · have h2 : (ζR (R := R) X).inv ≫ f ▷ 𝛑 = sign R q • (f ≫ (ζR (R := R) Y).inv) := by
      rw [← cancel_mono (ζR (R := R) Y).hom, Category.assoc, ζR_naturality hf,
        Linear.comp_smul, Iso.inv_hom_id_assoc, Linear.smul_comp, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    simp only [β, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, ζL_naturality hf, Linear.smul_comp, Category.assoc, Category.assoc,
      h2, Linear.comp_smul]
  · rw [MonoidalSupercategory.whiskerLeft_add (R := R),
      MonoidalSupercategory.add_whiskerRight (R := R),
      Preadditive.add_comp, Preadditive.comp_add, hf, hg]

/-- **(1.6).** `l_π ∘ β_1 = r_π`. -/
theorem β_unit : (β (R := R) (𝟙_ C)).hom ≫ (λ_ 𝛑).hom = (ρ_ 𝛑).hom := by
  rw [β_hom, Category.assoc, Category.assoc, Category.assoc,
    MonoidalSupercategory.leftUnitor_naturality (R := R),
    MonoidalSupercategory.unitors_equal R, Iso.hom_inv_id_assoc, ← Category.assoc,
    MonoidalSupercategory.rightUnitor_naturality (R := R), Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

@[reassoc]
theorem associator_ζL (X Y : C) :
    (α_ 𝛑 X Y).hom ≫ (ζL (R := R) (X ⊗ Y)).hom = (ζL (R := R) X).hom ▷ Y := by
  simp only [ζL]
  rw [← Category.assoc, ← MonoidalSupercategory.associator_naturality_left R,
    MonoidalSupercategory.leftUnitor_tensor R, Category.assoc, Iso.hom_inv_id_assoc,
    MonoidalSupercategory.comp_whiskerRight (R := R)]

@[reassoc]
theorem ζR_inv_associator (X Y : C) :
    (ζR (R := R) (X ⊗ Y)).inv ≫ (α_ X Y 𝛑).hom = X ◁ (ζR (R := R) Y).inv := by
  simp only [ζR]
  rw [Category.assoc, MonoidalSupercategory.associator_naturality_right R,
    MonoidalSupercategory.rightUnitor_tensor_inv R, Category.assoc, Iso.inv_hom_id_assoc,
    MonoidalSupercategory.whiskerLeft_comp (R := R)]

@[reassoc]
theorem ζR_inv_whiskerRight_associator_ζL (X Y : C) :
    (ζR (R := R) X).inv ▷ Y ≫ (α_ X 𝛑 Y).hom ≫ X ◁ (ζL (R := R) Y).hom = 𝟙 _ := by
  simp only [ζR, ζL]
  rw [MonoidalSupercategory.comp_whiskerRight (R := R),
    MonoidalSupercategory.whiskerLeft_comp (R := R),
    Category.assoc, ← Category.assoc ((X ◁ (𝛇).inv) ▷ Y),
    MonoidalSupercategory.associator_naturality_middle R, Category.assoc,
    ← Category.assoc (X ◁ (𝛇).inv ▷ Y), ← MonoidalSupercategory.whiskerLeft_comp (R := R),
    ← MonoidalSupercategory.comp_whiskerRight (R := R), Iso.inv_hom_id,
    MonoidalSupercategory.id_whiskerRight (R := R), MonoidalSupercategory.whiskerLeft_id (R := R),
    Category.id_comp, MonoidalSupercategory.triangle (R := R),
    ← MonoidalSupercategory.comp_whiskerRight (R := R), Iso.inv_hom_id,
    MonoidalSupercategory.id_whiskerRight (R := R)]

/-- **(1.7).** `(π, β)` satisfies the hexagon of the Drinfeld center:
`a_{λ,μ,π} ∘ β_{λ⊗μ} ∘ a_{π,λ,μ} = (1_λ ⊗ β_μ) ∘ a_{λ,π,μ} ∘ (β_λ ⊗ 1_μ)`. -/
theorem β_tensor (X Y : C) :
    (α_ 𝛑 X Y).hom ≫ (β (R := R) (X ⊗ Y)).hom ≫ (α_ X Y 𝛑).hom =
      (β (R := R) X).hom ▷ Y ≫ (α_ X 𝛑 Y).hom ≫ X ◁ (β (R := R) Y).hom := by
  simp only [β, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [associator_ζL_assoc, ζR_inv_associator, MonoidalSupercategory.comp_whiskerRight (R := R),
    MonoidalSupercategory.whiskerLeft_comp (R := R), Category.assoc,
    ζR_inv_whiskerRight_associator_ζL_assoc]

/-- `ζL_π = -ζR_π`. -/
theorem ζL_pi : (ζL (R := R) 𝛑).hom = -(ζR (R := R) 𝛑).hom := by
  rw [← cancel_mono (𝛇).hom]
  have h := MonoidalSupercategory.super_interchange (ζ_hom_mem (R := R) (C := C))
    (ζ_hom_mem (R := R) (C := C))
  rw [koszulSign_one_one, neg_one_smul] at h
  simp only [ζL, ζR, Category.assoc, Preadditive.neg_comp]
  rw [← MonoidalSupercategory.leftUnitor_naturality (R := R), ← Category.assoc, h,
    Preadditive.neg_comp, Category.assoc, MonoidalSupercategory.unitors_equal R,
    MonoidalSupercategory.rightUnitor_naturality (R := R)]

/-- **Brundan–Ellis, after Definition 1.12.** `β_π = -1`. -/
theorem β_pi : (β (R := R) 𝛑).hom = -𝟙 _ := by
  simp only [β, Iso.trans_hom, Iso.symm_hom]
  rw [ζL_pi, Preadditive.neg_comp, Iso.hom_inv_id]

/-! ### The isomorphism `ξ` and (1.8) -/

/-- The even isomorphism `ξ : π ⊗ π ≅ 1`, `ξ = r_1 ∘ (ζ ⊗ ζ)`; see `ξ_hom_eq` for the formula
of the paper. -/
def ξ : 𝛑 ⊗ 𝛑 ≅ 𝟙_ C := ζR (R := R) 𝛑 ≪≫ 𝛇

theorem ξ_hom : (ξ (R := R) (C := C)).hom = (ζR (R := R) 𝛑).hom ≫ (𝛇).hom := rfl

theorem ξ_inv : (ξ (R := R) (C := C)).inv = (𝛇).inv ≫ (ζR (R := R) 𝛑).inv := rfl

/-- **Brundan–Ellis, after Definition 1.12.** `ξ = (l_1 = r_1) ∘ (ζ ⊗ ζ)`, with the paper's
tensor product `ζ ⊗ ζ = (ζ ⊗ 1) ∘ (1 ⊗ ζ)` (`superTensorHom`). -/
theorem ξ_hom_eq : (ξ (R := R) (C := C)).hom =
    MonoidalSupercategory.superTensorHom (𝛇).hom (𝛇).hom ≫ (λ_ (𝟙_ C)).hom := by
  rw [ξ_hom, MonoidalSupercategory.superTensorHom, MonoidalSupercategory.unitors_equal R]
  simp only [ζR, Category.assoc]
  rw [← MonoidalSupercategory.rightUnitor_naturality (R := R)]

theorem ξ_hom_mem : (ξ (R := R) (C := C)).hom ∈ parity (R := R) (𝛑 ⊗ 𝛑) (𝟙_ C) 0 := by
  simpa using comp_mem (ζR_hom_mem (R := R) 𝛑) (ζ_hom_mem (R := R) (C := C))

theorem ξ_hom_eq_neg : (ξ (R := R) (C := C)).hom = -((ζL (R := R) 𝛑).hom ≫ (𝛇).hom) := by
  rw [ξ_hom, ζL_pi, Preadditive.neg_comp, neg_neg]

theorem ξ_whiskerRight_leftUnitor (X : C) :
    (ξ (R := R) (C := C)).hom ▷ X ≫ (λ_ X).hom =
      -((ζL (R := R) 𝛑).hom ▷ X ≫ (ζL (R := R) X).hom) := by
  rw [ξ_hom_eq_neg, MonoidalSupercategory.neg_whiskerRight R,
    MonoidalSupercategory.comp_whiskerRight (R := R), Preadditive.neg_comp]
  simp [ζL]

theorem rightUnitor_inv_whiskerLeft_ξ_inv (X : C) :
    (ρ_ X).inv ≫ X ◁ (ξ (R := R) (C := C)).inv =
      (ζR (R := R) X).inv ≫ X ◁ (ζR (R := R) 𝛑).inv := by
  rw [ξ_inv, MonoidalSupercategory.whiskerLeft_comp (R := R)]
  simp [ζR]

@[reassoc]
theorem whiskerLeft_ζR_inv_associator_inv_ζL (X : C) :
    𝛑 ◁ (ζR (R := R) X).inv ≫ (α_ 𝛑 X 𝛑).inv ≫ (ζL (R := R) X).hom ▷ 𝛑 =
      -((ζL (R := R) X).hom ≫ (ζR (R := R) X).inv) := by
  have hf : (𝛇).hom ▷ X ∈ parity (R := R) (𝛑 ⊗ X) (𝟙_ C ⊗ X) 1 :=
    MonoidalSupercategory.whiskerRight_mem X (ζ_hom_mem (R := R) (C := C))
  have hi := MonoidalSupercategory.super_interchange hf (ζ_inv_mem (R := R) (C := C))
  rw [koszulSign_one_one, neg_one_smul] at hi
  have hi' : (𝛑 ⊗ X) ◁ (𝛇).inv ≫ ((𝛇).hom ▷ X) ▷ 𝛑 =
      -(((𝛇).hom ▷ X) ▷ 𝟙_ C ≫ (𝟙_ C ⊗ X) ◁ (𝛇).inv) := by rw [hi, neg_neg]
  have he := MonoidalSupercategory.interchange_of_even_left
    (MonoidalSupercategory.leftUnitor_hom_mem (R := R) X) (ζ_inv_mem (R := R) (C := C))
  simp only [ζR, ζL, MonoidalSupercategory.whiskerLeft_comp (R := R),
    MonoidalSupercategory.comp_whiskerRight (R := R), Category.assoc]
  rw [MonoidalSupercategory.associator_inv_naturality_right_assoc R, reassoc_of% hi']
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
  rw [← he, ← MonoidalSupercategory.rightUnitor_tensor_inv_assoc R,
    ← Category.assoc ((𝛇).hom ▷ X ▷ 𝟙_ C), ← MonoidalSupercategory.comp_whiskerRight (R := R),
    MonoidalSupercategory.rightUnitor_inv_naturality_assoc R, Category.assoc]

@[reassoc]
theorem associator_whiskerLeft_ζL_ζL (X : C) :
    (α_ 𝛑 𝛑 X).hom ≫ 𝛑 ◁ (ζL (R := R) X).hom ≫ (ζL (R := R) X).hom =
      -((ζL (R := R) 𝛑).hom ▷ X ≫ (ζL (R := R) X).hom) := by
  rw [ζL_naturality (ζL_hom_mem (R := R) X), sign_one, neg_one_smul, Preadditive.comp_neg,
    associator_ζL_assoc]

@[reassoc]
theorem ζR_inv_whiskerRight_associator (X : C) :
    (ζR (R := R) X).inv ▷ 𝛑 ≫ (α_ X 𝛑 𝛑).hom = -(X ◁ (ζR (R := R) 𝛑).inv) := by
  have h := ζR_naturality (inv_mem _ (ζR_hom_mem (R := R) X))
  rw [sign_one, neg_one_smul, Iso.hom_inv_id] at h
  have h' : (ζR (R := R) X).inv ▷ 𝛑 = -(ζR (R := R) (X ⊗ 𝛑)).inv := by
    rw [← cancel_mono (ζR (R := R) (X ⊗ 𝛑)).hom, h, Preadditive.neg_comp, Iso.inv_hom_id]
  rw [h', Preadditive.neg_comp, ζR_inv_associator]

/-- **(1.8).** `(1_λ ⊗ ξ⁻¹) ∘ r_λ⁻¹ ∘ l_λ ∘ (ξ ⊗ 1_λ) =
a_{λ,π,π} ∘ (β_λ ⊗ 1_π) ∘ a_{π,λ,π}⁻¹ ∘ (1_π ⊗ β_λ) ∘ a_{π,π,λ}`. -/
theorem ξ_comm (X : C) :
    (ξ (R := R) (C := C)).hom ▷ X ≫ (λ_ X).hom ≫ (ρ_ X).inv ≫ X ◁ (ξ (R := R) (C := C)).inv =
      (α_ 𝛑 𝛑 X).hom ≫ 𝛑 ◁ (β (R := R) X).hom ≫ (α_ 𝛑 X 𝛑).inv ≫
        (β (R := R) X).hom ▷ 𝛑 ≫ (α_ X 𝛑 𝛑).hom := by
  rw [← Category.assoc, ξ_whiskerRight_leftUnitor, rightUnitor_inv_whiskerLeft_ξ_inv]
  simp only [β, Iso.trans_hom, Iso.symm_hom, MonoidalSupercategory.whiskerLeft_comp (R := R),
    MonoidalSupercategory.comp_whiskerRight (R := R), Category.assoc]
  rw [whiskerLeft_ζR_inv_associator_inv_ζL_assoc, ζR_inv_whiskerRight_associator]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.assoc]
  rw [associator_whiskerLeft_ζL_ζL_assoc]
  simp only [Preadditive.neg_comp, Category.assoc]

end MonoidalPiSupercategory

/-! ## Monoidal Π-categories (Definition 1.14) -/

section MonoidalPiCategory

open Functor.LaxMonoidal

/-- A monoidal Π-category (Brundan–Ellis, Definition 1.14(i)): an `R`-linear monoidal category
with an object `(π, β)` of its Drinfeld center (a half-braiding `β : π ⊗ - ≅ - ⊗ π`, i.e.
(1.7) and naturality) with `β_π = -1`, and an isomorphism `ξ : π ⊗ π ≅ 1` satisfying (1.8). -/
class MonoidalPiCategory (R : Type w) [CommRing R] (D : Type w₁) [Category.{w₂} D]
    [Preadditive D] [Linear R D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalLinear R D] where
  /-- The object `π`. -/
  pi : D
  /-- The half-braiding `β`. -/
  β : HalfBraiding pi
  β_pi : (β.β pi).hom = -𝟙 (pi ⊗ pi)
  /-- The isomorphism `ξ : π ⊗ π ≅ 1`. -/
  ξ : pi ⊗ pi ≅ 𝟙_ D
  /-- (1.8). -/
  ξ_comm : ∀ X : D, ξ.hom ▷ X ≫ (λ_ X).hom ≫ (ρ_ X).inv ≫ X ◁ ξ.inv =
    (α_ pi pi X).hom ≫ pi ◁ (β.β X).hom ≫ (α_ pi X pi).inv ≫ (β.β X).hom ▷ pi ≫
      (α_ X pi pi).hom

variable {R : Type w} [CommRing R] {D : Type w₁} [Category.{w₂} D] [Preadditive D]
  [Linear R D] [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear R D]
  {E : Type w₃} [Category.{w₄} E] [Preadditive E] [Linear R E] [MonoidalCategory E]
  [MonoidalPreadditive E] [MonoidalLinear R E] [MonoidalPiCategory R D] [MonoidalPiCategory R E]

variable (R) in
/-- A monoidal Π-functor (Brundan–Ellis, Definition 1.14(ii)): a monoidal functor `F` with an
isomorphism `j : π_E ≅ F π_D` compatible with the `β`s and the `ξ`s. -/
structure MonoidalPiFunctor (F : D ⥤ E) [F.Monoidal] where
  /-- The coherence map `j`. -/
  j : MonoidalPiCategory.pi (R := R) (D := E) ≅ F.obj (MonoidalPiCategory.pi (R := R) (D := D))
  β_comm : ∀ X : D, j.hom ▷ F.obj X ≫ μ F _ X ≫
      F.map ((MonoidalPiCategory.β (R := R) (D := D)).β X).hom =
    ((MonoidalPiCategory.β (R := R) (D := E)).β (F.obj X)).hom ≫ F.obj X ◁ j.hom ≫ μ F X _
  ξ_comm : (MonoidalPiCategory.ξ (R := R) (D := E)).hom ≫ ε F =
    (j.hom ⊗ j.hom) ≫ μ F _ _ ≫ F.map (MonoidalPiCategory.ξ (R := R) (D := D)).hom

/-- A monoidal Π-natural transformation (Brundan–Ellis, Definition 1.14(iii)): a monoidal
natural transformation `x` with `x_π ∘ j_F = j_G`. -/
def MonoidalPiFunctor.IsPiNatural {F G : D ⥤ E} [F.Monoidal] [G.Monoidal]
    (hF : MonoidalPiFunctor R F) (hG : MonoidalPiFunctor R G) (x : F ⟶ G)
    [NatTrans.IsMonoidal x] : Prop :=
  hF.j.hom ≫ x.app (MonoidalPiCategory.pi (R := R) (D := D)) = hG.j.hom

end MonoidalPiCategory

/-! ## The underlying monoidal Π-category of a monoidal Π-supercategory -/

namespace MonoidalPiSupercategory

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]
  [MonoidalPiSupercategory R C]

local notation "𝛑" => MonoidalPiSupercategory.pi (R := R) (C := C)

/-- **(1.7).** `(π, β)` is an object of the Drinfeld center of the underlying monoidal
category. -/
def halfBraiding : HalfBraiding (C := Underlying R C) ⟨𝛑⟩ where
  β U := Underlying.isoMk (β (R := R) U.obj) (β_hom_mem U.obj)
  monoidal U U' := Subtype.ext (by
    have h := β_tensor (R := R) U.obj U'.obj
    change (β (R := R) (U.obj ⊗ U'.obj)).hom = (α_ 𝛑 U.obj U'.obj).inv ≫
      (β (R := R) U.obj).hom ▷ U'.obj ≫ (α_ U.obj 𝛑 U'.obj).hom ≫
        U.obj ◁ (β (R := R) U'.obj).hom ≫ (α_ U.obj U'.obj 𝛑).inv
    rw [← cancel_epi (α_ 𝛑 U.obj U'.obj).hom, ← cancel_mono (α_ U.obj U'.obj 𝛑).hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact h)
  naturality f := Subtype.ext (β_naturality f.1)

/-- **Brundan–Ellis, (1.9), functor (2) on objects.** The underlying monoidal category of a
monoidal Π-supercategory is a monoidal Π-category, with `β` and `ξ := ζ ⊗ ζ`. -/
instance toMonoidalPiCategory : MonoidalPiCategory R (Underlying R C) where
  pi := ⟨𝛑⟩
  β := halfBraiding
  β_pi := Subtype.ext (β_pi (R := R))
  ξ := Underlying.isoMk (ξ (R := R) (C := C)) ξ_hom_mem
  ξ_comm X := Subtype.ext (ξ_comm (R := R) X.obj)

end MonoidalPiSupercategory

/-! ## Monoidal superfunctors give monoidal Π-functors -/

namespace MonoidalSuperfunctor

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]
  [MonoidalPiSupercategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [MonoidalCategoryStruct D] [MonoidalSupercategory R D] [MonoidalPiSupercategory R D]
  {F : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F] (hF : MonoidalSuperfunctor R F)

/-- The underlying functor of a monoidal superfunctor is monoidal. -/
def underlyingCoreMonoidal : (Underlying.map (R := R) F).CoreMonoidal where
  εIso := Underlying.isoMk hF.εIso hF.ε_mem
  μIso X Y := Underlying.isoMk (hF.μIso X.obj Y.obj) (hF.μ_mem _ _)
  μIso_hom_natural_left f X' := Subtype.ext (hF.μ_natural_left f.1 X'.obj)
  μIso_hom_natural_right X' f := Subtype.ext (hF.μ_natural_right X'.obj f.1)
  associativity X Y Z := Subtype.ext (hF.associativity X.obj Y.obj Z.obj)
  left_unitality X := Subtype.ext (hF.left_unitality X.obj)
  right_unitality X := Subtype.ext (hF.right_unitality X.obj)

local notation "𝛑C" => MonoidalPiSupercategory.pi (R := R) (C := C)
local notation "𝛑D" => MonoidalPiSupercategory.pi (R := R) (C := D)
local notation "𝛇C" => MonoidalPiSupercategory.ζ (R := R) (C := C)
local notation "𝛇D" => MonoidalPiSupercategory.ζ (R := R) (C := D)

/-- The coherence map `j := (F ζ_A)⁻¹ ∘ i ∘ ζ_B : π_B ≅ F π_A`. -/
def jIso : 𝛑D ≅ F.obj 𝛑C := 𝛇D ≪≫ hF.εIso ≪≫ F.mapIso (𝛇C).symm

omit [MonoidalSupercategory R C] [MonoidalSupercategory R D] in
theorem jIso_hom : (jIso hF).hom = (𝛇D).hom ≫ hF.εIso.hom ≫ F.map (𝛇C).inv := rfl

omit [MonoidalSupercategory R C] [MonoidalSupercategory R D] in
theorem jIso_hom_mem : (jIso hF).hom ∈ parity (R := R) 𝛑D (F.obj 𝛑C) 0 := by
  have := comp_mem (comp_mem (MonoidalPiSupercategory.ζ_hom_mem (R := R) (C := D)) hF.ε_mem)
    (Supercategory.map_mem F (MonoidalPiSupercategory.ζ_inv_mem (R := R) (C := C)))
  simpa using this

omit [MonoidalSupercategory R C] [MonoidalSupercategory R D] in
theorem jIso_hom_comp_map_ζ : (jIso hF).hom ≫ F.map (𝛇C).hom = (𝛇D).hom ≫ hF.εIso.hom := by
  rw [jIso_hom, Category.assoc, Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id,
    Category.comp_id]

theorem β_comm_left (X : C) :
    (jIso hF).hom ▷ F.obj X ≫ (hF.μIso 𝛑C X).hom ≫
        F.map (MonoidalPiSupercategory.β (R := R) X).hom =
      (𝛇D).hom ▷ F.obj X ≫ (λ_ (F.obj X)).hom ≫ F.map (ρ_ X).inv ≫ F.map (X ◁ (𝛇C).inv) := by
  rw [MonoidalPiSupercategory.β_hom, F.map_comp, F.map_comp, F.map_comp,
    ← reassoc_of% (hF.μ_natural_left (𝛇C).hom X), ← Category.assoc,
    ← MonoidalSupercategory.comp_whiskerRight (R := R), jIso_hom_comp_map_ζ,
    MonoidalSupercategory.comp_whiskerRight (R := R), Category.assoc,
    reassoc_of% (hF.left_unitality X).symm]

omit [MonoidalSupercategory R C] in
theorem β_comm_right (X : C) :
    (MonoidalPiSupercategory.β (R := R) (F.obj X)).hom ≫ F.obj X ◁ (jIso hF).hom ≫
        (hF.μIso X 𝛑C).hom =
      (𝛇D).hom ▷ F.obj X ≫ (λ_ (F.obj X)).hom ≫ F.map (ρ_ X).inv ≫ F.map (X ◁ (𝛇C).inv) := by
  rw [MonoidalPiSupercategory.β_hom]
  simp only [Category.assoc]
  congr 2
  rw [jIso_hom, MonoidalSupercategory.whiskerLeft_comp (R := R),
    MonoidalSupercategory.whiskerLeft_comp (R := R), Category.assoc,
    ← reassoc_of% (MonoidalSupercategory.whiskerLeft_comp (R := R) (F.obj X) (𝛇D).inv (𝛇D).hom),
    Iso.inv_hom_id, MonoidalSupercategory.whiskerLeft_id (R := R), Category.id_comp]
  simp only [Category.assoc]
  rw [hF.μ_natural_right, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Category.assoc, Iso.inv_comp_eq, hF.right_unitality X, Category.assoc, Category.assoc,
    ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.comp_id]

theorem ξ_comm_aux :
    (MonoidalPiSupercategory.ξ (R := R) (C := D)).hom ≫ hF.εIso.hom =
      ((jIso hF).hom ▷ 𝛑D ≫ F.obj 𝛑C ◁ (jIso hF).hom) ≫ (hF.μIso 𝛑C 𝛑C).hom ≫
        F.map (MonoidalPiSupercategory.ξ (R := R) (C := C)).hom := by
  rw [MonoidalPiSupercategory.ξ_hom, MonoidalPiSupercategory.ξ_hom]
  simp only [MonoidalPiSupercategory.ζR, F.map_comp, Category.assoc]
  rw [← reassoc_of% (hF.μ_natural_right 𝛑C (𝛇C).hom), ← reassoc_of%
    (MonoidalSupercategory.whiskerLeft_comp (R := R) (F.obj 𝛑C) (jIso hF).hom (F.map (𝛇C).hom)),
    jIso_hom_comp_map_ζ, MonoidalSupercategory.whiskerLeft_comp (R := R), Category.assoc,
    ← reassoc_of% (hF.right_unitality 𝛑C),
    reassoc_of% (MonoidalSupercategory.interchange_of_even_left (jIso_hom_mem hF)
      (MonoidalPiSupercategory.ζ_hom_mem (R := R) (C := D))),
    reassoc_of% (MonoidalSupercategory.rightUnitor_naturality (R := R) (jIso hF).hom),
    jIso_hom_comp_map_ζ hF]

/-- **Brundan–Ellis, (1.9), functor (2) on morphisms.** A monoidal superfunctor between monoidal
Π-supercategories gives a monoidal Π-functor between the underlying monoidal Π-categories, with
`j := (F ζ_A)⁻¹ ∘ i ∘ ζ_B`. -/
def toMonoidalPiFunctor :
    letI := (underlyingCoreMonoidal hF).toMonoidal
    MonoidalPiFunctor R (Underlying.map (R := R) F) :=
  letI := (underlyingCoreMonoidal hF).toMonoidal
  { j := Underlying.isoMk (jIso hF) (jIso_hom_mem hF)
    β_comm := fun X => Subtype.ext (by
      change (jIso hF).hom ▷ F.obj X.obj ≫ (hF.μIso 𝛑C X.obj).hom ≫
          F.map (MonoidalPiSupercategory.β (R := R) X.obj).hom =
        (MonoidalPiSupercategory.β (R := R) (F.obj X.obj)).hom ≫ F.obj X.obj ◁ (jIso hF).hom ≫
          (hF.μIso X.obj 𝛑C).hom
      rw [β_comm_left, β_comm_right])
    ξ_comm := Subtype.ext (by
      change (MonoidalPiSupercategory.ξ (R := R) (C := D)).hom ≫ hF.εIso.hom =
        ((jIso hF).hom ⊗ (jIso hF).hom) ≫ (hF.μIso 𝛑C 𝛑C).hom ≫
          F.map (MonoidalPiSupercategory.ξ (R := R) (C := C)).hom
      rw [MonoidalSupercategory.tensorHom_def (R := R), ξ_comm_aux]) }

end MonoidalSuperfunctor

/-! ## The monoidal Π-envelope -/

namespace Envelope

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]

/-- **Definition 1.16.** The Π-envelope of a monoidal supercategory is a monoidal
Π-supercategory with `π := Π¹ 1` and `ζ := (1_1)_1^0`. -/
instance instMonoidalPiSupercategory : MonoidalPiSupercategory R (Envelope R C) where
  pi := piUnit R C
  ζ := ζUnit
  ζ_hom_mem := ζUnit_hom_mem

end Envelope

end StringDiagrams

end
