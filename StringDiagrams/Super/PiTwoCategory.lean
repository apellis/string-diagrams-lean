import StringDiagrams.Super.TwoFunctorComp
import StringDiagrams.Super.PiCategory
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Π-2-categories and the functor `E₂`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 5.2, the functor `E₂ : Π-2-SCat → Π-2-Cat` of (5.4), and the 2-functor `𝔼₂` of
(5.6) on 2-morphisms.

## Definition 5.2

The paper states the axioms of Definition 5.2 for strict 2-categories and leaves the non-strict
case to the reader. We state them for an arbitrary bicategory in the sense of Mathlib, inserting
associators and unitors; composition of 1-morphisms is in diagrammatic order (`f ≫ g` is the
paper's `g f`), so the paper's `π_μ F` is `F ≫ π_μ` and `F π_λ` is `π_λ ≫ F`.

* `LinearBicategory R B`: the whiskerings are `R`-linear (a `k`-linear 2-category).
* `PiTwoCategory R B` (**Definition 5.2(i)**): 1-morphisms `π_λ : λ → λ`, natural isomorphisms
  `β_F : F ≫ π_μ ≅ π_λ ≫ F` making `(π, β)` an object of the Drinfeld center (the weak forms of
  Lemma 3.2(i)–(ii): `β_comp`, `β_id`), with `β_{π_λ} = -1` (`β_pi`), and 2-isomorphisms
  `ξ_λ : π_λ ≫ π_λ ≅ 1_λ` with `ξ_μ F ξ_λ⁻¹ = β_F π_λ ∘ π_μ β_F` (`ξ_comm`).
* Each hom category is then a Π-category with `Π := - ≫ π_μ` and `ξ_F := F ◁ ξ_μ` (with
  associator and unitor); the axiom `ξΠ = Πξ` is derived from `β_pi` and `ξ_comm`, as in the
  paper (`PiTwoCategory.homPiCategory`, `PiTwoCategory.ξHom_pi`).
* `PiTwoFunctor R F` (**Definition 5.2(ii)**): for a Mathlib pseudofunctor `F` (with coherence
  maps `mapComp`, `mapId`, inverse to the paper's `c`, `i`), 2-isomorphisms
  `j_λ : π_{Fλ} ≅ F π_λ` satisfying the two coherence diagrams (`β_comm`, `ξ_comm`).
* `PiTwoFunctor.IsPiTwoNatural` (**Definition 5.2(iii)**): the additional coherence axiom for a
  Mathlib oplax natural transformation (the paper's 2-natural transformations are oplax, see the
  footnote to Definition 2.2(iii)).

## The functor `E₂` (5.4)

* On objects: for a Π-2-supercategory `(𝔄, π, ζ)`, the underlying bicategory
  `Underlying2 R 𝔄` (`StringDiagrams.Super.UnderlyingBicategory`) is a Π-2-category with the
  `β` and `ξ` of Lemma 3.2 (`Underlying2.instPiTwoCategory`).
* On 2-superfunctors: `TwoSuperfunctor.toPseudofunctor` restricts a 2-superfunctor to the
  underlying bicategories; it is a Π-2-functor with `j` defined by `ℝζ_λ ∘ j = i ∘ ζ_{ℝλ}`
  (`TwoSuperfunctor.toPiTwoFunctor`, the two axioms `jβ_comm`, `jξ_comm`).
* On 2-natural transformations ((5.6)): `TwoNatTrans.toOplaxTrans`
  (`StringDiagrams.Super.TwoFunctorComp`), which is Π-2-natural (`TwoNatTrans.isPiTwoNatural`).

Applied to `PiSCat R` (`StringDiagrams.Super.PiTwo`), `Underlying2.instPiTwoCategory` makes the
underlying 2-category of `Π-𝔖ℭ𝔞𝔱` a Π-2-category, as stated after Definition 5.2. The basic
example `Π-ℭ𝔞𝔱` (the strict 2-category of Π-categories, Π-functors and Π-natural transformations)
is not constructed.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

section Defs

variable (R : Type w) [CommRing R] (B : Type u₁) [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]

/-- A preadditive bicategory: the hom categories are preadditive and whiskering is additive. -/
class PreadditiveBicategory : Prop where
  whiskerLeft_add {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h) :
    f ◁ (η + θ) = f ◁ η + f ◁ θ
  add_whiskerRight {a b c : B} {f g : a ⟶ b} (η θ : f ⟶ g) (h : b ⟶ c) :
    (η + θ) ▷ h = η ▷ h + θ ▷ h

/-- A `k`-linear bicategory: the hom categories are `R`-linear and whiskering is `R`-linear
(additivity is `PreadditiveBicategory`). -/
class LinearBicategory : Prop where
  whiskerLeft_smul {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (r : R) (η : g ⟶ h) :
    f ◁ (r • η) = r • (f ◁ η)
  smul_whiskerRight {a b c : B} {f g : a ⟶ b} (r : R) (η : f ⟶ g) (h : b ⟶ c) :
    (r • η) ▷ h = r • (η ▷ h)

/-- A Π-2-category (Brundan–Ellis, Definition 5.2(i)), with associators and unitors inserted in
the axioms: 1-morphisms `π_λ`, natural isomorphisms `β_F : F ≫ π_μ ≅ π_λ ≫ F` for `F : λ → μ`
making `(π, β)` an object of the Drinfeld center, with `β_{π_λ} = -1`, and 2-isomorphisms
`ξ_λ : π_λ ≫ π_λ ≅ 1_λ` with `ξ_μ F ξ_λ⁻¹ = β_F π_λ ∘ π_μ β_F`. -/
class PiTwoCategory [PreadditiveBicategory B] [LinearBicategory R B] where
  /-- The 1-morphisms `π_λ`. -/
  pi (a : B) : a ⟶ a
  /-- The isomorphisms `β_F : π_μ F ≅ F π_λ`. -/
  β {a b : B} (f : a ⟶ b) : f ≫ pi b ≅ pi a ≫ f
  β_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    (β f).hom ≫ pi a ◁ η = η ▷ pi b ≫ (β g).hom
  /-- Lemma 3.2(i): `β_{GF} = G β_F ∘ β_G F`. -/
  β_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (β (f ≫ g)).hom = (α_ f g (pi c)).hom ≫ f ◁ (β g).hom ≫ (α_ f (pi b) g).inv ≫
      (β f).hom ▷ g ≫ (α_ (pi a) f g).hom
  /-- Lemma 3.2(ii): `β_{1_λ} = 1_{π_λ}`. -/
  β_id (a : B) : (β (𝟙 a)).hom = (λ_ (pi a)).hom ≫ (ρ_ (pi a)).inv
  /-- `β_{π_λ} = -1`. -/
  β_pi (a : B) : (β (pi a)).hom = -𝟙 _
  /-- The 2-isomorphisms `ξ_λ : π_λ² ≅ 1_λ`. -/
  ξ (a : B) : pi a ≫ pi a ≅ 𝟙 a
  /-- `ξ_μ F ξ_λ⁻¹ = β_F π_λ ∘ π_μ β_F`. -/
  ξ_comm {a b : B} (f : a ⟶ b) :
    f ◁ (ξ b).hom ≫ (ρ_ f).hom ≫ (λ_ f).inv ≫ (ξ a).inv ▷ f =
      (α_ f (pi b) (pi b)).inv ≫ (β f).hom ▷ pi b ≫ (α_ (pi a) f (pi b)).hom ≫
        pi a ◁ (β f).hom ≫ (α_ (pi a) (pi a) f).inv

end Defs

namespace PreadditiveBicategory

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B]

instance postcomp_additive (a : B) {b c : B} (g : b ⟶ c) : (postcomp a g).Additive where
  map_add := add_whiskerRight _ _ _

instance precomp_additive (c : B) {a b : B} (f : a ⟶ b) : (precomp c f).Additive where
  map_add := whiskerLeft_add _ _ _

theorem whiskerLeft_neg {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    f ◁ (-η) = -(f ◁ η) :=
  (precomp c f).map_neg

theorem neg_whiskerRight {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (-η) ▷ h = -(η ▷ h) :=
  (postcomp a h).map_neg

@[simp] theorem whiskerLeft_zero {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} :
    f ◁ (0 : g ⟶ h) = 0 :=
  (precomp c f).map_zero _ _

@[simp] theorem zero_whiskerRight {a b c : B} {f g : a ⟶ b} (h : b ⟶ c) :
    (0 : f ⟶ g) ▷ h = 0 :=
  (postcomp a h).map_zero _ _

end PreadditiveBicategory

namespace LinearBicategory

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B]

instance postcomp_linear (a : B) {b c : B} (g : b ⟶ c) : (postcomp a g).Linear R where
  map_smul η r := smul_whiskerRight r η g

instance precomp_linear (c : B) {a b : B} (f : a ⟶ b) : (precomp c f).Linear R where
  map_smul η r := whiskerLeft_smul f r η

end LinearBicategory

namespace PiTwoCategory

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [PiTwoCategory R B]

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)
local notation "𝛏" => PiTwoCategory.ξ (R := R)

theorem β_inv_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    𝛑 a ◁ η ≫ (𝛃 g).inv = (𝛃 f).inv ≫ η ▷ 𝛑 b := by
  rw [Iso.eq_inv_comp, ← Category.assoc, β_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

theorem β_pi_inv (a : B) : (𝛃 (𝛑 a)).inv = -𝟙 _ := by
  rw [← cancel_epi (𝛃 (𝛑 a)).hom, Iso.hom_inv_id, β_pi]
  simp

/-- `ξ_μ π_μ = π_μ ξ_μ`, in the form `π_μ ◁ ξ_μ ≫ ρ = α⁻¹ ≫ ξ_μ ▷ π_μ ≫ λ` (from `β_pi` and
`ξ_comm`, as in the paper after Definition 5.2(i)). -/
theorem whiskerLeft_ξ_pi (a : B) :
    𝛑 a ◁ (𝛏 a).hom ≫ (ρ_ (𝛑 a)).hom =
      (α_ (𝛑 a) (𝛑 a) (𝛑 a)).inv ≫ (𝛏 a).hom ▷ 𝛑 a ≫ (λ_ (𝛑 a)).hom := by
  have h := ξ_comm (R := R) (𝛑 a)
  rw [β_pi, PreadditiveBicategory.neg_whiskerRight, PreadditiveBicategory.whiskerLeft_neg] at h
  simp only [Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id, Preadditive.neg_comp,
    Preadditive.comp_neg, neg_neg, Category.id_comp, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc] at h
  rw [← h]
  simp [← Bicategory.comp_whiskerRight_assoc]

/-- The isomorphism `ξ_F := F ◁ ξ_μ : (F ≫ π_μ) ≫ π_μ ≅ F` (with associator and unitor). -/
def ξHom {a b : B} (f : a ⟶ b) : (f ≫ 𝛑 b) ≫ 𝛑 b ≅ f :=
  α_ f (𝛑 b) (𝛑 b) ≪≫ whiskerLeftIso f (𝛏 b) ≪≫ ρ_ f

theorem ξHom_hom {a b : B} (f : a ⟶ b) :
    (ξHom (R := R) f).hom = (α_ f (𝛑 b) (𝛑 b)).hom ≫ f ◁ (𝛏 b).hom ≫ (ρ_ f).hom := rfl

theorem ξHom_inv {a b : B} (f : a ⟶ b) :
    (ξHom (R := R) f).inv = (ρ_ f).inv ≫ f ◁ (𝛏 b).inv ≫ (α_ f (𝛑 b) (𝛑 b)).inv := by
  simp [ξHom]

@[reassoc]
theorem ξHom_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝛑 b ▷ 𝛑 b ≫ (ξHom (R := R) g).hom = (ξHom (R := R) f).hom ≫ η := by
  rw [ξHom_hom, ξHom_hom, associator_naturality_left_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]
  simp only [Category.assoc]

theorem ξHom_pi {a b : B} (f : a ⟶ b) :
    (ξHom (R := R) (f ≫ 𝛑 b)).hom = (ξHom (R := R) f).hom ▷ 𝛑 b := by
  have key : (f ≫ 𝛑 b) ◁ (𝛏 b).hom ≫ (ρ_ (f ≫ 𝛑 b)).hom =
      (α_ f (𝛑 b) (𝛑 b ≫ 𝛑 b)).hom ≫ f ◁ (𝛑 b ◁ (𝛏 b).hom ≫ (ρ_ (𝛑 b)).hom) := by bicategory
  rw [ξHom_hom, ξHom_hom, key, whiskerLeft_ξ_pi]
  bicategory

variable (R B) in
/-- **Brundan–Ellis, after Definition 5.2(i).** Each hom category of a Π-2-category is a
Π-category with `Π := - ≫ π_μ` and `ξ_F := F ◁ ξ_μ`. -/
instance homPiCategory (a b : B) : PiCategory R (a ⟶ b) where
  pi := postcomp a (𝛑 b)
  ξ := NatIso.ofComponents (fun f => ξHom (R := R) f) fun η => ξHom_naturality η
  ξ_pi f := ξHom_pi f

@[simp] theorem pi_obj {a b : B} (f : a ⟶ b) : (PiCategory.pi (R := R)).obj f = f ≫ 𝛑 b := rfl

@[simp] theorem pi_map {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    (PiCategory.pi (R := R)).map η = η ▷ 𝛑 b := rfl

@[simp] theorem ξApp_hom {a b : B} (f : a ⟶ b) :
    (PiCategory.ξApp (R := R) f).hom = (ξHom (R := R) f).hom := rfl

@[simp] theorem ξApp_inv {a b : B} (f : a ⟶ b) :
    (PiCategory.ξApp (R := R) f).inv = (ξHom (R := R) f).inv := rfl

@[simp] theorem ξ_hom_app {a b : B} (f : a ⟶ b) :
    (PiCategory.ξ (R := R) (C := a ⟶ b)).hom.app f = (ξHom (R := R) f).hom := rfl

@[simp] theorem ξ_inv_app {a b : B} (f : a ⟶ b) :
    (PiCategory.ξ (R := R) (C := a ⟶ b)).inv.app f = (ξHom (R := R) f).inv := rfl

end PiTwoCategory

/-! ## Π-2-functors and Π-2-natural transformations -/

section PiTwoFunctor

variable (R : Type w) [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [PiTwoCategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [PiTwoCategory R C]

open PiTwoCategory

/-- A Π-2-functor structure on a pseudofunctor `F` (Brundan–Ellis, Definition 5.2(ii)):
2-isomorphisms `j_λ : π_{Fλ} ≅ F π_λ` such that
`F β_F ∘ c ∘ j(F -) = c ∘ (F -)j ∘ β_{F -}` and `F ξ_λ ∘ c ∘ jj = i ∘ ξ_{Fλ}`. Here `c` and `i`
are the inverses of Mathlib's `mapComp` and `mapId`. We include the `R`-linearity of `F` on
2-morphisms (the paper's Π-2-functors are `k`-linear 2-functors). -/
structure PiTwoFunctor (F : Pseudofunctor B C) where
  map₂_add {a b : B} {f g : a ⟶ b} (η θ : f ⟶ g) : F.map₂ (η + θ) = F.map₂ η + F.map₂ θ
  map₂_smul {a b : B} {f g : a ⟶ b} (r : R) (η : f ⟶ g) : F.map₂ (r • η) = r • F.map₂ η
  /-- The coherence 2-isomorphisms `j_λ : π_{Fλ} ≅ F π_λ`. -/
  j (a : B) : pi (R := R) (F.obj a) ≅ F.map (pi (R := R) a)
  /-- The first coherence diagram of Definition 5.2(ii). -/
  β_comm {a b : B} (f : a ⟶ b) :
    F.map f ◁ (j b).hom ≫ (F.mapComp f (pi (R := R) b)).inv ≫ F.map₂ (β (R := R) f).hom =
      (β (R := R) (F.map f)).hom ≫ (j a).hom ▷ F.map f ≫ (F.mapComp (pi (R := R) a) f).inv
  /-- The second coherence diagram of Definition 5.2(ii). -/
  ξ_comm (a : B) :
    (j a).hom ▷ pi (R := R) (F.obj a) ≫ F.map (pi (R := R) a) ◁ (j a).hom ≫
        (F.mapComp (pi (R := R) a) (pi (R := R) a)).inv ≫ F.map₂ (ξ (R := R) a).hom =
      (ξ (R := R) (F.obj a)).hom ≫ (F.mapId a).inv

variable {R}

/-- A Π-2-natural transformation (Brundan–Ellis, Definition 5.2(iii)): an oplax natural
transformation `(X, x)` (the paper's 2-natural transformation) with
`x_{π_λ} ∘ X_λ j ∘ β_{X_λ} = j X_λ`. -/
def PiTwoFunctor.IsPiTwoNatural {F G : Pseudofunctor B C} (hF : PiTwoFunctor R F)
    (hG : PiTwoFunctor R G) (η : Oplax.OplaxTrans F.toOplax G.toOplax) : Prop :=
  ∀ a : B, (β (R := R) (η.app a)).hom ≫ (hF.j a).hom ▷ η.app a ≫ η.naturality (pi (R := R) a) =
    η.app a ◁ (hG.j a).hom

end PiTwoFunctor

/-! ## `E₂` on objects: the underlying Π-2-category of a Π-2-supercategory -/

namespace Underlying2

open BicategoryStruct

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A]

instance (a b : Underlying2 R A) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (Underlying R (a.obj ⟶ b.obj)))

instance (a b : Underlying2 R A) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (Underlying R (a.obj ⟶ b.obj)))

instance instPreadditiveBicategory : PreadditiveBicategory (Underlying2 R A) where
  whiskerLeft_add f _ _ η θ :=
    Subtype.ext (TwoSupercategory.whiskerLeft_add (R := R) f.obj η.1 θ.1)
  add_whiskerRight η θ h :=
    Subtype.ext (TwoSupercategory.add_whiskerRight (R := R) η.1 θ.1 h.obj)

instance instLinearBicategory : LinearBicategory R (Underlying2 R A) where
  whiskerLeft_smul f _ _ r η := Subtype.ext (TwoSupercategory.whiskerLeft_smul f.obj r η.1)
  smul_whiskerRight r η h := Subtype.ext (TwoSupercategory.smul_whiskerRight r η.1 h.obj)

variable [PiTwoSupercategory R A]

/-- **Brundan–Ellis, (5.4), `E₂` on objects.** The underlying bicategory of a Π-2-supercategory
is a Π-2-category, with the `β` and `ξ` of Lemma 3.2. -/
instance instPiTwoCategory : PiTwoCategory R (Underlying2 R A) where
  pi a := ⟨PiTwoSupercategory.pi (R := R) a.obj⟩
  β f := Underlying.isoMk (PiTwoSupercategory.β (R := R) f.obj)
    (PiTwoSupercategory.β_hom_mem f.obj)
  β_naturality η := Subtype.ext (PiTwoSupercategory.β_naturality η.1)
  β_comp f g := Subtype.ext (PiTwoSupercategory.β_comp f.obj g.obj)
  β_id a := Subtype.ext (PiTwoSupercategory.β_id a.obj)
  β_pi a := Subtype.ext (PiTwoSupercategory.β_pi a.obj)
  ξ a := Underlying.isoMk (PiTwoSupercategory.ξ (R := R) a.obj) (PiTwoSupercategory.ξ_hom_mem a.obj)
  ξ_comm f := Subtype.ext (PiTwoSupercategory.ξ_comm f.obj)

@[simp] theorem pi_obj (a : Underlying2 R A) :
    (PiTwoCategory.pi (R := R) a).obj = PiTwoSupercategory.pi (R := R) a.obj := rfl

@[simp] theorem β_hom_val {a b : Underlying2 R A} (f : a ⟶ b) :
    (PiTwoCategory.β (R := R) f).hom.1 = (PiTwoSupercategory.β (R := R) f.obj).hom := rfl

@[simp] theorem β_inv_val {a b : Underlying2 R A} (f : a ⟶ b) :
    (PiTwoCategory.β (R := R) f).inv.1 = (PiTwoSupercategory.β (R := R) f.obj).inv := rfl

@[simp] theorem ξ_hom_val (a : Underlying2 R A) :
    (PiTwoCategory.ξ (R := R) a).hom.1 = (PiTwoSupercategory.ξ (R := R) a.obj).hom := rfl

@[simp] theorem ξ_inv_val (a : Underlying2 R A) :
    (PiTwoCategory.ξ (R := R) a).inv.1 = (PiTwoSupercategory.ξ (R := R) a.obj).inv := rfl

end Underlying2

/-! ## `E₂` on 2-superfunctors -/

namespace TwoSuperfunctor

open BicategoryStruct TwoSupercategory

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [TwoSupercategory R A']
  (F : TwoSuperfunctor R A A')

/-- **Brundan–Ellis, (5.4), `E₂` on 2-superfunctors.** The restriction of a 2-superfunctor to
the underlying bicategories, a pseudofunctor with coherence maps `c⁻¹` and `i⁻¹`. -/
@[simps]
def toPseudofunctor : Pseudofunctor (Underlying2 R A) (Underlying2 R A') where
  obj a := ⟨F.obj a.obj⟩
  map f := ⟨F.map f.obj⟩
  map₂ η := ⟨F.map₂ η.1, F.map₂_mem η.2⟩
  map₂_id f := Subtype.ext (F.map₂_id f.obj)
  map₂_comp η θ := Subtype.ext (F.map₂_comp η.1 θ.1)
  mapId a := (Underlying.isoMk (F.mapId a.obj) (F.mapId_hom_mem a.obj)).symm
  mapComp f g := (Underlying.isoMk (F.mapComp f.obj g.obj) (F.mapComp_hom_mem _ _)).symm
  map₂_whisker_left f _ _ η := Subtype.ext (by
    change F.map₂ (f.obj ◁ η.1) = (F.mapComp f.obj _).inv ≫ F.map f.obj ◁ F.map₂ η.1 ≫
      (F.mapComp f.obj _).hom
    rw [F.mapComp_naturality_right, Iso.inv_hom_id_assoc])
  map₂_whisker_right η h := Subtype.ext (by
    change F.map₂ (η.1 ▷ h.obj) = (F.mapComp _ h.obj).inv ≫ F.map₂ η.1 ▷ F.map h.obj ≫
      (F.mapComp _ h.obj).hom
    rw [F.mapComp_naturality_left, Iso.inv_hom_id_assoc])
  map₂_associator f g h := Subtype.ext (by
    change F.map₂ (associator f.obj g.obj h.obj).hom =
      (F.mapComp (f.obj ≫ g.obj) h.obj).inv ≫ (F.mapComp f.obj g.obj).inv ▷ F.map h.obj ≫
        (associator (F.map f.obj) (F.map g.obj) (F.map h.obj)).hom ≫
          F.map f.obj ◁ (F.mapComp g.obj h.obj).hom ≫ (F.mapComp f.obj (g.obj ≫ h.obj)).hom
    have e := F.map₂_associator f.obj g.obj h.obj
    refine (cancel_mono (F.map₂Iso (associator f.obj g.obj h.obj)).inv).1 ?_
    rw [map₂Iso_inv, ← F.map₂_comp, Iso.hom_inv_id, F.map₂_id]
    simp only [Category.assoc]
    rw [e, Iso.hom_inv_id_assoc, ← comp_whiskerRight'_assoc R, Iso.inv_hom_id,
      id_whiskerRight (R := R), Category.id_comp, Iso.inv_hom_id])
  map₂_left_unitor f := Subtype.ext (by
    change F.map₂ (leftUnitor f.obj).hom = (F.mapComp (𝟙 _) f.obj).inv ≫
      (F.mapId _).inv ▷ F.map f.obj ≫ (leftUnitor (F.map f.obj)).hom
    rw [← F.map₂_leftUnitor f.obj, ← comp_whiskerRight'_assoc R, Iso.inv_hom_id,
      id_whiskerRight (R := R), Category.id_comp, Iso.inv_hom_id_assoc])
  map₂_right_unitor f := Subtype.ext (by
    change F.map₂ (rightUnitor f.obj).hom = (F.mapComp f.obj (𝟙 _)).inv ≫
      F.map f.obj ◁ (F.mapId _).inv ≫ (rightUnitor (F.map f.obj)).hom
    rw [← F.map₂_rightUnitor f.obj, ← whiskerLeft_comp'_assoc R, Iso.inv_hom_id,
      whiskerLeft_id (R := R), Category.id_comp, Iso.inv_hom_id_assoc])

variable [PiTwoSupercategory R A] [PiTwoSupercategory R A']

local notation "𝛑" => PiTwoSupercategory.pi (R := R)
local notation "𝛇" => PiTwoSupercategory.ζ (R := R)

/-- The coherence map `j := (ℝζ_λ)⁻¹ ∘ i ∘ ζ_{ℝλ} : π_{ℝλ} ≅ ℝπ_λ` of (5.4). -/
def jIso (a : A) : 𝛑 (F.obj a) ≅ F.map (𝛑 a) :=
  𝛇 (F.obj a) ≪≫ F.mapId a ≪≫ F.map₂Iso (𝛇 a).symm

omit [TwoSupercategory R A] [TwoSupercategory R A'] in
theorem jIso_hom (a : A) :
    (F.jIso a).hom = (𝛇 (F.obj a)).hom ≫ (F.mapId a).hom ≫ F.map₂ (𝛇 a).inv := rfl

omit [TwoSupercategory R A] [TwoSupercategory R A'] in
theorem jIso_hom_mem (a : A) :
    (F.jIso a).hom ∈ Supercategory.parity (R := R) (𝛑 (F.obj a)) (F.map (𝛑 a)) 0 := by
  have := Supercategory.comp_mem (Supercategory.comp_mem
    (PiTwoSupercategory.ζ_hom_mem (R := R) (F.obj a)) (F.mapId_hom_mem a))
    (F.map₂_mem (PiTwoSupercategory.ζ_inv_mem (R := R) a))
  simpa [jIso_hom] using this

omit [TwoSupercategory R A] [TwoSupercategory R A'] in
/-- `ℝζ_λ ∘ j = i ∘ ζ_{ℝλ}`: the defining property of `j`. -/
@[reassoc]
theorem jIso_hom_comp_map₂_ζ (a : A) :
    (F.jIso a).hom ≫ F.map₂ (𝛇 a).hom = (𝛇 (F.obj a)).hom ≫ (F.mapId a).hom := by
  rw [jIso_hom, Category.assoc, Category.assoc, ← F.map₂_comp, Iso.inv_hom_id, F.map₂_id,
    Category.comp_id]

omit [TwoSupercategory R A] [TwoSupercategory R A'] in
@[reassoc]
theorem mapId_hom_comp_map₂_ζ_inv (a : A) :
    (F.mapId a).hom ≫ F.map₂ (𝛇 a).inv = (𝛇 (F.obj a)).inv ≫ (F.jIso a).hom := by
  rw [jIso_hom, Iso.inv_hom_id_assoc]

/-- The first axiom of Definition 5.2(ii) for `E₂ ℝ`. -/
theorem jβ_comm {a b : A} (f : a ⟶ b) :
    F.map f ◁ (F.jIso b).hom ≫ (F.mapComp f (𝛑 b)).hom ≫
        F.map₂ (PiTwoSupercategory.β (R := R) f).hom =
      (PiTwoSupercategory.β (R := R) (F.map f)).hom ≫ (F.jIso a).hom ▷ F.map f ≫
        (F.mapComp (𝛑 a) f).hom := by
  have hl := F.map₂_leftUnitor f
  have hr := F.map₂_rightUnitor f
  rw [PiTwoSupercategory.β_hom, PiTwoSupercategory.β_hom, F.map₂_comp, F.map₂_comp,
    F.map₂_comp]
  rw [← reassoc_of% (F.mapComp_naturality_right f (𝛇 b).hom), ← whiskerLeft_comp'_assoc R,
    jIso_hom_comp_map₂_ζ, whiskerLeft_comp'_assoc R]
  have e1 : F.map f ◁ (F.mapId b).hom ≫ (F.mapComp f (𝟙 b)).hom ≫
      F.map₂ (rightUnitor f).hom = (rightUnitor (F.map f)).hom := hr
  have e2' : (leftUnitor (F.map f)).hom ≫ F.map₂ (leftUnitor f).inv =
      (F.mapId a).hom ▷ F.map f ≫ (F.mapComp (𝟙 a) f).hom := by
    rw [← hl]
    simp only [Category.assoc]
    rw [← F.map₂_comp, Iso.hom_inv_id, F.map₂_id, Category.comp_id]
  have e2 : F.map₂ (leftUnitor f).inv = (leftUnitor (F.map f)).inv ≫
      (F.mapId a).hom ▷ F.map f ≫ (F.mapComp (𝟙 a) f).hom := by
    rw [← e2', Iso.inv_hom_id_assoc]
  rw [reassoc_of% e1, e2]
  simp only [Category.assoc]
  rw [← F.mapComp_naturality_left, ← comp_whiskerRight'_assoc R, mapId_hom_comp_map₂_ζ_inv,
    comp_whiskerRight'_assoc R]

/-- The second axiom of Definition 5.2(ii) for `E₂ ℝ`. -/
theorem jξ_comm (a : A) :
    (F.jIso a).hom ▷ 𝛑 (F.obj a) ≫ F.map (𝛑 a) ◁ (F.jIso a).hom ≫
        (F.mapComp (𝛑 a) (𝛑 a)).hom ≫ F.map₂ (PiTwoSupercategory.ξ (R := R) a).hom =
      (PiTwoSupercategory.ξ (R := R) (F.obj a)).hom ≫ (F.mapId a).hom := by
  have hl := F.map₂_leftUnitor (𝛑 a)
  have hj := F.jIso_hom_mem a
  rw [PiTwoSupercategory.ξ_hom, PiTwoSupercategory.ξ_hom, F.map₂_comp, F.map₂_comp]
  rw [← reassoc_of% (F.mapComp_naturality_left (𝛇 a).hom (𝛑 a))]
  have e1 : (F.mapComp (𝟙 a) (𝛑 a)).hom ≫ F.map₂ (leftUnitor (𝛑 a)).hom =
      (F.mapId a).inv ▷ F.map (𝛑 a) ≫ (leftUnitor (F.map (𝛑 a))).hom := by
    rw [← hl, ← comp_whiskerRight'_assoc R, Iso.inv_hom_id, id_whiskerRight (R := R),
      Category.id_comp]
  rw [reassoc_of% e1, ← whisker_exchange_of_even_right_assoc _ hj,
    ← comp_whiskerRight'_assoc R, jIso_hom_comp_map₂_ζ, comp_whiskerRight'_assoc R,
    whisker_exchange_of_even_left_assoc (F.mapId_hom_mem a), TwoSupercategory.hom_inv_whiskerRight_assoc R,
    TwoSupercategory.leftUnitor_naturality_assoc R, jIso_hom_comp_map₂_ζ]
  simp only [Category.assoc]

/-- **Brundan–Ellis, (5.4).** `E₂ ℝ` is a Π-2-functor with `j := (ℝζ)⁻¹ ∘ i ∘ ζ`. -/
def toPiTwoFunctor : PiTwoFunctor R F.toPseudofunctor where
  map₂_add η θ := Subtype.ext (F.map₂_add η.1 θ.1)
  map₂_smul r η := Subtype.ext (F.map₂_smul r η.1)
  j a := Underlying.isoMk (F.jIso a.obj) (F.jIso_hom_mem a.obj)
  β_comm f := Subtype.ext (F.jβ_comm f.obj)
  ξ_comm a := Subtype.ext (F.jξ_comm a.obj)

@[simp] theorem toPiTwoFunctor_j_hom_val (a : Underlying2 R A) :
    (F.toPiTwoFunctor.j a).hom.1 = (F.jIso a.obj).hom := rfl

end TwoSuperfunctor

/-! ## `𝔼₂` on 2-natural transformations ((5.6)) -/

namespace TwoNatTrans

open BicategoryStruct TwoSupercategory

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [TwoSupercategory R A']
  {F G : TwoSuperfunctor R A A'} (θ : TwoNatTrans F G)

variable [PiTwoSupercategory R A] [PiTwoSupercategory R A']

local notation "𝛑" => PiTwoSupercategory.pi (R := R)
local notation "𝛇" => PiTwoSupercategory.ζ (R := R)

/-- **Brundan–Ellis, (5.6).** `𝔼₂(X, x) = (X̲, x̲)` (the oplax transformation
`TwoNatTrans.toOplaxTrans` of the underlying bicategories) is Π-2-natural: the coherence axiom of
Definition 5.2(iii) holds. -/
theorem isPiTwoNatural :
    F.toPiTwoFunctor.IsPiTwoNatural G.toPiTwoFunctor θ.toOplaxTrans := fun a => Subtype.ext (by
  change (PiTwoSupercategory.β (R := R) (θ.X a.obj)).hom ≫ (F.jIso a.obj).hom ▷ θ.X a.obj ≫
    θ.x (𝛑 a.obj) = θ.X a.obj ◁ (G.jIso a.obj).hom
  have hn := θ.naturality (𝛇 a.obj).inv
  have hid := θ.x_id a.obj
  rw [TwoSuperfunctor.jIso_hom, comp_whiskerRight'_assoc R, comp_whiskerRight'_assoc R, hn,
    PiTwoSupercategory.β_hom_comp_ζ_assoc]
  rw [reassoc_of% hid, TwoSuperfunctor.jIso_hom, whiskerLeft_comp' R, whiskerLeft_comp' R])

end TwoNatTrans

end StringDiagrams

end
