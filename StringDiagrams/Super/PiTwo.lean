import StringDiagrams.Super.UnderlyingBicategory
import StringDiagrams.Super.SCat

/-!
# Π-2-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 3.1, Lemma 3.2 and Corollary 3.3.

A Π-2-supercategory `(𝔄, π, ζ)` is a 2-supercategory with 1-morphisms `π_λ : λ → λ` and odd
2-isomorphisms `ζ_λ : π_λ ⇒ 1_λ` (`StringDiagrams.PiTwoSupercategory`, Definition 3.1). It is
strict if the underlying 2-supercategory is (`BicategoryStruct.Strict`).

## Lemma 3.2

For a 1-morphism `F : λ → μ`, the paper defines (for strict `𝔄`)
`(β_{μ,λ})_F := -ζ_μ F ζ_λ⁻¹ : π_μ F ⇒ F π_λ`. We work with an arbitrary (not necessarily
strict) Π-2-supercategory, inserting the unitors: in the diagrammatic order `F ≫ π_μ` for
`π_μ F`,

`β F := F ◁ ζ_μ ≫ ρ_F ≫ λ_F⁻¹ ≫ ζ_λ⁻¹ ▷ F : F ≫ π_μ ≅ π_λ ≫ F`

(`PiTwoSupercategory.β`). The minus sign of the paper is absorbed by the super interchange
law: `β_hom_eq_neg_hcomp` recovers the literal formula
`-(λ⁻¹ ≫ (ζ_λ⁻¹ ⋆ F ζ_μ) ≫ π_λ ◁ ρ_F)`, where `⋆` is the horizontal composition
`TwoSupercategory.hcomp`. In a strict 2-supercategory the unitors and associators below are
identities (for `𝔖ℭ𝔞𝔱` definitionally), and the statements reduce to the printed ones.

* `β_hom_mem`: `β` is even; `β_naturality` (equation (3.1)) and `β_isSupernatural`: `β` is an
  even supernatural isomorphism `π_μ - ⇒ - π_λ` between superfunctors
  `ℋom(λ, μ) → ℋom(λ, μ)` (`TwoSupercategory.postcomp`, `TwoSupercategory.precomp`).
* (i) `β_comp`: `β_{GF} = G β_F ∘ β_G F`, with associators.
* (ii) `β_id`: `β_{1_λ} = 1_{π_λ}`, i.e. `λ_{π_λ} ≫ ρ_{π_λ}⁻¹`.
* (iii) `pi_whisker_ζ`: `π_λ ζ_λ = -ζ_λ π_λ`, and `β_pi`: `β_{π_λ} = -1`.
* (iv) `ξ λ := ζ_λ ζ_λ : π_λ² ≅ 1_λ` is even (`ξ_hom_mem`), with
  `ξ_μ F ξ_λ⁻¹ = β_F π_λ ∘ π_μ β_F` (`ξ_comm`).

That `(π, β)` is an object of the Drinfeld center (Definition 2.3) is
`PiTwoSupercategory.centerObj` in `StringDiagrams.Super.TwoFunctor`.

## Π-𝔖ℭ𝔞𝔱

`PiSCat R` is a strict Π-2-supercategory with `π_A = Π_A` and `ζ_A` the given odd
supernatural isomorphism `Π_A ⇒ I_A` (`PiSCat.instPiTwoSupercategory`). In it, the components
of `β F` and `ξ A` are those of `PiSupercategory.β` and `PiSupercategory.ξ` (`PiSCat.β_app`,
`PiSCat.ξ_app`), and Lemma 3.2 specializes to Corollary 3.3, which is proved directly in
`StringDiagrams.Super.Pi`; we re-derive it from Lemma 3.2 (`PiSCat.pi_map_ζ`,
`PiSCat.ξ_pi`, `PiSCat.β_comm`, `PiSCat.β_naturality_supernatural`, `PiSCat.β_comp`,
`PiSCat.β_id`, `PiSCat.β_pi`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct

universe w v u w₁

/-! ## The superfunctors `h -` and `- f` -/

namespace TwoSupercategory

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

variable (R) in
/-- Horizontal composition with a fixed 1-morphism `h : b ⟶ c` on the left in the paper's
notation (`h -`), i.e. `f ↦ f ≫ h`: a superfunctor `ℋom(a, b) → ℋom(a, c)`. -/
@[simps]
def postcomp {a b c : B} (h : b ⟶ c) : (a ⟶ b) ⥤ (a ⟶ c) where
  obj f := f ≫ h
  map η := η ▷ h
  map_id f := id_whiskerRight (R := R) f h
  map_comp η θ := comp_whiskerRight (R := R) η θ h

variable (R) in
/-- Horizontal composition with a fixed 1-morphism `f : a ⟶ b` on the right in the paper's
notation (`- f`), i.e. `g ↦ f ≫ g`: a superfunctor `ℋom(b, c) → ℋom(a, c)`. -/
@[simps]
def precomp {a b c : B} (f : a ⟶ b) : (b ⟶ c) ⥤ (a ⟶ c) where
  obj g := f ≫ g
  map η := f ◁ η
  map_id g := whiskerLeft_id (R := R) f g
  map_comp η θ := whiskerLeft_comp (R := R) f η θ

instance {a b c : B} (h : b ⟶ c) : (postcomp R (a := a) h).Additive where
  map_add := add_whiskerRight (R := R) _ _ h

instance {a b c : B} (h : b ⟶ c) : (postcomp R (a := a) h).Linear R where
  map_smul η r := smul_whiskerRight r η h

instance {a b c : B} (h : b ⟶ c) : IsSuperfunctor R (postcomp R (a := a) h) where
  map_mem hη := whiskerRight_mem h hη

instance {a b c : B} (f : a ⟶ b) : (precomp R (c := c) f).Additive where
  map_add := whiskerLeft_add (R := R) f _ _

instance {a b c : B} (f : a ⟶ b) : (precomp R (c := c) f).Linear R where
  map_smul η r := whiskerLeft_smul f r η

instance {a b c : B} (f : a ⟶ b) : IsSuperfunctor R (precomp R (c := c) f) where
  map_mem hη := whiskerLeft_mem f hη

end TwoSupercategory

/-! ## Π-2-supercategories -/

variable (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- A Π-2-supercategory (Brundan–Ellis, Definition 3.1): a 2-supercategory with 1-morphisms
`π_λ : λ → λ` and odd 2-isomorphisms `ζ_λ : π_λ ⇒ 1_λ`. It is strict if the 2-supercategory is
strict (`BicategoryStruct.Strict B`). -/
class PiTwoSupercategory where
  /-- The 1-morphisms `π_λ`. -/
  pi : ∀ a : B, a ⟶ a
  /-- The odd 2-isomorphisms `ζ_λ : π_λ ⇒ 1_λ`. -/
  ζ : ∀ a : B, pi a ≅ 𝟙 a
  ζ_hom_mem : ∀ a : B, (ζ a).hom ∈ parity (R := R) (pi a) (𝟙 a) 1

namespace PiTwoSupercategory

variable {R B} [PiTwoSupercategory R B]

open TwoSupercategory

section

variable {a b c : B}

omit [TwoSupercategory R B] in
theorem ζ_inv_mem (a : B) : (ζ (R := R) a).inv ∈ parity (R := R) (𝟙 a) (pi (R := R) a) 1 :=
  inv_mem _ (ζ_hom_mem a)

/-! ### The isomorphisms `β` -/

/-- **Lemma 3.2.** The even 2-isomorphism `β_F : π_μ F ⇒ F π_λ`, for `F : λ → μ`, in the
diagrammatic order: `β F := F ◁ ζ_μ ≫ ρ_F ≫ λ_F⁻¹ ≫ ζ_λ⁻¹ ▷ F : F ≫ π_μ ≅ π_λ ≫ F`. The
paper's formula `β_F = -ζ_μ F ζ_λ⁻¹` is `β_hom_eq_neg_hcomp`. -/
def β (f : a ⟶ b) : f ≫ pi (R := R) b ≅ pi (R := R) a ≫ f :=
  whiskerLeftIso (R := R) f (ζ (R := R) b) ≪≫ rightUnitor f ≪≫ (leftUnitor f).symm ≪≫
    whiskerRightIso (R := R) (ζ (R := R) a).symm f

theorem β_hom (f : a ⟶ b) : (β (R := R) f).hom =
    f ◁ (ζ (R := R) b).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv ≫
      (ζ (R := R) a).inv ▷ f := by
  simp [β]

theorem β_inv (f : a ⟶ b) : (β (R := R) f).inv =
    (ζ (R := R) a).hom ▷ f ≫ (leftUnitor f).hom ≫ (rightUnitor f).inv ≫
      f ◁ (ζ (R := R) b).inv := by
  simp [β]

/-- **Lemma 3.2.** `β_F` is even. -/
theorem β_hom_mem (f : a ⟶ b) :
    (β (R := R) f).hom ∈ parity (R := R) (f ≫ pi (R := R) b) (pi (R := R) a ≫ f) 0 := by
  rw [β_hom]
  have h := comp_mem (comp_mem (comp_mem (whiskerLeft_mem f (ζ_hom_mem (R := R) b))
    (rightUnitor_hom_mem (R := R) f)) (inv_mem _ (leftUnitor_hom_mem (R := R) f)))
    (whiskerRight_mem f (ζ_inv_mem (R := R) a))
  simpa [Category.assoc] using h

/-- `β_F` followed by `ζ_λ F` is `ζ_μ` on the other side: `ζ_λ F ∘ β_F = F ζ_μ` up to unitors.
This says that `ζ` is an (odd) morphism from `(π, β)` to the unit of the Drinfeld center. -/
@[reassoc]
theorem β_hom_comp_ζ (f : a ⟶ b) :
    (β (R := R) f).hom ≫ (ζ (R := R) a).hom ▷ f =
      f ◁ (ζ (R := R) b).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv := by
  rw [β_hom]; simp only [Category.assoc, inv_hom_whiskerRight R, Category.comp_id]

/-- **Lemma 3.2**, the paper's formula `β_F = -ζ_μ F ζ_λ⁻¹`: minus the horizontal composite of
`ζ_λ⁻¹ : 1_λ ⇒ π_λ` and `F ζ_μ : F ≫ π_μ ⇒ F ≫ 1_μ`, composed with the unitors
`F ≫ π_μ ≅ 1_λ ≫ F ≫ π_μ` and `π_λ ≫ F ≫ 1_μ ≅ π_λ ≫ F`. -/
theorem β_hom_eq_neg_hcomp (f : a ⟶ b) :
    (β (R := R) f).hom = -((leftUnitor (f ≫ pi (R := R) b)).inv ≫
      hcomp (ζ (R := R) a).inv (f ◁ (ζ (R := R) b).hom) ≫ pi (R := R) a ◁ (rightUnitor f).hom) := by
  rw [hcomp_eq (R := R) (ζ_inv_mem a) (whiskerLeft_mem f (ζ_hom_mem b)), koszulSign_one_one,
    neg_smul, one_smul, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.assoc,
    ← leftUnitor_inv_naturality_assoc R]
  have h := super_interchange (R := R) (ζ_inv_mem (R := R) a)
    (rightUnitor_hom_mem (R := R) f)
  rw [koszulSign_zero_right, one_smul] at h
  rw [h, ← leftUnitor_inv_naturality_assoc R, β_hom]

/-- **Lemma 3.2, equation (3.1).** `β` is natural: `x π_λ ∘ β_F = β_G ∘ π_μ x` for every
2-morphism `x : F ⇒ G`. -/
theorem β_naturality {f g : a ⟶ b} (x : f ⟶ g) :
    (β (R := R) f).hom ≫ pi (R := R) a ◁ x = x ▷ pi (R := R) b ≫ (β (R := R) g).hom := by
  refine induction_on (R := R) x (by simp [zero_whiskerRight R, whiskerLeft_zero R])
    (fun p x hx => ?_) (fun x y hx hy => ?_)
  · rw [β_hom, β_hom]
    simp only [Category.assoc]
    have h1 := super_interchange (R := R) (ζ_inv_mem (R := R) a) hx
    have h2 := super_interchange (R := R) hx (ζ_hom_mem (R := R) b)
    rw [h1, Linear.comp_smul, Linear.comp_smul, Linear.comp_smul,
      ← leftUnitor_inv_naturality_assoc R, ← rightUnitor_naturality_assoc R,
      ← Category.assoc (f ◁ _), ← koszulSign_smul_smul p 1 (f ◁ _ ≫ x ▷ 𝟙 b), ← h2,
      Linear.smul_comp, smul_smul, koszulSign_comm 1 p, koszulSign_mul_self, one_smul]
    simp only [Category.assoc]
  · rw [whiskerLeft_add (R := R), add_whiskerRight (R := R), Preadditive.comp_add,
      Preadditive.add_comp, hx, hy]

/-! ### The even isomorphism `ξ = ζζ` -/

/-- **Lemma 3.2(iv).** The 2-isomorphism `ξ_λ := ζ_λ ζ_λ : π_λ² ⇒ 1_λ`, in the form
`ζ_λ ▷ π_λ ≫ λ_{π_λ} ≫ ζ_λ`; see `ξ_hom_eq_hcomp` for the horizontal composite. -/
def ξ (a : B) : pi (R := R) a ≫ pi (R := R) a ≅ 𝟙 a :=
  whiskerRightIso (R := R) (ζ (R := R) a) (pi (R := R) a) ≪≫ leftUnitor (pi (R := R) a) ≪≫
    ζ (R := R) a

theorem ξ_hom (a : B) : (ξ (R := R) a).hom =
    (ζ (R := R) a).hom ▷ pi (R := R) a ≫ (leftUnitor (pi (R := R) a)).hom ≫ (ζ (R := R) a).hom := by
  simp [ξ]

theorem ξ_inv (a : B) : (ξ (R := R) a).inv =
    (ζ (R := R) a).inv ≫ (leftUnitor (pi (R := R) a)).inv ≫ (ζ (R := R) a).inv ▷ pi (R := R) a := by
  simp [ξ]

/-- `ξ_λ` is the horizontal composite `ζ_λ ζ_λ : π_λ π_λ ⇒ 1_λ 1_λ`, followed by the unitor
`1_λ 1_λ ≅ 1_λ`. -/
theorem ξ_hom_eq_hcomp (a : B) : (ξ (R := R) a).hom =
    hcomp (ζ (R := R) a).hom (ζ (R := R) a).hom ≫ (leftUnitor (𝟙 a)).hom := by
  rw [ξ_hom, hcomp, Category.assoc, leftUnitor_naturality R]

/-- **Lemma 3.2(iv).** `ξ_λ` is even. -/
theorem ξ_hom_mem (a : B) :
    (ξ (R := R) a).hom ∈ parity (R := R) (pi (R := R) a ≫ pi (R := R) a) (𝟙 a) 0 := by
  rw [ξ_hom]
  have h := comp_mem (comp_mem (whiskerRight_mem (pi (R := R) a) (ζ_hom_mem (R := R) a))
    (leftUnitor_hom_mem (R := R) (pi (R := R) a))) (ζ_hom_mem (R := R) a)
  simpa [Category.assoc] using h

end

end PiTwoSupercategory

/-! ## Π-𝔖ℭ𝔞𝔱 is a strict Π-2-supercategory -/

namespace PiSCat

open PiSupercategory

variable {R}

/-- The parity-switching superfunctor `Π_A` of a Π-supercategory, as a 1-morphism of
`Π-𝔖ℭ𝔞𝔱`. -/
def piHom (A : PiSCat.{w₁, v, u} R) : A ⟶ A := ⟨PiSupercategory.pi (R := R) (C := A)⟩

theorem ζ_inv_isSupernatural (A : PiSCat.{w₁, v, u} R) :
    IsSupernatural R 1 (F := 𝟭 A) (G := PiSupercategory.pi (R := R) (C := A))
      fun X => (PiSupercategory.ζ (R := R) X).inv :=
  IsSupernatural.of_twist (fun X => PiSupercategory.ζ_inv_mem X) fun {X Y} f => by
    rw [pi_map_eq, twist_twist, Iso.inv_hom_id_assoc]; rfl

/-- The odd supernatural isomorphism `ζ_A : Π_A ⇒ I_A`, as a 2-isomorphism of `Π-𝔖ℭ𝔞𝔱`. -/
def ζHom (A : PiSCat.{w₁, v, u} R) : piHom A ≅ 𝟙 A where
  hom := (PiSupercategory.ζ_isSupernatural (R := R) (C := A)).toSuperNatTrans
  inv := (ζ_inv_isSupernatural A).toSuperNatTrans
  hom_inv_id := hom_ext (fun X => by simp [IsSupernatural.toSuperNatTrans])
    (fun X => by simp [IsSupernatural.toSuperNatTrans])
  inv_hom_id := hom_ext (fun X => by simp [IsSupernatural.toSuperNatTrans])
    (fun X => by simp [IsSupernatural.toSuperNatTrans])

/-- **Brundan–Ellis, Section 3.** `Π-𝔖ℭ𝔞𝔱` is a (strict) Π-2-supercategory, with
`π_A := Π_A` and `ζ_A : Π_A ⇒ I_A` the given odd supernatural isomorphism. -/
instance instPiTwoSupercategory : PiTwoSupercategory R (PiSCat.{w₁, v, u} R) where
  pi := piHom
  ζ := ζHom
  ζ_hom_mem A :=
    Superfunctor.IsSupernatural.toSuperNatTrans_mem (PiSupercategory.ζ_isSupernatural (R := R) (C := A))

@[simp] theorem ζ_hom_app_one (A : PiSCat.{w₁, v, u} R) (X : A) :
    (PiTwoSupercategory.ζ (R := R) A).hom.app 1 X = (PiSupercategory.ζ (R := R) X).hom := rfl

@[simp] theorem ζ_hom_app_zero (A : PiSCat.{w₁, v, u} R) (X : A) :
    (PiTwoSupercategory.ζ (R := R) A).hom.app 0 X = 0 := rfl

@[simp] theorem ζ_inv_app_one (A : PiSCat.{w₁, v, u} R) (X : A) :
    (PiTwoSupercategory.ζ (R := R) A).inv.app 1 X = (PiSupercategory.ζ (R := R) X).inv := rfl

@[simp] theorem ζ_inv_app_zero (A : PiSCat.{w₁, v, u} R) (X : A) :
    (PiTwoSupercategory.ζ (R := R) A).inv.app 0 X = 0 := rfl

end PiSCat

end StringDiagrams

end
