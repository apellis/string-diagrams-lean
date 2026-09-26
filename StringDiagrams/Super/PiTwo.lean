import StringDiagrams.Super.UnderlyingBicategory
import StringDiagrams.Super.SCat

/-!
# Π-2-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 3.1, Lemma 3.2 and Corollary 3.3.

A Π-2-supercategory `(𝔄, π, ζ)` is a 2-supercategory with 1-morphisms `π_λ : λ → λ` and odd
2-isomorphisms `ζ_λ : π_λ ⇒ 1_λ` (`StringDiagrams.PiTwoSupercategory`, Definition 3.1). It is
strict if the underlying 2-supercategory is (`BicategoryStruct.Strict`).

Each morphism supercategory `ℋom(λ, μ)` is a Π-supercategory with `Π := π_μ -`
(`PiTwoSupercategory.homPiLeft`) or `Π := - π_λ` (`PiTwoSupercategory.homPiRight`).

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
`PiTwoSupercategory.centerObj` in `StringDiagrams.Super.DrinfeldCenter`, where `ζ` and `ξ`
also become isomorphisms `(π, β) ≅ 1` and `(π, β) ⊗ (π, β) ≅ 1` of the Drinfeld center.

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

/-! ### The Π-supercategories `ℋom(λ, μ)` -/

variable (a b) in
/-- Each morphism supercategory `ℋom(λ, μ)` of a Π-2-supercategory is a Π-supercategory with
`Π := π_μ -` (i.e. `f ↦ f ≫ π_μ`) and `ζ_F := F ζ_μ` (followed by the unitor). -/
def homPiLeft : PiSupercategory R (a ⟶ b) where
  pi := postcomp R (pi (R := R) b)
  ζ f := whiskerLeftIso (R := R) f (ζ (R := R) b) ≪≫ rightUnitor f
  ζ_isSupernatural :=
    { mem := fun f => by
        simpa using comp_mem (whiskerLeft_mem f (ζ_hom_mem (R := R) b))
          (rightUnitor_hom_mem (R := R) f)
      naturality := fun {f g q η} hη => by
        simp only [postcomp_obj, postcomp_map, Functor.id_obj, Functor.id_map, Iso.trans_hom,
          whiskerLeftIso_hom, one_mul]
        rw [← Category.assoc, super_interchange hη (ζ_hom_mem (R := R) b), Linear.smul_comp,
          Category.assoc, rightUnitor_naturality R, koszulSign_smul (R := R), mul_one,
          Category.assoc] }

variable (a b) in
/-- Each morphism supercategory `ℋom(λ, μ)` of a Π-2-supercategory is also a Π-supercategory
with `Π := - π_λ` (i.e. `f ↦ π_λ ≫ f`) and `ζ_F := ζ_λ F` (followed by the unitor); by
Lemma 3.2, `β_{μ,λ}` is an even supernatural isomorphism between the two parity-switching
functors (`β_isSupernatural`). -/
def homPiRight : PiSupercategory R (a ⟶ b) where
  pi := precomp R (pi (R := R) a)
  ζ f := whiskerRightIso (R := R) (ζ (R := R) a) f ≪≫ leftUnitor f
  ζ_isSupernatural :=
    { mem := fun f => by
        simpa using comp_mem (whiskerRight_mem f (ζ_hom_mem (R := R) a))
          (leftUnitor_hom_mem (R := R) f)
      naturality := fun {f g q η} hη => by
        simp only [precomp_obj, precomp_map, Functor.id_obj, Functor.id_map, Iso.trans_hom,
          whiskerRightIso_hom, one_mul]
        have h := super_interchange (R := R) (ζ_hom_mem (R := R) a) hη
        rw [← Category.assoc, ← koszulSign_smul_smul 1 q (pi (R := R) a ◁ η ≫ _), ← h,
          Linear.smul_comp, Category.assoc, leftUnitor_naturality R, koszulSign_smul (R := R),
          Category.assoc, one_mul] }

/-! ### Lemma 3.2 -/

variable (a b) in
/-- **Lemma 3.2.** `β_{μ,λ}` is an even supernatural isomorphism `π_μ - ⇒ - π_λ` between the
superfunctors `ℋom(λ, μ) → ℋom(λ, μ)` given by horizontal composition with `π_μ` and
`π_λ`. -/
theorem β_isSupernatural :
    IsSupernatural R 0 (F := postcomp R (a := a) (pi (R := R) b))
      (G := precomp R (c := b) (pi (R := R) a)) fun f => (β (R := R) f).hom where
  mem f := β_hom_mem f
  naturality {f g q x} _ := by
    simp only [postcomp_obj, postcomp_map, precomp_obj, precomp_map, zero_mul, sign_zero,
      one_smul]
    exact (β_naturality x).symm

/-- **Lemma 3.2(i).** `(β_{ν,λ})_{GF} = G (β_{μ,λ})_F ∘ (β_{ν,μ})_G F`, i.e.
`β_{F ≫ G} = α ≫ F ◁ β_G ≫ α⁻¹ ≫ β_F ▷ G ≫ α`. -/
theorem β_comp (f : a ⟶ b) (g : b ⟶ c) :
    (β (R := R) (f ≫ g)).hom =
      (associator f g (pi (R := R) c)).hom ≫ f ◁ (β (R := R) g).hom ≫
        (associator f (pi (R := R) b) g).inv ≫ (β (R := R) f).hom ▷ g ≫
          (associator (pi (R := R) a) f g).hom := by
  symm
  simp only [β_hom, whiskerLeft_comp' R, comp_whiskerRight' R, Category.assoc]
  rw [associator_inv_naturality_middle_assoc R, ← comp_whiskerRight'_assoc R,
    ← whiskerLeft_comp' R, Iso.inv_hom_id, whiskerLeft_id (R := R), id_whiskerRight (R := R),
    Category.id_comp, ← triangle (R := R), Category.assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_inv_hom_assoc R, associator_naturality_left R, ← leftUnitor_comp_inv_assoc R,
    ← associator_naturality_right_assoc R, ← rightUnitor_comp_assoc R]

/-- **Lemma 3.2(ii).** `(β_{λ,λ})_{1_λ} = 1_{π_λ}`, i.e. `β_{1_λ} = λ_{π_λ} ≫ ρ_{π_λ}⁻¹`. -/
theorem β_id (a : B) :
    (β (R := R) (𝟙 a)).hom = (leftUnitor (pi (R := R) a)).hom ≫ (rightUnitor (pi (R := R) a)).inv := by
  rw [β_hom, ← unitors_equal R, Iso.hom_inv_id_assoc, id_whiskerLeft (R := R),
    whiskerRight_id (R := R), Category.assoc, Category.assoc, ← unitors_equal R,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

/-- **Lemma 3.2(iii).** `π_λ ζ_λ = -ζ_λ π_λ`, i.e.
`ζ_λ ▷ π_λ ≫ λ_{π_λ} = -(π_λ ◁ ζ_λ ≫ ρ_{π_λ})`. -/
theorem pi_whisker_ζ (a : B) :
    (ζ (R := R) a).hom ▷ pi (R := R) a ≫ (leftUnitor (pi (R := R) a)).hom =
      -(pi (R := R) a ◁ (ζ (R := R) a).hom ≫ (rightUnitor (pi (R := R) a)).hom) := by
  have h := super_interchange (R := R) (ζ_hom_mem (R := R) a) (ζ_hom_mem (R := R) a)
  rw [koszulSign_one_one, neg_smul, one_smul, id_whiskerLeft (R := R),
    whiskerRight_id (R := R), ← unitors_inv_equal R] at h
  apply (cancel_mono ((ζ (R := R) a).hom ≫ (leftUnitor (𝟙 a)).inv)).1
  simpa only [Category.assoc, Preadditive.neg_comp] using h

/-- **Lemma 3.2(iii).** `(β_{λ,λ})_{π_λ} = -1_{π_λ²}`. -/
theorem β_pi (a : B) : (β (R := R) (pi (R := R) a)).hom = -𝟙 _ := by
  have h : pi (R := R) a ◁ (ζ (R := R) a).hom ≫ (rightUnitor (pi (R := R) a)).hom =
      -((ζ (R := R) a).hom ▷ pi (R := R) a ≫ (leftUnitor (pi (R := R) a)).hom) := by
    rw [pi_whisker_ζ, neg_neg]
  rw [β_hom, ← Category.assoc, h]
  simp only [Preadditive.neg_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [hom_inv_whiskerRight R]

/-- **Lemma 3.2(iv).** `ξ_μ F ξ_λ⁻¹ = (β_{μ,λ})_F π_λ ∘ π_μ (β_{μ,λ})_F` in
`Hom(π_μ² F, F π_λ²)`, where `ξ_μ F ξ_λ⁻¹ = F ◁ ξ_μ ≫ ρ_F ≫ λ_F⁻¹ ≫ ξ_λ⁻¹ ▷ F` (both
factors are even, so the order of the horizontal composition does not matter). -/
theorem ξ_comm (f : a ⟶ b) :
    f ◁ (ξ (R := R) b).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv ≫ (ξ (R := R) a).inv ▷ f =
      (associator f (pi (R := R) b) (pi (R := R) b)).inv ≫ (β (R := R) f).hom ▷ pi (R := R) b ≫
        (associator (pi (R := R) a) f (pi (R := R) b)).hom ≫ pi (R := R) a ◁ (β (R := R) f).hom ≫
          (associator (pi (R := R) a) (pi (R := R) a) f).inv := by
  -- Notation: `(pi (R := R) a) = π_λ`, `(pi (R := R) b) = π_μ`, `z = ζ_λ`, `y = ζ_μ`.
  have hz := ζ_hom_mem (R := R) a
  have hy := ζ_hom_mem (R := R) b
  have hβ := β_hom_mem (R := R) f
  -- The key identity: the right-hand side followed by `ξ_λ F` is `F ξ_μ` (with unitors).
  have key : (associator f (pi (R := R) b) (pi (R := R) b)).inv ≫ (β (R := R) f).hom ▷ (pi (R := R) b) ≫ (associator (pi (R := R) a) f (pi (R := R) b)).hom ≫
      (pi (R := R) a) ◁ (β (R := R) f).hom ≫ (associator (pi (R := R) a) (pi (R := R) a) f).inv ≫ (ξ (R := R) a).hom ▷ f =
        f ◁ (ξ (R := R) b).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv := by
    rw [ξ_hom, comp_whiskerRight' R, comp_whiskerRight' R,
      ← associator_inv_naturality_left_assoc R]
    have h2 : (pi (R := R) a) ◁ (β (R := R) f).hom ≫ (ζ (R := R) a).hom ▷ ((pi (R := R) a) ≫ f) =
        (ζ (R := R) a).hom ▷ (f ≫ (pi (R := R) b)) ≫ 𝟙 a ◁ (β (R := R) f).hom :=
      (whisker_exchange_of_even_right (ζ (R := R) a).hom hβ).symm
    rw [reassoc_of% h2, ← leftUnitor_comp_assoc R, leftUnitor_naturality_assoc R,
      β_hom_comp_ζ, ← associator_naturality_left_assoc R,
      ← leftUnitor_whiskerRight_assoc R, ← comp_whiskerRight'_assoc R,
      ← comp_whiskerRight'_assoc R, Category.assoc, β_hom_comp_ζ_assoc, Iso.inv_hom_id,
      Category.comp_id, comp_whiskerRight'_assoc R,
      whisker_exchange_of_even_left_assoc (rightUnitor_hom_mem (R := R) f),
      super_interchange_assoc (whiskerLeft_mem f hy) hy, koszulSign_one_one, neg_smul, one_smul,
      Preadditive.comp_neg, rightUnitor_naturality_assoc R, rightUnitor_naturality_assoc R,
      ← associator_inv_naturality_right_assoc R, ← whiskerLeft_rightUnitor_assoc R,
      ξ_hom, ← Category.assoc ((ζ (R := R) b).hom ▷ (pi (R := R) b)), pi_whisker_ζ, Preadditive.neg_comp,
      whiskerLeft_neg R, whiskerLeft_comp' R, whiskerLeft_comp' R]
    simp only [Preadditive.neg_comp, Category.assoc]
  rw [← reassoc_of% key]
  simp only [Category.assoc, hom_inv_whiskerRight R, Category.comp_id]

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

/-! ### Corollary 3.3 from Lemma 3.2 -/

section Corollary

variable {A B C : PiSCat.{w₁, v, u} R}

@[simp] theorem piHom_obj (X : A.carrier) :
    Superfunctor.obj (PiTwoSupercategory.pi (R := R) A) X = (PiSupercategory.pi (R := R)).obj X :=
  rfl

@[simp] theorem piHom_map {X Y : A.carrier} (f : X ⟶ Y) :
    Superfunctor.map (PiTwoSupercategory.pi (R := R) A) f = (PiSupercategory.pi (R := R)).map f :=
  rfl

/-- In `Π-𝔖ℭ𝔞𝔱`, the components of `β_F` of Lemma 3.2 are those of `β_F` of Corollary 3.3
(`PiSupercategory.β`). -/
theorem β_app_zero (F : A ⟶ B) (X : A.carrier) :
    (PiTwoSupercategory.β (R := R) F).hom.app 0 X = (PiSupercategory.β R F.toFunctor X).hom := by
  simp [PiTwoSupercategory.β_hom, PiSupercategory.β_hom]

theorem β_app_one (F : A ⟶ B) (X : A.carrier) :
    (PiTwoSupercategory.β (R := R) F).hom.app 1 X = 0 := by
  simp [PiTwoSupercategory.β_hom]

/-- In `Π-𝔖ℭ𝔞𝔱`, the components of `ξ` of Lemma 3.2 are those of `ξ` of (1.4)
(`PiSupercategory.ξ`). -/
theorem ξ_app_zero (A : PiSCat.{w₁, v, u} R) (X : A.carrier) :
    (PiTwoSupercategory.ξ (R := R) A).hom.app 0 X = (PiSupercategory.ξ (R := R) X).hom := by
  simp [PiTwoSupercategory.ξ_hom, PiSupercategory.ξ_hom]

/-- **Corollary 3.3(i)**, derived from Lemma 3.2(iii): `Π ζ = -ζ Π`. (Proved directly as
`PiSupercategory.pi_map_ζ`.) -/
theorem pi_map_ζ (A : PiSCat.{w₁, v, u} R) (X : A.carrier) :
    (PiSupercategory.pi (R := R)).map (PiSupercategory.ζ (R := R) X).hom =
      -(PiSupercategory.ζ (R := R) ((PiSupercategory.pi (R := R)).obj X)).hom := by
  simpa using congrArg (fun t => t.app 1 X) (PiTwoSupercategory.pi_whisker_ζ (R := R) A)

/-- **Corollary 3.3(i)**, derived from Lemma 3.2(iii): `Π ξ = ξ Π`. (Proved directly as
`PiSupercategory.ξ_pi`.) -/
theorem ξ_pi (A : PiSCat.{w₁, v, u} R) (X : A.carrier) :
    (PiSupercategory.ξ (R := R) ((PiSupercategory.pi (R := R)).obj X)).hom =
      (PiSupercategory.pi (R := R)).map (PiSupercategory.ξ (R := R) X).hom := by
  have h : (PiSupercategory.ζ (R := R) ((PiSupercategory.pi (R := R)).obj X)).hom =
      -(PiSupercategory.pi (R := R)).map (PiSupercategory.ζ (R := R) X).hom := by
    rw [pi_map_ζ A, neg_neg]
  rw [PiSupercategory.ξ_hom, PiSupercategory.ξ_hom, h, Functor.map_neg, Preadditive.neg_comp,
    Preadditive.comp_neg, neg_neg, Functor.map_comp]

/-- **Corollary 3.3(ii)**, derived from Lemma 3.2(iv):
`ξ_B F ξ_A⁻¹ = β_F Π_A ∘ Π_B β_F`. (Proved directly as `PiSupercategory.β_comm`.) -/
theorem β_comm (F : A ⟶ B) (X : A.carrier) :
    (PiSupercategory.ξ (R := R) (F.obj X)).hom ≫ F.map (PiSupercategory.ξ (R := R) X).inv =
      (PiSupercategory.pi (R := R)).map (PiSupercategory.β R F.toFunctor X).hom ≫
        (PiSupercategory.β R F.toFunctor ((PiSupercategory.pi (R := R)).obj X)).hom := by
  have h := congrArg (fun t => t.app 0 X) (PiTwoSupercategory.ξ_comm (R := R) F)
  simp [PiTwoSupercategory.ξ_hom, PiTwoSupercategory.ξ_inv, PiTwoSupercategory.β_hom] at h
  simpa [PiSupercategory.ξ_hom, PiSupercategory.β_hom, PiSupercategory.ξ] using h

/-- **Corollary 3.3(iii)**, derived from Lemma 3.2 (equation (3.1)): for a supernatural
transformation `x : F ⇒ G` of parity `p`, `β_G ∘ Π_B x = x Π_A ∘ β_F`. (Proved directly as
`PiSupercategory.β_naturality_supernatural`.) -/
theorem β_naturality_supernatural {F G : A ⟶ B} {p : ZMod 2}
    {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p (F := F.toFunctor) (G := G.toFunctor) x) (X : A.carrier) :
    (PiSupercategory.pi (R := R)).map (x X) ≫ (PiSupercategory.β R G.toFunctor X).hom =
      (PiSupercategory.β R F.toFunctor X).hom ≫ x ((PiSupercategory.pi (R := R)).obj X) := by
  have h := congrArg (fun t => t.app p X)
    (PiTwoSupercategory.β_naturality (R := R) (a := A) (b := B)
      (Superfunctor.homMk hx.toSuperNatTrans : F ⟶ G))
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simpa [comp_app, ← β_app_zero, β_app_one, IsSupernatural.toSuperNatTrans,
      SuperNatTrans.zmod2_one_add_one] using h.symm

/-- **Corollary 3.3(iv)**, derived from Lemma 3.2(i): `β_{GF} = G β_F ∘ β_G F`. (Proved
directly as `PiSupercategory.β_comp`.) -/
theorem β_comp (F : A ⟶ B) (G : B ⟶ C) (X : A.carrier) :
    (PiSupercategory.β R (F.toFunctor ⋙ G.toFunctor) X).hom =
      (PiSupercategory.β R G.toFunctor (F.obj X)).hom ≫
        G.map (PiSupercategory.β R F.toFunctor X).hom := by
  have h := congrArg (fun t => t.app 0 X) (PiTwoSupercategory.β_comp (R := R) F G)
  simp only [comp_app_zero, associator_hom, associator_inv, id_app_zero, id_app_one,
    whiskerLeft_app, whiskerRight_app, β_app_zero, β_app_one] at h
  simpa using h

/-- **Corollary 3.3(iv)**, derived from Lemma 3.2(ii): `β_I = 1_Π`. (Proved directly as
`PiSupercategory.β_id`.) -/
theorem β_id (A : PiSCat.{w₁, v, u} R) (X : A.carrier) :
    (PiSupercategory.β R (𝟭 A.carrier) X).hom = 𝟙 _ := by
  have h := congrArg (fun t => t.app 0 X) (PiTwoSupercategory.β_id (R := R) A)
  simp only [β_app_zero] at h
  simpa using h

/-- **Corollary 3.3(iv)**, derived from Lemma 3.2(iii): `β_Π = -1_{Π²}`. (Proved directly as
`PiSupercategory.β_pi`.) -/
theorem β_pi (A : PiSCat.{w₁, v, u} R) (X : A.carrier) :
    (PiSupercategory.β R (PiSupercategory.pi (R := R) (C := A.carrier)) X).hom = -𝟙 _ := by
  have h := congrArg (fun t => t.app 0 X) (PiTwoSupercategory.β_pi (R := R) A)
  simp only [β_app_zero] at h
  simpa using h

end Corollary

end PiSCat

end StringDiagrams

end
