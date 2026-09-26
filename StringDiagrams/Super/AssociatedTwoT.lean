import StringDiagrams.Super.AssociatedTwo

/-!
# Lemma 5.4: `D₂ ∘ E₂ ≅ I`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Lemma 5.4.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

/-! ## Values of 2-morphisms of the underlying bicategory -/

namespace Underlying2

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A] {a b : Underlying2 R A}

@[simp] theorem add₂_val {f g : a ⟶ b} (x y : f ⟶ g) : (x + y).1 = x.1 + y.1 := rfl

@[simp] theorem sub₂_val {f g : a ⟶ b} (x y : f ⟶ g) : (x - y).1 = x.1 - y.1 := rfl

@[simp] theorem neg₂_val {f g : a ⟶ b} (x : f ⟶ g) : (-x).1 = -x.1 := rfl

@[simp] theorem zero₂_val {f g : a ⟶ b} : (0 : f ⟶ g).1 = 0 := rfl

@[simp] theorem smul₂_val {f g : a ⟶ b} (r : R) (x : f ⟶ g) : (r • x).1 = r • x.1 := rfl

variable [PiTwoSupercategory R A]

@[simp] theorem pi_obj_obj (f : a ⟶ b) :
    ((PiCategory.pi (R := R)).obj f).obj = f.obj ≫ PiTwoSupercategory.pi (R := R) b.obj := rfl

end Underlying2

/-! ## Lemma 5.4: `E₂ ∘ D₂ = I` -/

namespace Associated2

section Unit

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [PiTwoCategory R B]

variable (R B) in
/-- **Lemma 5.4, `E₂ ∘ D₂ = I`.** The identification of a Π-2-category `𝔄` with the underlying
Π-2-category of `𝔄̂`: the identity on objects and 1-morphisms, `x ↦ (x, 0)` on 2-morphisms, with
identity coherence maps (a strict pseudofunctor). -/
@[simps]
def unit : Pseudofunctor B (Underlying2 R (Associated2 R B)) where
  obj a := ⟨⟨a⟩⟩
  map f := ⟨⟨f⟩⟩
  map₂ η := ⟨Associated.homMk η 0, Associated.mem_parity_zero.2 rfl⟩
  map₂_id f := rfl
  map₂_comp η θ := Subtype.ext (hom₂_ext (by simp) (by simp))
  mapId a := Iso.refl _
  mapComp f g := Iso.refl _
  map₂_whisker_left := by intros; apply Subtype.ext; apply hom₂_ext <;> simp
  map₂_whisker_right := by intros; apply Subtype.ext; apply hom₂_ext <;> simp
  map₂_associator f g h := Subtype.ext (hom₂_ext (by simp) (by simp))
  map₂_left_unitor f := Subtype.ext (hom₂_ext (by simp) (by simp))
  map₂_right_unitor f := Subtype.ext (hom₂_ext (by simp) (by simp))

/-- **Lemma 5.4, `E₂ ∘ D₂ = I`.** The identification is bijective on 2-morphisms (and the identity
on objects and 1-morphisms). -/
theorem unit_map₂_bijective {a b : B} (f g : a ⟶ b) :
    Function.Bijective ((unit R B).map₂ : (f ⟶ g) → ((unit R B).map f ⟶ (unit R B).map g)) := by
  refine ⟨fun x y h => ?_, fun x => ⟨x.1.1, Subtype.ext (hom₂_ext rfl ?_)⟩⟩
  · exact congrArg (fun t => t.1.1) h
  · exact (Associated.mem_parity_zero.1 x.2).symm

/-- **Lemma 5.4, `E₂ ∘ D₂ = I`.** The identification is a (strict) Π-2-functor with `j = 1`: the
Π-2-category underlying `𝔄̂` has the same `π`, `β` and `ξ` as `𝔄` (`β_hom_eq`, `ξ_hom_eq`). -/
def unitPiTwoFunctor : PiTwoFunctor R (unit R B) where
  map₂_add η θ := Subtype.ext (hom₂_ext rfl (by simp))
  map₂_smul r η := Subtype.ext (hom₂_ext rfl (by simp))
  j a := Iso.refl _
  β_comm {a b} f := by
    apply Subtype.ext
    simp only [Iso.refl_hom, Iso.refl_inv, unit_mapComp, Bicategory.whiskerLeft_id,
      Bicategory.id_whiskerRight, Underlying2.comp₂_val, Underlying2.id₂_val, Category.id_comp,
      Category.comp_id]
    erw [Category.id_comp, Category.comp_id]
    exact (β_hom_eq (R := R) (a := ⟨a⟩) (b := ⟨b⟩) ⟨f⟩).symm
  ξ_comm a := by
    apply Subtype.ext
    simp only [Iso.refl_hom, Iso.refl_inv, unit_mapComp, unit_mapId, Bicategory.whiskerLeft_id,
      Bicategory.id_whiskerRight, Underlying2.comp₂_val, Underlying2.id₂_val, Category.id_comp,
      Category.comp_id]
    erw [Category.id_comp, Category.comp_id]
    exact (ξ_hom_eq (R := R) ⟨a⟩).symm

end Unit

end Associated2

/-! ## Lemma 5.4: `D₂ ∘ E₂ ≅ I` -/

namespace Associated2

open BicategoryStruct TwoSupercategory

section T

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A] [PiTwoSupercategory R A]

local notation "𝛑" => PiTwoSupercategory.pi (R := R)
local notation "𝛇" => PiTwoSupercategory.ζ (R := R)

/-- The odd 2-isomorphism `ζ_μ G := G ◁ ζ_μ ≫ r_G : G π_μ ≅ G` (the paper's `ζ_μ G`, with the
unitor). -/
def ζG {a b : A} (g : a ⟶ b) : g ≫ 𝛑 b ≅ g :=
  whiskerLeftIso (R := R) g (𝛇 b) ≪≫ rightUnitor g

theorem ζG_hom {a b : A} (g : a ⟶ b) :
    (ζG (R := R) g).hom = g ◁ (𝛇 b).hom ≫ (rightUnitor g).hom := rfl

theorem ζG_hom_mem {a b : A} (g : a ⟶ b) :
    (ζG (R := R) g).hom ∈ parity (R := R) (g ≫ 𝛑 b) g 1 := by
  simpa [ζG_hom] using comp_mem (whiskerLeft_mem g (PiTwoSupercategory.ζ_hom_mem (R := R) b))
    (rightUnitor_hom_mem (R := R) g)

/-- Supernaturality of `ζG` on even 2-morphisms. -/
@[reassoc]
theorem ζG_naturality_even {a b : A} {g h : a ⟶ b} {η : g ⟶ h}
    (hη : η ∈ parity (R := R) g h 0) :
    η ▷ 𝛑 b ≫ (ζG (R := R) h).hom = (ζG (R := R) g).hom ≫ η := by
  rw [ζG_hom, ζG_hom, ← Category.assoc, whisker_exchange_of_even_left hη, Category.assoc,
    TwoSupercategory.rightUnitor_naturality R, Category.assoc]

/-- `ξ` of the Π-2-category `E₂ 𝔄`, on a hom category: `ξ_G = -ζ_μ G ∘ ζ_μ G π_μ`. -/
theorem ξHom_val {a b : Underlying2 R A} (g : a ⟶ b) :
    (PiTwoCategory.ξHom (R := R) g).hom.1 =
      -((ζG (R := R) (g.obj ≫ 𝛑 b.obj)).hom ≫ (ζG (R := R) g.obj).hom) := by
  rw [PiTwoCategory.ξHom_hom]
  change (associator g.obj (𝛑 b.obj) (𝛑 b.obj)).hom ≫ g.obj ◁ (PiTwoSupercategory.ξ (R := R) b.obj).hom ≫
    (rightUnitor g.obj).hom = _
  rw [PiTwoSupercategory.ξ_hom, ← Category.assoc ((𝛇 b.obj).hom ▷ _), PiTwoSupercategory.pi_whisker_ζ]
  simp only [Preadditive.neg_comp, whiskerLeft_neg R, Preadditive.comp_neg, ζG_hom,
    whiskerLeft_comp' R, Category.assoc, neg_inj]
  rw [← TwoSupercategory.associator_naturality_right_assoc R,
    TwoSupercategory.whiskerLeft_rightUnitor R]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- `a⁻¹ ∘ ζ_ν(F G) = F ζ_ν G`. -/
@[reassoc]
theorem associator_inv_ζG {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    (associator f g (𝛑 c)).inv ≫ (ζG (R := R) (f ≫ g)).hom = f ◁ (ζG (R := R) g).hom := by
  rw [ζG_hom, ζG_hom, ← Category.assoc, ← TwoSupercategory.associator_inv_naturality_right R,
    Category.assoc, ← TwoSupercategory.whiskerLeft_rightUnitor R, whiskerLeft_comp' R]

/-- `ζ_ν(F G) ∘ (β_G)⁻¹ = ζ_μ F G`, i.e. `ζ_ν G ∘ β_G⁻¹ = G ζ_μ` whiskered by `F`. -/
theorem βR_inv_ζG {a b c : Underlying2 R A} (f : a ⟶ b) (g : b ⟶ c) :
    (PiTwoCategory.βR (R := R) f g).inv.1 ≫ (ζG (R := R) (f.obj ≫ g.obj)).hom =
      (ζG (R := R) f.obj).hom ▷ g.obj := by
  rw [PiTwoCategory.βR_inv]
  change ((associator f.obj (𝛑 b.obj) g.obj).hom ≫
      f.obj ◁ (PiTwoSupercategory.β (R := R) g.obj).inv ≫ (associator f.obj g.obj (𝛑 c.obj)).inv) ≫
    (ζG (R := R) (f.obj ≫ g.obj)).hom = _
  rw [Category.assoc, Category.assoc, associator_inv_ζG, ← whiskerLeft_comp' R,
    PiTwoSupercategory.β_inv, ζG_hom]
  simp only [Category.assoc, TwoSupercategory.whiskerLeft_inv_hom_assoc R, Iso.inv_hom_id,
    Category.comp_id]
  rw [ζG_hom, comp_whiskerRight' R, whisker_assoc (R := R), ← TwoSupercategory.triangle (R := R),
    whiskerLeft_comp' R]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable (R A) in
/-- **Lemma 5.4.** The 2-superfunctor `𝕋_𝔄 : (E₂ 𝔄)^ → 𝔄`: the identity on objects and
1-morphisms, and `x̂ ↦ x₀ + ζ_μ G ∘ x₁` on 2-morphisms (the paper's `𝕋_𝔄 x̂ := ζ_μ G ∘ x` for odd
`x̂`), with identity coherence maps. -/
@[simps]
def T : TwoSuperfunctor R (Associated2 R (Underlying2 R A)) A where
  obj a := a.obj.obj
  map f := f.obj.obj
  map₂ {a b f g} x := x.1.1 + x.2.1 ≫ (ζG (R := R) g.obj.obj).hom
  map₂_id f := by simp
  map₂_comp {a b f g h} x y := by
    have h1 := ζG_naturality_even (R := R) y.1.2
    have h2 := ζG_naturality_even (R := R) y.2.2
    simp only [Underlying2.pi_obj_obj] at h2
    simp only [comp₂_fst, comp₂_snd, Underlying2.comp₂_val, Underlying2.add₂_val,
      Underlying2.sub₂_val, PiTwoCategory.pi_map, Underlying2.whiskerRight_val, ξHom_val,
      Underlying2.pi_obj, Underlying2.pi_obj_obj,
      Preadditive.add_comp, Preadditive.comp_add, Preadditive.sub_comp, Category.assoc,
      Preadditive.comp_neg, sub_neg_eq_add]
    rw [← h1, ← reassoc_of% h2]
    abel
  map₂_add x y := by
    simp only [add₂_fst, add₂_snd, Underlying2.add₂_val, Preadditive.add_comp]; abel
  map₂_smul r x := by simp [smul_add]
  map₂_mem {a b f g p x} hx := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [mem_parity_zero'] at hx
      simp only [hx, Underlying.zero_val, Limits.zero_comp, add_zero]
      exact x.1.2
    · rw [mem_parity_one'] at hx
      simp only [hx, Underlying.zero_val, zero_add]
      simpa using comp_mem x.2.2 (ζG_hom_mem (R := R) g.obj.obj)
  mapComp f g := Iso.refl _
  mapId a := Iso.refl _
  mapComp_hom_mem _ _ := id_mem _
  mapId_hom_mem _ := id_mem _
  mapComp_naturality_left {a b c f f'} η g := by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, whiskerRight_fst,
      whiskerRight_snd, Underlying2.whiskerRight_val, Underlying2.comp₂_val, Category.assoc,
      add_whiskerRight (R := R), comp_whiskerRight' R, comp_obj, Underlying2.comp_obj]
    rw [βR_inv_ζG]
  mapComp_naturality_right {a b c} f g h η := by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, whiskerLeft_fst,
      whiskerLeft_snd, Underlying2.whiskerLeft_val, Underlying2.comp₂_val, Category.assoc,
      whiskerLeft_add (R := R), whiskerLeft_comp' R, comp_obj, Underlying2.comp_obj]
    erw [associator_inv_ζG]
  map₂_associator f g h := by
    simp [whiskerLeft_id (R := R), id_whiskerRight (R := R)]
  map₂_leftUnitor f := by simp [id_whiskerRight (R := R)]
  map₂_rightUnitor f := by simp [whiskerLeft_id (R := R)]

/-- **Lemma 5.4.** `𝕋_𝔄` is bijective on 2-morphisms. -/
theorem T_map₂_injective {a b : Associated2 R (Underlying2 R A)} {f g : a ⟶ b} {x y : f ⟶ g}
    (h : (T R A).map₂ x = (T R A).map₂ y) : x = y := by
  have hζ := ζG_hom_mem (R := R) g.obj.obj
  have hx1 : x.2.1 ≫ (ζG (R := R) g.obj.obj).hom ∈ parity (R := R) f.obj.obj g.obj.obj 1 := by
    simpa using comp_mem x.2.2 hζ
  have hy1 : y.2.1 ≫ (ζG (R := R) g.obj.obj).hom ∈ parity (R := R) f.obj.obj g.obj.obj 1 := by
    simpa using comp_mem y.2.2 hζ
  have hx0 : x.1.1 ∈ parity (R := R) f.obj.obj g.obj.obj (1 + 1) := x.1.2
  have hy0 : y.1.1 ∈ parity (R := R) f.obj.obj g.obj.obj (1 + 1) := y.1.2
  have e0 : x.1.1 = y.1.1 := by
    rw [← proj_eq_of_add (R := R) (p := 0) rfl x.1.2 hx1,
      ← proj_eq_of_add (R := R) (p := 0) rfl y.1.2 hy1]
    exact congrArg (proj R 0) h
  have e1 : x.2.1 ≫ (ζG (R := R) g.obj.obj).hom = y.2.1 ≫ (ζG (R := R) g.obj.obj).hom := by
    rw [← proj_eq_of_add (R := R) (p := 1) (add_comm _ _) hx1 hx0,
      ← proj_eq_of_add (R := R) (p := 1) (add_comm _ _) hy1 hy0]
    exact congrArg (proj R 1) h
  exact hom₂_ext (Subtype.ext e0) (Subtype.ext ((cancel_mono _).1 e1))

variable (R A) in
/-- The inverse of `𝕋_𝔄` on 2-morphisms: `h ↦ (h₀, ζ_μ G⁻¹ ∘ h₁)`. -/
def Tinv₂ {a b : Associated2 R (Underlying2 R A)} {f g : a ⟶ b}
    (h : f.obj.obj ⟶ g.obj.obj) : f ⟶ g :=
  (⟨proj R 0 h, proj_mem 0 h⟩, ⟨proj R 1 h ≫ (ζG (R := R) g.obj.obj).inv,
    by simpa using comp_mem (proj_mem 1 h) (inv_mem _ (ζG_hom_mem (R := R) g.obj.obj))⟩)

theorem T_map₂_Tinv₂ {a b : Associated2 R (Underlying2 R A)} {f g : a ⟶ b}
    (h : f.obj.obj ⟶ g.obj.obj) : (T R A).map₂ (Tinv₂ R A h) = h := by
  simp [Tinv₂, proj_add_proj]

/-- **Lemma 5.4.** `𝕋_𝔄` is an isomorphism of 2-supercategories: it is the identity on objects
and 1-morphisms and bijective on 2-morphisms. -/
theorem T_map₂_bijective {a b : Associated2 R (Underlying2 R A)} (f g : a ⟶ b) :
    Function.Bijective ((T R A).map₂ : (f ⟶ g) → (f.obj.obj ⟶ g.obj.obj)) :=
  ⟨fun _ _ h => T_map₂_injective h, fun h => ⟨Tinv₂ R A h, T_map₂_Tinv₂ h⟩⟩

/-- **Lemma 5.4 / Theorem 5.5.** `𝕋_𝔄` carries `ζ` of `(E₂ 𝔄)^` to `ζ` of `𝔄`. -/
theorem T_map₂_ζ (a : Associated2 R (Underlying2 R A)) :
    (T R A).map₂ (PiTwoSupercategory.ζ (R := R) a).hom =
      (PiTwoSupercategory.ζ (R := R) a.obj.obj).hom := by
  simp only [T_map₂, ζ_eq, ζ_hom_fst, ζ_hom_snd, Underlying2.zero₂_val, zero_add]
  change (leftUnitor (𝛑 a.obj.obj)).inv ≫ 𝟙 a.obj.obj ◁ (𝛇 a.obj.obj).hom ≫
    (rightUnitor (𝟙 a.obj.obj)).hom = _
  rw [← TwoSupercategory.leftUnitor_inv_naturality_assoc R, ← TwoSupercategory.unitors_equal R,
    Iso.inv_hom_id, Category.comp_id]

end T

end Associated2

end StringDiagrams

end
