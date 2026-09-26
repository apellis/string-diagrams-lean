import StringDiagrams.Super.Underlying

/-!
# The Π-supercategory associated to a Π-category, and `Π-SCat ≃ Π-Cat`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §5: the
functor `D₁ : Π-Cat → Π-SCat` of (5.2), and the object-level content of Lemma 5.1 (the second
half of Theorem 1.9).

For a Π-category `(A, Π, ξ)` the associated supercategory `Â` (`StringDiagrams.Associated R C`)
has the objects of `A` and
`Hom_Â(λ, μ)₀ := Hom_A(λ, μ)`, `Hom_Â(λ, μ)₁ := Hom_A(λ, Πμ)`;
a morphism of `Â` is a pair `(f₀, f₁)`. It is a Π-supercategory with `Π̂ = Π` on objects and
`ζ_λ = 1̂_{Πλ}`, the identity of `Πλ` viewed as an odd morphism `Πλ → λ`.

## A sign correction

The paper defines the composite of odd morphisms `f̂ : λ → μ`, `ĝ : μ → ν` (coming from
`f : λ → Πμ`, `g : μ → Πν`) as `ĝ ∘ f̂ := ξ_ν ∘ Π g ∘ f`. With `ξ := ζζ` as in
Definition 1.7 and (5.1), this sign is inconsistent with the proof of Lemma 5.1: there, the
step "supernaturality of `ζ` gives `ζ_{Πν} ∘ Π g = -g ∘ ζ_μ`" is applied to the *even*
morphism `g : μ → Πν` of `A`, for which supernaturality gives `ζ_{Πν} ∘ Π g = g ∘ ζ_μ`. With
the printed rule, `T_A` reverses the sign of composites of odd morphisms, and the Π-category
underlying `Â` is `(A, Π, -ξ)` rather than `(A, Π, ξ)` (for `A = SVec`: odd morphisms are odd
linear maps and the printed rule gives `ĝ ∘ f̂ = -(g ∘ f)`).

We therefore use `ĝ ∘ f̂ := -ξ_ν ∘ Π g ∘ f` (`Associated.comp_fst`); equivalently, our `Â` is
the paper's construction applied to `(A, Π, -ξ)`. Note that `(A, Π, ξ) ↦ (A, Π, -ξ)`,
`(F, β) ↦ (F, β)` is an automorphism of `Π-Cat` (the axioms of Definition 1.6 are invariant
under negating all `ξ`), so the printed functor `D₁` is also an equivalence, and the statement
of Theorem 1.9 is unaffected; only the explicit inverse and the identities `E₁ ∘ D₁ = I`,
`T_A` of the proof of Lemma 5.1 need the corrected sign. With it, both hold:

* `Associated.unit`, `Associated.counit` (**Lemma 5.1**, `E₁ ∘ D₁ = I`): the underlying
  Π-category of `Â` is isomorphic to `(A, Π, ξ)` by mutually inverse functors
  (`unit_comp_counit`, `counit_comp_unit`) that commute strictly with `Π` and `ξ`
  (`unit_comp_pi`, `ξ_unit`); `unitPiFunctor` is the corresponding Π-functor with `β = 1`.
* `Associated.T` (**Lemma 5.1**, `D₁ ∘ E₁ ≅ I`): for a Π-supercategory `A`, the superfunctor
  `T_A : (A̲)^ ⥤ A`, `f̂ ↦ f` (even), `f̂ ↦ ζ_μ ∘ f` (odd), is an isomorphism of
  supercategories with inverse `Associated.Tinv` (`T_comp_Tinv`, `Tinv_comp_T`), and
  `T_A ζ = ζ T_A` (`T_map_ζ`).
* `Associated.map` (the functor `D₁` on morphisms, (5.2)): a Π-functor `(F, β_F)` induces a
  superfunctor `F̂ : Â ⥤ B̂`, with `D₁(G F) = D₁ G ∘ D₁ F` and `D₁(I) = I` (`map_comp`,
  `map_id`); naturality of `T`: `F ∘ T_A = T_B ∘ (F̲)^` (`T_naturality`).

On 2-morphisms, `D₁` sends a Π-natural transformation to an even supernatural transformation
(`isSupernatural_mapNatTrans`, (5.3)); `E₁` on 2-morphisms is `Underlying.isPiNatural`. The
remaining content of Theorem 5.3 (that `T` is a Π-2-natural isomorphism `D₁ ∘ E₁ ≅ I`) is not
formalized here.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ w₃ w₄ w₅ w₆

/-- The objects of the Π-supercategory `Â` associated to a Π-category `A` (Brundan–Ellis,
(5.2)). -/
@[ext]
structure Associated (R : Type w) (C : Type w₁) where
  /-- The object of `A`. -/
  obj : C

namespace Associated

section Category

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [PiCategory R C]

local notation "𝚷" => PiCategory.pi (R := R) (C := C)

/-- Composition in `Â`. -/
def compHom {X Y Z : C} (f : (X ⟶ Y) × (X ⟶ 𝚷.obj Y)) (g : (Y ⟶ Z) × (Y ⟶ 𝚷.obj Z)) :
    (X ⟶ Z) × (X ⟶ 𝚷.obj Z) :=
  (f.1 ≫ g.1 - f.2 ≫ 𝚷.map g.2 ≫ (PiCategory.ξApp (R := R) Z).hom, f.1 ≫ g.2 + f.2 ≫ 𝚷.map g.1)

/-- The associated supercategory `Â`: a morphism `λ ⟶ μ` is a pair `(f₀, f₁)` with
`f₀ : λ ⟶ μ` (even part) and `f₁ : λ ⟶ Π μ` (odd part). Composition:
`(f₀, f₁) ≫ (g₀, g₁) = (f₀ ≫ g₀ - f₁ ≫ Π g₁ ≫ ξ, f₀ ≫ g₁ + f₁ ≫ Π g₀)` (see the module
docstring for the sign). -/
instance : Category (Associated R C) where
  Hom X Y := (X.obj ⟶ Y.obj) × (X.obj ⟶ 𝚷.obj Y.obj)
  id X := (𝟙 X.obj, 0)
  comp f g := compHom f g
  id_comp f := by ext <;> simp [compHom]
  comp_id f := by ext <;> simp [compHom]
  assoc {W X Y Z} f g h := by
    ext
    · simp only [compHom, Preadditive.add_comp, Preadditive.sub_comp, Preadditive.comp_add,
        Preadditive.comp_sub, Functor.map_add, Functor.map_sub, Functor.map_comp,
        Category.assoc]
      rw [← PiCategory.ξApp_naturality (R := R) h.1]
      abel
    · simp only [compHom, Preadditive.add_comp, Preadditive.sub_comp, Preadditive.comp_add,
        Preadditive.comp_sub, Functor.map_add, Functor.map_sub, Functor.map_comp,
        Category.assoc]
      rw [← PiCategory.ξApp_naturality (R := R) h.2, PiCategory.ξApp_pi]
      abel

variable {X Y Z : Associated R C}

@[simp] theorem id_fst : (𝟙 X : X ⟶ X).1 = 𝟙 X.obj := rfl

@[simp] theorem id_snd : (𝟙 X : X ⟶ X).2 = 0 := rfl

/-- The even part of a composite; for two odd morphisms this is `-ξ ∘ Π g ∘ f`. -/
@[simp] theorem comp_fst (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 - f.2 ≫ 𝚷.map g.2 ≫ (PiCategory.ξApp (R := R) Z.obj).hom := rfl

@[simp] theorem comp_snd (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).2 = f.1 ≫ g.2 + f.2 ≫ 𝚷.map g.1 := rfl

@[ext] theorem hom_ext {f g : X ⟶ Y} (h₁ : f.1 = g.1) (h₂ : f.2 = g.2) : f = g := Prod.ext h₁ h₂

/-- The morphism `λ ⟶ μ` of `Â` with even part `f₀ : λ ⟶ μ` and odd part `f₁ : λ ⟶ Π μ`. -/
def homMk (f₀ : X.obj ⟶ Y.obj) (f₁ : X.obj ⟶ 𝚷.obj Y.obj) : X ⟶ Y := (f₀, f₁)

@[simp] theorem homMk_fst (f₀ : X.obj ⟶ Y.obj) (f₁ : X.obj ⟶ 𝚷.obj Y.obj) :
    (homMk f₀ f₁ : X ⟶ Y).1 = f₀ := rfl

@[simp] theorem homMk_snd (f₀ : X.obj ⟶ Y.obj) (f₁ : X.obj ⟶ 𝚷.obj Y.obj) :
    (homMk f₀ f₁ : X ⟶ Y).2 = f₁ := rfl

instance : Preadditive (Associated R C) where
  homGroup X Y := inferInstanceAs (AddCommGroup ((X.obj ⟶ Y.obj) × (X.obj ⟶ 𝚷.obj Y.obj)))
  add_comp _ _ Z f f' g := by
    refine Prod.ext ?_ ?_
    · change (f.1 + f'.1) ≫ g.1 - (f.2 + f'.2) ≫ 𝚷.map g.2 ≫ (PiCategory.ξApp (R := R) Z.obj).hom =
        (f.1 ≫ g.1 - f.2 ≫ 𝚷.map g.2 ≫ (PiCategory.ξApp (R := R) Z.obj).hom) +
          (f'.1 ≫ g.1 - f'.2 ≫ 𝚷.map g.2 ≫ (PiCategory.ξApp (R := R) Z.obj).hom)
      simp only [Preadditive.add_comp]; abel
    · change (f.1 + f'.1) ≫ g.2 + (f.2 + f'.2) ≫ 𝚷.map g.1 =
        (f.1 ≫ g.2 + f.2 ≫ 𝚷.map g.1) + (f'.1 ≫ g.2 + f'.2 ≫ 𝚷.map g.1)
      simp only [Preadditive.add_comp]; abel
  comp_add _ _ Z f g g' := by
    refine Prod.ext ?_ ?_
    · change f.1 ≫ (g.1 + g'.1) - f.2 ≫ 𝚷.map (g.2 + g'.2) ≫ (PiCategory.ξApp (R := R) Z.obj).hom =
        (f.1 ≫ g.1 - f.2 ≫ 𝚷.map g.2 ≫ (PiCategory.ξApp (R := R) Z.obj).hom) +
          (f.1 ≫ g'.1 - f.2 ≫ 𝚷.map g'.2 ≫ (PiCategory.ξApp (R := R) Z.obj).hom)
      simp only [Preadditive.comp_add, Functor.map_add, Preadditive.add_comp]; abel
    · change f.1 ≫ (g.2 + g'.2) + f.2 ≫ 𝚷.map (g.1 + g'.1) =
        (f.1 ≫ g.2 + f.2 ≫ 𝚷.map g.1) + (f.1 ≫ g'.2 + f.2 ≫ 𝚷.map g'.1)
      simp only [Preadditive.comp_add, Functor.map_add]; abel

@[simp] theorem add_fst (f g : X ⟶ Y) : (f + g).1 = f.1 + g.1 := rfl

@[simp] theorem add_snd (f g : X ⟶ Y) : (f + g).2 = f.2 + g.2 := rfl

@[simp] theorem zero_fst : (0 : X ⟶ Y).1 = 0 := rfl

@[simp] theorem zero_snd : (0 : X ⟶ Y).2 = 0 := rfl

@[simp] theorem neg_fst (f : X ⟶ Y) : (-f).1 = -f.1 := rfl

@[simp] theorem neg_snd (f : X ⟶ Y) : (-f).2 = -f.2 := rfl

@[simp] theorem sub_fst (f g : X ⟶ Y) : (f - g).1 = f.1 - g.1 := rfl

@[simp] theorem sub_snd (f g : X ⟶ Y) : (f - g).2 = f.2 - g.2 := rfl

instance : Linear R (Associated R C) where
  homModule X Y := inferInstanceAs (Module R ((X.obj ⟶ Y.obj) × (X.obj ⟶ 𝚷.obj Y.obj)))
  smul_comp _ _ Z r f g := by
    refine Prod.ext ?_ ?_
    · change (r • f.1) ≫ g.1 - (r • f.2) ≫ 𝚷.map g.2 ≫ (PiCategory.ξApp (R := R) Z.obj).hom =
        r • (f.1 ≫ g.1 - f.2 ≫ 𝚷.map g.2 ≫ (PiCategory.ξApp (R := R) Z.obj).hom)
      simp only [Linear.smul_comp, smul_sub]
    · change (r • f.1) ≫ g.2 + (r • f.2) ≫ 𝚷.map g.1 = r • (f.1 ≫ g.2 + f.2 ≫ 𝚷.map g.1)
      simp only [Linear.smul_comp, smul_add]
  comp_smul _ _ Z f r g := by
    refine Prod.ext ?_ ?_
    · change f.1 ≫ (r • g.1) - f.2 ≫ 𝚷.map (r • g.2) ≫ (PiCategory.ξApp (R := R) Z.obj).hom =
        r • (f.1 ≫ g.1 - f.2 ≫ 𝚷.map g.2 ≫ (PiCategory.ξApp (R := R) Z.obj).hom)
      simp only [Linear.comp_smul, Functor.map_smul, Linear.smul_comp, smul_sub]
    · change f.1 ≫ (r • g.2) + f.2 ≫ 𝚷.map (r • g.1) = r • (f.1 ≫ g.2 + f.2 ≫ 𝚷.map g.1)
      simp only [Linear.comp_smul, Functor.map_smul, Linear.smul_comp, smul_add]

@[simp] theorem smul_fst (r : R) (f : X ⟶ Y) : (r • f).1 = r • f.1 := rfl

@[simp] theorem smul_snd (r : R) (f : X ⟶ Y) : (r • f).2 = r • f.2 := rfl

/-! ## The supercategory structure -/

/-- The even morphisms are the pairs `(f₀, 0)`, the odd ones the pairs `(0, f₁)`. -/
def parityAssoc (X Y : Associated R C) (p : ZMod 2) : Submodule R (X ⟶ Y) :=
  if p = 0 then LinearMap.ker (LinearMap.snd R _ _) else LinearMap.ker (LinearMap.fst R _ _)

theorem mem_parityAssoc_zero {f : X ⟶ Y} : f ∈ parityAssoc X Y 0 ↔ f.2 = 0 := by
  simp only [parityAssoc, if_pos rfl, LinearMap.mem_ker]; rfl

theorem mem_parityAssoc_one {f : X ⟶ Y} : f ∈ parityAssoc X Y 1 ↔ f.1 = 0 := by
  simp only [parityAssoc, if_neg (show ¬((1 : ZMod 2) = 0) by decide), LinearMap.mem_ker]; rfl

instance : Supercategory R (Associated R C) where
  parity := parityAssoc
  isInternal X Y := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    have h := LinearMap.isCompl_range_inl_inr (R := R) (M := X.obj ⟶ Y.obj)
      (M₂ := X.obj ⟶ (PiCategory.pi (R := R)).obj Y.obj)
    rw [LinearMap.range_inl, LinearMap.range_inr] at h
    simpa [parityAssoc, show ¬((1 : ZMod 2) = 0) by decide] using h
  id_mem X := mem_parityAssoc_zero.2 rfl
  comp_mem {X Y Z p q f g} hf hg := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;> rcases parity_eq_zero_or_one q with rfl | rfl
    · rw [mem_parityAssoc_zero] at hf hg; rw [add_zero, mem_parityAssoc_zero]; simp [hf, hg]
    · rw [mem_parityAssoc_zero] at hf; rw [mem_parityAssoc_one] at hg
      rw [zero_add, mem_parityAssoc_one]; simp [hf, hg]
    · rw [mem_parityAssoc_one] at hf; rw [mem_parityAssoc_zero] at hg
      rw [add_zero, mem_parityAssoc_one]; simp [hf, hg]
    · rw [mem_parityAssoc_one] at hf hg
      rw [show (1 : ZMod 2) + 1 = 0 from rfl, mem_parityAssoc_zero]; simp [hf, hg]

theorem mem_parity_zero {f : X ⟶ Y} : f ∈ parity (R := R) X Y 0 ↔ f.2 = 0 :=
  mem_parityAssoc_zero

theorem mem_parity_one {f : X ⟶ Y} : f ∈ parity (R := R) X Y 1 ↔ f.1 = 0 :=
  mem_parityAssoc_one

theorem proj_zero (f : X ⟶ Y) : proj R 0 f = (f.1, 0) :=
  proj_eq_of_add (h := (0, f.2)) (by ext <;> simp) (mem_parity_zero.2 rfl) (mem_parity_one.2 rfl)

theorem proj_one (f : X ⟶ Y) : proj R 1 f = (0, f.2) :=
  proj_eq_of_add (h := (f.1, 0)) (by ext <;> simp) (mem_parity_one.2 rfl) (mem_parity_zero.2 rfl)

theorem twist_one (f : X ⟶ Y) : twist R 1 f = (f.1, -f.2) := by
  rw [twist_apply, proj_zero, proj_one]
  ext <;> simp

/-! ## The Π-supercategory structure -/

/-- The odd isomorphism `ζ_λ = 1̂_{Πλ} : Πλ ≅ λ`; its inverse is `-ξ_λ⁻¹` viewed as an odd
morphism `λ → Πλ`. -/
def ζIso (X : Associated R C) : (⟨𝚷.obj X.obj⟩ : Associated R C) ≅ X where
  hom := homMk 0 (𝟙 _)
  inv := homMk 0 (-(PiCategory.ξApp (R := R) X.obj).inv)
  hom_inv_id := by
    ext
    · simp only [comp_fst, homMk_fst, homMk_snd, id_fst, Category.id_comp, Functor.map_neg,
        Preadditive.neg_comp, Limits.zero_comp, zero_sub, neg_neg]
      rw [PiCategory.ξApp_pi, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    · simp
  inv_hom_id := by
    ext
    · simp
    · simp

theorem ζIso_mem (X : Associated R C) : (ζIso X).hom ∈ parity (R := R) _ X 1 :=
  mem_parity_one.2 rfl

/-- **Brundan–Ellis, (5.2).** The associated supercategory is a Π-supercategory with
`Π̂ λ = Π λ` and `ζ_λ = 1̂_{Πλ}`. -/
instance : PiSupercategory R (Associated R C) :=
  PiSupercategory.ofIso (fun X => ⟨𝚷.obj X.obj⟩) ζIso ζIso_mem

@[simp] theorem pi_obj (X : Associated R C) :
    (PiSupercategory.pi (R := R)).obj X = ⟨𝚷.obj X.obj⟩ := rfl

theorem ζ_hom (X : Associated R C) :
    (PiSupercategory.ζ (R := R) X).hom = homMk (X := ⟨𝚷.obj X.obj⟩) 0 (𝟙 _) := rfl

/-- `Π̂ f̂ = Π f` for even `f̂` (Brundan–Ellis, (5.2)). -/
theorem pi_map_fst (f : X ⟶ Y) :
    ((PiSupercategory.pi (R := R)).map f).1 = 𝚷.map f.1 := by
  show ((ζIso X).hom ≫ twist R 1 f ≫ (ζIso Y).inv).1 = _
  simp only [twist_one, ζIso, comp_fst, comp_snd, homMk_fst, homMk_snd]
  simp only [Limits.zero_comp, Category.id_comp, Functor.map_neg, Functor.map_add,
    Functor.map_comp, Functor.map_zero, Preadditive.neg_comp, Preadditive.comp_neg,
    Preadditive.add_comp, zero_add, zero_sub, neg_neg, Limits.comp_zero, add_zero,
    Category.assoc]
  rw [PiCategory.ξApp_pi, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  simp

/-- `Π̂ f̂ = -Π f` for odd `f̂` (Brundan–Ellis, (5.2)). -/
theorem pi_map_snd (f : X ⟶ Y) :
    ((PiSupercategory.pi (R := R)).map f).2 = -𝚷.map f.2 := by
  show ((ζIso X).hom ≫ twist R 1 f ≫ (ζIso Y).inv).2 = _
  simp only [twist_one, ζIso, comp_fst, comp_snd, homMk_fst, homMk_snd]
  simp only [Limits.zero_comp, Category.id_comp, Functor.map_neg, Functor.map_add,
    Functor.map_comp, Functor.map_zero, Preadditive.neg_comp, Preadditive.comp_neg,
    Preadditive.add_comp, zero_add, zero_sub, neg_neg, Limits.comp_zero, add_zero,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [PiCategory.ξApp_pi]
  simp only [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id, neg_zero, zero_add]

/-- The even isomorphism `ξ̂ = ζ̂ζ̂` of `Â` is `ξ` (with the corrected sign). -/
theorem ξ_hom (X : Associated R C) :
    (PiSupercategory.ξ (R := R) X).hom = homMk (X := ⟨𝚷.obj (𝚷.obj X.obj)⟩)
      (PiCategory.ξApp (R := R) X.obj).hom 0 := by
  ext
  · rw [PiSupercategory.ξ_hom, comp_fst, pi_map_fst, pi_map_snd]
    simp [ζ_hom]
  · rw [PiSupercategory.ξ_hom, comp_snd, pi_map_fst, pi_map_snd]
    simp [ζ_hom]

end Category

/-! ## Lemma 5.1: `E₁ ∘ D₁ = I` -/

section Unit

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [PiCategory R C]

variable (R C) in
/-- The identification of `A` with the underlying category of `Â`, `f ↦ (f, 0)`. -/
def unit : C ⥤ Underlying R (Associated R C) where
  obj X := ⟨⟨X⟩⟩
  map f := ⟨homMk f 0, mem_parity_zero.2 rfl⟩
  map_id _ := rfl
  map_comp f g := Underlying.hom_ext (by ext <;> simp)

@[simp] theorem unit_obj (X : C) : (unit R C).obj X = ⟨⟨X⟩⟩ := rfl

@[simp] theorem unit_map_val {X Y : C} (f : X ⟶ Y) :
    ((unit R C).map f).1 = homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f 0 := rfl

variable (R C) in
/-- The inverse identification, `(f, 0) ↦ f`. -/
def counit : Underlying R (Associated R C) ⥤ C where
  obj X := X.obj.obj
  map f := f.1.1
  map_id _ := rfl
  map_comp f g := by
    show (f.1 ≫ g.1).1 = _
    rw [comp_fst, mem_parity_zero.1 f.2]
    simp

theorem unit_comp_counit : unit R C ⋙ counit R C = 𝟭 C := rfl

theorem counit_comp_unit : counit R C ⋙ unit R C = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map, eqToHom_refl,
      Category.comp_id, Category.id_comp]
    exact Underlying.hom_ext (hom_ext rfl (mem_parity_zero.1 f.2).symm)

theorem unit_map_pi {X Y : C} (f : X ⟶ Y) :
    (PiCategory.pi (R := R)).map ((unit R C).map f) =
      (unit R C).map ((PiCategory.pi (R := R)).map f) :=
  Underlying.hom_ext (hom_ext (pi_map_fst _) (by simp [pi_map_snd]))

/-- `unit` commutes with `Π` on the nose. -/
theorem unit_comp_pi :
    unit R C ⋙ PiCategory.pi (R := R) = PiCategory.pi (R := R) ⋙ unit R C :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by
    simp only [Functor.comp_obj, Functor.comp_map, eqToHom_refl, Category.comp_id,
      Category.id_comp]
    exact unit_map_pi f

/-- `unit` carries `ξ` to the `ξ` of the underlying Π-category of `Â`
(**Lemma 5.1**, `E₁ ∘ D₁ = I`; this uses the corrected sign). -/
theorem ξ_unit (X : C) :
    (PiCategory.ξApp (R := R) ((unit R C).obj X)).hom =
      (unit R C).map (PiCategory.ξApp (R := R) X).hom :=
  Underlying.hom_ext (ξ_hom _)

/-- `unit` as a Π-functor with `β = 1`. -/
def unitPiFunctor : PiFunctor R (unit R C) where
  β := NatIso.ofComponents (fun X => Iso.refl _) fun f => by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.refl_hom, Category.comp_id,
      Category.id_comp]
    exact unit_map_pi f
  comm X := by
    have h := ξ_unit (R := R) (C := C) X
    rw [PiCategory.ξApp_hom, PiCategory.ξApp_hom] at h
    simp only [NatIso.ofComponents_hom_app, Iso.refl_hom, CategoryTheory.Functor.map_id,
      Category.id_comp]
    rw [h, ← Functor.map_comp, Iso.hom_inv_id_app]
    rfl

end Unit

/-! ## `D₁` on Π-functors -/

section Map

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [PiCategory R C] {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [PiCategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [PiCategory R E]

/-- The functor `D₁` on Π-functors (Brundan–Ellis, (5.2)): `F̂(f₀, f₁) = (F f₀, β_F⁻¹ ∘ F f₁)`. -/
@[simps]
def map {F : C ⥤ D} [F.Additive] (hF : PiFunctor R F) : Associated R C ⥤ Associated R D where
  obj X := ⟨F.obj X.obj⟩
  map f := homMk (F.map f.1) (F.map f.2 ≫ hF.β.inv.app _)
  map_id X := by ext <;> simp
  map_comp {X Y Z} f g := by
    have n1 := hF.β.inv.naturality g.1
    have n2 := hF.β.inv.naturality g.2
    have c := hF.comm Z.obj
    simp only [Functor.comp_obj, Functor.comp_map] at n1 n2
    have c' : F.map (PiCategory.ξApp (R := R) Z.obj).hom =
        hF.β.inv.app _ ≫ (PiCategory.pi (R := R)).map (hF.β.inv.app Z.obj) ≫
          (PiCategory.ξApp (R := R) (F.obj Z.obj)).hom := by
      rw [PiCategory.ξApp_hom, PiCategory.ξApp_hom, ← cancel_epi
        ((PiCategory.ξ (R := R)).hom.app (F.obj Z.obj) ≫
          F.map ((PiCategory.ξ (R := R)).inv.app Z.obj))]
      rw [Category.assoc, ← F.map_comp, Iso.inv_hom_id_app]
      simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
      rw [reassoc_of% c]
      simp only [Iso.hom_inv_id_app_assoc]
      rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      simp
    ext
    · simp only [comp_fst, homMk_fst, homMk_snd, Functor.map_sub, Functor.map_comp,
        Category.assoc]
      rw [c', reassoc_of% n2]
    · simp only [comp_snd, homMk_fst, homMk_snd, Functor.map_add, Functor.map_comp,
        Category.assoc, Preadditive.add_comp]
      rw [n1]

instance {F : C ⥤ D} [F.Additive] (hF : PiFunctor R F) : (map hF).Additive where
  map_add := by intros; ext <;> simp [Preadditive.add_comp]

instance {F : C ⥤ D} [F.Additive] [F.Linear R] (hF : PiFunctor R F) : (map hF).Linear R where
  map_smul _ _ := by ext <;> simp

instance {F : C ⥤ D} [F.Additive] [F.Linear R] (hF : PiFunctor R F) :
    IsSuperfunctor R (map hF) where
  map_mem {X Y p f} hf := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [mem_parity_zero] at hf ⊢; simp [hf]
    · rw [mem_parity_one] at hf ⊢; simp [hf]

theorem map_id : map (PiFunctor.id R C) = 𝟭 (Associated R C) :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by ext <;> simp

theorem map_comp {F : C ⥤ D} [F.Additive] {G : D ⥤ E} [G.Additive] (hF : PiFunctor R F)
    (hG : PiFunctor R G) : map (hF.comp hG) = map hF ⋙ map hG :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by
    ext <;> simp

/-- **Brundan–Ellis, (5.3).** `D₁` on 2-morphisms: a Π-natural transformation `y : F ⟶ G`
gives the even supernatural transformation `ŷ_λ := y_λ` between `F̂` and `Ĝ`. -/
theorem isSupernatural_mapNatTrans {F G : C ⥤ D} [F.Additive] [F.Linear R] [G.Additive]
    [G.Linear R] {hF : PiFunctor R F} {hG : PiFunctor R G} {y : F ⟶ G}
    (hy : PiFunctor.IsPiNatural R hF hG y) :
    IsSupernatural R 0 (F := map hF) (G := map hG) fun X => homMk (y.app X.obj) 0 := by
  refine isSupernatural_of_natTrans (F := map hF) (G := map hG)
    ({ app := fun X : Associated R C => homMk (Y := (map hG).obj X) (y.app X.obj) 0
       naturality := fun X Y f => ?_ } : map hF ⟶ map hG) (fun X => mem_parity_zero.2 rfl)
  have h : hF.β.inv.app Y.obj ≫ (PiCategory.pi (R := R)).map (y.app Y.obj) =
      y.app ((PiCategory.pi (R := R)).obj Y.obj) ≫ hG.β.inv.app Y.obj := by
    rw [← cancel_epi (hF.β.hom.app Y.obj), Iso.hom_inv_id_app_assoc, reassoc_of% (hy Y.obj),
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  ext
  · simp [y.naturality]
  · simp only [comp_snd, map_map, homMk_fst, homMk_snd, Category.assoc, Functor.map_zero,
      Limits.comp_zero, zero_add, add_zero, Limits.zero_comp]
    rw [h, ← Category.assoc, ← Category.assoc, y.naturality]

end Map

/-! ## Lemma 5.1: `D₁ ∘ E₁ ≅ I` -/

section T

variable {R : Type w} [CommRing R] {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A]
  [Supercategory R A] [PiSupercategory R A]

variable (R A) in
/-- **Lemma 5.1.** The superfunctor `T_A : (A̲)^ ⥤ A`: `(f₀, f₁) ↦ f₀ + ζ_μ ∘ f₁`. -/
@[simps]
def T : Associated R (Underlying R A) ⥤ A where
  obj X := X.obj.obj
  map {X Y} f := f.1.1 + f.2.1 ≫ (PiSupercategory.ζ (R := R) Y.obj.obj).hom
  map_id X := by simp
  map_comp {X Y Z} f g := by
    have h1 := PiSupercategory.ζ_naturality (R := R) g.1.1
    have h2 := PiSupercategory.ζ_naturality (R := R)
      (g.2.1 ≫ (PiSupercategory.ζ (R := R) Z.obj.obj).hom)
    rw [twist_one_of_mem g.1.2, sign_zero, one_smul] at h1
    rw [twist_one_of_mem (comp_mem g.2.2 (PiSupercategory.ζ_hom_mem (R := R) Z.obj.obj)),
      zero_add, sign_one, neg_one_smul, Functor.map_comp, Category.assoc] at h2
    simp only [comp_fst, comp_snd, Underlying.comp_val, Underlying.pi_map_val,
      Underlying.ξApp_hom_val, Underlying.add_val, Underlying.sub_val, PiSupercategory.ξ_hom,
      Preadditive.add_comp, Preadditive.comp_add, Preadditive.sub_comp, Category.assoc]
    rw [h1, h2]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp]
    abel

instance : (T R A).Additive where
  map_add := by intros; simp [Preadditive.add_comp]; abel

instance : (T R A).Linear R where
  map_smul _ _ := by simp [smul_add]

instance : IsSuperfunctor R (T R A) where
  map_mem {X Y p f} hf := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [mem_parity_zero] at hf
      simp only [T_map, hf, Underlying.zero_val, Limits.zero_comp, add_zero]
      exact f.1.2
    · rw [mem_parity_one] at hf
      simp only [T_map, hf, Underlying.zero_val, zero_add]
      simpa using comp_mem f.2.2 (PiSupercategory.ζ_hom_mem (R := R) Y.obj.obj)

/-- `T_A` is injective on morphisms. -/
theorem T_map_injective {X Y : Associated R (Underlying R A)} {f g : X ⟶ Y}
    (h : (T R A).map f = (T R A).map g) : f = g := by
  have hζ := PiSupercategory.ζ_hom_mem (R := R) Y.obj.obj
  have hf1 : f.2.1 ≫ (PiSupercategory.ζ (R := R) Y.obj.obj).hom ∈
      parity (R := R) X.obj.obj Y.obj.obj 1 := by simpa using comp_mem f.2.2 hζ
  have hg1 : g.2.1 ≫ (PiSupercategory.ζ (R := R) Y.obj.obj).hom ∈
      parity (R := R) X.obj.obj Y.obj.obj 1 := by simpa using comp_mem g.2.2 hζ
  have hf0 : f.1.1 ∈ parity (R := R) X.obj.obj Y.obj.obj (1 + 1) := f.1.2
  have hg0 : g.1.1 ∈ parity (R := R) X.obj.obj Y.obj.obj (1 + 1) := g.1.2
  have e0 : f.1.1 = g.1.1 := by
    rw [← proj_eq_of_add (R := R) (p := 0) rfl f.1.2 hf1,
      ← proj_eq_of_add (R := R) (p := 0) rfl g.1.2 hg1]
    exact congrArg (proj R 0) h
  have e1 : f.2.1 ≫ (PiSupercategory.ζ (R := R) Y.obj.obj).hom =
      g.2.1 ≫ (PiSupercategory.ζ (R := R) Y.obj.obj).hom := by
    rw [← proj_eq_of_add (R := R) (p := 1) (add_comm _ _) hf1 hf0,
      ← proj_eq_of_add (R := R) (p := 1) (add_comm _ _) hg1 hg0]
    exact congrArg (proj R 1) h
  exact hom_ext (Subtype.ext e0) (Subtype.ext ((cancel_mono _).1 e1))

variable (R A) in
/-- **Lemma 5.1.** The inverse of `T_A`: `h ↦ (h₀, ζ_μ⁻¹ ∘ h₁)`. -/
@[simps obj]
def Tinv : A ⥤ Associated R (Underlying R A) where
  obj X := ⟨⟨X⟩⟩
  map {X Y} h := (⟨proj R 0 h, proj_mem 0 h⟩, ⟨proj R 1 h ≫ (PiSupercategory.ζ (R := R) Y).inv,
    by simpa using comp_mem (proj_mem 1 h) (PiSupercategory.ζ_inv_mem (R := R) Y)⟩)
  map_id X := T_map_injective (by simp [proj_id, show ¬((1 : ZMod 2) = 0) by decide])
  map_comp {X Y Z} f g := T_map_injective (by
    rw [(T R A).map_comp]
    simp only [T_map, Category.assoc, Iso.inv_hom_id, Category.comp_id, proj_add_proj])

theorem T_map_Tinv_map {X Y : A} (h : X ⟶ Y) : (T R A).map ((Tinv R A).map h) = h := by
  simp [Tinv, proj_add_proj]

theorem Tinv_comp_T : Tinv R A ⋙ T R A = 𝟭 A :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by simpa using T_map_Tinv_map f

theorem T_comp_Tinv : T R A ⋙ Tinv R A = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by
    simpa using T_map_injective (T_map_Tinv_map ((T R A).map f))

/-- `T_A` carries `ζ` of `(A̲)^` to `ζ` of `A`. -/
theorem T_map_ζ (X : Associated R (Underlying R A)) :
    (T R A).map (PiSupercategory.ζ (R := R) X).hom =
      (PiSupercategory.ζ (R := R) X.obj.obj).hom := by
  simp [ζ_hom, ζIso]

variable {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [PiSupercategory R B]

/-- **Lemma 5.1**, naturality of `T`: `F ∘ T_A = T_B ∘ (F̲)^` for a superfunctor `F` between
Π-supercategories. -/
theorem T_naturality (F : A ⥤ B) [F.Additive] [F.Linear R] [IsSuperfunctor R F] :
    map (Underlying.piFunctor (R := R) F) ⋙ T R B = T R A ⋙ F :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by
    simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    change F.map f.1.1 + (F.map f.2.1 ≫ (PiSupercategory.β R F Y.obj.obj).inv) ≫
      (PiSupercategory.ζ (R := R) (F.obj Y.obj.obj)).hom =
        F.map (f.1.1 + f.2.1 ≫ (PiSupercategory.ζ (R := R) Y.obj.obj).hom)
    rw [PiSupercategory.β_inv, F.map_add, F.map_comp]
    simp

end T

end Associated

end StringDiagrams

end
