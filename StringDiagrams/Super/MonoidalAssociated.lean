import StringDiagrams.Super.Associated
import StringDiagrams.Super.MonoidalPi

/-!
# The monoidal Π-supercategory associated to a monoidal Π-category (Theorem 1.15, second half)

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Theorem 1.15 (the functor (2) of (1.9) is an equivalence `Π-SMon ≃ Π-Mon`), whose proof in the
paper is the one-object case of the functor `D₂` of (5.5) and of Lemma 5.4.

## The construction

Let `(A, π, β, ξ)` be a monoidal Π-category (Definition 1.14). Then `A` is a Π-category with
`Π := π ⊗ -` and `ξ_λ := l_λ ∘ (ξ ⊗ 1_λ) ∘ a⁻¹` (`MonoidalPiCategory.toPiCategory`; the axiom
`ξΠ = Πξ` follows from (1.8) and `β_π = -1`, `MonoidalPiCategory.ξL_pi`). Its associated
supercategory `Â` (`StringDiagrams.Associated`, with the composition rule corrected in
`StringDiagrams.Super.Associated`) is a monoidal supercategory
(`Associated.monoidalSupercategory`) with:

* `λ ⊗ μ` as in `A`, unit `1`, and coherence maps those of `A` viewed as even isomorphisms;
* `f̂ ▷ μ = D₁(- ⊗ μ)(f̂)`, `λ ◁ ĝ = D₁(λ ⊗ -)(ĝ)`, where `- ⊗ μ` and `λ ⊗ -` are Π-functors
  with `β = a⁻¹` and `β = a ∘ (β_λ ⊗ 1) ∘ a⁻¹` respectively (`tensorRightPi`, `tensorLeftPi`;
  the Π-functor axiom for `λ ⊗ -` is (1.8)).

It is a monoidal Π-supercategory (`Associated.instMonoidalPiSupercategory`) with `π̂ = π` and
`ζ = r_π⁻¹ : π → π ⊗ 1` viewed as an odd morphism `π → 1`. The super interchange law
(`Associated.super_interchange_assoc`) uses (1.7), `β_π = -1` and the naturality of `β`; the
unit axiom (1.6) for `β` is derived from (1.7) (`MonoidalPiCategory.β_unit`).

## Theorem 1.15, second half

* `E ∘ D = I` on objects: the identification `A ⥤ E(D(A))`, `f ↦ (f, 0)`, is a strict monoidal
  Π-functor with `j = 1` (`Associated.unitMonoidalPiFunctor`), i.e. the monoidal Π-category
  underlying `Â` has the same `π`, `β` (`Associated.β_hom_eq`) and `ξ` (`Associated.ξ_hom_eq`)
  as `A`; with `Associated.counit` it is an isomorphism of categories.
* `D` on morphisms: a monoidal Π-functor `(F, j)` gives a monoidal superfunctor `F̂`
  (`Associated.mapMonoidal`, via the Π-functor `MonoidalPiFunctor.toPiFunctor` with
  `β_F = μ_{π,-} ∘ (j ⊗ 1)`); `E ∘ D = I` on morphisms: the underlying functor of `F̂` is `F`
  (`Associated.unit_comp_map`) and its coherence map `ĵ` is `j` (`Associated.jIso_mapMonoidal_hom`).
* `D ∘ E ≅ I`: for a monoidal Π-supercategory `A`, `T_A : (A̲)^ ⥤ A`, `f̂ ↦ f₀ + ζ_μ ∘ f₁`
  (`Associated.Tmon`), is an isomorphism of supercategories (`Tmon_comp_TmonInv`,
  `TmonInv_comp_Tmon`), a strict monoidal superfunctor (`Associated.TmonMonoidal`), carries
  `ζ` to `ζ` (`Tmon_map_ζ`), and is natural: `T_B ∘ (G̲)^ = G ∘ T_A` for every monoidal
  superfunctor `G` (`Associated.Tmon_naturality`).

The categories `Π-SMon` and `Π-Mon` themselves are not constructed; as for Lemma 5.1 in
`StringDiagrams.Super.Associated`, the content of the equivalence is stated directly on
objects and morphisms.

## Sign corrections

The vertical composition of two odd morphisms in `Â` carries the sign `-ξ` (see the erratum for
Lemma 5.1 in `StringDiagrams.Super.Associated`). Correspondingly, the paper's tensor product
`f̂ ⊗ ĝ` of two odd morphisms is `+ξ ∘ (1_π ⊗ β⁻¹ ⊗ 1) ∘ (f ⊗ g)`
(`Associated.superTensorHom_odd_odd`), whereas (5.5) prints
`-ξ_ν KH ∘ π_ν (β_{ν,μ})⁻¹_K H ∘ yx`. Both printed signs are those of the construction applied
to `(A, π, β, -ξ)`; with them, the monoidal Π-category underlying `Â` would have `-ξ` in place
of `ξ` and `T_A` would reverse the sign of odd–odd composites and tensor products. The printed
statement of Theorem 1.15 is unaffected, since `(A, π, β, ξ) ↦ (A, π, β, -ξ)` is an
automorphism of `Π-Mon`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe w w₁ w₂ w₃ w₄

namespace MonoidalPiCategory

variable {R : Type w} [CommRing R] {D : Type w₁} [Category.{w₂} D] [Preadditive D]
  [Linear R D] [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear R D]
  [MonoidalPiCategory R D]

local notation "𝛑" => MonoidalPiCategory.pi (R := R) (D := D)
local notation "𝛃" => MonoidalPiCategory.β (R := R) (D := D)
local notation "𝛏" => MonoidalPiCategory.ξ (R := R) (D := D)

omit [MonoidalLinear R D] [MonoidalPiCategory R D] in
theorem whiskerLeft_neg' (X : D) {Y Z : D} (f : Y ⟶ Z) : X ◁ (-f) = -(X ◁ f) :=
  (tensorLeft X).map_neg

omit [MonoidalLinear R D] [MonoidalPiCategory R D] in
theorem neg_whiskerRight' {X Y : D} (f : X ⟶ Y) (Z : D) : (-f) ▷ Z = -(f ▷ Z) :=
  (tensorRight Z).map_neg

variable (R) in
include R in
/-- (1.8) at `λ = π`, using `β_π = -1`: `l_π ∘ (ξ ⊗ 1_π) = r_π ∘ (1_π ⊗ ξ) ∘ a_{π,π,π}`. -/
theorem ξ_whiskerRight_pi :
    (𝛏).hom ▷ 𝛑 ≫ (λ_ 𝛑).hom = (α_ 𝛑 𝛑 𝛑).hom ≫ 𝛑 ◁ (𝛏).hom ≫ (ρ_ 𝛑).hom := by
  have h := ξ_comm (R := R) (D := D) 𝛑
  rw [β_pi (R := R), whiskerLeft_neg', neg_whiskerRight']
    at h
  simp only [MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight,
    Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.id_comp,
    Iso.hom_inv_id_assoc] at h
  rw [← h]
  simp [← MonoidalCategory.whiskerLeft_comp_assoc]

/-- The isomorphism `ξ_λ := l_λ ∘ (ξ ⊗ 1_λ) ∘ a⁻¹ : π ⊗ (π ⊗ λ) ≅ λ`. -/
def ξL (X : D) : 𝛑 ⊗ (𝛑 ⊗ X) ≅ X := (α_ 𝛑 𝛑 X).symm ≪≫ whiskerRightIso 𝛏 X ≪≫ λ_ X

theorem ξL_hom (X : D) : (ξL (R := R) X).hom = (α_ 𝛑 𝛑 X).inv ≫ (𝛏).hom ▷ X ≫ (λ_ X).hom := rfl

theorem ξL_inv (X : D) : (ξL (R := R) X).inv = (λ_ X).inv ≫ (𝛏).inv ▷ X ≫ (α_ 𝛑 𝛑 X).hom := by
  simp [ξL]

@[reassoc]
theorem ξL_naturality {X Y : D} (f : X ⟶ Y) :
    𝛑 ◁ 𝛑 ◁ f ≫ (ξL (R := R) Y).hom = (ξL (R := R) X).hom ≫ f := by
  rw [ξL_hom, ξL_hom, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    leftUnitor_naturality]
  simp only [Category.assoc]

theorem ξL_pi (X : D) : (ξL (R := R) (𝛑 ⊗ X)).hom = 𝛑 ◁ (ξL (R := R) X).hom := by
  have key : (𝛏).hom ▷ (𝛑 ⊗ X) ≫ (λ_ (𝛑 ⊗ X)).hom =
      (α_ (𝛑 ⊗ 𝛑) 𝛑 X).inv ≫ ((𝛏).hom ▷ 𝛑 ≫ (λ_ 𝛑).hom) ▷ X := by monoidal
  rw [ξL_hom, ξL_hom, key, ξ_whiskerRight_pi]
  monoidal

variable (R D) in
/-- **Brundan–Ellis, Definition 5.2(i) in the one-object case.** A monoidal Π-category is a
Π-category with `Π := π ⊗ -` and `ξ_λ := l_λ ∘ (ξ ⊗ 1_λ) ∘ a⁻¹`. (This is a definition rather
than an instance, to avoid clashing with other Π-category structures.) -/
abbrev toPiCategory : PiCategory R D where
  pi := tensorLeft 𝛑
  ξ := NatIso.ofComponents (fun X => ξL (R := R) X) fun f => ξL_naturality f
  ξ_pi X := ξL_pi X

attribute [local instance] toPiCategory

@[simp] theorem pi_obj (X : D) : (PiCategory.pi (R := R)).obj X = 𝛑 ⊗ X := rfl

@[simp] theorem pi_map {X Y : D} (f : X ⟶ Y) : (PiCategory.pi (R := R)).map f = 𝛑 ◁ f := rfl

@[simp] theorem ξApp_hom (X : D) : (PiCategory.ξApp (R := R) X).hom = (ξL (R := R) X).hom := rfl

@[simp] theorem ξApp_inv (X : D) : (PiCategory.ξApp (R := R) X).inv = (ξL (R := R) X).inv := rfl

@[simp] theorem ξ_hom_app (X : D) :
    (PiCategory.ξ (R := R) (C := D)).hom.app X = (ξL (R := R) X).hom := rfl

@[simp] theorem ξ_inv_app (X : D) :
    (PiCategory.ξ (R := R) (C := D)).inv.app X = (ξL (R := R) X).inv := rfl

/-! ### Whiskering functors are Π-functors -/

/-- The half-braiding inverse is natural. -/
@[reassoc]
theorem β_inv_naturality {X Y : D} (f : X ⟶ Y) :
    f ▷ 𝛑 ≫ ((𝛃).β Y).inv = ((𝛃).β X).inv ≫ 𝛑 ◁ f := by
  rw [Iso.eq_inv_comp, ← HalfBraiding.naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- `β_{π ⊗ λ} = -(a⁻¹ ∘ (1_π ⊗ β_λ))`, from (1.7) and `β_π = -1`. -/
theorem β_pi_tensor_hom (X : D) :
    ((𝛃).β (𝛑 ⊗ X)).hom = -(𝛑 ◁ ((𝛃).β X).hom ≫ (α_ 𝛑 X 𝛑).inv) := by
  rw [HalfBraiding.monoidal, β_pi (R := R), neg_whiskerRight', MonoidalCategory.id_whiskerRight]
  simp

theorem β_pi_tensor_inv (X : D) :
    ((𝛃).β (𝛑 ⊗ X)).inv = -((α_ 𝛑 X 𝛑).hom ≫ 𝛑 ◁ ((𝛃).β X).inv) := by
  rw [← cancel_epi ((𝛃).β (𝛑 ⊗ X)).hom, Iso.hom_inv_id, β_pi_tensor_hom]
  simp [← MonoidalCategory.whiskerLeft_comp]

theorem β_pi_inv : ((𝛃).β 𝛑).inv = -𝟙 _ := by
  rw [← cancel_epi ((𝛃).β 𝛑).hom, Iso.hom_inv_id, β_pi (R := R)]
  simp

/-- The isomorphism `π ⊗ (λ ⊗ μ) ≅ λ ⊗ (π ⊗ μ)` built from `β_λ`: the structure making `λ ⊗ -`
a Π-functor. -/
def βL (X Z : D) : 𝛑 ⊗ (X ⊗ Z) ≅ X ⊗ (𝛑 ⊗ Z) :=
  (α_ 𝛑 X Z).symm ≪≫ whiskerRightIso ((𝛃).β X) Z ≪≫ α_ X 𝛑 Z

theorem βL_hom (X Z : D) :
    (βL (R := R) X Z).hom = (α_ 𝛑 X Z).inv ≫ ((𝛃).β X).hom ▷ Z ≫ (α_ X 𝛑 Z).hom := rfl

theorem βL_inv (X Z : D) :
    (βL (R := R) X Z).inv = (α_ X 𝛑 Z).inv ≫ ((𝛃).β X).inv ▷ Z ≫ (α_ 𝛑 X Z).hom := by
  simp [βL]

@[reassoc]
theorem βL_naturality (X : D) {Z Z' : D} (f : Z ⟶ Z') :
    𝛑 ◁ X ◁ f ≫ (βL (R := R) X Z').hom = (βL (R := R) X Z).hom ≫ X ◁ 𝛑 ◁ f := by
  simp only [βL_hom, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right]

/-- (1.8), whiskered: the Π-functor axiom for `λ ⊗ -`. -/
theorem βL_comm (X Z : D) :
    (ξL (R := R) (X ⊗ Z)).hom ≫ X ◁ (ξL (R := R) Z).inv =
      𝛑 ◁ (βL (R := R) X Z).hom ≫ (βL (R := R) X (𝛑 ⊗ Z)).hom := by
  have h := ξ_comm (R := R) (D := D) X
  have key : (ξL (R := R) (X ⊗ Z)).hom ≫ X ◁ (ξL (R := R) Z).inv =
      ((α_ 𝛑 𝛑 (X ⊗ Z)).inv ≫ (α_ (𝛑 ⊗ 𝛑) X Z).inv) ≫
        ((𝛏).hom ▷ X ≫ (λ_ X).hom ≫ (ρ_ X).inv ≫ X ◁ (𝛏).inv) ▷ Z ≫
          ((α_ X (𝛑 ⊗ 𝛑) Z).hom ≫ X ◁ (α_ 𝛑 𝛑 Z).hom) := by
    rw [ξL_hom, ξL_inv]; monoidal
  rw [key, h, βL_hom, βL_hom]
  monoidal

variable (R) in
/-- `λ ⊗ -` is a Π-functor with `β := a_{λ,π,-} ∘ (β_λ ⊗ 1) ∘ a⁻¹`. -/
def tensorLeftPi (X : D) : PiFunctor R (tensorLeft X) where
  β := NatIso.ofComponents (fun Z => βL (R := R) X Z) fun f => βL_naturality X f
  comm Z := βL_comm X Z

@[simp] theorem tensorLeftPi_β_hom_app (X Z : D) :
    (tensorLeftPi R X).β.hom.app Z = (βL (R := R) X Z).hom := rfl

@[simp] theorem tensorLeftPi_β_inv_app (X Z : D) :
    (tensorLeftPi R X).β.inv.app Z = (βL (R := R) X Z).inv := rfl

/-- The Π-functor axiom for `- ⊗ μ` (a coherence statement). -/
theorem αR_comm (X Y : D) :
    (ξL (R := R) (X ⊗ Y)).hom ≫ (ξL (R := R) X).inv ▷ Y =
      𝛑 ◁ (α_ 𝛑 X Y).inv ≫ (α_ 𝛑 (𝛑 ⊗ X) Y).inv := by
  have key : (ξL (R := R) (X ⊗ Y)).hom ≫ (ξL (R := R) X).inv ▷ Y =
      (α_ 𝛑 𝛑 (X ⊗ Y)).inv ≫ ((𝛏).hom ▷ (X ⊗ Y) ≫ (𝛏).inv ▷ (X ⊗ Y)) ≫
        (α_ (𝛑 ⊗ 𝛑) X Y).inv ≫ (α_ 𝛑 𝛑 X).hom ▷ Y := by
    rw [ξL_hom, ξL_inv]; monoidal
  rw [key, ← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id,
    MonoidalCategory.id_whiskerRight]
  monoidal

variable (R) in
/-- `- ⊗ μ` is a Π-functor with `β := a⁻¹`. -/
def tensorRightPi (Y : D) : PiFunctor R (tensorRight Y) where
  β := NatIso.ofComponents (fun X => (α_ 𝛑 X Y).symm) fun f =>
    associator_inv_naturality_middle 𝛑 f Y
  comm X := αR_comm X Y

@[simp] theorem tensorRightPi_β_hom_app (X Y : D) :
    (tensorRightPi R Y).β.hom.app X = (α_ 𝛑 X Y).inv := rfl

@[simp] theorem tensorRightPi_β_inv_app (X Y : D) :
    (tensorRightPi R Y).β.inv.app X = (α_ 𝛑 X Y).hom := rfl

/-- `βL` is natural in its first variable. -/
@[reassoc]
theorem βL_inv_naturality_left {X X' : D} (f : X ⟶ X') (Z : D) :
    f ▷ (𝛑 ⊗ Z) ≫ (βL (R := R) X' Z).inv = (βL (R := R) X Z).inv ≫ 𝛑 ◁ f ▷ Z := by
  simp only [βL_inv, Category.assoc]
  rw [associator_inv_naturality_left_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
    β_inv_naturality, MonoidalCategory.comp_whiskerRight_assoc, associator_naturality_middle]

/-- **(1.6).** `l_π ∘ β_1 = r_π`: the unit axiom for the half-braiding follows from (1.7). -/
theorem β_unit : ((𝛃).β (𝟙_ D)).hom ≫ (λ_ 𝛑).hom = (ρ_ 𝛑).hom := by
  set b := ((𝛃).β (𝟙_ D)).hom with hbdef
  set e := (ρ_ 𝛑).inv ≫ b ≫ (λ_ 𝛑).hom with he
  have hb : b = (ρ_ 𝛑).hom ≫ e ≫ (λ_ 𝛑).inv := by simp [he]
  have H := (𝛃).naturality (λ_ (𝟙_ D)).hom
  rw [HalfBraiding.monoidal, ← hbdef, hb] at H
  have H2 : ((𝛑 ◁ (λ_ (𝟙_ D)).hom ≫ (ρ_ 𝛑).hom) ≫ e) ≫ (λ_ 𝛑).inv =
      ((𝛑 ◁ (λ_ (𝟙_ D)).hom ≫ (ρ_ 𝛑).hom) ≫ (e ≫ e)) ≫ (λ_ 𝛑).inv := by
    calc _ = 𝛑 ◁ (λ_ (𝟙_ D)).hom ≫ (ρ_ 𝛑).hom ≫ e ≫ (λ_ 𝛑).inv := by simp
      _ = _ := H
      _ = _ := by monoidal
  have H3 : e = e ≫ e := by
    have := (cancel_mono _).1 H2
    exact (cancel_epi _).1 this
  have hiso : IsIso e := by rw [he]; infer_instance
  have he1 : e = 𝟙 _ := by
    rw [← cancel_mono e, Category.id_comp]; exact H3.symm
  rw [hb, he1]; simp

end MonoidalPiCategory

/-! ## Monoidal Π-functors are Π-functors -/

namespace MonoidalPiFunctor

variable {R : Type w} [CommRing R] {D : Type w₁} [Category.{w₂} D] [Preadditive D]
  [Linear R D] [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear R D]
  [MonoidalPiCategory R D]
  {E : Type w₃} [Category.{w₄} E] [Preadditive E] [Linear R E] [MonoidalCategory E]
  [MonoidalPreadditive E] [MonoidalLinear R E] [MonoidalPiCategory R E]

attribute [local instance] MonoidalPiCategory.toPiCategory

open Functor.LaxMonoidal Functor.OplaxMonoidal MonoidalPiCategory

local notation "𝛑D" => MonoidalPiCategory.pi (R := R) (D := D)
local notation "𝛑E" => MonoidalPiCategory.pi (R := R) (D := E)
local notation "𝛏D" => MonoidalPiCategory.ξ (R := R) (D := D)
local notation "𝛏E" => MonoidalPiCategory.ξ (R := R) (D := E)

variable {F : D ⥤ E} [F.Monoidal] (hF : MonoidalPiFunctor R F)

/-- The isomorphism `μ_{π,λ} ∘ (j ⊗ 1) : π ⊗ F λ ≅ F (π ⊗ λ)` making a monoidal Π-functor a
Π-functor for `Π = π ⊗ -`. -/
def βF (X : D) : 𝛑E ⊗ F.obj X ≅ F.obj (𝛑D ⊗ X) :=
  whiskerRightIso hF.j (F.obj X) ≪≫ Functor.Monoidal.μIso F 𝛑D X

theorem βF_hom (X : D) : (hF.βF X).hom = hF.j.hom ▷ F.obj X ≫ μ F 𝛑D X := rfl

theorem βF_inv (X : D) : (hF.βF X).inv = δ F 𝛑D X ≫ hF.j.inv ▷ F.obj X := by
  simp [βF]

@[reassoc]
theorem βF_naturality {X Y : D} (f : X ⟶ Y) :
    𝛑E ◁ F.map f ≫ (hF.βF Y).hom = (hF.βF X).hom ≫ F.map (𝛑D ◁ f) := by
  rw [βF_hom, βF_hom, whisker_exchange_assoc, μ_natural_right, Category.assoc]

theorem βF_comm (X : D) :
    (ξL (R := R) (F.obj X)).hom ≫ F.map (ξL (R := R) X).inv =
      𝛑E ◁ (hF.βF X).hom ≫ (hF.βF (𝛑D ⊗ X)).hom := by
  rw [← cancel_mono (F.map (ξL (R := R) X).hom), Category.assoc, ← F.map_comp, Iso.inv_hom_id,
    F.map_id, Category.comp_id]
  have hξ := hF.ξ_comm
  have e1 : (ξL (R := R) (F.obj X)).hom =
      (α_ 𝛑E 𝛑E (F.obj X)).inv ≫ ((𝛏E).hom ≫ ε F) ▷ F.obj X ≫ μ F (𝟙_ D) X ≫
        F.map (λ_ X).hom := by
    rw [ξL_hom, Functor.LaxMonoidal.left_unitality F X, MonoidalCategory.comp_whiskerRight_assoc]
  rw [e1, hξ, tensorHom_def', MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight, MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [μ_natural_left_assoc, βF_hom, βF_hom, ξL_hom, F.map_comp, F.map_comp,
    MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, Functor.LaxMonoidal.associativity_inv_assoc]
  have e2 : (α_ 𝛑E 𝛑E (F.obj X)).inv ≫ (𝛑E ◁ hF.j.hom) ▷ F.obj X ≫
      hF.j.hom ▷ F.obj 𝛑D ▷ F.obj X =
      𝛑E ◁ hF.j.hom ▷ F.obj X ≫ hF.j.hom ▷ (F.obj 𝛑D ⊗ F.obj X) ≫
        (α_ (F.obj 𝛑D) (F.obj 𝛑D) (F.obj X)).inv := by monoidal
  rw [reassoc_of% e2]

variable (R) in
/-- **Brundan–Ellis, (5.2) for monoidal Π-functors.** A monoidal Π-functor is a Π-functor for
`Π = π ⊗ -`, with `β_F := μ_{π,-} ∘ (j ⊗ 1)`. -/
def toPiFunctor : PiFunctor R F where
  β := NatIso.ofComponents hF.βF fun f => hF.βF_naturality f
  comm X := hF.βF_comm X

@[simp] theorem toPiFunctor_β_hom_app (X : D) : (hF.toPiFunctor R).β.hom.app X = (hF.βF X).hom :=
  rfl

@[simp] theorem toPiFunctor_β_inv_app (X : D) : (hF.toPiFunctor R).β.inv.app X = (hF.βF X).inv :=
  rfl

/-- The compatibility of `β_F` with the whiskerings `λ ⊗ -`, from the first axiom of
Definition 1.14(ii). -/
theorem βL_βF (X Y : D) :
    𝛑E ◁ μ F X Y ≫ (hF.βF (X ⊗ Y)).hom ≫ F.map (βL (R := R) X Y).hom =
      (βL (R := R) (F.obj X) (F.obj Y)).hom ≫ F.obj X ◁ (hF.βF Y).hom ≫ μ F X (𝛑D ⊗ Y) := by
  have hβ := hF.β_comm X
  rw [βF_hom, βL_hom, F.map_comp, F.map_comp]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, Functor.LaxMonoidal.associativity_inv_assoc,
    ← μ_natural_left_assoc]
  have e1 : hF.j.hom ▷ (F.obj X ⊗ F.obj Y) ≫ (α_ (F.obj 𝛑D) (F.obj X) (F.obj Y)).inv =
      (α_ 𝛑E (F.obj X) (F.obj Y)).inv ≫ (hF.j.hom ▷ F.obj X) ▷ F.obj Y := by monoidal
  rw [reassoc_of% e1, ← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc]
  simp only [Category.assoc]
  rw [hβ]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [Functor.LaxMonoidal.associativity, βF_hom, βL_hom]
  simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp]
  have e2 : (F.obj X ◁ hF.j.hom) ▷ F.obj Y ≫ (α_ (F.obj X) (F.obj 𝛑D) (F.obj Y)).hom =
      (α_ (F.obj X) 𝛑E (F.obj Y)).hom ≫ F.obj X ◁ hF.j.hom ▷ F.obj Y := by monoidal
  rw [reassoc_of% e2]

theorem βL_βF_inv (X Y : D) :
    F.obj X ◁ (hF.βF Y).inv ≫ (βL (R := R) (F.obj X) (F.obj Y)).inv ≫ 𝛑E ◁ μ F X Y =
      μ F X (𝛑D ⊗ Y) ≫ F.map (βL (R := R) X Y).inv ≫ (hF.βF (X ⊗ Y)).inv := by
  have h := hF.βL_βF X Y
  rw [← cancel_epi (F.obj X ◁ (hF.βF Y).hom), ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    ← cancel_epi (βL (R := R) (F.obj X) (F.obj Y)).hom, Iso.hom_inv_id_assoc,
    ← reassoc_of% h]
  simp [← F.map_comp_assoc]

theorem βF_inv_whiskerRight (Y X' : D) :
    μ F (𝛑D ⊗ Y) X' ≫ F.map (α_ 𝛑D Y X').hom ≫ (hF.βF (Y ⊗ X')).inv =
      (hF.βF Y).inv ▷ F.obj X' ≫ (α_ 𝛑E (F.obj Y) (F.obj X')).hom ≫ 𝛑E ◁ μ F Y X' := by
  rw [βF_inv, βF_inv, Functor.Monoidal.map_associator]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ,
    Category.comp_id, MonoidalCategory.comp_whiskerRight]
  rw [whisker_exchange]
  monoidal

end MonoidalPiFunctor

/-! ## General facts about the associated supercategory -/

namespace Associated

section General

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [PiCategory R C] {E : Type w₃} [Category.{w₄} E] [Preadditive E] [Linear R E] [PiCategory R E]

/-- The even isomorphism `(e, 0)` of `Â` given by an isomorphism `e` of `A`. -/
@[simps]
def evenIso {X Y : Associated R C} (e : X.obj ≅ Y.obj) : X ≅ Y where
  hom := homMk e.hom 0
  inv := homMk e.inv 0
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

theorem homMk_comp_homMk_even {X Y Z : Associated R C} (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) :
    (homMk f 0 : X ⟶ Y) ≫ (homMk g 0 : Y ⟶ Z) = homMk (f ≫ g) 0 := by
  ext <;> simp

theorem homMk_even_mem {X Y : Associated R C} (f : X.obj ⟶ Y.obj) :
    (homMk f 0 : X ⟶ Y) ∈ parity (R := R) X Y 0 :=
  mem_parity_zero.2 rfl

/-- **Brundan–Ellis, (5.3).** The naturality square of `ŷ = (y, 0)` for a Π-natural
transformation `y`, on an arbitrary morphism of `Â`. -/
theorem map_naturality {F G : C ⥤ E} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
    {hF : PiFunctor R F} {hG : PiFunctor R G} {y : F ⟶ G} (hy : PiFunctor.IsPiNatural R hF hG y)
    {X Y : Associated R C} (f : X ⟶ Y) :
    (map hF).map f ≫ homMk (Y := (map hG).obj Y) (y.app Y.obj) 0 =
      homMk (X := (map hF).obj X) (y.app X.obj) 0 ≫ (map hG).map f :=
  (isSupernatural_mapNatTrans hy).naturality_zero f

end General

section Monoidal

variable {R : Type w} [CommRing R] {D : Type w₁} [Category.{w₂} D] [Preadditive D]
  [Linear R D] [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear R D]
  [MonoidalPiCategory R D]

attribute [local instance] MonoidalPiCategory.toPiCategory

open MonoidalPiCategory

local notation "𝛑" => MonoidalPiCategory.pi (R := R) (D := D)
local notation "𝛃" => MonoidalPiCategory.β (R := R) (D := D)
local notation "𝛏" => MonoidalPiCategory.ξ (R := R) (D := D)

theorem map_map_map {F G : D ⥤ D} [F.Additive] [G.Additive] (hF : PiFunctor R F)
    (hG : PiFunctor R G) {X Y : Associated R D} (f : X ⟶ Y) :
    (map hG).map ((map hF).map f) = (map (hF.comp hG)).map f := by
  ext <;> simp

theorem map_id_map {X Y : Associated R D} (f : X ⟶ Y) : (map (PiFunctor.id R D)).map f = f := by
  ext <;> simp

/-- The monoidal structure on `Â` (Brundan–Ellis, (5.5) with one object): `λ ⊗ μ` as in `A`,
`λ ◁ ĝ = (λ ◁ g₀, β-corrected λ ◁ g₁)` and `f̂ ▷ μ = (f₀ ▷ μ, a ∘ (f₁ ▷ μ))`, i.e. the functors
`D₁(λ ⊗ -)` and `D₁(- ⊗ μ)` of the Π-functors `tensorLeftPi`, `tensorRightPi`; the coherence
maps are those of `A`, viewed as even isomorphisms. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Associated R D) where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  whiskerLeft X _ _ g := (map (tensorLeftPi R X.obj)).map g
  whiskerRight f Y := (map (tensorRightPi R Y.obj)).map f
  tensorUnit := ⟨𝟙_ D⟩
  associator X Y Z := evenIso (α_ X.obj Y.obj Z.obj)
  leftUnitor X := evenIso (λ_ X.obj)
  rightUnitor X := evenIso (ρ_ X.obj)

@[simp] theorem tensorObj_obj (X Y : Associated R D) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

@[simp] theorem tensorUnit_obj : (𝟙_ (Associated R D)).obj = 𝟙_ D := rfl

@[simp] theorem whiskerLeft_fst (X : Associated R D) {Y Z : Associated R D} (g : Y ⟶ Z) :
    (X ◁ g).1 = X.obj ◁ g.1 := rfl

@[simp] theorem whiskerLeft_snd (X : Associated R D) {Y Z : Associated R D} (g : Y ⟶ Z) :
    (X ◁ g).2 = X.obj ◁ g.2 ≫ (βL (R := R) X.obj Z.obj).inv := rfl

@[simp] theorem whiskerRight_fst {X Y : Associated R D} (f : X ⟶ Y) (Z : Associated R D) :
    (f ▷ Z).1 = f.1 ▷ Z.obj := rfl

@[simp] theorem whiskerRight_snd {X Y : Associated R D} (f : X ⟶ Y) (Z : Associated R D) :
    (f ▷ Z).2 = f.2 ▷ Z.obj ≫ (α_ 𝛑 Y.obj Z.obj).hom := rfl

@[simp] theorem associator_hom_fst (X Y Z : Associated R D) :
    (α_ X Y Z).hom.1 = (α_ X.obj Y.obj Z.obj).hom := rfl

@[simp] theorem associator_hom_snd (X Y Z : Associated R D) : (α_ X Y Z).hom.2 = 0 := rfl

@[simp] theorem associator_inv_fst (X Y Z : Associated R D) :
    (α_ X Y Z).inv.1 = (α_ X.obj Y.obj Z.obj).inv := rfl

@[simp] theorem associator_inv_snd (X Y Z : Associated R D) : (α_ X Y Z).inv.2 = 0 := rfl

@[simp] theorem leftUnitor_hom_fst (X : Associated R D) : (λ_ X).hom.1 = (λ_ X.obj).hom := rfl

@[simp] theorem leftUnitor_hom_snd (X : Associated R D) : (λ_ X).hom.2 = 0 := rfl

@[simp] theorem leftUnitor_inv_fst (X : Associated R D) : (λ_ X).inv.1 = (λ_ X.obj).inv := rfl

@[simp] theorem leftUnitor_inv_snd (X : Associated R D) : (λ_ X).inv.2 = 0 := rfl

@[simp] theorem rightUnitor_hom_fst (X : Associated R D) : (ρ_ X).hom.1 = (ρ_ X.obj).hom := rfl

@[simp] theorem rightUnitor_hom_snd (X : Associated R D) : (ρ_ X).hom.2 = 0 := rfl

@[simp] theorem rightUnitor_inv_fst (X : Associated R D) : (ρ_ X).inv.1 = (ρ_ X.obj).inv := rfl

@[simp] theorem rightUnitor_inv_snd (X : Associated R D) : (ρ_ X).inv.2 = 0 := rfl

/-! ### The super interchange law -/

/-- The key identity for the super interchange law on two odd morphisms. -/
theorem odd_odd_key {X X' Y Y' : D} (f : X ⟶ 𝛑 ⊗ X') (g : Y ⟶ 𝛑 ⊗ Y') :
    X ◁ g ≫ (βL (R := R) X Y').inv ≫ 𝛑 ◁ f ▷ Y' ≫ 𝛑 ◁ (α_ 𝛑 X' Y').hom =
      -(f ▷ Y ≫ (α_ 𝛑 X' Y).hom ≫ 𝛑 ◁ X' ◁ g ≫ 𝛑 ◁ (βL (R := R) X' Y').inv) := by
  rw [← βL_inv_naturality_left_assoc, whisker_exchange_assoc, βL_inv, β_pi_tensor_inv,
    neg_whiskerRight', βL_inv]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg]
  congr 1
  monoidal

theorem super_interchange_assoc {X X' Y Y' : Associated R D} {p q : ZMod 2} {f : X ⟶ X'}
    {g : Y ⟶ Y'} (hf : f ∈ parity (R := R) X X' p) (hg : g ∈ parity (R := R) Y Y' q) :
    f ▷ Y ≫ X' ◁ g = koszulSign p q • (X ◁ g ≫ f ▷ Y') := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [mem_parity_zero] at hf hg
    rw [koszulSign_zero_left, one_smul]
    ext
    · simp [hf, hg, whisker_exchange]
    · simp [hf, hg]
  · rw [mem_parity_zero] at hf; rw [mem_parity_one] at hg
    rw [koszulSign_zero_left, one_smul]
    ext
    · simp [hf, hg]
    · simp only [comp_snd, whiskerRight_fst, whiskerLeft_snd, whiskerRight_snd, hf, hg,
        whiskerLeft_fst, MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp, add_zero,
        zero_add, MonoidalPreadditive.whiskerLeft_zero, Limits.comp_zero, tensorLeft_map,
        Functor.map_zero, Category.assoc, MonoidalPiCategory.pi_obj, MonoidalPiCategory.pi_map]
      rw [← whisker_exchange_assoc, βL_inv_naturality_left]
  · rw [mem_parity_one] at hf; rw [mem_parity_zero] at hg
    rw [koszulSign_zero_right, one_smul]
    ext
    · simp [hf, hg]
    · simp only [comp_snd, whiskerRight_fst, whiskerLeft_snd, whiskerRight_snd, hf, hg,
        whiskerLeft_fst, MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp, add_zero,
        zero_add, MonoidalPreadditive.whiskerLeft_zero, Limits.comp_zero, Category.assoc]
      rw [whisker_exchange_assoc]
      simp
  · rw [mem_parity_one] at hf hg
    rw [koszulSign_one_one, neg_one_smul]
    ext
    · simp only [comp_fst, whiskerRight_fst, whiskerLeft_snd, whiskerRight_snd, hf, hg,
        whiskerLeft_fst, neg_fst, MonoidalPreadditive.zero_whiskerRight,
        MonoidalPreadditive.whiskerLeft_zero, Limits.zero_comp, zero_sub, neg_neg,
        Category.assoc, PiCategory.pi, tensorLeft_map, MonoidalCategory.whiskerLeft_comp,
        ξApp_hom, tensorObj_obj]
      rw [reassoc_of% (odd_odd_key (R := R) f.2 g.2)]
      simp
    · simp [hf, hg]

/-! ### Naturality of the coherence maps -/

section Naturality

variable (R)

/-- `a_{-,μ,ν}` as a Π-natural transformation `(- ⊗ μ) ⊗ ν ⟶ - ⊗ (μ ⊗ ν)`. -/
def αLeft (Y Z : D) : tensorRight Y ⋙ tensorRight Z ⟶ tensorRight (Y ⊗ Z) where
  app X := (α_ X Y Z).hom
  naturality _ _ f := associator_naturality_left f Y Z

theorem αLeft_isPiNatural (Y Z : D) :
    PiFunctor.IsPiNatural R ((tensorRightPi R Y).comp (tensorRightPi R Z)) (tensorRightPi R (Y ⊗ Z))
      (αLeft Y Z) := fun X => by
  simp [αLeft]

/-- `a_{λ,-,ν}` as a Π-natural transformation. -/
def αMiddle (X Z : D) : tensorLeft X ⋙ tensorRight Z ⟶ tensorRight Z ⋙ tensorLeft X where
  app Y := (α_ X Y Z).hom
  naturality _ _ f := associator_naturality_middle X f Z

theorem αMiddle_isPiNatural (X Z : D) :
    PiFunctor.IsPiNatural R ((tensorLeftPi R X).comp (tensorRightPi R Z))
      ((tensorRightPi R Z).comp (tensorLeftPi R X)) (αMiddle X Z) := fun Y => by
  simp only [αMiddle, PiFunctor.comp_β, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, tensorRightPi_β_hom_app, tensorLeftPi_β_hom_app, tensorRight_map,
    tensorLeft_map, MonoidalPiCategory.pi_obj, MonoidalPiCategory.pi_map, Functor.comp_obj,
    tensorLeft_obj, tensorRight_obj, βL_hom]
  monoidal

/-- `a_{λ,μ,-}` as a Π-natural transformation. -/
def αRight (X Y : D) : tensorLeft (X ⊗ Y) ⟶ tensorLeft Y ⋙ tensorLeft X where
  app Z := (α_ X Y Z).hom
  naturality _ _ f := associator_naturality_right X Y f

theorem αRight_isPiNatural (X Y : D) :
    PiFunctor.IsPiNatural R (tensorLeftPi R (X ⊗ Y))
      ((tensorLeftPi R Y).comp (tensorLeftPi R X)) (αRight X Y) := fun Z => by
  simp only [αRight, PiFunctor.comp_β, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, tensorLeftPi_β_hom_app, tensorLeft_map, MonoidalPiCategory.pi_obj,
    MonoidalPiCategory.pi_map, Functor.comp_obj, tensorLeft_obj, βL_hom, HalfBraiding.monoidal]
  monoidal

/-- `l` as a Π-natural transformation. -/
def lNat : tensorLeft (𝟙_ D) ⟶ 𝟭 D where
  app X := (λ_ X).hom
  naturality _ _ f := leftUnitor_naturality f

theorem lNat_isPiNatural :
    PiFunctor.IsPiNatural R (tensorLeftPi R (𝟙_ D)) (PiFunctor.id R D) lNat := fun Z => by
  have h := MonoidalPiCategory.β_unit (R := R) (D := D)
  rw [← Iso.eq_comp_inv] at h
  simp only [lNat, tensorLeftPi_β_hom_app, βL_hom, h, MonoidalPiCategory.pi_obj,
    MonoidalPiCategory.pi_map, PiFunctor.id_β, Iso.refl_hom, NatTrans.id_app, Functor.id_obj,
    Category.comp_id, tensorLeft_obj]
  monoidal

/-- `r` as a Π-natural transformation. -/
def rNat : tensorRight (𝟙_ D) ⟶ 𝟭 D where
  app X := (ρ_ X).hom
  naturality _ _ f := rightUnitor_naturality f

theorem rNat_isPiNatural :
    PiFunctor.IsPiNatural R (tensorRightPi R (𝟙_ D)) (PiFunctor.id R D) rNat := fun Z => by
  simp only [rNat, tensorRightPi_β_hom_app, MonoidalPiCategory.pi_obj, MonoidalPiCategory.pi_map,
    PiFunctor.id_β, Iso.refl_hom, NatTrans.id_app, Functor.id_obj, Category.comp_id,
    tensorRight_obj]
  monoidal

end Naturality

theorem associator_naturality_left_assoc' {X X' : Associated R D} (f : X ⟶ X')
    (Y Z : Associated R D) :
    (f ▷ Y) ▷ Z ≫ (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) := by
  have h := map_naturality (αLeft_isPiNatural R Y.obj Z.obj) f
  rw [← map_map_map] at h
  exact h

theorem associator_naturality_middle_assoc' (X : Associated R D) {Y Y' : Associated R D}
    (g : Y ⟶ Y') (Z : Associated R D) :
    (X ◁ g) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ (g ▷ Z) := by
  have h := map_naturality (αMiddle_isPiNatural R X.obj Z.obj) g
  rw [← map_map_map, ← map_map_map] at h
  exact h

theorem associator_naturality_right_assoc' (X Y : Associated R D) {Z Z' : Associated R D}
    (h : Z ⟶ Z') : (X ⊗ Y) ◁ h ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ Y ◁ h := by
  have e := map_naturality (αRight_isPiNatural R X.obj Y.obj) h
  rw [← map_map_map] at e
  exact e

theorem leftUnitor_naturality_assoc' {X Y : Associated R D} (f : X ⟶ Y) :
    𝟙_ (Associated R D) ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  have h := map_naturality (lNat_isPiNatural R) f
  rw [map_id_map] at h
  exact h

theorem rightUnitor_naturality_assoc' {X Y : Associated R D} (f : X ⟶ Y) :
    f ▷ 𝟙_ (Associated R D) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  have h := map_naturality (rNat_isPiNatural R) f
  rw [map_id_map] at h
  exact h

/-- **Brundan–Ellis, Theorem 1.15 / (5.5) with one object.** The associated supercategory `Â`
of a monoidal Π-category is a monoidal supercategory. -/
instance monoidalSupercategory : MonoidalSupercategory R (Associated R D) where
  tensorHom_def _ _ := rfl
  whiskerLeft_id X Y := (map (tensorLeftPi R X.obj)).map_id Y
  id_whiskerRight X Y := (map (tensorRightPi R Y.obj)).map_id X
  whiskerLeft_comp X _ _ _ f g := (map (tensorLeftPi R X.obj)).map_comp f g
  comp_whiskerRight f g W := (map (tensorRightPi R W.obj)).map_comp f g
  whiskerLeft_add X _ _ f g := (map (tensorLeftPi R X.obj)).map_add
  add_whiskerRight f g Z := (map (tensorRightPi R Z.obj)).map_add
  whiskerLeft_smul X _ _ r f := Functor.Linear.map_smul (F := map (tensorLeftPi R X.obj)) f r
  smul_whiskerRight r f Z := Functor.Linear.map_smul (F := map (tensorRightPi R Z.obj)) f r
  whiskerLeft_mem X _ _ _ _ hf := IsSuperfunctor.map_mem (F := map (tensorLeftPi R X.obj)) hf
  whiskerRight_mem Z hf := IsSuperfunctor.map_mem (F := map (tensorRightPi R Z.obj)) hf
  super_interchange hf hg := super_interchange_assoc hf hg
  associator_naturality :=
    MonoidalSupercategory.associator_naturality_of_whiskers (fun _ _ => rfl)
      (fun X _ _ _ f g => (map (tensorLeftPi R X.obj)).map_comp f g)
      (fun f g W => (map (tensorRightPi R W.obj)).map_comp f g)
      associator_naturality_left_assoc' associator_naturality_middle_assoc'
      associator_naturality_right_assoc'
  leftUnitor_naturality := leftUnitor_naturality_assoc'
  rightUnitor_naturality := rightUnitor_naturality_assoc'
  pentagon W X Y Z := by ext <;> simp [homMk_comp_homMk_even, pentagon]
  triangle X Y := by ext <;> simp [triangle]
  associator_hom_mem _ _ _ := mem_parity_zero.2 rfl
  leftUnitor_hom_mem _ := mem_parity_zero.2 rfl
  rightUnitor_hom_mem _ := mem_parity_zero.2 rfl

/-- **The corrected odd–odd horizontal rule** ((5.5) with one object). For odd `f̂ : X₁ → Y₁`,
`ĝ : X₂ → Y₂` coming from `f : X₁ → π ⊗ Y₁`, `g : X₂ → π ⊗ Y₂`, the paper's tensor product
`f̂ ⊗ ĝ = (f̂ ⊗ 1) ∘ (1 ⊗ ĝ)` in `Â` is the even morphism
`ξ_{Y₁ ⊗ Y₂} ∘ (1_π ⊗ β⁻¹_{Y₁} ⊗ 1) ∘ (f ⊗ g)` (up to associators), *without* the minus sign
printed in (5.5). -/
theorem superTensorHom_odd_odd {X₁ Y₁ X₂ Y₂ : Associated R D} {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂}
    (hf : f.1 = 0) (hg : g.1 = 0) :
    MonoidalSupercategory.superTensorHom f g =
      homMk ((f.2 ⊗ g.2) ≫ (α_ 𝛑 Y₁.obj (𝛑 ⊗ Y₂.obj)).hom ≫ 𝛑 ◁ (βL (R := R) Y₁.obj Y₂.obj).inv ≫
        (ξL (R := R) (Y₁.obj ⊗ Y₂.obj)).hom) 0 := by
  ext
  · simp only [MonoidalSupercategory.superTensorHom, comp_fst, whiskerLeft_fst, whiskerRight_fst,
      whiskerLeft_snd, whiskerRight_snd, hf, hg, homMk_fst, MonoidalPreadditive.whiskerLeft_zero,
      MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp, zero_sub, ξApp_hom,
      MonoidalPiCategory.pi_map, tensorLeft_map, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, tensorObj_obj]
    rw [reassoc_of% (odd_odd_key (R := R) f.2 g.2)]
    simp only [Preadditive.neg_comp, neg_neg, tensorHom_def, Category.assoc,
      MonoidalPiCategory.pi_obj, associator_naturality_right_assoc]
  · simp [MonoidalSupercategory.superTensorHom, hf, hg]

/-! ### The monoidal Π-supercategory structure -/

/-- The odd isomorphism `ζ : π ≅ 1` of `Â`: the morphism `r_π⁻¹ : π → π ⊗ 1` of `A`, viewed as
an odd morphism `π → 1` of `Â` (Brundan–Ellis, (5.5): `ζ := 1_π` viewed as odd). -/
def ζUnit : (⟨𝛑⟩ : Associated R D) ≅ 𝟙_ (Associated R D) :=
  evenIso (ρ_ 𝛑).symm ≪≫ ζIso (𝟙_ (Associated R D))

@[simp] theorem ζUnit_hom_fst : (ζUnit (R := R) (D := D)).hom.1 = 0 := by
  simp [ζUnit, ζIso]

@[simp] theorem ζUnit_hom_snd : (ζUnit (R := R) (D := D)).hom.2 = (ρ_ 𝛑).inv := by
  simp [ζUnit, ζIso]

@[simp] theorem ζUnit_inv_fst : (ζUnit (R := R) (D := D)).inv.1 = 0 := by
  simp [ζUnit, ζIso]

@[simp] theorem ζUnit_inv_snd :
    (ζUnit (R := R) (D := D)).inv.2 = -((ξL (R := R) (𝟙_ D)).inv ≫ 𝛑 ◁ (ρ_ 𝛑).hom) := by
  simp [ζUnit, ζIso]

theorem ζUnit_hom_mem :
    (ζUnit (R := R) (D := D)).hom ∈ parity (R := R) (⟨𝛑⟩ : Associated R D) (𝟙_ _) 1 :=
  mem_parity_one.2 ζUnit_hom_fst

/-- **Brundan–Ellis, Theorem 1.15 (functor `D`, on objects).** The associated supercategory of a
monoidal Π-category is a monoidal Π-supercategory with `π̂ = π` and `ζ = r_π⁻¹` viewed as an odd
morphism `π → 1`. -/
instance instMonoidalPiSupercategory : MonoidalPiSupercategory R (Associated R D) where
  pi := ⟨𝛑⟩
  ζ := ζUnit
  ζ_hom_mem := ζUnit_hom_mem

@[simp] theorem pi_eq : MonoidalPiSupercategory.pi (R := R) (C := Associated R D) = ⟨𝛑⟩ := rfl

theorem ζ_eq : MonoidalPiSupercategory.ζ (R := R) (C := Associated R D) = ζUnit := rfl

/-- **`E ∘ D = I` on `ξ`.** The isomorphism `ξ̂ = (l_1 = r_1) ∘ (ζ̂ ⊗ ζ̂)` of `Â` is `ξ`, viewed as
an even morphism. This uses the corrected sign of the composition of odd morphisms in `Â`. -/
theorem ξ_hom_eq :
    (MonoidalPiSupercategory.ξ (R := R) (C := Associated R D)).hom =
      homMk (X := ⟨𝛑 ⊗ 𝛑⟩) (Y := 𝟙_ _) (𝛏).hom 0 := by
  have hβ : (βL (R := R) 𝛑 (𝟙_ D)).inv = -𝟙 _ := by
    rw [βL_inv, β_pi_inv, neg_whiskerRight']; simp
  ext
  · simp [MonoidalPiSupercategory.ξ_hom, MonoidalPiSupercategory.ζR, ζ_eq, hβ]
    rw [ξL_hom]
    monoidal
  · simp [MonoidalPiSupercategory.ξ_hom, MonoidalPiSupercategory.ζR, ζ_eq]

/-- **`E ∘ D = I` on `β`.** The half-braiding `β̂_λ = (1_λ ⊗ ζ̂⁻¹) ∘ r_λ⁻¹ ∘ l_λ ∘ (ζ̂ ⊗ 1_λ)` of
`Â` is `β_λ`, viewed as an even morphism. -/
theorem β_hom_eq (X : Associated R D) :
    (MonoidalPiSupercategory.β (R := R) X).hom =
      homMk (X := ⟨𝛑 ⊗ X.obj⟩) (Y := ⟨X.obj ⊗ 𝛑⟩) ((𝛃).β X.obj).hom 0 := by
  rw [← cancel_mono (MonoidalPiSupercategory.ζR (R := R) X).hom]
  simp only [MonoidalPiSupercategory.β, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  ext
  · simp [MonoidalPiSupercategory.ζL, MonoidalPiSupercategory.ζR, ζ_eq]
  · simp [MonoidalPiSupercategory.ζL, MonoidalPiSupercategory.ζR, ζ_eq]
    have e : ((𝛃).β X.obj).hom ≫ (ρ_ (X.obj ⊗ 𝛑)).inv ≫ (α_ X.obj 𝛑 (𝟙_ D)).hom ≫
        (βL (R := R) X.obj (𝟙_ D)).inv ≫ (α_ 𝛑 X.obj (𝟙_ D)).inv ≫ (ρ_ (𝛑 ⊗ X.obj)).hom =
        ((𝛃).β X.obj).hom ≫ (ρ_ (X.obj ⊗ 𝛑)).inv ≫ ((𝛃).β X.obj).inv ▷ 𝟙_ D ≫
          (ρ_ (𝛑 ⊗ X.obj)).hom := by
      rw [βL_inv]; monoidal
    rw [e, ← rightUnitor_inv_naturality_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]

/-! ### `E ∘ D = I` -/

section EDI

/-- The identification `unit : A ⥤ E(D(A))`, `f ↦ (f, 0)`, is strictly monoidal. -/
def unitCoreMonoidal : (unit R D).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left f X' := Underlying.hom_ext (by ext <;> simp)
  μIso_hom_natural_right X' f := Underlying.hom_ext (by ext <;> simp)
  associativity X Y Z := Underlying.hom_ext (by ext <;> simp)
  left_unitality X := Underlying.hom_ext (by ext <;> simp)
  right_unitality X := Underlying.hom_ext (by ext <;> simp)

attribute [local instance] unitCoreMonoidal in
instance unitMonoidal : (unit R D).Monoidal := unitCoreMonoidal.toMonoidal

@[simp] theorem unit_ε : Functor.LaxMonoidal.ε (unit R D) = 𝟙 _ := rfl

@[simp] theorem unit_μ (X Y : D) : Functor.LaxMonoidal.μ (unit R D) X Y = 𝟙 _ := rfl

/-- **Brundan–Ellis, Theorem 1.15, `E ∘ D = I`.** The identification `A ⥤ E(D(A))` is a
(strict) monoidal Π-functor with `j = 1`: the monoidal Π-category underlying the monoidal
Π-supercategory `Â` has the same `π`, `β` and `ξ` as `A` (`β_hom_eq`, `ξ_hom_eq`). With `counit`
it is an isomorphism of categories (`unit_comp_counit`, `counit_comp_unit`). -/
def unitMonoidalPiFunctor : MonoidalPiFunctor R (unit R D) where
  j := Iso.refl _
  β_comm X := Underlying.hom_ext (by
    simp only [Iso.refl_hom, MonoidalCategory.id_whiskerRight, unit_μ, Category.id_comp,
      MonoidalCategory.whiskerLeft_id, Category.comp_id]
    exact (β_hom_eq (R := R) ⟨X⟩).symm)
  ξ_comm := Underlying.hom_ext (by
    simp only [Iso.refl_hom, unit_ε, Category.comp_id, unit_μ, Category.id_comp,
      MonoidalCategory.tensor_id]
    exact ξ_hom_eq (R := R))

end EDI

/-! ### `D` on monoidal Π-functors -/

section MapMonoidal

variable {E : Type w₃} [Category.{w₄} E] [Preadditive E] [Linear R E] [MonoidalCategory E]
  [MonoidalPreadditive E] [MonoidalLinear R E] [MonoidalPiCategory R E]
  {F : D ⥤ E} [F.Additive] [F.Linear R] [F.Monoidal] (hF : MonoidalPiFunctor R F)

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- **Brundan–Ellis, Theorem 1.15 (functor `D` on morphisms).** A monoidal Π-functor
`(F, c, i, j)` induces a monoidal superfunctor `F̂ : Â ⥤ B̂` (`F̂ = D₁(F, β_F)` with
`β_F = μ_{π,-} ∘ (j ⊗ 1)`), with coherence maps `c` and `i` viewed as even isomorphisms. -/
def mapMonoidal : MonoidalSuperfunctor R (map (hF.toPiFunctor R)) where
  μIso X Y := evenIso (Functor.Monoidal.μIso F X.obj Y.obj)
  εIso := evenIso (Functor.Monoidal.εIso F)
  μ_mem _ _ := mem_parity_zero.2 rfl
  ε_mem := mem_parity_zero.2 rfl
  μ_natural_left f X' := by
    ext
    · simp
    · simp only [comp_snd, whiskerRight_fst, whiskerRight_snd, map_map, homMk_fst, homMk_snd,
        evenIso_hom, Functor.Monoidal.μIso_hom, MonoidalPiCategory.pi_map, tensorLeft_map,
        Limits.comp_zero, zero_add, add_zero, Functor.map_comp, Category.assoc,
        MonoidalPiFunctor.toPiFunctor_β_inv_app, MonoidalCategory.comp_whiskerRight, tensorObj_obj,
        map_obj_obj, MonoidalPiCategory.pi_obj, Functor.map_zero, Limits.zero_comp]
      rw [← μ_natural_left_assoc, hF.βF_inv_whiskerRight]
  μ_natural_right X' f := by
    ext
    · simp
    · simp only [comp_snd, whiskerLeft_fst, whiskerLeft_snd, map_map, homMk_fst, homMk_snd,
        evenIso_hom, Functor.Monoidal.μIso_hom, MonoidalPiCategory.pi_map, tensorLeft_map,
        Limits.comp_zero, zero_add, add_zero, Functor.map_comp, Category.assoc,
        MonoidalPiFunctor.toPiFunctor_β_inv_app, MonoidalCategory.whiskerLeft_comp, tensorObj_obj,
        map_obj_obj, MonoidalPiCategory.pi_obj, Functor.map_zero, Limits.zero_comp]
      rw [← μ_natural_right_assoc, ← hF.βL_βF_inv]
  associativity X Y Z := by ext <;> simp
  left_unitality X := by ext <;> simp
  right_unitality X := by ext <;> simp

/-- **`E ∘ D = I` on morphisms.** The underlying functor of `F̂` is `F` (under the identifications
`unit`). -/
theorem unit_comp_map : unit R D ⋙ Underlying.map (map (hF.toPiFunctor R)) = F ⋙ unit R E :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => Underlying.hom_ext (by ext <;> simp)

/-- **`E ∘ D = I` on morphisms.** The coherence map `ĵ := (F̂ ζ_A)⁻¹ ∘ i ∘ ζ_B` of the monoidal
Π-functor underlying `F̂` is `j`, viewed as an even morphism. -/
theorem jIso_mapMonoidal_hom :
    (MonoidalSuperfunctor.jIso (mapMonoidal hF)).hom =
      homMk (X := (⟨MonoidalPiCategory.pi (R := R) (D := E)⟩ : Associated R E))
        (Y := ⟨F.obj (MonoidalPiCategory.pi (R := R) (D := D))⟩) hF.j.hom 0 := by
  ext
  · simp [MonoidalSuperfunctor.jIso, ζ_eq, mapMonoidal]
    simp only [MonoidalPiCategory.whiskerLeft_neg', Preadditive.neg_comp, Preadditive.comp_neg,
      neg_neg]
    have hin : ε F ≫ F.map (ξL (R := R) (𝟙_ D)).inv ≫
        F.map (α_ (MonoidalPiCategory.pi (R := R) (D := D)) (MonoidalPiCategory.pi (R := R))
          (𝟙_ D)).inv ≫ F.map (ρ_ (MonoidalPiCategory.pi (R := R) (D := D) ⊗
            MonoidalPiCategory.pi (R := R))).hom ≫
          (hF.βF (MonoidalPiCategory.pi (R := R) (D := D))).inv =
        (MonoidalPiCategory.ξ (R := R) (D := E)).inv ≫
          MonoidalPiCategory.pi (R := R) (D := E) ◁ hF.j.hom := by
      have e : F.map (ξL (R := R) (𝟙_ D)).inv ≫
          F.map (α_ (MonoidalPiCategory.pi (R := R) (D := D)) (MonoidalPiCategory.pi (R := R))
            (𝟙_ D)).inv ≫ F.map (ρ_ (MonoidalPiCategory.pi (R := R) (D := D) ⊗
              MonoidalPiCategory.pi (R := R))).hom =
          F.map (MonoidalPiCategory.ξ (R := R) (D := D)).inv := by
        rw [← F.map_comp, ← F.map_comp, MonoidalPiCategory.ξL_inv]
        congr 1
        monoidal
      rw [reassoc_of% e, ← cancel_epi (MonoidalPiCategory.ξ (R := R) (D := E)).hom,
        reassoc_of% hF.ξ_comm, Iso.hom_inv_id_assoc, MonoidalPiFunctor.βF_inv]
      simp [tensorHom_def']
    rw [hin, MonoidalCategory.whiskerLeft_comp_assoc, MonoidalPiCategory.ξL_naturality,
      MonoidalPiCategory.ξL_hom]
    have h8 := MonoidalPiCategory.ξ_whiskerRight_pi R (D := E)
    simp only [Category.assoc]
    rw [reassoc_of% h8]
    simp
  · simp [MonoidalSuperfunctor.jIso, ζ_eq, mapMonoidal]

end MapMonoidal

end Monoidal

/-! ## `D ∘ E ≅ I` for monoidal Π-supercategories -/

section TMon

variable {R : Type w} [CommRing R] {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A]
  [Supercategory R A] [MonoidalCategoryStruct A] [MonoidalSupercategory R A]
  [MonoidalPiSupercategory R A]

attribute [local instance] MonoidalPiCategory.toPiCategory

open MonoidalPiSupercategory

local notation "𝛑" => MonoidalPiSupercategory.pi (R := R) (C := A)

/-- `ξ_λ` of the underlying monoidal Π-category, in terms of `ζ`: `ξ_λ = -ζ_λ ∘ ζ_{π ⊗ λ}`. -/
theorem ξL_und_val (X : Underlying R A) :
    (MonoidalPiCategory.ξL (R := R) X).hom.1 =
      -((ζL (R := R) (𝛑 ⊗ X.obj)).hom ≫ (ζL (R := R) X.obj).hom) := by
  rw [MonoidalPiCategory.ξL_hom]
  change (α_ 𝛑 𝛑 X.obj).inv ≫ (MonoidalPiSupercategory.ξ (R := R) (C := A)).hom ▷ X.obj ≫
    (λ_ X.obj).hom = _
  rw [ξ_whiskerRight_leftUnitor, ← associator_ζL]
  simp

variable (R A) in
/-- **Brundan–Ellis, Theorem 1.15, `D ∘ E ≅ I`.** The superfunctor `T_A : (A̲)^ ⥤ A`,
`(f₀, f₁) ↦ f₀ + ζ_μ ∘ f₁` with `ζ_μ = l_μ ∘ (ζ ⊗ 1_μ)`. -/
@[simps]
def Tmon : Associated R (Underlying R A) ⥤ A where
  obj X := X.obj.obj
  map {X Y} f := f.1.1 + f.2.1 ≫ (ζL (R := R) Y.obj.obj).hom
  map_id X := by simp
  map_comp {X Y Z} f g := by
    have h1 := ζL_naturality (R := R) g.1.2
    have h2 := ζL_naturality (R := R) g.2.2
    rw [sign_zero, one_smul] at h1 h2
    simp only [comp_fst, comp_snd, Underlying.comp_val, Underlying.add_val, Underlying.sub_val,
      MonoidalPiCategory.pi_map, MonoidalPiCategory.ξApp_hom, ξL_und_val,
      Underlying.whiskerLeft_val, Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.sub_comp, Category.assoc]
    have h1' : (MonoidalPiCategory.pi (R := R) (D := Underlying R A)).obj ◁ g.1.1 ≫
        (ζL (R := R) Z.obj.obj).hom = (ζL (R := R) Y.obj.obj).hom ≫ g.1.1 := h1
    have h2' : (MonoidalPiCategory.pi (R := R) (D := Underlying R A)).obj ◁ g.2.1 ≫
        (ζL (R := R) (𝛑 ⊗ Z.obj.obj)).hom = (ζL (R := R) Y.obj.obj).hom ≫ g.2.1 := h2
    simp only [Preadditive.comp_neg, Preadditive.neg_comp]
    rw [reassoc_of% h2', h1', sub_eq_add_neg, neg_neg]
    abel

instance : (Tmon R A).Additive where
  map_add := by intros; simp [Preadditive.add_comp]; abel

instance : (Tmon R A).Linear R where
  map_smul _ _ := by simp [smul_add]

instance : IsSuperfunctor R (Tmon R A) where
  map_mem {X Y p f} hf := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [mem_parity_zero] at hf
      simp only [Tmon_map, hf, Underlying.zero_val, Limits.zero_comp, add_zero]
      exact f.1.2
    · rw [mem_parity_one] at hf
      simp only [Tmon_map, hf, Underlying.zero_val, zero_add]
      simpa using comp_mem f.2.2 (ζL_hom_mem (R := R) Y.obj.obj)

/-- `T_A` is injective on morphisms. -/
theorem Tmon_map_injective {X Y : Associated R (Underlying R A)} {f g : X ⟶ Y}
    (h : (Tmon R A).map f = (Tmon R A).map g) : f = g := by
  have hζ := ζL_hom_mem (R := R) Y.obj.obj
  have hf1 : f.2.1 ≫ (ζL (R := R) Y.obj.obj).hom ∈ parity (R := R) X.obj.obj Y.obj.obj 1 := by
    simpa using comp_mem f.2.2 hζ
  have hg1 : g.2.1 ≫ (ζL (R := R) Y.obj.obj).hom ∈ parity (R := R) X.obj.obj Y.obj.obj 1 := by
    simpa using comp_mem g.2.2 hζ
  have hf0 : f.1.1 ∈ parity (R := R) X.obj.obj Y.obj.obj (1 + 1) := f.1.2
  have hg0 : g.1.1 ∈ parity (R := R) X.obj.obj Y.obj.obj (1 + 1) := g.1.2
  have e0 : f.1.1 = g.1.1 := by
    rw [← proj_eq_of_add (R := R) (p := 0) rfl f.1.2 hf1,
      ← proj_eq_of_add (R := R) (p := 0) rfl g.1.2 hg1]
    exact congrArg (proj R 0) h
  have e1 : f.2.1 ≫ (ζL (R := R) Y.obj.obj).hom = g.2.1 ≫ (ζL (R := R) Y.obj.obj).hom := by
    rw [← proj_eq_of_add (R := R) (p := 1) (add_comm _ _) hf1 hf0,
      ← proj_eq_of_add (R := R) (p := 1) (add_comm _ _) hg1 hg0]
    exact congrArg (proj R 1) h
  exact hom_ext (Subtype.ext e0) (Subtype.ext ((cancel_mono _).1 e1))

variable (R A) in
/-- The inverse of `T_A`: `h ↦ (h₀, ζ_μ⁻¹ ∘ h₁)`. -/
@[simps obj]
def TmonInv : A ⥤ Associated R (Underlying R A) where
  obj X := ⟨⟨X⟩⟩
  map {X Y} h := (⟨proj R 0 h, proj_mem 0 h⟩, ⟨proj R 1 h ≫ (ζL (R := R) Y).inv,
    by simpa using comp_mem (proj_mem 1 h) (inv_mem _ (ζL_hom_mem (R := R) Y))⟩)
  map_id X := Tmon_map_injective (by simp [proj_id, show ¬((1 : ZMod 2) = 0) by decide])
  map_comp {X Y Z} f g := Tmon_map_injective (by
    rw [(Tmon R A).map_comp]
    simp only [Tmon_map, Category.assoc, Iso.inv_hom_id, Category.comp_id, proj_add_proj])

theorem Tmon_map_TmonInv_map {X Y : A} (h : X ⟶ Y) : (Tmon R A).map ((TmonInv R A).map h) = h := by
  simp [TmonInv, proj_add_proj]

/-- **Theorem 1.15, `D ∘ E ≅ I`:** `T_A` is an isomorphism of supercategories. -/
theorem TmonInv_comp_Tmon : TmonInv R A ⋙ Tmon R A = 𝟭 A :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by simpa using Tmon_map_TmonInv_map f

theorem Tmon_comp_TmonInv : Tmon R A ⋙ TmonInv R A = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by
    simpa using Tmon_map_injective (Tmon_map_TmonInv_map ((Tmon R A).map f))

/-- `T_A` carries `ζ` of `(A̲)^` to `ζ` of `A`. -/
theorem Tmon_map_ζ :
    (Tmon R A).map (MonoidalPiSupercategory.ζ (R := R) (C := Associated R (Underlying R A))).hom =
      (MonoidalPiSupercategory.ζ (R := R) (C := A)).hom := by
  simp only [Tmon_map, ζ_eq, ζUnit_hom_fst, ζUnit_hom_snd, Underlying.zero_val, zero_add]
  change (ρ_ 𝛑).inv ≫ (MonoidalPiSupercategory.ζ (R := R) (C := A)).hom ▷ 𝟙_ A ≫ (λ_ (𝟙_ A)).hom = _
  rw [MonoidalSupercategory.rightUnitor_inv_naturality_assoc R,
    MonoidalSupercategory.unitors_equal R, Iso.inv_hom_id, Category.comp_id]

theorem Tmon_map_whiskerRight {X Y : Associated R (Underlying R A)} (f : X ⟶ Y)
    (Z : Associated R (Underlying R A)) :
    (Tmon R A).map (f ▷ Z) = (Tmon R A).map f ▷ Z.obj.obj := by
  simp only [Tmon_map, whiskerRight_fst, whiskerRight_snd, Underlying.whiskerRight_val,
    Underlying.comp_val, Underlying.associator_hom_val, Category.assoc,
    MonoidalSupercategory.add_whiskerRight (R := R), MonoidalSupercategory.comp_whiskerRight (R := R)]
  erw [associator_ζL]

theorem Tmon_map_whiskerLeft (X : Associated R (Underlying R A))
    {Y Z : Associated R (Underlying R A)} (g : Y ⟶ Z) :
    (Tmon R A).map (X ◁ g) = X.obj.obj ◁ (Tmon R A).map g := by
  simp only [Tmon_map, whiskerLeft_fst, whiskerLeft_snd, Underlying.whiskerLeft_val,
    Underlying.comp_val, Category.assoc, MonoidalSupercategory.whiskerLeft_add (R := R),
    MonoidalSupercategory.whiskerLeft_comp (R := R)]
  congr 2
  have e : (MonoidalPiCategory.βL (R := R) X.obj Z.obj).inv.1 =
      (α_ X.obj.obj 𝛑 Z.obj.obj).inv ≫
        ((ζR (R := R) X.obj.obj).hom ≫ (ζL (R := R) X.obj.obj).inv) ▷ Z.obj.obj ≫
          (α_ 𝛑 X.obj.obj Z.obj.obj).hom := by
    simp [MonoidalPiCategory.βL_inv]
    rfl
  erw [e]
  simp only [Category.assoc, MonoidalSupercategory.comp_whiskerRight (R := R)]
  erw [associator_ζL]
  rw [← MonoidalSupercategory.comp_whiskerRight (R := R), Iso.inv_hom_id,
    MonoidalSupercategory.id_whiskerRight (R := R), Category.comp_id,
    ← cancel_epi (α_ X.obj.obj 𝛑 Z.obj.obj).hom, Iso.hom_inv_id_assoc]
  simp only [ζR, ζL, MonoidalSupercategory.comp_whiskerRight (R := R),
    MonoidalSupercategory.whiskerLeft_comp (R := R)]
  rw [← reassoc_of% (MonoidalSupercategory.associator_naturality_middle R X.obj.obj
    (MonoidalPiSupercategory.ζ (R := R) (C := A)).hom Z.obj.obj),
    MonoidalSupercategory.triangle (R := R)]

@[simp] theorem Tmon_map_homMk {X Y : Associated R (Underlying R A)} (f : X.obj ⟶ Y.obj) :
    (Tmon R A).map (homMk f 0) = f.1 := by
  simp [Tmon_map]

/-- **Theorem 1.15, `D ∘ E ≅ I`:** `T_A` is a strict monoidal superfunctor. -/
def TmonMonoidal : MonoidalSuperfunctor R (Tmon R A) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  μ_mem _ _ := id_mem _
  ε_mem := id_mem _
  μ_natural_left f X' := by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (Tmon_map_whiskerRight f X').symm
  μ_natural_right X' f := by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (Tmon_map_whiskerLeft X' f).symm
  associativity X Y Z := by
    simp [MonoidalSupercategory.id_whiskerRight (R := R),
      MonoidalSupercategory.whiskerLeft_id (R := R)]
  left_unitality X := by simp [MonoidalSupercategory.id_whiskerRight (R := R)]
  right_unitality X := by simp [MonoidalSupercategory.whiskerLeft_id (R := R)]

section Naturality

variable {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [MonoidalCategoryStruct B] [MonoidalSupercategory R B] [MonoidalPiSupercategory R B]
  {G : A ⥤ B} [G.Additive] [G.Linear R] [IsSuperfunctor R G] (hG : MonoidalSuperfunctor R G)

theorem βF_comp_map_ζL (Y : Underlying R A) :
    letI := (MonoidalSuperfunctor.underlyingCoreMonoidal hG).toMonoidal
    ((hG.toMonoidalPiFunctor).βF Y).hom.1 ≫ G.map (ζL (R := R) Y.obj).hom =
      (ζL (R := R) (G.obj Y.obj)).hom := by
  letI := (MonoidalSuperfunctor.underlyingCoreMonoidal hG).toMonoidal
  have e : ((hG.toMonoidalPiFunctor).βF Y).hom.1 = (MonoidalSuperfunctor.jIso hG).hom ▷ G.obj Y.obj ≫
      (hG.μIso (MonoidalPiSupercategory.pi (R := R) (C := A)) Y.obj).hom := rfl
  rw [e, ζL, G.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% (hG.μ_natural_left _ Y.obj), ← Category.assoc,
    ← MonoidalSupercategory.comp_whiskerRight (R := R),
    MonoidalSuperfunctor.jIso_hom_comp_map_ζ, MonoidalSupercategory.comp_whiskerRight (R := R),
    Category.assoc, ← hG.left_unitality]
  rfl

/-- **Theorem 1.15, naturality of `T`:** `T_B ∘ (G̲)^ = G ∘ T_A` for a monoidal superfunctor `G`
between monoidal Π-supercategories. -/
theorem Tmon_naturality :
    letI := (MonoidalSuperfunctor.underlyingCoreMonoidal hG).toMonoidal
    map ((hG.toMonoidalPiFunctor).toPiFunctor R) ⋙ Tmon R B = Tmon R A ⋙ G := by
  letI := (MonoidalSuperfunctor.underlyingCoreMonoidal hG).toMonoidal
  have h2 : ∀ Y : Underlying R A, ((hG.toMonoidalPiFunctor).βF Y).inv.1 ≫ (ζL (R := R) (G.obj Y.obj)).hom =
      G.map (ζL (R := R) Y.obj).hom := fun Y => by
    rw [← βF_comp_map_ζL hG Y, ← Category.assoc, ← Underlying.comp_val, Iso.inv_hom_id]
    exact Category.id_comp _
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => ?_
  simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
  change G.map f.1.1 + (G.map f.2.1 ≫ ((hG.toMonoidalPiFunctor).βF Y.obj).inv.1) ≫
    (ζL (R := R) (G.obj Y.obj.obj)).hom = G.map (f.1.1 + f.2.1 ≫ (ζL (R := R) Y.obj.obj).hom)
  rw [G.map_add, G.map_comp, Category.assoc, h2 Y.obj]

end Naturality

end TMon

end Associated

end StringDiagrams

end
