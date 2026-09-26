import StringDiagrams.Super.TwoEnvelopeUniversal

/-!
# Π-2-supercategories and the Π-envelope

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definitions 3.1 and 4.4 and Lemma 4.7.

* `TwoEnvelope.instPiTwoSupercategory`: the Π-envelope `𝔄_π` of a 2-supercategory is a
  Π-2-supercategory with `π_λ = Π¹ 1_λ` and `ζ_λ = (1_{1_λ})_1^0` (Definition 4.4).
* `PiTwoSupercategory.homPi`: in a Π-2-supercategory `(𝔅, π, ζ)` each morphism supercategory
  `ℋom(λ, μ)` is a Π-supercategory with `Π = π_μ -` (in the diagrammatic order `F ↦ F ≫ π_μ`)
  and `ζ_F = ζ_μ F` (`F ◁ ζ_μ ≫ ρ_F`), as in Section 3 of the paper.
* `TwoEnvelope.extendPi`: **Lemma 4.7(i)** for a Π-2-supercategory `𝔅`, the extension
  `ℝ̃ : 𝔄_π → 𝔅` of `TwoEnvelope.extend` with these Π-structures; Lemma 4.7(ii) and
  Theorem 4.9 then apply verbatim (`TwoEnvelope.extendTwoNatTrans`, ...).
* The coherence map `c̃` of Lemma 4.7(i) is defined in `TwoEnvelope.extendComp` as
  `(-1)^{ab} (ζ^{a+b})⁻¹ ∘ c ∘ (ζᵇ ζᵃ)`. For a Π-2-supercategory it agrees with the paper's
  `c̃_{ΠᵇG, ΠᵃF} = m_{b,a} c_{G,F} ∘ π^b (β^a)⁻¹_{ℝG} (ℝF)`, where `m_{b,a}` is the identity
  unless `a = b = 1` and `m_{1,1} = -ξ`, in all four cases, the associators and unitors of the
  non-strict setting inserted: `TwoEnvelope.extendComp_J` (`a = b = 0`),
  `TwoEnvelope.extendComp_zero_one`, `TwoEnvelope.extendComp_one_zero` (through `β`) and
  `TwoEnvelope.extendComp_one_one` (through `β` and `-ξ`). In particular the printed sign
  `m_{1,1} = -ξ` is correct.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

/-! ## The Π-envelope is a Π-2-supercategory -/

namespace TwoEnvelope

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- **Definition 4.4.** The Π-envelope is a Π-2-supercategory with `π_λ = Π¹ 1_λ` and
`ζ_λ = (1_{1_λ})_1^0`. -/
instance instPiTwoSupercategory : PiTwoSupercategory R (TwoEnvelope R B) where
  pi a := π R a
  ζ a := ζ R a
  ζ_hom_mem a := ζ_hom_mem a

end TwoEnvelope

/-! ## The Π-supercategories `ℋom(λ, μ)` of a Π-2-supercategory -/

namespace PiTwoSupercategory

variable {R : Type w} [CommRing R]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C] [PiTwoSupercategory R C]

/-- The odd 2-isomorphism `ζ_μ F : π_μ F ≅ F`, i.e. `F ≫ π_μ ≅ F`. -/
def ζHom {a b : C} (f : a ⟶ b) : f ≫ pi (R := R) b ≅ f :=
  whiskerLeftIso (R := R) f (ζ (R := R) b) ≪≫ rightUnitor f

theorem ζHom_hom {a b : C} (f : a ⟶ b) :
    (ζHom (R := R) f).hom = f ◁ (ζ (R := R) b).hom ≫ (rightUnitor f).hom := rfl

theorem ζHom_inv {a b : C} (f : a ⟶ b) :
    (ζHom (R := R) f).inv = (rightUnitor f).inv ≫ f ◁ (ζ (R := R) b).inv := rfl

theorem ζHom_hom_mem {a b : C} (f : a ⟶ b) :
    (ζHom (R := R) f).hom ∈ parity (R := R) (f ≫ pi (R := R) b) f 1 := by
  have := comp_mem (whiskerLeft_mem f (ζ_hom_mem (R := R) b)) (rightUnitor_hom_mem (R := R) f)
  simpa using this

variable (R C) in
/-- In a Π-2-supercategory each morphism supercategory `ℋom(λ, μ)` is a Π-supercategory with
`Π = π_μ -` and `ζ_F = ζ_μ F` (Section 3). -/
def homPi (a b : C) : PiSupercategory R (a ⟶ b) :=
  PiSupercategory.ofIso (fun f => f ≫ pi (R := R) b) (fun f => ζHom (R := R) f) ζHom_hom_mem

/-- The identity behind the formula for `c̃` in the case `a = b = 1`: for `G : μ → ν`,
`ζ_μ ▷ (G ≫ π_ν) ≫ λ ≫ G ◁ ζ_ν ≫ ρ = α⁻¹ ≫ (β_G)⁻¹ ▷ π_ν ≫ α ≫ G ◁ ξ_ν ≫ ρ`. -/
theorem ζ_ζ_eq_β_ξ {b c : C} (g : b ⟶ c) :
    (ζ (R := R) b).hom ▷ (g ≫ pi (R := R) c) ≫ (leftUnitor _).hom ≫ g ◁ (ζ (R := R) c).hom ≫
        (rightUnitor g).hom =
      (associator _ g _).inv ≫ (β (R := R) g).inv ▷ pi (R := R) c ≫ (associator g _ _).hom ≫
        g ◁ (ξ (R := R) c).hom ≫ (rightUnitor g).hom := by
  rw [β_inv, ξ_hom]
  simp only [comp_whiskerRight (R := R), whiskerLeft_comp (R := R), Category.assoc]
  rw [associator_naturality_middle_assoc R, TwoEnvelope.whiskerLeft_comp_comp R,
    TwoEnvelope.inv_hom_whiskerRight' R, whiskerLeft_id (R := R), Category.id_comp,
    reassoc_of% (TwoSupercategory.triangle (R := R) g (pi (R := R) c)),
    TwoEnvelope.inv_hom_whiskerRight'_assoc R, ← associator_inv_naturality_left_assoc R,
    ← Category.assoc (associator _ _ _).inv, ← leftUnitor_comp R]

end PiTwoSupercategory

/-! ## Lemma 4.7(i) for Π-2-supercategories -/

namespace TwoEnvelope

open PiTwoSupercategory

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C] [PiTwoSupercategory R C]

/-- **Lemma 4.7(i)** for a Π-2-supercategory `(𝔅, π, ζ)`: the extension `ℝ̃ : 𝔄_π → 𝔅` of a
2-superfunctor `ℝ : 𝔄 → 𝔅`, with `ℝ̃(ΠᵃF) = π_{ℝμ}ᵃ (ℝF)`. -/
def extendPi (F : TwoSuperfunctor R B C) : TwoSuperfunctor R (TwoEnvelope R B) C :=
  letI := homPi R C
  extend F

/-- The 1-morphism `Π¹F` of `𝔄_π`. -/
def Pm {a b : B} (f : a ⟶ b) : (⟨a⟩ : TwoEnvelope R B) ⟶ ⟨b⟩ := Envelope.mk 1 f

omit [TwoSupercategory R B] in
/-- **Lemma 4.7(i)**, the coherence map `c̃` in the case `a = b = 1`: it is the paper's
`m_{1,1} c_{G,F} ∘ π_ν (β_{ℝG})⁻¹ (ℝF)` with `m_{1,1} = -ξ_ν`, i.e. the composite
`(ℝF π)(ℝG π) ≅ ℝF (π (ℝG π)) → ℝF ((ℝG π) π) ≅ (ℝF ℝG)(π π) → ℝ(FG)(π π) → ℝ(FG)`
of the associators, `ℝF ◁ (β_{ℝG})⁻¹ ▷ π`, `c ▷ ππ`, `ℝ(FG) ◁ (-ξ)` and the unitor. -/
theorem extendComp_one_one (F : TwoSuperfunctor R B C) {a b c : B} (f₀ : a ⟶ b)
    (g₀ : b ⟶ c) :
    letI := homPi R C
    (extendComp F (Pm (R := R) f₀) (Pm g₀)).hom =
      (associator (F.map f₀) (pi (R := R) (F.obj b)) (F.map g₀ ≫ pi (R := R) (F.obj c))).hom ≫
        F.map f₀ ◁ (associator (pi (R := R) (F.obj b)) (F.map g₀) (pi (R := R) (F.obj c))).inv ≫
        F.map f₀ ◁ ((β (R := R) (F.map g₀)).inv ▷ pi (R := R) (F.obj c)) ≫
        F.map f₀ ◁ (associator (F.map g₀) (pi (R := R) (F.obj c)) (pi (R := R) (F.obj c))).hom ≫
        (associator (F.map f₀) (F.map g₀) (pi (R := R) (F.obj c) ≫ pi (R := R) (F.obj c))).inv ≫
        (F.mapComp f₀ g₀).hom ▷ (pi (R := R) (F.obj c) ≫ pi (R := R) (F.obj c)) ≫
        F.map (f₀ ≫ g₀) ◁ (-(ξ (R := R) (F.obj c)).hom) ≫ (rightUnitor (F.map (f₀ ≫ g₀))).hom := by
  letI := homPi R C
  show sign R (1 * 1) • ((ζHom (R := R) (F.map f₀)).hom ▷ (F.map g₀ ≫ pi (R := R) (F.obj c)) ≫
    F.map f₀ ◁ (ζHom (R := R) (F.map g₀)).hom ≫ (F.mapComp f₀ g₀).hom ≫ 𝟙 _) = _
  have key := ζ_ζ_eq_β_ξ (R := R) (F.map g₀)
  rw [mul_one, sign_one, neg_one_smul, Category.comp_id, ζHom_hom, ζHom_hom,
    comp_whiskerRight (R := R), whisker_assoc (R := R),
    ← TwoSupercategory.triangle (R := R), whiskerLeft_neg R, Preadditive.neg_comp,
    Preadditive.comp_neg, Preadditive.comp_neg, Preadditive.comp_neg, Preadditive.comp_neg,
    Preadditive.comp_neg, Preadditive.comp_neg]
  congr 1
  have key' := congrArg (fun t => F.map f₀ ◁ t) key
  simp only [whiskerLeft_comp (R := R)] at key'
  simp only [Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp (R := R)]
  rw [reassoc_of% key']
  rw [reassoc_of% (TwoEnvelope.interchange_even_left R (F.mapComp_hom_mem f₀ g₀) _),
    rightUnitor_naturality R, ← associator_inv_naturality_right_assoc R,
    ← Category.assoc (associator _ _ _).inv, ← whiskerLeft_rightUnitor R]

omit [TwoSupercategory R B] in
/-- **Lemma 4.7(i)**, the coherence map `c̃` in the case `a = 1`, `b = 0`: it is the paper's
`c_{G,F} π_ν ∘ (β_{ℝG})⁻¹ (ℝF)` (`m_{0,1}` is the identity), i.e.
`(ℝF π) ℝG ≅ ℝF (π ℝG) → ℝF (ℝG π) ≅ (ℝF ℝG) π → ℝ(FG) π`. -/
theorem extendComp_one_zero (F : TwoSuperfunctor R B C) {a b c : B} (f₀ : a ⟶ b)
    (g₀ : b ⟶ c) :
    letI := homPi R C
    (extendComp F (Pm (R := R) f₀) (Jm g₀)).hom =
      (associator (F.map f₀) (pi (R := R) (F.obj b)) (F.map g₀)).hom ≫
        F.map f₀ ◁ (β (R := R) (F.map g₀)).inv ≫
        (associator (F.map f₀) (F.map g₀) (pi (R := R) (F.obj c))).inv ≫
        (F.mapComp f₀ g₀).hom ▷ pi (R := R) (F.obj c) := by
  letI := homPi R C
  show sign R (1 * 0) • ((ζHom (R := R) (F.map f₀)).hom ▷ F.map g₀ ≫
    F.map f₀ ◁ 𝟙 (F.map g₀) ≫ (F.mapComp f₀ g₀).hom ≫ (ζHom (R := R) (F.map (f₀ ≫ g₀))).inv) = _
  rw [mul_zero, sign_zero, one_smul, whiskerLeft_id (R := R), Category.id_comp, ζHom_hom,
    ζHom_inv, comp_whiskerRight (R := R), whisker_assoc (R := R),
    ← TwoSupercategory.triangle (R := R), β_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp (R := R)]
  congr 3
  rw [associator_inv_naturality_right_assoc R,
    ← TwoEnvelope.interchange_even_left R (F.mapComp_hom_mem f₀ g₀),
    rightUnitor_inv_naturality_assoc R, rightUnitor_comp_inv R, Category.assoc]

omit [TwoSupercategory R B] in
/-- **Lemma 4.7(i)**, the coherence map `c̃` in the case `a = 0`, `b = 1`: it is the paper's
`c_{G,F} π_ν` (`β⁰` and `m_{1,0}` are identities), i.e.
`ℝF (ℝG π) ≅ (ℝF ℝG) π → ℝ(FG) π`. -/
theorem extendComp_zero_one (F : TwoSuperfunctor R B C) {a b c : B} (f₀ : a ⟶ b)
    (g₀ : b ⟶ c) :
    letI := homPi R C
    (extendComp F (Jm (R := R) f₀) (Pm g₀)).hom =
      (associator (F.map f₀) (F.map g₀) (pi (R := R) (F.obj c))).inv ≫
        (F.mapComp f₀ g₀).hom ▷ pi (R := R) (F.obj c) := by
  letI := homPi R C
  show sign R (0 * 1) • (𝟙 (F.map f₀) ▷ (F.map g₀ ≫ pi (R := R) (F.obj c)) ≫
    F.map f₀ ◁ (ζHom (R := R) (F.map g₀)).hom ≫ (F.mapComp f₀ g₀).hom ≫
      (ζHom (R := R) (F.map (f₀ ≫ g₀))).inv) = _
  rw [zero_mul, sign_zero, one_smul, id_whiskerRight (R := R), Category.id_comp, ζHom_hom,
    ζHom_inv, whiskerLeft_comp (R := R), whiskerLeft_rightUnitor R]
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc R, ← rightUnitor_naturality_assoc R,
    Iso.hom_inv_id_assoc,
    ← reassoc_of% (TwoEnvelope.interchange_even_left R (F.mapComp_hom_mem f₀ g₀) _),
    whiskerLeft_hom_inv' R, Category.comp_id]

end TwoEnvelope

end StringDiagrams

end
