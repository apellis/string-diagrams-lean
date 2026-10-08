import StringDiagrams.Super.DrinfeldCenterPi
import StringDiagrams.Super.TwoEnvelopePi
import StringDiagrams.Super.Superalgebra

/-!
# Remark 5.7: the Drinfeld center of `𝔄̲` is in general larger than that of `𝔄`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Remark 5.7,
whose last sentence asserts that the monoidal category underlying the Drinfeld center of a
Π-2-supercategory `𝔄` is monoidally equivalent to the Drinfeld center of `𝔄̲`. The corrected
statement, with the Π-center of `𝔄̲`, is `DrinfeldCenter.centerEquivalence`
(`StringDiagrams.Super.DrinfeldCenterPi`). Here we show that the comparison with the full
Drinfeld center of `𝔄̲` is not essentially surjective in general.

* `UnitTwo R`: the unit 2-supercategory (one object, one 1-morphism, 2-morphisms `R`, all even).
* `TwoNatTrans.naturality_of_iso`: a transformation of the identity of `𝔄̲` isomorphic to
  `𝔼₂` of a 2-natural transformation of `𝔄` is natural with respect to all 2-morphisms of `𝔄`
  (the components of a modification are even, so they supercommute with odd 2-morphisms).
* `TwoEnvelope.parityTwist`: for `B` without odd 2-morphisms and `𝔄 = B_π`, the strong
  transformation of the identity of `𝔄̲` with components `1_λ` and naturality 2-morphisms
  `(-1)^{|F|}` (on 1-morphisms `F = Π^{|F|} F₀`); it is natural for even 2-morphisms because
  there are none between 1-morphisms of different parity.
* `TwoEnvelope.parityTwist_not_iso`: if `2 • 1_{1_a} ≠ 0`, it is not isomorphic to `𝔼₂ θ` for any
  2-natural `θ : 𝕀 ⇒ 𝕀` of `𝔄` (naturality with respect to `ζ_a : π_a ⇒ 1_a` would give
  `z = -z` for an isomorphism `z`); hence `TwoEnvelope.parityTwistObj_not_mem_essImage`,
  `TwoEnvelope.parityTwist_not_isPiTwoNatural`, and for `𝔄 = I_π` over `ℤ`:
  `remark57_toCenter2_not_essSurj`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory
open scoped Oplax.OplaxTrans Oplax.OplaxTrans.OplaxFunctor

universe w

/-! ## The unit 2-supercategory -/

/-- The single object of the unit 2-supercategory. -/
inductive UnitTwo (R : Type w) : Type
  | pt

namespace UnitTwo

/-- The single 1-morphism of the unit 2-supercategory. -/
structure Hom1 (R : Type w) : Type where

variable (R : Type w) [CommRing R]

/-- The 2-morphisms of the unit 2-supercategory: the elements of `R`. -/
instance : Category (Hom1 R) where
  Hom _ _ := R
  id _ := (1 : R)
  comp a b := (a * b : R)
  id_comp a := one_mul (a : R)
  comp_id a := mul_one (a : R)
  assoc a b c := mul_assoc (a : R) b c

theorem comp_def {f g h : Hom1 R} (a : f ⟶ g) (b : g ⟶ h) : a ≫ b = (a * b : R) := rfl

theorem id_def (f : Hom1 R) : 𝟙 f = (1 : R) := rfl

instance : Preadditive (Hom1 R) where
  homGroup _ _ := inferInstanceAs (AddCommGroup R)
  add_comp _ _ _ a a' b := add_mul (a : R) a' b
  comp_add _ _ _ a b b' := mul_add (a : R) b b'

instance : Linear R (Hom1 R) where
  homModule _ _ := inferInstanceAs (Module R R)
  smul_comp _ _ _ r a b := smul_mul_assoc r (a : R) b
  comp_smul _ _ _ a r b := mul_smul_comm r (a : R) b

instance : Supercategory R (Hom1 R) where
  parity _ _ p := trivialGrading R p
  isInternal _ _ := isInternal_trivialGrading
  id_mem _ := by simp
  comp_mem {_ _ _ p q a b} ha hb := SetLike.GradedMul.mul_mem (A := trivialGrading R) ha hb

theorem mem_parity_one {f g : Hom1 R} {a : f ⟶ g} (h : a ∈ parity (R := R) f g 1) : a = 0 := by
  change a ∈ trivialGrading R 1 at h
  simpa using h

/-- The bicategory data: one object, one 1-morphism, 2-morphisms `R`, whiskering the identity. -/
instance : BicategoryStruct (UnitTwo R) where
  Hom _ _ := Hom1 R
  id _ := ⟨⟩
  comp _ _ := ⟨⟩
  homCategory _ _ := inferInstanceAs (Category (Hom1 R))
  whiskerLeft _ _ _ η := η
  whiskerRight η _ := η
  associator _ _ _ := Iso.refl _
  leftUnitor _ := Iso.refl _
  rightUnitor _ := Iso.refl _

instance (a b : UnitTwo R) : Preadditive (a ⟶ b) := inferInstanceAs (Preadditive (Hom1 R))

instance (a b : UnitTwo R) : Linear R (a ⟶ b) := inferInstanceAs (Linear R (Hom1 R))

instance (a b : UnitTwo R) : Supercategory R (a ⟶ b) := inferInstanceAs (Supercategory R (Hom1 R))

/-- **The unit 2-supercategory** (one object, one 1-morphism, endomorphisms `R` in even
parity). -/
instance : TwoSupercategory R (UnitTwo R) where
  whiskerLeft_id _ _ := rfl
  whiskerLeft_comp _ _ _ _ _ _ := rfl
  id_whiskerLeft η := ((one_mul _).trans (mul_one (η : R))).symm
  comp_whiskerLeft _ _ _ _ η := ((one_mul _).trans (mul_one (η : R))).symm
  id_whiskerRight _ _ := rfl
  comp_whiskerRight _ _ _ := rfl
  whiskerRight_id η := ((one_mul _).trans (mul_one (η : R))).symm
  whiskerRight_comp η _ _ := ((one_mul _).trans (mul_one (η : R))).symm
  whisker_assoc _ _ _ η _ := ((one_mul _).trans (mul_one (η : R))).symm
  pentagon _ _ _ _ := show ((1 : R) * ((1 : R) * 1) = 1 * 1) by simp
  triangle _ _ := show ((1 : R) * 1 = 1) by simp
  whiskerLeft_add _ _ _ _ _ := rfl
  add_whiskerRight _ _ _ := rfl
  whiskerLeft_smul _ _ _ _ _ := rfl
  smul_whiskerRight _ _ _ := rfl
  whiskerLeft_mem _ := id
  whiskerRight_mem _ := id
  super_interchange {_ _ _ _ _ _ _ p q η θ} hη hθ := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [koszulSign_zero_left, one_smul]
      exact mul_comm (η : R) θ
    · rcases parity_eq_zero_or_one q with rfl | rfl
      · rw [koszulSign_zero_right, one_smul]
        exact mul_comm (η : R) θ
      · rw [mem_parity_one R hη]
        change (0 * θ : R) = koszulSign 1 1 • (θ * 0 : R)
        simp
  associator_hom_mem _ _ _ := by simp [parity]
  leftUnitor_hom_mem _ := by simp [parity]
  rightUnitor_hom_mem _ := by simp [parity]

theorem noOdd : TwoSupercategory.NoOdd R (UnitTwo R) := fun _ _ _ _ => trivialGrading_one

end UnitTwo

/-! ## Isomorphism invariance of naturality with respect to all 2-morphisms -/

namespace TwoNatTrans

open BicategoryStruct TwoSupercategory
open scoped Oplax.OplaxTrans Oplax.OplaxTrans.OplaxFunctor

variable {R : Type w} [CommRing R] {A : Type*} [BicategoryStruct A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A]

include R in
private theorem solve_aux {c d : A} (h : c ⟶ d) {Xc Yc : c ⟶ c} {Xd Yd : d ⟶ d}
    (Γc : Xc ⟶ Yc) (Γd : Xd ⟶ Yd) (Δd : Yd ⟶ Xd) (hΔΓ : Δd ≫ Γd = 𝟙 Yd)
    (yh : h ≫ Yd ⟶ Yc ≫ h) (xh : h ≫ Xd ⟶ Xc ≫ h) (hm : h ◁ Γd ≫ yh = xh ≫ Γc ▷ h) :
    yh = h ◁ Δd ≫ xh ≫ Γc ▷ h := by
  rw [← hm, ← Category.assoc, ← whiskerLeft_comp (R := R), hΔΓ, whiskerLeft_id (R := R),
    Category.id_comp]

private theorem exchange_aux {a b : A} {f g : a ⟶ b} (ε : f ⟶ g) {Xa Ya : a ⟶ a}
    {Xb Yb : b ⟶ b} (Γa : Xa ⟶ Ya) (Δb : Yb ⟶ Xb) (hΓa : Γa ∈ parity (R := R) Xa Ya 0)
    (hΔb : Δb ∈ parity (R := R) Yb Xb 0) (xf : f ≫ Xb ⟶ Xa ≫ f) (xg : g ≫ Xb ⟶ Xa ≫ g)
    (hθ : ε ▷ Xb ≫ xg = xf ≫ Xa ◁ ε) :
    ε ▷ Yb ≫ g ◁ Δb ≫ xg ≫ Γa ▷ g = (f ◁ Δb ≫ xf ≫ Γa ▷ f) ≫ Ya ◁ ε := by
  rw [← Category.assoc, whisker_exchange_of_even_right (R := R) ε hΔb, Category.assoc,
    ← Category.assoc (ε ▷ Xb), hθ, Category.assoc, ← whisker_exchange_of_even_left (R := R) hΓa ε]
  simp only [Category.assoc]

/-- If an oplax transformation `η` of the identity of `𝔄̲` is isomorphic (by a modification,
whose components are even) to `𝔼₂` of a 2-natural transformation `θ : 𝕀 ⇒ 𝕀` of `𝔄`, then `η`
is natural with respect to all 2-morphisms of `𝔄`, not only the even ones. -/
theorem naturality_of_iso (θ : EndId R A) (η : idU R A ⟶ idU R A) (e : θ.toOplax ≅ η)
    {a b : A} {f g : a ⟶ b} (ε : f ⟶ g) :
    ε ▷ (η.app ⟨b⟩).obj ≫ (η.naturality (Underlying2.hom1 (R := R) g)).1 =
      (η.naturality (Underlying2.hom1 (R := R) f)).1 ≫ (η.app ⟨a⟩).obj ◁ ε := by
  have hΔΓ : ∀ c : A, (e.inv.as.app ⟨c⟩).1 ≫ (e.hom.as.app ⟨c⟩).1 = 𝟙 _ := fun c =>
    congrArg (fun k => (k.as.app ⟨c⟩).1) e.inv_hom_id
  have key : ∀ {c d : A} (h : c ⟶ d), (η.naturality (Underlying2.hom1 (R := R) h)).1 =
      h ◁ (e.inv.as.app ⟨d⟩).1 ≫ θ.x h ≫ (e.hom.as.app ⟨c⟩).1 ▷ h := fun {c d} h =>
    solve_aux (R := R) h (e.hom.as.app ⟨c⟩).1 (e.hom.as.app ⟨d⟩).1 (e.inv.as.app ⟨d⟩).1 (hΔΓ d)
      _ (θ.x h) (congrArg Subtype.val (e.hom.as.naturality (Underlying2.hom1 (R := R) h)))
  rw [key, key]
  exact exchange_aux (R := R) ε (e.hom.as.app ⟨a⟩).1 (e.inv.as.app ⟨b⟩).1
    (e.hom.as.app ⟨a⟩).2 (e.inv.as.app ⟨b⟩).2 (θ.x f) (θ.x g) (θ.naturality ε)

end TwoNatTrans

/-! ## The parity twist on the Π-envelope of an even 2-supercategory -/

namespace TwoEnvelope

open Bicategory
open scoped Oplax.OplaxTrans Oplax.OplaxTrans.OplaxFunctor

variable {R : Type w} [CommRing R] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- In the Π-envelope of a 2-supercategory without odd 2-morphisms, an even 2-morphism between
1-morphisms of different parity is zero. -/
theorem eq_zero_of_par_ne (hB : TwoSupercategory.NoOdd R B) {a b : Underlying2 R (TwoEnvelope R B)}
    {f g : a ⟶ b} (ε : f ⟶ g) (h : f.obj.par ≠ g.obj.par) : ε = 0 := by
  have hm : Envelope.toHom ε.1 ∈ parity (R := R) f.obj.obj g.obj.obj (0 + (f.obj.par + g.obj.par)) :=
    Envelope.mem_parity_iff.1 ε.2
  have h1 : (0 : ZMod 2) + (f.obj.par + g.obj.par) = 1 := by
    rcases parity_eq_zero_or_one f.obj.par with h0 | h0 <;>
      rcases parity_eq_zero_or_one g.obj.par with h0' | h0' <;> simp_all
  rw [h1, hB] at hm
  exact Subtype.ext ((Submodule.mem_bot R).1 hm)

variable (R B) in
/-- The parity twist: the transformation of the identity of `𝔄̲ = (𝔄_π)̲` with components `1_λ`
and naturality 2-morphisms `(-1)^{|F|} (ρ_F ∘ λ_F⁻¹)`, where `|F|` is the parity of the
1-morphism `F = Π^{|F|} F₀` of the Π-envelope. It is natural with respect to the even
2-morphisms when `𝔄` has no odd 2-morphisms. -/
def parityTwist (hB : TwoSupercategory.NoOdd R B) :
    OplaxFunctor.id (Underlying2 R (TwoEnvelope R B)) ⟶
      OplaxFunctor.id (Underlying2 R (TwoEnvelope R B)) where
  app a := (Oplax.OplaxTrans.id (OplaxFunctor.id (Underlying2 R (TwoEnvelope R B)))).app a
  naturality f := sign R f.obj.par • (Oplax.OplaxTrans.id (OplaxFunctor.id (Underlying2 R (TwoEnvelope R B)))).naturality f
  naturality_naturality {a b f g} ε := by
    by_cases h : f.obj.par = g.obj.par
    · rw [h, Linear.comp_smul, Linear.smul_comp,
        (Oplax.OplaxTrans.id (OplaxFunctor.id (Underlying2 R (TwoEnvelope R B)))).naturality_naturality ε]
    · rw [eq_zero_of_par_ne hB ε h]
      have h0 : (OplaxFunctor.id (Underlying2 R (TwoEnvelope R B))).map₂ (0 : f ⟶ g) = 0 := rfl
      rw [h0, PreadditiveBicategory.whiskerLeft_zero, PreadditiveBicategory.zero_whiskerRight,
        Limits.comp_zero, Limits.zero_comp]
  naturality_id a := by
    rw [show (𝟙 a : a ⟶ a).obj.par = 0 from rfl, sign_zero, one_smul]
    exact (Oplax.OplaxTrans.id (OplaxFunctor.id (Underlying2 R (TwoEnvelope R B)))).naturality_id a
  naturality_comp {a b c} f g := by
    rw [show (f ≫ g).obj.par = f.obj.par + g.obj.par from rfl, sign_add]
    simp only [Linear.smul_comp, Linear.comp_smul, LinearBicategory.whiskerLeft_smul,
      LinearBicategory.smul_whiskerRight, smul_smul]
    congr 1
    exact (Oplax.OplaxTrans.id (OplaxFunctor.id (Underlying2 R (TwoEnvelope R B)))).naturality_comp f g

theorem parityTwist_app (hB : TwoSupercategory.NoOdd R B) (a : Underlying2 R (TwoEnvelope R B)) :
    ((parityTwist R B hB).app a).obj = 𝟙 a.obj := rfl

theorem parityTwist_naturality (hB : TwoSupercategory.NoOdd R B)
    {a b : Underlying2 R (TwoEnvelope R B)} (f : a ⟶ b) :
    ((parityTwist R B hB).naturality f).1 =
      sign R f.obj.par • ((BicategoryStruct.rightUnitor f.obj).hom ≫
        (BicategoryStruct.leftUnitor f.obj).inv) := rfl

/-- The parity twist is a strong transformation (an object of the Drinfeld center of `𝔄̲`). -/
theorem parityTwist_isStrong (hB : TwoSupercategory.NoOdd R B) :
    IsStrongOplax (parityTwist R B hB) := fun {a b} f => by
  let n := (Oplax.OplaxTrans.id (OplaxFunctor.id (Underlying2 R (TwoEnvelope R B)))).naturality f
  have : IsIso n := by
    change IsIso ((Bicategory.rightUnitor f).hom ≫ (Bicategory.leftUnitor f).inv)
    infer_instance
  refine ⟨⟨sign R f.obj.par • inv n, ?_, ?_⟩⟩
  · change (sign R f.obj.par • n) ≫ (sign R f.obj.par • inv n) = 𝟙 _
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_mul_self, one_smul, IsIso.hom_inv_id]
  · change (sign R f.obj.par • inv n) ≫ (sign R f.obj.par • n) = 𝟙 _
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_mul_self, one_smul, IsIso.inv_hom_id]

open TwoSupercategory in
/-- **The parity twist is not isomorphic to `𝔼₂` of a 2-natural transformation of `𝕀`.** If
`2 • 1_{1_a} ≠ 0` in `B`, then no 2-natural transformation `θ : 𝕀 ⇒ 𝕀` of `𝔄 = B_π` has
`𝔼₂ θ` isomorphic to the parity twist: an isomorphic transformation would be natural with
respect to the odd 2-morphism `ζ_a : π_a ⇒ 1_a` (`TwoNatTrans.naturality_of_iso`), which forces
`2 • 1 = 0`. -/
theorem parityTwist_not_iso (hB : TwoSupercategory.NoOdd R B) (a : B)
    (h2 : (2 : R) • 𝟙 (𝟙 a) ≠ 0) (θ : TwoNatTrans.EndId R (TwoEnvelope R B)) :
    IsEmpty (θ.toOplax ≅ parityTwist R B hB) := ⟨fun e => by
  let A : TwoEnvelope R B := ⟨a⟩
  have h := TwoNatTrans.naturality_of_iso θ _ e (a := A) (b := A)
    (f := PiTwoSupercategory.pi (R := R) A) (g := 𝟙 A) (PiTwoSupercategory.ζ (R := R) A).hom
  change BicategoryStruct.whiskerRight (PiTwoSupercategory.ζ (R := R) A).hom (𝟙 A) ≫
      (sign R 0 • ((BicategoryStruct.rightUnitor (𝟙 A)).hom ≫
        (BicategoryStruct.leftUnitor (𝟙 A)).inv)) =
    (sign R 1 • ((BicategoryStruct.rightUnitor (PiTwoSupercategory.pi (R := R) A)).hom ≫
        (BicategoryStruct.leftUnitor (PiTwoSupercategory.pi (R := R) A)).inv)) ≫
      BicategoryStruct.whiskerLeft (𝟙 A) (PiTwoSupercategory.ζ (R := R) A).hom at h
  rw [sign_zero, sign_one, one_smul, neg_one_smul, Preadditive.neg_comp, ← Category.assoc,
    rightUnitor_naturality (R := R), Category.assoc, Category.assoc,
    ← leftUnitor_inv_naturality (R := R)] at h
  set z := (BicategoryStruct.rightUnitor (PiTwoSupercategory.pi (R := R) A)).hom ≫
    (PiTwoSupercategory.ζ (R := R) A).hom ≫ (BicategoryStruct.leftUnitor (𝟙 A)).inv with hz
  have hz2 : (2 : R) • z = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel z
  have hone : (2 : R) • 𝟙 (PiTwoSupercategory.pi (R := R) A) = 0 := by
    have : 𝟙 (PiTwoSupercategory.pi (R := R) A) =
        (BicategoryStruct.rightUnitor (PiTwoSupercategory.pi (R := R) A)).inv ≫ z ≫
          (BicategoryStruct.leftUnitor (𝟙 A)).hom ≫ (PiTwoSupercategory.ζ (R := R) A).inv := by
      simp [hz]
    rw [this, ← Linear.comp_smul, ← Linear.smul_comp, hz2, Limits.zero_comp, Limits.comp_zero]
  apply h2
  have := congrArg Envelope.toHom hone
  rw [Envelope.toHom_smul, Envelope.toHom_id] at this
  exact this⟩

end TwoEnvelope

/-! ## Remark 5.7: the printed statement -/

namespace DrinfeldCenter

variable {R : Type w} [CommRing R] {A : Type*} [BicategoryStruct A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A] [PiTwoSupercategory R A]

variable (R A) in
/-- The comparison functor `Z(𝔄)̲ → Z(𝔄̲)` from the underlying category of the Drinfeld center
of `𝔄` to the Drinfeld center (Definition 2.3) of the 2-category `𝔄̲ = E₂ 𝔄`. It factors through
the Π-center (`toPiCenter`). -/
def toCenter2 : Underlying R (DrinfeldCenter R A) ⥤ Center2 (Underlying2 R A) :=
  toPiCenter R A ⋙ ObjectProperty.ιOfLE (fun _ h => h.1)

end DrinfeldCenter

namespace TwoEnvelope

variable {R : Type w} [CommRing R] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

variable (R B) in
/-- The parity twist as an object of the Drinfeld center of `𝔄̲`, for `𝔄 = B_π`. -/
def parityTwistObj (hB : TwoSupercategory.NoOdd R B) : Center2 (Underlying2 R (TwoEnvelope R B)) :=
  ⟨MonoidalOpposite.mop (parityTwist R B hB), parityTwist_isStrong hB⟩

/-- **Remark 5.7, as printed, fails.** For `𝔄 = B_π` with `B` without odd 2-morphisms and
`2 • 1_{1_a} ≠ 0` for some object `a`, the parity twist is an object of the Drinfeld center of
`𝔄̲` that is not isomorphic to the image of any object of the Drinfeld center of `𝔄`: the
comparison functor `Z(𝔄)̲ → Z(𝔄̲)` is not essentially surjective. -/
theorem parityTwistObj_not_mem_essImage (hB : TwoSupercategory.NoOdd R B) (a : B)
    (h2 : (2 : R) • 𝟙 (𝟙 a) ≠ 0) :
    ¬ (DrinfeldCenter.toCenter2 R (TwoEnvelope R B)).essImage (parityTwistObj R B hB) := by
  rintro ⟨X, ⟨e⟩⟩
  exact (parityTwist_not_iso hB a h2 X.obj.toTwoNatTrans).false
    ((centerProp (Underlying2 R (TwoEnvelope R B))).ι.mapIso e).unmop

/-- The parity twist is not Π-2-natural: it is not in the Π-center of `𝔄̲`. -/
theorem parityTwist_not_isPiTwoNatural (hB : TwoSupercategory.NoOdd R B) (a : B)
    (h2 : (2 : R) • 𝟙 (𝟙 a) ≠ 0) :
    ¬ (PiTwoFunctor.id R (Underlying2 R (TwoEnvelope R B))).IsPiTwoNatural
      (PiTwoFunctor.id R _) (parityTwist R B hB) := fun hπ =>
  (parityTwist_not_iso hB a h2 (DrinfeldCenter.ofPiCenter
    (⟨MonoidalOpposite.mop (parityTwist R B hB), parityTwist_isStrong hB, hπ⟩ :
      PiCenter R (Underlying2 R (TwoEnvelope R B)))).toTwoNatTrans).false (Iso.refl _)

end TwoEnvelope

/-- **Brundan–Ellis, Remark 5.7 (printed form), counterexample.** For the Π-envelope
`𝔄 = I_π` of the unit 2-supercategory over `ℤ`, the comparison functor from the monoidal
category underlying the Drinfeld center of `𝔄` to the Drinfeld center of `𝔄̲` is not
essentially surjective (the corrected statement, with the Π-center of `𝔄̲`, is
`DrinfeldCenter.centerEquivalence`). -/
theorem remark57_toCenter2_not_essSurj :
    ¬ (DrinfeldCenter.toCenter2 ℤ (TwoEnvelope ℤ (UnitTwo ℤ))).EssSurj := fun h =>
  TwoEnvelope.parityTwistObj_not_mem_essImage (UnitTwo.noOdd ℤ) UnitTwo.pt
    (show (2 : ℤ) • (1 : ℤ) ≠ 0 by norm_num) (h.mem_essImage _)

end StringDiagrams

end
