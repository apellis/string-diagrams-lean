/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.GSKarLaurent
import StringDiagrams.Super.K0HomRank
import Mathlib.RingTheory.LaurentSeries

/-!
# The graded dimension pairing on `K₀` of a graded super Karoubi envelope

Let `C` be a graded supercategory over a field `k` whose Hom spaces are degreewise finite
dimensional and bounded below in degree. For an object `P` of `GSKar k C` and `X` in
`GSKar k C`, the degree `n` maps `P → X` are the maps `Qⁿ P → X` of the envelope, so the graded
dimension of the space of all maps `P → X` is the Laurent series `∑ₙ dim (Qⁿ P ⟶ X) qⁿ`. Adding
the maps into `Π X` with a factor `π` gives the graded superdimension, an element of
`Zπ((q))`. This is the categorical pairing `([P], [X]) ↦ gdim HOM(P, X)` of Khovanov–Lauda,
arXiv:0803.4121v2, §2.5, in the super setting of Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, §11 (Hill–Wang, arXiv:1202.2769v2, Proposition 6.8).

## Main definitions and results

* `GSKar.homCoeff P n : K₀ (GSKar k C) →+ ℤ`, `[X] ↦ dim (Qⁿ P ⟶ X)` (`homCoeff_mk`).
* `GSKar.homCoeff_T_smul`: `homCoeff P n (qᵐ x) = homCoeff P (n - m) x`.
* `GSKar.pairing P : K₀ (GSKar k C) →+ LaurentSeries Zπ`, the graded superdimension of
  `HOM(P, -)` (`coeff_pairing`).
* `GSKar.pairing_smul`: the pairing is linear over `Zπ[q, q⁻¹]`, acting on `Zπ((q))` through
  `laurentToSeries`.
* `GSKar.homCoeff_of`, `GSKar.superCoeff_of`: on objects `X, Y` of `C` (as objects `GSKar.of`
  of the envelope), the coefficient of `qⁿ` is `dim HOM(X, Y)ₙ,₀ + dim HOM(X, Y)ₙ,₁ π`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Limits Idempotents Module

/-- The embedding `Zπ[q, q⁻¹] → Zπ((q))`. -/
def laurentToSeries : LaurentPolynomial Zπ →+* LaurentSeries Zπ :=
  LaurentPolynomial.eval₂ HahnSeries.C
    ⟨HahnSeries.single 1 1, HahnSeries.single (-1) 1,
      by rw [HahnSeries.single_mul_single]; simp,
      by rw [HahnSeries.single_mul_single]; simp⟩

@[simp] theorem laurentToSeries_C (a : Zπ) :
    laurentToSeries (LaurentPolynomial.C a) = HahnSeries.C a :=
  LaurentPolynomial.eval₂_C _ _ _

theorem laurentToSeries_T_one :
    laurentToSeries (LaurentPolynomial.T 1) = HahnSeries.single 1 1 := by
  rw [laurentToSeries, LaurentPolynomial.eval₂_T, zpow_one]

theorem laurentToSeries_T_neg_one :
    laurentToSeries (LaurentPolynomial.T (-1)) = HahnSeries.single (-1) 1 := by
  rw [laurentToSeries, LaurentPolynomial.eval₂_T, zpow_neg_one]
  rfl

namespace K₀

variable (R : Type*) [CommRing R] (A : Type*) [Category A] [Preadditive A] [Linear R A]
  [QPiCategory R A] [HasBinaryBiproducts A]

set_option backward.isDefEq.respectTransparency false in
theorem piInvolution_eq_laurentEnd (x : K₀ A) :
    piInvolution R A x = laurentEnd R A (LaurentPolynomial.C Zπ.π) x := by
  rw [laurentEnd_C, Zπ.toEnd_π]

/-- `[Π]` commutes with the action of `Zπ[q, q⁻¹]`. -/
theorem piInvolution_laurentEnd (r : LaurentPolynomial Zπ) (x : K₀ A) :
    piInvolution R A (laurentEnd R A r x) = laurentEnd R A r (piInvolution R A x) := by
  rw [piInvolution_eq_laurentEnd, piInvolution_eq_laurentEnd]
  have h : laurentEnd R A (LaurentPolynomial.C Zπ.π) * laurentEnd R A r =
      laurentEnd R A r * laurentEnd R A (LaurentPolynomial.C Zπ.π) := by
    rw [← map_mul, ← map_mul, mul_comm (LaurentPolynomial.C Zπ.π) r]
  exact congrArg (fun φ : AddMonoid.End (K₀ A) => φ x) h

end K₀

namespace GSKar

open GradedSupercategory Supercategory

variable {k C : Type*} [Field k] [Category C] [Preadditive C] [Linear k C]
  [Supercategory k C] [GradedSupercategory k C] [DegreeHomFinite (k := k) (C := C)]

/-- `Q⁻¹` is bijective on Hom spaces, `k`-linearly. -/
def homQinvEquiv (A B : GSKar k C) :
    (A ⟶ B) ≃ₗ[k] ((QPiCategory.Qinv (R := k)).obj A ⟶ (QPiCategory.Qinv (R := k)).obj B) :=
  let ff := (QPiCategory.qEquivalence k (GSKar k C)).fullyFaithfulInverse
  { toFun := (QPiCategory.Qinv (R := k)).map
    invFun := ff.preimage
    left_inv := ff.preimage_map
    right_inv := ff.map_preimage
    map_add' := fun _ _ => (QPiCategory.Qinv (R := k)).map_add
    map_smul' := fun c f => (QPiCategory.Qinv (R := k)).map_smul c f }

/-- Maps into `Q X` are maps out of `Q⁻¹`, `k`-linearly. -/
def homQEquiv (A X : GSKar k C) :
    (A ⟶ (QPiCategory.Q (R := k)).obj X) ≃ₗ[k] ((QPiCategory.Qinv (R := k)).obj A ⟶ X) :=
  homQinvEquiv A _ ≪≫ₗ Linear.homCongr k (Iso.refl _)
    ((QPiCategory.qEquivalence k (GSKar k C)).unitIso.app X).symm

/-- `Q⁻¹ Qⁿ P ≅ Qⁿ⁻¹ P`. -/
def qinvShiftIso (P : GSKar k C) (n : ℤ) :
    (QPiCategory.Qinv (R := k)).obj ((shiftFunctor n).obj P) ≅ (shiftFunctor (n - 1)).obj P :=
  (QPiCategory.Qinv (R := k)).mapIso
      (eqToIso (by rw [sub_add_cancel]) ≪≫ ((shiftSuccIso (n - 1)).app P).symm) ≪≫
    ((QPiCategory.qEquivalence k (GSKar k C)).unitIso.app _).symm

variable (k) in
/-- **The degree `n` part of the graded dimension of `HOM(P, -)`** on `K₀`:
`[X] ↦ dim (Qⁿ P ⟶ X)`. -/
def homCoeff (P : GSKar k C) (n : ℤ) : K₀ (GSKar k C) →+ ℤ :=
  K₀.homRank k ((shiftFunctor n).obj P) fun _ => inferInstance

@[simp] theorem homCoeff_mk (P X : GSKar k C) (n : ℤ) :
    homCoeff k P n (K₀.mk X) = finrank k ((shiftFunctor n).obj P ⟶ X) :=
  K₀.homRank_mk _ _ _

theorem homCoeff_mk_Q (P X : GSKar k C) (n : ℤ) :
    homCoeff k P n (K₀.mk ((QPiCategory.Q (R := k)).obj X)) = homCoeff k P (n - 1) (K₀.mk X) := by
  rw [homCoeff_mk, homCoeff_mk, (homQEquiv _ X).finrank_eq,
    (Linear.homCongr k (qinvShiftIso P n) (Iso.refl X)).finrank_eq]

/-- Shifting the second argument shifts the coefficients. -/
theorem homCoeff_T_one_smul (P : GSKar k C) (n : ℤ) (x : K₀ (GSKar k C)) :
    letI := moduleLaurent k C
    homCoeff k P n ((LaurentPolynomial.T 1 : LaurentPolynomial Zπ) • x) =
      homCoeff k P (n - 1) x := by
  let := moduleLaurent k C
  have : (homCoeff k P n).comp (K₀.laurentEnd k (GSKar k C) (LaurentPolynomial.T 1)) =
      homCoeff k P (n - 1) := K₀.hom_ext fun X => by
    change homCoeff k P n ((LaurentPolynomial.T 1 : LaurentPolynomial Zπ) • K₀.mk X) = _
    rw [K₀.T_smul_mk, homCoeff_mk_Q]
  exact DFunLike.congr_fun this x

theorem homCoeff_T_neg_one_smul (P : GSKar k C) (n : ℤ) (x : K₀ (GSKar k C)) :
    letI := moduleLaurent k C
    homCoeff k P n ((LaurentPolynomial.T (-1) : LaurentPolynomial Zπ) • x) =
      homCoeff k P (n + 1) x := by
  let := moduleLaurent k C
  conv_rhs => rw [← one_smul (LaurentPolynomial Zπ) x, ← LaurentPolynomial.T_zero,
    show (0 : ℤ) = 1 + -1 by norm_num, LaurentPolynomial.T_add, mul_smul,
    homCoeff_T_one_smul, add_sub_cancel_right]

/-- Maps out of sufficiently negative shifts of `P` vanish. -/
theorem homCoeff_eventually_zero (h : HomBoundedBelow (k := k) (C := C)) (P : GSKar k C)
    (x : K₀ (GSKar k C)) : ∃ N : ℤ, ∀ n < N, homCoeff k P n x = 0 := by
  obtain ⟨X, Y, rfl⟩ := K₀.exists_eq_mk_sub_mk x
  obtain ⟨N₁, h₁⟩ := shift_hom_boundedBelow h P X
  obtain ⟨N₂, h₂⟩ := shift_hom_boundedBelow h P Y
  refine ⟨min N₁ N₂, fun n hn => ?_⟩
  have := h₁ n (lt_of_lt_of_le hn (min_le_left _ _))
  have := h₂ n (lt_of_lt_of_le hn (min_le_right _ _))
  rw [map_sub, homCoeff_mk, homCoeff_mk, Module.finrank_zero_of_subsingleton,
    Module.finrank_zero_of_subsingleton, sub_self]

variable (k) in
/-- The coefficients of the graded superdimension of `HOM(P, -)`: the degree `n` maps into `X`,
plus `π` times the degree `n` maps into `Π X`. -/
def superCoeff (P : GSKar k C) (n : ℤ) : K₀ (GSKar k C) →+ Zπ :=
  (Int.castAddHom Zπ).comp (homCoeff k P n) +
    (AddMonoidHom.mulRight Zπ.π).comp ((Int.castAddHom Zπ).comp
      ((homCoeff k P n).comp (K₀.piInvolution k (GSKar k C))))

theorem superCoeff_apply (P : GSKar k C) (n : ℤ) (x : K₀ (GSKar k C)) :
    superCoeff k P n x = (homCoeff k P n x : Zπ) +
      (homCoeff k P n (K₀.piInvolution k (GSKar k C) x) : Zπ) * Zπ.π := rfl

variable (k) in
/-- **The graded dimension pairing** `[X] ↦ gdim HOM(P, X) ∈ Zπ((q))`: the coefficient of `qⁿ` is
`dim (Qⁿ P ⟶ X) + dim (Qⁿ P ⟶ Π X) π` (`coeff_pairing`). -/
def pairing (h : HomBoundedBelow (k := k) (C := C)) (P : GSKar k C) :
    K₀ (GSKar k C) →+ LaurentSeries Zπ where
  toFun x := HahnSeries.ofSuppBddBelow (fun n => superCoeff k P n x) (by
    obtain ⟨N₁, h₁⟩ := homCoeff_eventually_zero h P x
    obtain ⟨N₂, h₂⟩ := homCoeff_eventually_zero h P (K₀.piInvolution k (GSKar k C) x)
    refine ⟨min N₁ N₂, fun n hn => ?_⟩
    by_contra! hlt
    apply hn
    change superCoeff k P n x = 0
    rw [superCoeff_apply, h₁ n (lt_of_lt_of_le hlt (min_le_left _ _)),
      h₂ n (lt_of_lt_of_le hlt (min_le_right _ _))]
    simp)
  map_zero' := by
    ext n
    simp
  map_add' x y := by
    ext n
    simp

@[simp] theorem coeff_pairing (h : HomBoundedBelow (k := k) (C := C)) (P : GSKar k C)
    (x : K₀ (GSKar k C)) (n : ℤ) :
    (pairing k h P x).coeff n = superCoeff k P n x :=
  rfl

theorem pairing_T_one_smul (h : HomBoundedBelow (k := k) (C := C)) (P : GSKar k C)
    (x : K₀ (GSKar k C)) :
    letI := moduleLaurent k C
    pairing k h P ((LaurentPolynomial.T 1 : LaurentPolynomial Zπ) • x) =
      HahnSeries.single 1 1 * pairing k h P x := by
  let := moduleLaurent k C
  ext n
  have hc : (HahnSeries.single (1 : ℤ) (1 : Zπ) * pairing k h P x).coeff n =
      (pairing k h P x).coeff (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by ring]
    rw [HahnSeries.coeff_single_mul_add, one_mul]
  rw [hc, coeff_pairing, coeff_pairing, superCoeff_apply, superCoeff_apply,
    homCoeff_T_one_smul]
  congr 3
  change homCoeff k P n (K₀.piInvolution k (GSKar k C)
    (K₀.laurentEnd k (GSKar k C) (LaurentPolynomial.T 1) x)) = _
  rw [← homCoeff_T_one_smul]
  exact congrArg _ (K₀.piInvolution_laurentEnd k (GSKar k C) _ x)

theorem pairing_T_neg_one_smul (h : HomBoundedBelow (k := k) (C := C)) (P : GSKar k C)
    (x : K₀ (GSKar k C)) :
    letI := moduleLaurent k C
    pairing k h P ((LaurentPolynomial.T (-1) : LaurentPolynomial Zπ) • x) =
      HahnSeries.single (-1) 1 * pairing k h P x := by
  let := moduleLaurent k C
  ext n
  have hc : (HahnSeries.single (-1 : ℤ) (1 : Zπ) * pairing k h P x).coeff n =
      (pairing k h P x).coeff (n + 1) := by
    conv_lhs => rw [show n = (n + 1) + -1 by ring]
    rw [HahnSeries.coeff_single_mul_add, one_mul]
  rw [hc, coeff_pairing, coeff_pairing, superCoeff_apply, superCoeff_apply,
    homCoeff_T_neg_one_smul]
  congr 3
  change homCoeff k P n (K₀.piInvolution k (GSKar k C)
    (K₀.laurentEnd k (GSKar k C) (LaurentPolynomial.T (-1)) x)) = _
  rw [← homCoeff_T_neg_one_smul]
  exact congrArg _ (K₀.piInvolution_laurentEnd k (GSKar k C) _ x)

theorem pairing_π_smul (h : HomBoundedBelow (k := k) (C := C)) (P : GSKar k C)
    (x : K₀ (GSKar k C)) :
    letI := moduleLaurent k C
    pairing k h P ((LaurentPolynomial.C Zπ.π : LaurentPolynomial Zπ) • x) =
      HahnSeries.C Zπ.π * pairing k h P x := by
  let := moduleLaurent k C
  have hx : (LaurentPolynomial.C Zπ.π : LaurentPolynomial Zπ) • x =
      K₀.piInvolution k (GSKar k C) x :=
    (K₀.piInvolution_eq_laurentEnd k (GSKar k C) x).symm
  ext n
  rw [hx, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, coeff_pairing, coeff_pairing,
    superCoeff_apply, superCoeff_apply, K₀.piInvolution_piInvolution, smul_eq_mul]
  linear_combination (-((homCoeff k P n (K₀.piInvolution k (GSKar k C) x) : ℤ) : Zπ)) *
    Zπ.π_mul_π

/-- **The graded dimension pairing is `Zπ[q, q⁻¹]`-linear.** -/
theorem pairing_smul (h : HomBoundedBelow (k := k) (C := C)) (P : GSKar k C)
    (r : LaurentPolynomial Zπ) (x : K₀ (GSKar k C)) :
    letI := moduleLaurent k C
    pairing k h P (r • x) = laurentToSeries r * pairing k h P x := by
  let := moduleLaurent k C
  let M : LaurentPolynomial Zπ → Prop := fun r =>
    ∀ x, pairing k h P (r • x) = laurentToSeries r * pairing k h P x
  have hmul : ∀ {r s}, M r → M s → M (r * s) := fun hr hs x => by
    rw [mul_smul, hr, hs, map_mul]
    exact (mul_assoc (laurentToSeries _) (laurentToSeries _) (pairing k h P x)).symm
  have hadd : ∀ {r s}, M r → M s → M (r + s) := fun hr hs x => by
    rw [add_smul, map_add, hr, hs, map_add]
    ring
  have hint : ∀ m : ℤ, M (m : LaurentPolynomial Zπ) := fun m x => by
    rw [Int.cast_smul_eq_zsmul, map_zsmul, map_intCast]
    exact zsmul_eq_mul (pairing k h P x) m
  have hC : ∀ a : Zπ, M (LaurentPolynomial.C a) := by
    intro a
    obtain ⟨m, b, rfl⟩ := Zπ.exists_eq_add_mul_π a
    rw [map_add, map_mul, map_intCast, map_intCast]
    exact hadd (hint m) (hmul (hint b) fun x => by rw [pairing_π_smul, laurentToSeries_C])
  have hT1 : M (LaurentPolynomial.T 1) := fun x => by
    rw [pairing_T_one_smul, laurentToSeries_T_one]
  have hTm1 : M (LaurentPolynomial.T (-1)) := fun x => by
    rw [pairing_T_neg_one_smul, laurentToSeries_T_neg_one]
  revert x
  induction r using LaurentPolynomial.induction_on with
  | h_C a => exact hC a
  | h_add hp hq => exact hadd hp hq
  | h_C_mul_T n a ih =>
    rw [LaurentPolynomial.T_add, ← mul_assoc]
    exact hmul ih hT1
  | h_C_mul_T_Z n a ih =>
    have e : (LaurentPolynomial.T (-(n : ℤ) - 1) : LaurentPolynomial Zπ) =
        LaurentPolynomial.T (-(n : ℤ)) * LaurentPolynomial.T (-1) := by
      rw [← LaurentPolynomial.T_add]
      congr 1
    rw [e, ← mul_assoc]
    exact hmul ih hTm1

/-! ### Coefficients between shifted objects of `C` -/

variable (k) in
/-- The object `Qⁿ Πᵖ X` of `GSKar k C`, for an object `X` of `C`. -/
def of (X : C) (n : ℤ) (p : ZMod 2) : GSKar k C :=
  (toKaroubi _).obj ((Mat_.embedding _).obj (⟨⟨⟨p, ⟨n, X⟩⟩⟩⟩ : ShiftBase k C))

/-- Maps between objects of `C`, viewed in `GSKar k C`, are maps of the base category. -/
def homOfEquiv (A B : ShiftBase k C) :
    ((toKaroubi _).obj ((Mat_.embedding _).obj A) ⟶ (toKaroubi _).obj ((Mat_.embedding _).obj B))
      ≃ₗ[k] (A ⟶ B) where
  toFun φ := φ.f PUnit.unit PUnit.unit
  invFun g := (toKaroubi _).map ((Mat_.embedding _).map g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := by
    apply Karoubi.hom_ext
    funext i j
    cases i; cases j
    rfl
  right_inv _ := rfl

/-- Maps `Qᵐ Πᵖ X → Qⁿ Πᵖ' Y` in the base category are the maps `X → Y` of degree `m - n` and
parity `p + p'`. -/
def baseHomEquiv (X Y : C) (m n : ℤ) (p p' : ZMod 2) :
    ((⟨⟨⟨p, ⟨m, X⟩⟩⟩⟩ : ShiftBase k C) ⟶ ⟨⟨⟨p', ⟨n, Y⟩⟩⟩⟩) ≃ₗ[k]
      ↥(degree (R := k) X Y (m - n) ⊓ Supercategory.parity (R := k) X Y (p + p')) where
  toFun g := ⟨g.1.1, by
    have h1 : g.1.1 ∈ degree (R := k) X Y (0 + (m - n)) := g.1.2
    have h2 : g.1.1 ∈ Supercategory.parity (R := k) X Y (0 + (p + p')) := g.2
    rw [zero_add] at h1 h2
    exact ⟨h1, h2⟩⟩
  invFun g := ⟨⟨g.1, by
      change g.1 ∈ degree (R := k) X Y (0 + (m - n))
      rw [zero_add]; exact g.2.1⟩, by
    change g.1 ∈ Supercategory.parity (R := k) X Y (0 + (p + p'))
    rw [zero_add]; exact g.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [DegreeHomFinite (k := k) (C := C)] in
/-- `F(X, 1) ≅ (F X, 1)` in the idempotent completion. -/
def mapFunctorToKaroubiIso {D E : Type*} [Category D] [Category E] (F : D ⥤ E) (A : D) :
    (Karoubi.mapFunctor F).obj ((toKaroubi D).obj A) ≅ (toKaroubi E).obj (F.obj A) where
  hom := ⟨𝟙 _, by simp [Karoubi.mapFunctor]⟩
  inv := ⟨𝟙 _, by simp [Karoubi.mapFunctor]⟩
  hom_inv_id := by
    ext
    change 𝟙 (F.obj A) ≫ 𝟙 (F.obj A) = F.map (𝟙 A)
    simp
  inv_hom_id := by
    ext
    change 𝟙 (F.obj A) ≫ 𝟙 (F.obj A) = 𝟙 (F.obj A)
    simp

/-- `Qⁿ` applied to `Qᵐ Πᵖ X` is `Q^{m+n} Πᵖ X`. -/
def shiftOfIso (X : C) (m n : ℤ) (p : ZMod 2) :
    (shiftFunctor n).obj (of k X m p) ≅ of k X (m + n) p :=
  mapFunctorToKaroubiIso _ _ ≪≫
    (toKaroubi _).mapIso ((Mat_.embedding _).mapIso (eqToIso (baseShift_obj n _)))

/-- `Π (Qᵐ Πᵖ X) ≅ Qᵐ Π^{p+1} X`. -/
def piOfIso (X : C) (m : ℤ) (p : ZMod 2) :
    (PiCategory.pi (R := k)).obj (of k X m p) ≅ of k X m (p + 1) :=
  mapFunctorToKaroubiIso (PiCategory.pi (R := k) (C := Mat_ (ShiftBase k C)))
    ((Mat_.embedding _).obj ⟨⟨⟨p, ⟨m, X⟩⟩⟩⟩)

/-- **The coefficients of the pairing between objects of `C`**: the coefficient of `qⁿ` in the
graded dimension of `HOM(X, Πᵖ Y)` is the dimension of the maps `X → Y` of degree `n` and
parity `p`. -/
theorem homCoeff_of (X Y : C) (n : ℤ) (p : ZMod 2) :
    homCoeff k (of k X 0 0) n (K₀.mk (of k Y 0 p)) =
      finrank k ↥(degree (R := k) X Y n ⊓ Supercategory.parity (R := k) X Y p) := by
  rw [homCoeff_mk, (Linear.homCongr k (shiftOfIso X 0 n 0) (Iso.refl _)).finrank_eq]
  refine congrArg _ ((((homOfEquiv (⟨⟨⟨0, ⟨0 + n, X⟩⟩⟩⟩ : ShiftBase k C) ⟨⟨⟨p, ⟨0, Y⟩⟩⟩⟩).trans
    (baseHomEquiv X Y (0 + n) 0 0 p)).finrank_eq).trans ?_)
  rw [zero_add, sub_zero, zero_add]

/-- **The pairing between objects of `C`**: the coefficient of `qⁿ` in the graded
superdimension of `HOM(X, Y)` is `dim HOM(X, Y)ₙ,₀ + dim HOM(X, Y)ₙ,₁ π`. -/
theorem superCoeff_of (X Y : C) (n : ℤ) :
    superCoeff k (of k X 0 0) n (K₀.mk (of k Y 0 0)) =
      (finrank k ↥(degree (R := k) X Y n ⊓ Supercategory.parity (R := k) X Y 0) : Zπ) +
        (finrank k ↥(degree (R := k) X Y n ⊓ Supercategory.parity (R := k) X Y 1) : Zπ) * Zπ.π := by
  rw [superCoeff_apply, K₀.piInvolution_mk, K₀.mk_eq_mk_of_iso (piOfIso Y 0 0), zero_add,
    homCoeff_of, homCoeff_of]
  rfl

end GSKar

end StringDiagrams
