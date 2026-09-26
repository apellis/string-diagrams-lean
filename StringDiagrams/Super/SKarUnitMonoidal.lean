import StringDiagrams.Super.SKarUnit
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The equivalence `SKar(I) ≃ SVec_fd` is monoidal (Example 1.17(ii))

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 1.17(ii): the super Karoubi envelope `SKar(I)` of the unit supercategory is *monoidally*
equivalent to `SVec_fd`.

The functor `SKarUnit.toSVec : SKar(I) ⥤ SVec̲`, `(M, p) ↦ p(⊕ᵢ Π^{aᵢ} k)`, is made a monoidal
functor. The tensor product of `(M, p)` and `(N, q)` in `SKar(I)` is `(M ⊗ N, p ⊗ q)`, where
`M ⊗ N` is indexed by `M.ι × N.ι` and `p ⊗ q` is the Kronecker product of the scalar matrices
(`SKarUnit.scalMat_tensorHom`; the signs of Definition 1.16 are trivial since all morphisms of
`I` are even). The tensorator is induced by the even isomorphism
`(⊕ᵢ Π^{aᵢ} k) ⊗ (⊕ⱼ Π^{bⱼ} k) ≅ ⊕_{(i,j)} Π^{aᵢ + bⱼ} k`, `v ⊗ w ↦ ((i, j) ↦ vᵢ wⱼ)`
(`SKarUnit.tmulFun`), restricted to the images of the idempotents.
-/

noncomputable section

namespace StringDiagrams.SKarUnit

open CategoryTheory Limits Idempotents Supercategory MonoidalCategory Matrix TensorProduct

universe u

variable {k : Type u} [CommRing k]

/-! ## Scalars of tensor products -/

theorem par_tensorObj (X Y : D k) : par (X ⊗ Y) = par X + par Y := rfl

/-- In `I̲_π`, the tensor product of morphisms is the product of scalars: the signs of
Definition 1.16 are trivial because every morphism of `I` is even. -/
theorem scal_tensorHom {X X' Y Y' : D k} (f : X ⟶ X') (g : Y ⟶ Y') :
    scal (f ⊗ g) = scal f * scal g := by
  by_cases hY : par Y = par Y'
  · change SuperalgebraCat.toElem (Envelope.toHom (f.1 ⊗ g.1)) = _
    rw [Envelope.tensorHom_def', Envelope.toHom_comp,
      Envelope.toHom_whiskerRight_of_mem (UnitSupercat.mem_parity_zero _),
      Envelope.toHom_whiskerLeft_of_mem _ (UnitSupercat.mem_parity_zero _), mul_zero, sign_zero,
      one_smul, zero_add, show Y.obj.par + Y'.obj.par = 0 by
        rw [show Y.obj.par = Y'.obj.par from hY, zmod2_add_self],
      mul_zero, sign_zero, one_smul]
    exact mul_comm _ _
  · rw [hom_ext (f := g) (g := 0) (by rw [scal_eq_zero_of_ne g hY, scal_zero]),
      MonoidalPreadditive.tensor_zero, scal_zero, scal_zero, mul_zero]

theorem scalMat_tensorHom {M M' N N' : Mat_ (D k)} (f : M ⟶ M') (g : N ⟶ N') :
    scalMat (f ⊗ g) = kroneckerMap (· * ·) (scalMat f) (scalMat g) := by
  ext x y
  exact scal_tensorHom (f x.1 y.1) (g x.2 y.2)

theorem scal_associator_hom (X Y Z : D k) : scal (α_ X Y Z).hom = 1 := rfl

theorem scal_leftUnitor_hom (X : D k) : scal (λ_ X).hom = 1 := rfl

theorem scal_rightUnitor_hom (X : D k) : scal (ρ_ X).hom = 1 := rfl

/-- The scalar matrix of a permutation matrix with invertible-scalar entries `1`. -/
theorem scalMat_permMat {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] {X : ι → D k}
    {Y : κ → D k} (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i)) (hφ : ∀ i, scal (φ i) = 1) (i : ι)
    (j : κ) : scalMat (Mat_.permMat e φ) i j = if e i = j then 1 else 0 := by
  by_cases h : e i = j
  · subst h
    rw [if_pos rfl, scalMat, Mat_.permMat_apply_self, hφ]
  · rw [if_neg h, scalMat, Mat_.permMat_apply_of_ne _ _ h, scal_zero]

theorem vecMul_perm {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (u : ι → k) (j : κ) : (u ᵥ* fun i j => if e i = j then (1 : k) else 0) j = u (e.symm j) := by
  rw [vecMul, dotProduct, Finset.sum_eq_single (e.symm j)]
  · rw [Equiv.apply_symm_apply, if_pos rfl, mul_one]
  · intro i _ hi
    rw [if_neg, mul_zero]
    intro h; exact hi (by rw [← h, Equiv.symm_apply_apply])
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The tensor product of free objects -/

/-- `(⊕ᵢ k) ⊗ (⊕ⱼ k) → ⊕_{(i,j)} k`, `v ⊗ w ↦ ((i, j) ↦ vᵢ wⱼ)`. -/
def tmulFun (ι κ : Type) : (ι → k) ⊗[k] (κ → k) →ₗ[k] (ι × κ → k) :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun w x => v x.1 * w x.2
          map_add' := fun w w' => by funext x; simp [mul_add]
          map_smul' := fun c w => by funext x; simp [mul_left_comm] }
      map_add' := fun v v' => by ext w x; simp [add_mul]
      map_smul' := fun c v => by ext w x; simp [mul_assoc] }

@[simp] theorem tmulFun_tmul {ι κ : Type} (v : ι → k) (w : κ → k) :
    tmulFun ι κ (v ⊗ₜ w) = fun x => v x.1 * w x.2 := rfl

theorem tmulFun_single {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (i : ι) (j : κ) :
    tmulFun ι κ (Pi.single i (1 : k) ⊗ₜ Pi.single j (1 : k)) = Pi.single (i, j) 1 := by
  rw [tmulFun_tmul]
  funext x
  obtain ⟨x₁, x₂⟩ := x
  simp only [Pi.single_apply, Prod.mk.injEq]
  by_cases h₁ : x₁ = i <;> by_cases h₂ : x₂ = j <;> simp [h₁, h₂]

/-- The Kronecker product acts on pure tensors: `(v A) ⊗ (w B) ↦ (v ⊗ w) (A ⊗ B)`. -/
theorem tmulFun_vecMul {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] (A : Matrix ι ι' k)
    (B : Matrix κ κ' k) (v : ι → k) (w : κ → k) :
    tmulFun ι' κ' ((v ᵥ* A) ⊗ₜ (w ᵥ* B)) = tmulFun ι κ (v ⊗ₜ w) ᵥ* kroneckerMap (· * ·) A B := by
  funext x
  simp only [tmulFun_tmul, vecMul, dotProduct, kroneckerMap_apply, Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem tmulFun_vecMul' {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] (A : Matrix ι ι' k)
    (B : Matrix κ κ' k) (t : (ι → k) ⊗[k] (κ → k)) :
    tmulFun ι' κ' (TensorProduct.map A.vecMulLinear B.vecMulLinear t) =
      tmulFun ι κ t ᵥ* kroneckerMap (· * ·) A B := by
  induction t using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero, Matrix.zero_vecMul]
  | tmul v w => exact tmulFun_vecMul A B v w
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, add_vecMul]

section Field

variable {K : Type u} [Field K]

theorem tmulFun_surjective (ι κ : Type) [Fintype ι] [Fintype κ] :
    Function.Surjective (tmulFun (k := K) ι κ) := by
  classical
  rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun K (ι × κ)).span_eq, Submodule.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  rw [Pi.basisFun_apply]
  exact ⟨_, tmulFun_single (k := K) i j⟩

theorem tmulFun_injective (ι κ : Type) [Fintype ι] [Fintype κ] :
    Function.Injective (tmulFun (k := K) ι κ) := by
  classical
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 (tmulFun_surjective ι κ)
  rw [Module.finrank_tensorProduct, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_prod]

theorem tmulFun_bijective (ι κ : Type) [Fintype ι] [Fintype κ] :
    Function.Bijective (tmulFun (k := K) ι κ) :=
  ⟨tmulFun_injective ι κ, tmulFun_surjective ι κ⟩

end Field

/-! ## The tensorator on free objects -/

/-- The even map `(⊕ᵢ Π^{aᵢ} k) ⊗ (⊕ⱼ Π^{bⱼ} k) → ⊕_{(i,j)} Π^{aᵢ+bⱼ} k`,
`v ⊗ w ↦ ((i, j) ↦ vᵢ wⱼ)`. -/
def freeTensor (M N : Mat_ (D k)) : freeObj M ⊗ freeObj N ⟶ freeObj (M ⊗ N) :=
  SVec.ofHom (tmulFun M.ι N.ι)

theorem freeTensor_tmul (M N : Mat_ (D k)) (v : M.ι → k) (w : N.ι → k) :
    freeTensor M N (v ⊗ₜ w) = fun x => v x.1 * w x.2 := rfl

theorem freeTensor_apply (M N : Mat_ (D k)) (t : (M.ι → k) ⊗[k] (N.ι → k)) :
    freeTensor M N t = tmulFun M.ι N.ι t := rfl

theorem par_tensor_X (M N : Mat_ (D k)) (x : M.ι × N.ι) :
    par ((M ⊗ N).X x) = par (M.X x.1) + par (N.X x.2) := rfl

/-- `freeTensor` is even. -/
theorem freeTensor_mem (M N : Mat_ (D k)) :
    freeTensor M N ∈ SVec.parityHom (freeObj M ⊗ freeObj N) (freeObj (M ⊗ N)) 0 := by
  intro q
  apply TensorProduct.ext'
  intro v w
  change freeTensor M N ((SVec.tensorObj (freeObj M) (freeObj N)).proj q (v ⊗ₜ w)) =
    (freeObj (M ⊗ N)).proj (q + 0) (freeTensor M N (v ⊗ₜ w))
  rw [add_zero, SVec.tensorObj_proj_tmul, map_add, freeTensor_tmul, freeTensor_tmul,
    freeTensor_tmul]
  funext x
  rw [Pi.add_apply, freeObj_proj_apply, freeObj_proj_apply, freeObj_proj_apply,
    freeObj_proj_apply, freeObj_proj_apply, par_tensor_X]
  rcases parity_eq_zero_or_one (par (M.X x.1)) with h1 | h1 <;>
    rcases parity_eq_zero_or_one (par (N.X x.2)) with h2 | h2 <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;> simp [h1, h2]

theorem matHom_tensor_apply {M M' N N' : Mat_ (D k)} (f : M ⟶ M') (g : N ⟶ N')
    (t : (M.ι → k) ⊗[k] (N.ι → k)) :
    matHom (f ⊗ g) (tmulFun M.ι N.ι t) = tmulFun M'.ι N'.ι
      (TensorProduct.map (SVec.toLinearMap (matHom f)) (SVec.toLinearMap (matHom g)) t) := by
  rw [matHom_apply, scalMat_tensorHom, ← tmulFun_vecMul']
  rfl

/-! ## The tensorator on the images of idempotents -/

theorem tensorObj_p (P Q : SKar k (UnitSupercat k)) : (P ⊗ Q).p = P.p ⊗ Q.p := rfl

/-- The tensorator `p(⊕ᵢ Π^{aᵢ} k) ⊗ q(⊕ⱼ Π^{bⱼ} k) → ⊕_{(i,j)} Π^{aᵢ+bⱼ} k`. -/
def μLin (P Q : SKar k (UnitSupercat k)) :
    (imgSubmodule P ⊗[k] imgSubmodule Q) →ₗ[k] (P.X.ι × Q.X.ι → k) :=
  tmulFun P.X.ι Q.X.ι ∘ₗ TensorProduct.map (imgSubmodule P).subtype (imgSubmodule Q).subtype

theorem μLin_tmul (P Q : SKar k (UnitSupercat k)) (v : imgSubmodule P) (w : imgSubmodule Q) :
    μLin P Q (v ⊗ₜ w) = fun x => v.1 x.1 * w.1 x.2 := rfl

/-- The tensorator takes values in the image of `p ⊗ q`. -/
theorem μLin_mem (P Q : SKar k (UnitSupercat k)) (t : imgSubmodule P ⊗[k] imgSubmodule Q) :
    μLin P Q t ∈ imgSubmodule (P ⊗ Q) := by
  rw [mem_imgSubmodule, tensorObj_p]
  induction t using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero]; exact LinearMap.map_zero (matHom (P.p ⊗ Q.p))
  | tmul v w =>
    change matHom (P.p ⊗ Q.p) (tmulFun _ _ (v.1 ⊗ₜ w.1)) = tmulFun _ _ (v.1 ⊗ₜ w.1)
    rw [matHom_tensor_apply, TensorProduct.map_tmul]
    change tmulFun _ _ (matHom P.p v.1 ⊗ₜ matHom Q.p w.1) = _
    rw [mem_imgSubmodule.1 v.2, mem_imgSubmodule.1 w.2]
  | add t t' h h' =>
    rw [LinearMap.map_add]
    erw [LinearMap.map_add (matHom (P.p ⊗ Q.p))]
    exact congrArg₂ (· + ·) h h'

theorem μLin_apply_mem_imgSubmodule (P Q : SKar k (UnitSupercat k)) (u : P.X.ι × Q.X.ι → k)
    (hu : u ∈ imgSubmodule (P ⊗ Q)) (t : (P.X.ι → k) ⊗[k] (Q.X.ι → k)) (ht : tmulFun _ _ t = u) :
    μLin P Q (TensorProduct.map
      (LinearMap.codRestrict (imgSubmodule P) (SVec.toLinearMap (matHom P.p)) (matHom_p_mem P))
      (LinearMap.codRestrict (imgSubmodule Q) (SVec.toLinearMap (matHom Q.p)) (matHom_p_mem Q)) t)
      = u := by
  rw [μLin, LinearMap.comp_apply,
    ← LinearMap.comp_apply (TensorProduct.map (imgSubmodule P).subtype (imgSubmodule Q).subtype),
    ← TensorProduct.map_comp, LinearMap.subtype_comp_codRestrict,
    LinearMap.subtype_comp_codRestrict, ← matHom_tensor_apply, ← tensorObj_p, ht]
  exact mem_imgSubmodule.1 hu

/-- The inclusion of the tensor product of the images into the tensor product of the free
objects is even. -/
theorem inclT_mem (P Q : SKar k (UnitSupercat k)) :
    SVec.ofHom (TensorProduct.map (imgSubmodule P).subtype (imgSubmodule Q).subtype) ∈
      SVec.parityHom (imgObj P ⊗ imgObj Q) (freeObj P.X ⊗ freeObj Q.X) 0 := by
  intro q
  apply TensorProduct.ext'
  intro v w
  change TensorProduct.map _ _ ((SVec.tensorObj (imgObj P) (imgObj Q)).proj q (v ⊗ₜ w)) =
    (SVec.tensorObj (freeObj P.X) (freeObj Q.X)).proj (q + 0) (v.1 ⊗ₜ w.1)
  rw [add_zero, SVec.tensorObj_proj_tmul, SVec.tensorObj_proj_tmul, map_add,
    TensorProduct.map_tmul, TensorProduct.map_tmul]
  simp only [Submodule.subtype_apply]
  rw [SVec.sub_proj_apply, SVec.sub_proj_apply, SVec.sub_proj_apply, SVec.sub_proj_apply]

section Field

variable {K : Type u} [Field K]

theorem range_μLin (P Q : SKar K (UnitSupercat K)) :
    LinearMap.range (μLin P Q) = imgSubmodule (P ⊗ Q) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    exact μLin_mem P Q t
  · intro u hu
    obtain ⟨t, ht⟩ := tmulFun_surjective P.X.ι Q.X.ι u
    exact ⟨_, μLin_apply_mem_imgSubmodule P Q u hu t ht⟩

theorem μLin_injective (P Q : SKar K (UnitSupercat K)) : Function.Injective (μLin P Q) := by
  refine (tmulFun_injective _ _).comp ?_
  change Function.Injective
    (TensorProduct.map (imgSubmodule P).subtype (imgSubmodule Q).subtype)
  rw [← LinearMap.lTensor_comp_rTensor]
  exact (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)).comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _))

/-- **The tensorator**, as a linear isomorphism
`p(⊕ᵢ Π^{aᵢ} K) ⊗ q(⊕ⱼ Π^{bⱼ} K) ≅ (p ⊗ q)(⊕_{(i,j)} Π^{aᵢ+bⱼ} K)`. -/
def μEquiv (P Q : SKar K (UnitSupercat K)) :
    (imgSubmodule P ⊗[K] imgSubmodule Q) ≃ₗ[K] imgSubmodule (P ⊗ Q) :=
  LinearEquiv.ofBijective (LinearMap.codRestrict _ (μLin P Q) (μLin_mem P Q))
    ⟨fun t t' h => μLin_injective P Q (congrArg Subtype.val h), fun u => by
      have hu : u.1 ∈ LinearMap.range (μLin P Q) := by rw [range_μLin]; exact u.2
      obtain ⟨t, ht⟩ := hu
      exact ⟨t, Subtype.ext ht⟩⟩

theorem μEquiv_apply_coe (P Q : SKar K (UnitSupercat K)) (t : imgSubmodule P ⊗[K] imgSubmodule Q) :
    (μEquiv P Q t).1 = μLin P Q t := rfl

theorem μEquiv_tmul_coe (P Q : SKar K (UnitSupercat K)) (v : imgSubmodule P)
    (w : imgSubmodule Q) : (μEquiv P Q (v ⊗ₜ w)).1 = fun x => v.1 x.1 * w.1 x.2 :=
  rfl

/-- The tensorator is even. -/
theorem μEquiv_hom_mem (P Q : SKar K (UnitSupercat K)) :
    (SVec.isoOfLinearEquiv (μEquiv P Q)).hom ∈
      SVec.parityHom (imgObj P ⊗ imgObj Q) (imgObj (P ⊗ Q)) 0 := by
  refine SVec.mem_parityHom_of_apply_mem fun q t ht => ?_
  rw [add_zero, SVec.mem_sub_part_iff]
  have h1 := SVec.apply_mem_part (inclT_mem P Q) ht
  have h2 := SVec.apply_mem_part (freeTensor_mem P.X Q.X) h1
  rw [add_zero, add_zero] at h2
  exact h2

/-- **Example 1.17(ii).** The tensorator `F(P) ⊗ F(Q) ≅ F(P ⊗ Q)` of `F = toSVec`. -/
def μIso (P Q : SKar K (UnitSupercat K)) :
    (toSVec K).obj P ⊗ (toSVec K).obj Q ≅ (toSVec K).obj (P ⊗ Q) :=
  Underlying.isoMk (SVec.isoOfLinearEquiv (μEquiv P Q)) (μEquiv_hom_mem P Q)

theorem μIso_hom_apply_coe (P Q : SKar K (UnitSupercat K))
    (t : imgSubmodule P ⊗[K] imgSubmodule Q) :
    ((μIso P Q).hom.1 t).1 = μLin P Q t := rfl

/-! ## The unit -/

theorem unit_p : (𝟙_ (SKar K (UnitSupercat K))).p = 𝟙 (𝟙_ (Mat_ (D K))) := rfl

theorem par_unit_X (i : (𝟙_ (Mat_ (D K))).ι) : par ((𝟙_ (Mat_ (D K))).X i) = 0 := rfl

/-- `K ≅ (⊕_{⋆} Π⁰ K)`. -/
def εEquiv : K ≃ₗ[K] imgSubmodule (𝟙_ (SKar K (UnitSupercat K))) where
  toFun c := ⟨fun _ => c, by
    rw [mem_imgSubmodule, unit_p]
    change matHom (𝟙 (𝟙_ (Mat_ (D K)))) _ = _
    rw [matHom_id]
    rfl⟩
  invFun v := v.1 PUnit.unit
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv v := Subtype.ext (funext fun _ => rfl)

theorem εEquiv_apply_coe (c : K) : (εEquiv c).1 = fun _ => c := rfl

theorem εEquiv_hom_mem :
    (SVec.isoOfLinearEquiv (εEquiv (K := K))).hom ∈
      SVec.parityHom SVec.unit (imgObj (𝟙_ (SKar K (UnitSupercat K)))) 0 := by
  refine SVec.mem_parityHom_of_apply_mem fun q c hc => ?_
  rw [add_zero, SVec.mem_sub_part_iff, mem_freeObj_part_iff]
  intro i hi
  change (0 : ZMod 2) ≠ q at hi
  rcases parity_eq_zero_or_one q with rfl | rfl
  · exact absurd rfl hi
  · rw [SVec.mem_part_iff, SVec.unit_proj_one_apply] at hc
    change c = 0
    exact hc.symm

/-- **Example 1.17(ii).** The unit constraint `K ≅ F(𝟙)` of `F = toSVec`. -/
def εIso : 𝟙_ (Underlying K (SVec K)) ≅ (toSVec K).obj (𝟙_ (SKar K (UnitSupercat K))) :=
  Underlying.isoMk (SVec.isoOfLinearEquiv εEquiv) εEquiv_hom_mem

end Field

/-! ## Coherence -/

section Coherence

variable {K : Type u} [Field K]

theorem vecMul_scalMat_permMat {ι κ : Type} [Fintype ι] [Fintype κ] {X : ι → D K} {Y : κ → D K}
    (e : ι ≃ κ) (φ : ∀ i, X i ⟶ Y (e i)) (hφ : ∀ i, scal (φ i) = 1) (u : ι → K) (j : κ) :
    (u ᵥ* scalMat (Mat_.permMat e φ)) j = u (e.symm j) := by
  classical
  rw [show scalMat (Mat_.permMat e φ) = fun i j => if e i = j then 1 else 0 from
    funext₂ (scalMat_permMat e φ hφ), vecMul_perm]

/-- The associator of `Mat_(I̲_π)` acts on `⊕ Π^{aᵢ+bⱼ+cₗ} K` by reindexing. -/
theorem matHom_associator_hom (M N P : Mat_ (D K)) (y : ((M ⊗ N) ⊗ P).ι → K)
    (x : (M ⊗ (N ⊗ P)).ι) :
    matHom (α_ M N P).hom y x = y ((Equiv.prodAssoc M.ι N.ι P.ι).symm x) := by
  rw [matHom_apply]
  exact vecMul_scalMat_permMat (Y := (M ⊗ (N ⊗ P)).X) (Equiv.prodAssoc M.ι N.ι P.ι)
    (fun z => (α_ (M.X z.1.1) (N.X z.1.2) (P.X z.2)).hom) (fun _ => rfl) y x

/-- The left unitor of `Mat_(I̲_π)` acts by reindexing. -/
theorem matHom_leftUnitor_hom (M : Mat_ (D K)) (y : (𝟙_ (Mat_ (D K)) ⊗ M).ι → K) (i : M.ι) :
    matHom (λ_ M).hom y i = y ((Equiv.punitProd M.ι).symm i) := by
  rw [matHom_apply]
  exact vecMul_scalMat_permMat (Equiv.punitProd M.ι) (fun x => (λ_ (M.X x.2)).hom) (fun _ => rfl)
    y i

/-- The right unitor of `Mat_(I̲_π)` acts by reindexing. -/
theorem matHom_rightUnitor_hom (M : Mat_ (D K)) (y : (M ⊗ 𝟙_ (Mat_ (D K))).ι → K) (i : M.ι) :
    matHom (ρ_ M).hom y i = y ((Equiv.prodPUnit M.ι).symm i) := by
  rw [matHom_apply]
  exact vecMul_scalMat_permMat (Equiv.prodPUnit M.ι) (fun x => (ρ_ (M.X x.1)).hom) (fun _ => rfl)
    y i

theorem associator_hom_f (P Q R : SKar K (UnitSupercat K)) :
    (α_ P Q R).hom.f = (α_ P.X Q.X R.X).hom ≫ (P.p ⊗ (Q.p ⊗ R.p)) := rfl

theorem leftUnitor_hom_f (P : SKar K (UnitSupercat K)) :
    (λ_ P).hom.f = (λ_ P.X).hom ≫ P.p := rfl

theorem rightUnitor_hom_f (P : SKar K (UnitSupercat K)) :
    (ρ_ P).hom.f = (ρ_ P.X).hom ≫ P.p := rfl

theorem matHom_associator_hom_f (P Q R : SKar K (UnitSupercat K))
    (y : (freeObj ((P ⊗ Q) ⊗ R).X).carrier) :
    matHom (α_ P Q R).hom.f y = matHom (P.p ⊗ (Q.p ⊗ R.p)) (matHom (α_ P.X Q.X R.X).hom y) :=
  congrArg (fun φ => φ y) (matHom_comp (α_ P.X Q.X R.X).hom (P.p ⊗ (Q.p ⊗ R.p)))

theorem matHom_leftUnitor_hom_f (P : SKar K (UnitSupercat K))
    (y : (freeObj (𝟙_ (SKar K (UnitSupercat K)) ⊗ P).X).carrier) :
    matHom (λ_ P).hom.f y = matHom P.p (matHom (λ_ P.X).hom y) :=
  congrArg (fun φ => φ y) (matHom_comp (λ_ P.X).hom P.p)

theorem matHom_rightUnitor_hom_f (P : SKar K (UnitSupercat K))
    (y : (freeObj (P ⊗ 𝟙_ (SKar K (UnitSupercat K))).X).carrier) :
    matHom (ρ_ P).hom.f y = matHom P.p (matHom (ρ_ P.X).hom y) :=
  congrArg (fun φ => φ y) (matHom_comp (ρ_ P.X).hom P.p)

theorem tensor_p_apply_tmul (P Q : SKar K (UnitSupercat K)) (v : imgSubmodule P)
    (w : imgSubmodule Q) :
    matHom (P.p ⊗ Q.p) (tmulFun P.X.ι Q.X.ι (v.1 ⊗ₜ w.1)) = tmulFun P.X.ι Q.X.ι (v.1 ⊗ₜ w.1) :=
  mem_imgSubmodule.1 (μLin_mem P Q (v ⊗ₜ w))

/-- Naturality of the tensorator with respect to tensor products of morphisms. -/
theorem μIso_natural {P P' Q Q' : SKar K (UnitSupercat K)} (φ : P ⟶ P') (ψ : Q ⟶ Q')
    (t : imgSubmodule P ⊗[K] imgSubmodule Q) :
    (μIso P' Q').hom.1 (TensorProduct.map (SVec.toLinearMap ((toSVec K).map φ).1)
      (SVec.toLinearMap ((toSVec K).map ψ).1) t) =
      ((toSVec K).map (φ ⊗ ψ)).1 ((μIso P Q).hom.1 t) := by
  apply Subtype.ext
  rw [μIso_hom_apply_coe, toSVec_map_apply, μIso_hom_apply_coe]
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero]
    exact (LinearMap.map_zero (matHom (φ ⊗ ψ).f)).symm
  | tmul v w =>
    rw [TensorProduct.map_tmul]
    change tmulFun _ _ (matHom φ.f v.1 ⊗ₜ matHom ψ.f w.1) =
      matHom (φ.f ⊗ ψ.f) (tmulFun _ _ (v.1 ⊗ₜ w.1))
    rw [matHom_tensor_apply, TensorProduct.map_tmul]
    rfl
  | add t t' h h' =>
    rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add]
    erw [LinearMap.map_add (matHom (φ ⊗ ψ).f)]
    exact congrArg₂ (· + ·) h h'

theorem toSVec_map_id_toLinearMap (P : SKar K (UnitSupercat K)) :
    SVec.toLinearMap ((toSVec K).map (𝟙 P)).1 = LinearMap.id := by
  rw [CategoryTheory.Functor.map_id]; rfl

/-- Associativity of the tensorator. -/
theorem μIso_associativity (P Q R : SKar K (UnitSupercat K)) :
    (μIso P Q).hom ▷ (toSVec K).obj R ≫ (μIso (P ⊗ Q) R).hom ≫ (toSVec K).map (α_ P Q R).hom =
        (α_ ((toSVec K).obj P) ((toSVec K).obj Q) ((toSVec K).obj R)).hom ≫
          (toSVec K).obj P ◁ (μIso Q R).hom ≫ (μIso P (Q ⊗ R)).hom := by
  apply Underlying.hom_ext
  apply SVec.hom_ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t t' h h' => rw [map_add, map_add, h, h']
  | tmul t u =>
    induction t using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
    | add t t' h h' => rw [TensorProduct.add_tmul, map_add, map_add, h, h']
    | tmul v w =>
      simp only [Underlying.comp_val, Underlying.whiskerRight_val, Underlying.whiskerLeft_val,
        Underlying.associator_hom_val]
      erw [SVec.comp_apply, SVec.comp_apply, SVec.comp_apply, SVec.comp_apply]
      change ((toSVec K).map (α_ P Q R).hom).1 ((μIso (P ⊗ Q) R).hom.1
        ((μIso P Q).hom.1 (v ⊗ₜ w) ⊗ₜ u)) = (μIso P (Q ⊗ R)).hom.1
          ((SVec.whiskerLeft (imgObj P) (μIso Q R).hom.1) (v ⊗ₜ (w ⊗ₜ u)))
      rw [SVec.whiskerLeft_of_mem _ (μIso Q R).hom.2, SVec.sgn_zero]
      apply Subtype.ext
      rw [toSVec_map_apply, μIso_hom_apply_coe]
      refine (matHom_associator_hom_f P Q R _).trans ?_
      have e1 : matHom (α_ P.X Q.X R.X).hom (μLin (P ⊗ Q) R ((μIso P Q).hom.1 (v ⊗ₜ w) ⊗ₜ u)) =
          tmulFun P.X.ι (Q.X.ι × R.X.ι) (v.1 ⊗ₜ tmulFun Q.X.ι R.X.ι (w.1 ⊗ₜ u.1)) := by
        funext x
        refine (matHom_associator_hom P.X Q.X R.X _ x).trans ?_
        change (v.1 x.1 * w.1 x.2.1) * u.1 x.2.2 = v.1 x.1 * (w.1 x.2.1 * u.1 x.2.2)
        rw [mul_assoc]
      rw [e1]
      refine (matHom_tensor_apply P.p (Q.p ⊗ R.p) _).trans ?_
      rw [TensorProduct.map_tmul]
      refine (congrArg (tmulFun P.X.ι (Q.X.ι × R.X.ι)) (congrArg₂ (fun a b => a ⊗ₜ[K] b)
        (mem_imgSubmodule.1 v.2) (tensor_p_apply_tmul Q R w u))).trans ?_
      rfl

/-- Left unitality of the tensorator. -/
theorem μIso_left_unitality (P : SKar K (UnitSupercat K)) :
    (λ_ ((toSVec K).obj P)).hom = εIso.hom ▷ (toSVec K).obj P ≫
      (μIso (𝟙_ (SKar K (UnitSupercat K))) P).hom ≫ (toSVec K).map (λ_ P).hom := by
  apply Underlying.hom_ext
  apply SVec.hom_ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t t' h h' => rw [map_add, map_add, h, h']
  | tmul c v =>
    simp only [Underlying.comp_val, Underlying.whiskerRight_val, Underlying.leftUnitor_hom_val]
    erw [SVec.comp_apply, SVec.comp_apply, SVec.leftUnitor_hom_tmul]
    change c • v = ((toSVec K).map (λ_ P).hom).1
      ((μIso (𝟙_ (SKar K (UnitSupercat K))) P).hom.1 (εIso.hom.1 c ⊗ₜ v))
    apply Subtype.ext
    rw [toSVec_map_apply, μIso_hom_apply_coe]
    change (c • v).1 = matHom ((λ_ P.X).hom ≫ P.p)
      (μLin (𝟙_ (SKar K (UnitSupercat K))) P (εIso.hom.1 c ⊗ₜ v))
    rw [matHom_comp, SVec.comp_apply]
    have e1 : matHom (λ_ P.X).hom (μLin (𝟙_ (SKar K (UnitSupercat K))) P (εIso.hom.1 c ⊗ₜ v)) =
        c • v.1 := by
      funext i
      exact matHom_leftUnitor_hom P.X _ i
    rw [e1, LinearMap.map_smul, mem_imgSubmodule.1 v.2]
    rfl


/-- Right unitality of the tensorator. -/
theorem μIso_right_unitality (P : SKar K (UnitSupercat K)) :
    (ρ_ ((toSVec K).obj P)).hom = (toSVec K).obj P ◁ εIso.hom ≫
      (μIso P (𝟙_ (SKar K (UnitSupercat K)))).hom ≫ (toSVec K).map (ρ_ P).hom := by
  apply Underlying.hom_ext
  apply SVec.hom_ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t t' h h' => rw [map_add, map_add, h, h']
  | tmul v c =>
    simp only [Underlying.comp_val, Underlying.whiskerLeft_val, Underlying.rightUnitor_hom_val]
    erw [SVec.comp_apply, SVec.comp_apply, SVec.rightUnitor_hom_tmul]
    change c • v = ((toSVec K).map (ρ_ P).hom).1 ((μIso P (𝟙_ (SKar K (UnitSupercat K)))).hom.1
      ((SVec.whiskerLeft (imgObj P) εIso.hom.1) (v ⊗ₜ c)))
    rw [SVec.whiskerLeft_of_mem _ εIso.hom.2, SVec.sgn_zero]
    apply Subtype.ext
    rw [toSVec_map_apply, μIso_hom_apply_coe]
    change (c • v).1 = matHom ((ρ_ P.X).hom ≫ P.p)
      (μLin P (𝟙_ (SKar K (UnitSupercat K))) (v ⊗ₜ εIso.hom.1 c))
    rw [matHom_comp, SVec.comp_apply]
    have e1 : matHom (ρ_ P.X).hom (μLin P (𝟙_ (SKar K (UnitSupercat K))) (v ⊗ₜ εIso.hom.1 c)) =
        c • v.1 := by
      funext i
      refine (matHom_rightUnitor_hom P.X _ i).trans ?_
      change v.1 i * c = c * v.1 i
      rw [mul_comm]
    rw [e1, LinearMap.map_smul, mem_imgSubmodule.1 v.2]
    rfl


/-- **Brundan–Ellis, Example 1.17(ii).** The functor `SKar(I) ⥤ SVec̲` is monoidal: the
tensorator `F(P) ⊗ F(Q) ≅ F(P ⊗ Q)` is `v ⊗ w ↦ ((i, j) ↦ vᵢ wⱼ)` and the unit constraint is
`K ≅ F(𝟙)`. -/
def toSVecCoreMonoidal : (toSVec K).CoreMonoidal where
  εIso := εIso
  μIso := μIso
  μIso_hom_natural_left {P P'} φ Q := by
    apply Underlying.hom_ext
    apply SVec.hom_ext
    intro t
    change (μIso P' Q).hom.1 (TensorProduct.map (SVec.toLinearMap ((toSVec K).map φ).1)
      LinearMap.id t) = ((toSVec K).map (φ ▷ Q)).1 ((μIso P Q).hom.1 t)
    rw [show φ ▷ Q = φ ⊗ 𝟙 Q from rfl, ← μIso_natural φ (𝟙 Q) t, toSVec_map_id_toLinearMap]
  μIso_hom_natural_right {Q Q'} P ψ := by
    apply Underlying.hom_ext
    apply SVec.hom_ext
    intro t
    change (μIso P Q').hom.1 ((SVec.whiskerLeft (imgObj P) ((toSVec K).map ψ).1) t) =
      ((toSVec K).map (P ◁ ψ)).1 ((μIso P Q).hom.1 t)
    rw [SVec.whiskerLeft_of_mem _ ((toSVec K).map ψ).2, SVec.sgn_zero,
      show P ◁ ψ = 𝟙 P ⊗ ψ from rfl, ← μIso_natural (𝟙 P) ψ t, toSVec_map_id_toLinearMap]
    rfl
  associativity := μIso_associativity
  left_unitality := μIso_left_unitality
  right_unitality := μIso_right_unitality

/-- **Brundan–Ellis, Example 1.17(ii).** `SKar(I) ⥤ SVec̲` is a monoidal functor; together with
`toSVec_full`, `toSVec_faithful` and `exists_iso_toSVec_obj`, `SKar(I)` is monoidally
equivalent to `SVec_fd`. -/
instance toSVecMonoidal : (toSVec K).Monoidal := toSVecCoreMonoidal.toMonoidal

end Coherence

end StringDiagrams.SKarUnit

end
