import StringDiagrams.Super.SVec

/-!
# The product `A ⊠ B` of supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, the
paragraph after Example 1.2: for supercategories `A` and `B`, the supercategory `A ⊠ B` has
objects the pairs `(λ, μ)` of objects of `A` and `B`, morphism superspaces
`Hom((λ, μ), (σ, τ)) := Hom_A(λ, σ) ⊗ Hom_B(μ, τ)`, and composition defined using the symmetric
braiding of `SVec`, so that `(f ⊗ g) ∘ (h ⊗ k) = (-1)^{|g||h|} (f ∘ h) ⊗ (g ∘ k)`: the sign
involves the two middle factors.

We construct `A ⊠ B` for supercategories over `k` whose morphism modules live in the universe
of `k`, so that the morphism superspaces `Supercategory.homSVec` are superspaces in the sense
of `StringDiagrams.SVec` and `Hom_A(λ, σ) ⊗ Hom_B(μ, τ)` is their tensor product
`SVec.tensorObj`. The composition rule for homogeneous morphisms is
`BoxProd.tmulHom_comp_tmulHom`; in diagrammatic order `x ≫ y = y ∘ x` it reads
`(f ⊗ g) ≫ (h ⊗ l) = (-1)^{|f||l|} (f ≫ h) ⊗ (g ≫ l)`.

## Main definitions

* `Supercategory.homSVec C X Y`: the morphism superspace `Hom(X, Y)` of a supercategory.
* `BoxProd k C D`, with its instances `Category`, `Preadditive`, `Linear k` and `Supercategory k`
  (the morphisms of parity `p` are the elements of parity `p` of the tensor product of
  superspaces).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory TensorProduct

universe u w₁ w₂

variable {k : Type u} [CommRing k]

namespace Supercategory

variable (k) (C : Type w₁) [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

/-- The morphism superspace `Hom(X, Y)` of a supercategory whose morphism modules live in the
universe of `k`. -/
abbrev homSVec (X Y : C) : SVec k where
  carrier := X ⟶ Y
  odd := proj k 1
  odd_comp_odd := LinearMap.ext fun f => proj_proj 1 f

variable {C}

theorem homSVec_proj (X Y : C) (p : ZMod 2) : (homSVec k C X Y).proj p = proj k p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SVec.proj_zero]
    ext f
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    exact (eq_sub_of_add_eq (proj_add_proj f)).symm
  · rfl

theorem mem_homSVec_part_iff {X Y : C} {p : ZMod 2} {f : X ⟶ Y} :
    f ∈ (homSVec k C X Y).part p ↔ f ∈ parity (R := k) X Y p := by
  rw [SVec.mem_part_iff, homSVec_proj]
  exact (mem_iff_proj (R := k)).symm

end Supercategory

/-- The product `C ⊠ D` of two supercategories over `k` (Brundan–Ellis, after Example 1.2):
objects are pairs of objects. (The ground ring is part of the type.) -/
@[nolint unusedArguments]
structure BoxProd (k : Type u) [CommRing k] (C : Type w₁) (D : Type w₂) where
  /-- The first component. -/
  fst : C
  /-- The second component. -/
  snd : D

namespace BoxProd

variable {C : Type w₁} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  {D : Type w₂} [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]

variable (k) in
/-- The morphism superspace `Hom_C(X₁, Y₁) ⊗ Hom_D(X₂, Y₂)` of `C ⊠ D`. -/
abbrev homObj (X Y : BoxProd k C D) : SVec k :=
  SVec.tensorObj (homSVec k C X.fst Y.fst) (homSVec k D X.snd Y.snd)

/-! ## Composition -/

section Comp

variable (X Y Z : BoxProd k C D)

/-- `f ↦ h ↦ f_q ≫ h`. -/
def projComp (q : ZMod 2) : (X.fst ⟶ Y.fst) →ₗ[k] (Y.fst ⟶ Z.fst) →ₗ[k] (X.fst ⟶ Z.fst) :=
  (Linear.comp (S := k) X.fst Y.fst Z.fst) ∘ₗ proj k q

/-- `g ↦ l ↦ g ≫ (l₀ + (-1)^q l₁)`. -/
def sgnComp (q : ZMod 2) : (X.snd ⟶ Y.snd) →ₗ[k] (Y.snd ⟶ Z.snd) →ₗ[k] (X.snd ⟶ Z.snd) :=
  (Linear.comp (S := k) X.snd Y.snd Z.snd).compl₂ (twist k q)

omit [Category.{u, w₂} D] [Preadditive D] [Linear k D] [Supercategory k D] in
theorem projComp_apply (q : ZMod 2) (f : X.fst ⟶ Y.fst) (h : Y.fst ⟶ Z.fst) :
    projComp X Y Z q f h = proj k q f ≫ h := rfl

omit [Category.{u, w₁} C] [Preadditive C] [Linear k C] [Supercategory k C] in
theorem sgnComp_apply (q : ZMod 2) (g : X.snd ⟶ Y.snd) (l : Y.snd ⟶ Z.snd) :
    sgnComp X Y Z q g l = g ≫ twist k q l := rfl

/-- The quadrilinear map `(f, g, h, l) ↦ (f_q ≫ h) ⊗ (g ≫ (l₀ + (-1)^q l₁))`. -/
def quadMap (q : ZMod 2) : (X.fst ⟶ Y.fst) →ₗ[k] (X.snd ⟶ Y.snd) →ₗ[k] (Y.fst ⟶ Z.fst) →ₗ[k]
    (Y.snd ⟶ Z.snd) →ₗ[k] homObj k X Z :=
  LinearMap.mk₂ k
    (fun f g => (TensorProduct.mk k (homSVec k C X.fst Z.fst) (homSVec k D X.snd Z.snd)).compl₁₂
      (projComp X Y Z q f) (sgnComp X Y Z q g))
    (fun f f' g => by
      ext h l
      simp only [LinearMap.compl₁₂_apply, LinearMap.add_apply, map_add, TensorProduct.mk_apply])
    (fun r f g => by
      ext h l
      simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, map_smul, TensorProduct.mk_apply,
        smul_tmul'])
    (fun f g g' => by
      ext h l
      simp only [LinearMap.compl₁₂_apply, LinearMap.add_apply, map_add, TensorProduct.mk_apply])
    (fun r g g' => by
      ext h l
      simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, map_smul, TensorProduct.mk_apply])

theorem quadMap_apply (q : ZMod 2) (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) (h : Y.fst ⟶ Z.fst)
    (l : Y.snd ⟶ Z.snd) :
    quadMap X Y Z q f g h l = (proj k q f ≫ h) ⊗ₜ[k] (g ≫ twist k q l) := rfl

/-- Composition in `C ⊠ D`, as a bilinear map:
`(f ⊗ g) ≫ (h ⊗ l) = Σ_q (f_q ≫ h) ⊗ (g ≫ (l₀ + (-1)^q l₁))`. -/
def compMap : homObj k X Y →ₗ[k] homObj k Y Z →ₗ[k] homObj k X Z :=
  (TensorProduct.uncurry (RingHom.id k) (homSVec k C Y.fst Z.fst) (homSVec k D Y.snd Z.snd)
    (homObj k X Z)) ∘ₗ
    TensorProduct.lift (quadMap X Y Z 0 + quadMap X Y Z 1)

theorem compMap_tmul_tmul (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) (h : Y.fst ⟶ Z.fst)
    (l : Y.snd ⟶ Z.snd) :
    compMap X Y Z (f ⊗ₜ g) (h ⊗ₜ l) =
      (proj k 0 f ≫ h) ⊗ₜ[k] (g ≫ l) + (proj k 1 f ≫ h) ⊗ₜ[k] (g ≫ twist k 1 l) := by
  simp only [compMap, LinearMap.comp_apply, TensorProduct.lift.tmul, TensorProduct.uncurry_apply,
    LinearMap.add_apply]
  rw [quadMap_apply, quadMap_apply, twist_zero]

/-- **The composition rule of `C ⊠ D`** for homogeneous `f`, `l`:
`(f ⊗ g) ≫ (h ⊗ l) = (-1)^{|f||l|} (f ≫ h) ⊗ (g ≫ l)`. -/
theorem compMap_tmul_of_mem {p r : ZMod 2} {f : X.fst ⟶ Y.fst}
    (hf : f ∈ parity (R := k) X.fst Y.fst p) (g : X.snd ⟶ Y.snd) (h : Y.fst ⟶ Z.fst)
    {l : Y.snd ⟶ Z.snd} (hl : l ∈ parity (R := k) Y.snd Z.snd r) :
    compMap X Y Z (f ⊗ₜ g) (h ⊗ₜ l) = koszulSign p r • ((f ≫ h) ⊗ₜ[k] (g ≫ l)) := by
  rw [compMap_tmul_tmul, koszulSign_smul (R := k), twist_one_of_mem hl, Linear.comp_smul]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [proj_of_mem hf, proj_of_mem_ne hf (by decide), Limits.zero_comp, zero_tmul, add_zero,
      zero_mul, sign_zero, one_smul]
  · rw [proj_of_mem hf, proj_of_mem_ne hf (by decide), Limits.zero_comp, zero_tmul, zero_add,
      one_mul, tmul_smul]

end Comp

/-! ## The category `C ⊠ D` -/

/-- Linear maps out of `Hom((X₁, X₂), (Y₁, Y₂))` are determined by their values on the tensors
`f ⊗ g` of homogeneous morphisms. -/
theorem hom_ext_homogeneous {X Y : BoxProd k C D} {M : Type u} [AddCommGroup M] [Module k M]
    {φ ψ : homObj k X Y →ₗ[k] M}
    (h : ∀ (p q : ZMod 2) (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd), f ∈ parity (R := k) X.fst Y.fst p →
      g ∈ parity (R := k) X.snd Y.snd q → φ (f ⊗ₜ g) = ψ (f ⊗ₜ g)) : φ = ψ :=
  SVec.ext_tensor fun p q f g hf hg =>
    h p q f g ((mem_homSVec_part_iff k).1 hf) ((mem_homSVec_part_iff k).1 hg)

set_option linter.unusedVariables false in
/-- Induction on `Hom((X₁, X₂), (Y₁, Y₂))` with homogeneous generators. -/
theorem induction_on_homogeneous {X Y : BoxProd k C D} {P : homObj k X Y → Prop} (x : homObj k X Y)
    (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd), f ∈ parity (R := k) X.fst Y.fst p →
      g ∈ parity (R := k) X.snd Y.snd q → P (f ⊗ₜ g))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using TensorProduct.inductionOn with
  | tmul f g =>
    rw [← proj_add_proj (R := k) f, ← proj_add_proj (R := k) g, add_tmul, tmul_add, tmul_add]
    exact add _ _ (add _ _ (tmul 0 0 _ _ (proj_mem 0 f) (proj_mem 0 g))
        (tmul 0 1 _ _ (proj_mem 0 f) (proj_mem 1 g)))
      (add _ _ (tmul 1 0 _ _ (proj_mem 1 f) (proj_mem 0 g))
        (tmul 1 1 _ _ (proj_mem 1 f) (proj_mem 1 g)))
  | add x y hx hy => exact add x y hx hy

instance instCategory : Category.{u} (BoxProd k C D) where
  Hom X Y := homObj k X Y
  id X := 𝟙 X.fst ⊗ₜ 𝟙 X.snd
  comp {X Y Z} x y := compMap X Y Z x y
  id_comp {X Y} x := by
    refine LinearMap.congr_fun (hom_ext_homogeneous (φ := compMap X X Y (𝟙 X.fst ⊗ₜ 𝟙 X.snd))
      (ψ := LinearMap.id) fun p q h l hh hl => ?_) x
    rw [compMap_tmul_of_mem _ _ _ (id_mem X.fst) _ _ hl, koszulSign_zero_left, one_smul,
      Category.id_comp, Category.id_comp, LinearMap.id_apply]
  comp_id {X Y} x := by
    refine LinearMap.congr_fun (hom_ext_homogeneous (φ := (compMap X Y Y).flip (𝟙 Y.fst ⊗ₜ 𝟙 Y.snd))
      (ψ := LinearMap.id) fun p q f g hf hg => ?_) x
    rw [LinearMap.flip_apply, compMap_tmul_of_mem _ _ _ hf _ _ (id_mem Y.snd), koszulSign_zero_right,
      one_smul, Category.comp_id, Category.comp_id, LinearMap.id_apply]
  assoc {W X Y Z} x y z := by
    induction x using induction_on_homogeneous with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | tmul a b f g hf hg =>
      induction y using induction_on_homogeneous with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | tmul c d h l hh hl =>
        induction z using induction_on_homogeneous with
        | zero => simp only [map_zero]
        | add z z' hz hz' => simp only [map_add, hz, hz']
        | tmul e e' m n hm hn =>
          rw [compMap_tmul_of_mem _ _ _ hf _ _ hl, compMap_tmul_of_mem _ _ _ hh _ _ hn,
            koszulSign_smul (R := k), koszulSign_smul (R := k), map_smul, LinearMap.smul_apply,
            map_smul, compMap_tmul_of_mem _ _ _ (comp_mem hf hh) _ _ hn,
            compMap_tmul_of_mem _ _ _ hf _ _ (comp_mem hl hn), koszulSign_smul (R := k),
            koszulSign_smul (R := k), smul_smul, smul_smul, ← sign_add, ← sign_add,
            Category.assoc, Category.assoc]
          congr 2
          ring

theorem hom_def (X Y : BoxProd k C D) : (X ⟶ Y) = homObj k X Y := rfl

theorem id_def (X : BoxProd k C D) : 𝟙 X = 𝟙 X.fst ⊗ₜ[k] 𝟙 X.snd := rfl

theorem comp_def {X Y Z : BoxProd k C D} (x : X ⟶ Y) (y : Y ⟶ Z) : x ≫ y = compMap X Y Z x y := rfl

instance : Preadditive (BoxProd k C D) where
  homGroup X Y := inferInstanceAs (AddCommGroup (homObj k X Y))
  add_comp P Q R x x' y :=
    (LinearMap.congr_fun ((compMap P Q R).map_add x x') y).trans (LinearMap.add_apply _ _ _)
  comp_add P Q R x y y' := (compMap P Q R x).map_add y y'

instance : Linear k (BoxProd k C D) where
  homModule X Y := inferInstanceAs (Module k (homObj k X Y))
  smul_comp P Q R r x y :=
    (LinearMap.congr_fun ((compMap P Q R).map_smul r x) y).trans (LinearMap.smul_apply _ _ _)
  comp_smul P Q R x r y := (compMap P Q R x).map_smul r y

/-- The morphism `f ⊗ g : (X₁, X₂) ⟶ (Y₁, Y₂)` of `C ⊠ D`. -/
def tmulHom {X Y : BoxProd k C D} (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) : X ⟶ Y := f ⊗ₜ[k] g

theorem tmulHom_def {X Y : BoxProd k C D} (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) :
    tmulHom f g = (f ⊗ₜ[k] g : homObj k X Y) := rfl

theorem id_eq_tmulHom (X : BoxProd k C D) : 𝟙 X = tmulHom (𝟙 X.fst) (𝟙 X.snd) := rfl

theorem tmulHom_add_left {X Y : BoxProd k C D} (f f' : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) :
    tmulHom (f + f') g = tmulHom f g + tmulHom f' g :=
  add_tmul f f' g

theorem tmulHom_add_right {X Y : BoxProd k C D} (f : X.fst ⟶ Y.fst) (g g' : X.snd ⟶ Y.snd) :
    tmulHom f (g + g') = tmulHom f g + tmulHom f g' :=
  tmul_add f g g'

theorem tmulHom_smul_left {X Y : BoxProd k C D} (r : k) (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) :
    tmulHom (r • f) g = r • tmulHom f g :=
  (smul_tmul' r f g).symm

theorem tmulHom_smul_right {X Y : BoxProd k C D} (r : k) (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) :
    tmulHom f (r • g) = r • tmulHom f g :=
  tmul_smul r f g

/-- **The composition rule of `C ⊠ D`** (Brundan–Ellis, after Example 1.2): the paper's
`(f ⊗ g) ∘ (h ⊗ l) = (-1)^{|g||h|} (f ∘ h) ⊗ (g ∘ l)` reads, in diagrammatic order,
`(f ⊗ g) ≫ (h ⊗ l) = (-1)^{|f||l|} (f ≫ h) ⊗ (g ≫ l)` for homogeneous `f`, `l`. -/
theorem tmulHom_comp_tmulHom {X Y Z : BoxProd k C D} {p r : ZMod 2} {f : X.fst ⟶ Y.fst}
    (hf : f ∈ parity (R := k) X.fst Y.fst p) (g : X.snd ⟶ Y.snd) (h : Y.fst ⟶ Z.fst)
    {l : Y.snd ⟶ Z.snd} (hl : l ∈ parity (R := k) Y.snd Z.snd r) :
    tmulHom f g ≫ tmulHom h l = koszulSign p r • tmulHom (f ≫ h) (g ≫ l) :=
  compMap_tmul_of_mem X Y Z hf g h hl

/-! ## The supercategory `C ⊠ D` -/

theorem tmul_mem_part {X Y : BoxProd k C D} {p q : ZMod 2} {f : X.fst ⟶ Y.fst} {g : X.snd ⟶ Y.snd}
    (hf : f ∈ parity (R := k) X.fst Y.fst p) (hg : g ∈ parity (R := k) X.snd Y.snd q) :
    (f ⊗ₜ g : X ⟶ Y) ∈ (homObj k X Y).part (p + q) :=
  SVec.tmul_mem_part ((mem_homSVec_part_iff k).2 hf) ((mem_homSVec_part_iff k).2 hg)

theorem compMap_proj_proj_mem {X Y Z : BoxProd k C D} (p q : ZMod 2) (x : X ⟶ Y) (y : Y ⟶ Z) :
    compMap X Y Z ((homObj k X Y).proj p x) ((homObj k Y Z).proj q y) ∈
      (homObj k X Z).part (p + q) := by
  induction x using induction_on_homogeneous with
  | zero => rw [map_zero, map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add x x' hx hx' => rw [map_add, map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hx'
  | tmul a b f g hf hg =>
    induction y using induction_on_homogeneous with
    | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
    | add y y' hy hy' => rw [map_add, map_add]; exact Submodule.add_mem _ hy hy'
    | tmul c d h l hh hl =>
      rw [SVec.proj_apply_of_mem_part _ (tmul_mem_part hf hg),
        SVec.proj_apply_of_mem_part _ (tmul_mem_part hh hl)]
      split_ifs with h1 h2 h2
      · rw [compMap_tmul_of_mem _ _ _ hf _ _ hl]
        refine Submodule.smul_of_tower_mem _ _ ?_
        have := tmul_mem_part (comp_mem hf hh) (comp_mem hg hl)
        rwa [h1, h2, add_add_add_comm]
      · simp only [map_zero]; exact Submodule.zero_mem _
      · simp only [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
      · simp only [map_zero]; exact Submodule.zero_mem _

/-- **Brundan–Ellis, after Example 1.2.** `C ⊠ D` is a supercategory: the morphisms of parity
`p` are the elements of parity `p` of the tensor product of superspaces
`Hom_C(X₁, Y₁) ⊗ Hom_D(X₂, Y₂)`. -/
instance instSupercategory : Supercategory k (BoxProd k C D) where
  parity X Y p := (homObj k X Y).part p
  isInternal X Y := SVec.isInternal_part (homObj k X Y)
  id_mem X := by simpa using! tmul_mem_part (id_mem X.fst) (id_mem X.snd)
  comp_mem {X Y Z p q x y} hx hy := by
    have := compMap_proj_proj_mem p q x y
    rwa [(SVec.mem_part_iff _).1 hx, (SVec.mem_part_iff _).1 hy] at this

theorem mem_parity_iff {X Y : BoxProd k C D} {p : ZMod 2} {x : X ⟶ Y} :
    x ∈ parity (R := k) X Y p ↔ x ∈ (homObj k X Y).part p := Iff.rfl

/-- `f ⊗ g` has parity `|f| + |g|`. -/
theorem tmul_mem_parity {X Y : BoxProd k C D} {p q : ZMod 2} {f : X.fst ⟶ Y.fst} {g : X.snd ⟶ Y.snd}
    (hf : f ∈ parity (R := k) X.fst Y.fst p) (hg : g ∈ parity (R := k) X.snd Y.snd q) :
    (f ⊗ₜ g : X ⟶ Y) ∈ parity (R := k) X Y (p + q) :=
  tmul_mem_part hf hg

end BoxProd

end StringDiagrams

end
