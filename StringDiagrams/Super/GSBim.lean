import StringDiagrams.Super.GSMod
import StringDiagrams.Super.GSVecMonoidal
import StringDiagrams.Super.SBim
import StringDiagrams.Super.GradedTwo

/-!
# The graded 2-supercategory `𝔊𝔖𝔅𝔦𝔪` of graded superbimodules

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6 (after
Definition 6.2): the graded 2-supercategory `𝔊𝔖𝔅𝔦𝔪` whose objects are graded superalgebras,
whose morphism supercategories are `ℋom(A, B) := B-GSMod-A` (`StringDiagrams.Super.GSMod`), and
whose horizontal composition is the tensor product.

* The graded balanced tensor product: for graded superbimodules `M` (over `(A, B)`) and `N`
  (over `(B, C)`), the balanced tensor product `M ⊗_B N` of `StringDiagrams.Super.BalancedTensor`
  with the grading `(M ⊗_B N)ₙ` = image of `(M ⊗_k N)ₙ = ⨁_{r+s=n} Mᵣ ⊗ Nₛ`
  (`GradedSuperBimodule.tensor`, `GradedSuperBimodule.tensorDeg`). That this is a grading of the
  quotient is proved by descending the projections of `M ⊗_k N` onto its homogeneous
  components (`GradedSuperspace.tensorProj`) to the quotient: the balancing relations form a
  homogeneous submodule (`GradedSuperBimodule.tensorProj_balance_mem`);
  `GradedSuperBimodule.isInternal_tensorDeg`. The generators `m ⊗ n` have degree `|m| + |n|`
  (`GradedSuperBimodule.btmul_mem_tensorDeg`).
* The whiskerings `f ⊗ 1`, `1 ⊗ g` of homogeneous homomorphisms are homogeneous of the same
  degree, and the associator and unitors of the balanced tensor product have degree `0`
  (`GradedSuperBimodule.whiskerRight_mem_degHom`, `whiskerLeft_mem_degHom`,
  `assoc_hom_mem_degHom`, `leftUnitor_hom_mem_degHom`, …); the regular graded superbimodule
  `GradedSuperBimodule.regular`.
* `GSuperAlg k`: graded superalgebras (bundled, extending `SuperAlg k`), with the structure of
  a graded 2-supercategory `𝔊𝔖𝔅𝔦𝔪` (`GSuperAlg.instTwoSupercategory`,
  `GSuperAlg.instGradedTwoSupercategory`): `Hom(A, B) := GSMod B A` (the paper's `B-GSMod-A`),
  `M ≫ N := N ⊗_B M`, identities the regular graded superbimodules; the 2-supercategory axioms
  are those of `𝔖𝔅𝔦𝔪` (`StringDiagrams.Super.SBim`). As for `𝔖𝔅𝔦𝔪`, the coherence maps are not
  identities. The graded `(Q, Π)`-structures of the morphism supercategories `B-GSMod-A`
  (`StringDiagrams.Super.GSMod`) make `𝔊𝔖𝔅𝔦𝔪` a graded `(Q, Π)`-2-supercategory
  (`GSuperAlg.instQPiTwoSupercategory`, with `q_A`, `q_A⁻¹`, `π_A` the shifts of the regular
  graded superbimodule); this is not stated in the paper.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory TensorProduct SuperBimodule

universe u v v' v'' v'''

variable {k : Type u} [CommRing k]

/-! ## The graded balanced tensor product -/

section Tensor

variable {A : Type v} [Ring A] [Algebra k A] {B : Type v'} [Ring B] [Algebra k B]
  {C : Type v''} [Ring C] [Algebra k C] {D : Type v'''} [Ring D] [Algebra k D]
  {𝒢 : GradedSuperalgebra k A} {ℋ : GradedSuperalgebra k B} {𝒦 : GradedSuperalgebra k C}
  {𝒟 : GradedSuperalgebra k D}

namespace GradedSuperBimodule

/-- The bilinear map `(m, n) ↦ m ⊗ n` into the balanced tensor product. -/
def btmulBi {𝒜 : ZMod 2 → Submodule k A} {ℬ : ZMod 2 → Submodule k B}
    {𝒞 : ZMod 2 → Submodule k C} [GradedAlgebra ℬ] (M : SuperBimodule 𝒜 ℬ)
    (N : SuperBimodule ℬ 𝒞) : M.toSVec →ₗ[k] N.toSVec →ₗ[k] (SuperBimodule.tensor M N).toSVec :=
  (TensorProduct.mk k M.toSVec N.toSVec).compr₂ (SVec.toLinearMap (tensorMkHom M N))

@[simp] theorem btmulBi_apply {𝒜 : ZMod 2 → Submodule k A} {ℬ : ZMod 2 → Submodule k B}
    {𝒞 : ZMod 2 → Submodule k C} [GradedAlgebra ℬ] (M : SuperBimodule 𝒜 ℬ)
    (N : SuperBimodule ℬ 𝒞) (m : M.toSVec) (n : N.toSVec) :
    btmulBi M N m n = btmul M N m n := rfl

variable (M : GradedSuperBimodule 𝒢 ℋ) (N : GradedSuperBimodule ℋ 𝒦)

/-- The grading `(M ⊗_k N)ₙ = ⨁_{r+s=n} Mᵣ ⊗ Nₛ` of the tensor product over `k`. -/
abbrev tensorDegK (n : ℤ) :
    Submodule k (SVec.tensorObj M.toSuperBimodule.toSVec N.toSuperBimodule.toSVec) :=
  GradedSuperspace.tensorDeg M.toGradedSuperspace N.toGradedSuperspace n

set_option backward.isDefEq.respectTransparency false in
/-- The projection of `M ⊗_k N` onto `(M ⊗_k N)ₙ` carries the balancing elements into the
balancing relations: the balancing relations form a homogeneous submodule. -/
theorem tensorProj_balance_mem (n : ℤ) (m : M.toSuperBimodule.toSVec) (b : B)
    (x : N.toSuperBimodule.toSVec) :
    GradedSuperspace.tensorProj M.toGradedSuperspace N.toGradedSuperspace n
      (balance M.toSuperBimodule N.toSuperBimodule m b x) ∈
        balanceRel M.toSuperBimodule N.toSuperBimodule := by
  refine M.toGradedSuperspace.induction_on_deg m ?_ (fun r m hm => ?_) (fun m m' hm hm' => ?_)
  · rw [show balance M.toSuperBimodule N.toSuperBimodule 0 b x = 0 by simp [balance], map_zero]
    exact Submodule.zero_mem _
  · refine DirectSum.Decomposition.inductionOn ℋ.degree (motive := fun b =>
      GradedSuperspace.tensorProj M.toGradedSuperspace N.toGradedSuperspace n
        (balance M.toSuperBimodule N.toSuperBimodule m b x) ∈
          balanceRel M.toSuperBimodule N.toSuperBimodule) ?_ (fun {s} b => ?_)
      (fun b b' hb hb' => ?_) b
    · dsimp only
      rw [show balance M.toSuperBimodule N.toSuperBimodule m 0 x = 0 by simp [balance], map_zero]
      exact Submodule.zero_mem _
    · dsimp only
      refine N.toGradedSuperspace.induction_on_deg x ?_ (fun t x hx => ?_) (fun x x' hx hx' => ?_)
      · rw [show balance M.toSuperBimodule N.toSuperBimodule m b 0 = 0 by simp [balance], map_zero]
        exact Submodule.zero_mem _
      · rw [balance, map_sub,
          GradedSuperspace.tensorProj_tmul _ _ n (r + s) t (M.ract_mem b.2 hm) hx,
          GradedSuperspace.tensorProj_tmul _ _ n r (t + s) hm (N.lact_mem b.2 hx)]
        by_cases h : r + s + t = n
        · rw [ite_eq_left h, ite_eq_left (by omega)]
          exact balance_mem _ _ m b x
        · rw [ite_eq_right h, ite_eq_right (by omega), sub_zero]
          exact Submodule.zero_mem _
      · rw [balance_add_right, map_add]; exact Submodule.add_mem _ hx hx'
    · dsimp only at hb hb' ⊢
      rw [balance_add_middle, map_add]; exact Submodule.add_mem _ hb hb'
  · rw [balance_add_left, map_add]; exact Submodule.add_mem _ hm hm'

theorem balanceRel_tensorProj (n : ℤ) :
    ∀ x ∈ balanceRel M.toSuperBimodule N.toSuperBimodule,
      GradedSuperspace.tensorProj M.toGradedSuperspace N.toGradedSuperspace n x ∈
        balanceRel M.toSuperBimodule N.toSuperBimodule :=
  fun _ hx => balanceRel_le _ _ (S := (balanceRel M.toSuperBimodule N.toSuperBimodule).comap
    (GradedSuperspace.tensorProj M.toGradedSuperspace N.toGradedSuperspace n))
    (fun _ _ _ m b x _ _ _ => tensorProj_balance_mem M N n m b x) hx

/-- The projection of `M ⊗_B N` onto `(M ⊗_B N)ₙ`, descended from `M ⊗_k N`. -/
def tensorProjQ (n : ℤ) :
    (SuperBimodule.tensor M.toSuperBimodule N.toSuperBimodule).toSVec ⟶
      (SuperBimodule.tensor M.toSuperBimodule N.toSuperBimodule).toSVec :=
  SVec.quotMap (SVec.ofHom (GradedSuperspace.tensorProj M.toGradedSuperspace N.toGradedSuperspace n))
    (balanceRel_tensorProj M N n)

theorem tensorProjQ_tensorMk (n : ℤ)
    (x : SVec.tensorObj M.toSuperBimodule.toSVec N.toSuperBimodule.toSVec) :
    tensorProjQ M N n (tensorMk M.toSuperBimodule N.toSuperBimodule x) =
      tensorMk M.toSuperBimodule N.toSuperBimodule
        (GradedSuperspace.tensorProj M.toGradedSuperspace N.toGradedSuperspace n x) :=
  SVec.quotMap_mk _ _ x

/-- The grading of the balanced tensor product: `(M ⊗_B N)ₙ` is the image of `(M ⊗_k N)ₙ`. -/
def tensorDeg (n : ℤ) : Submodule k (SuperBimodule.tensor M.toSuperBimodule N.toSuperBimodule).toSVec :=
  (tensorDegK M N n).map (SVec.toLinearMap (tensorMkHom M.toSuperBimodule N.toSuperBimodule))

/-- `m ⊗ n` has degree `|m| + |n|`. -/
theorem btmul_mem_tensorDeg {r s : ℤ} {m : M.toSuperBimodule.toSVec} {x : N.toSuperBimodule.toSVec}
    (hm : m ∈ M.deg r) (hx : x ∈ N.deg s) :
    btmul M.toSuperBimodule N.toSuperBimodule m x ∈ tensorDeg M N (r + s) :=
  Submodule.mem_map_of_mem (GradedSuperspace.tmul_mem_tensorDeg _ _ hm hx)

set_option backward.isDefEq.respectTransparency false in
/-- `(M ⊗_B N)ₙ` is spanned by the `m ⊗ n` with `m ∈ Mᵣ`, `n ∈ Nₛ`, `r + s = n`. -/
theorem tensorDeg_le_iff {n : ℤ}
    {S : Submodule k (SuperBimodule.tensor M.toSuperBimodule N.toSuperBimodule).toSVec} :
    tensorDeg M N n ≤ S ↔ ∀ (r s : ℤ), r + s = n → ∀ m ∈ M.deg r, ∀ x ∈ N.deg s,
      btmul M.toSuperBimodule N.toSuperBimodule m x ∈ S := by
  rw [tensorDeg, Submodule.map_le_iff_le_comap, GradedSuperspace.tensorDeg_le_iff]
  exact Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- `M ⊗_B N = ⨁ₙ (M ⊗_B N)ₙ`. -/
theorem isInternal_tensorDeg : DirectSum.IsInternal (tensorDeg M N) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · refine iSupIndep_of_projections _ (fun n => SVec.toLinearMap (tensorProjQ M N n))
      (fun n => ?_) (fun n m hmn => ?_)
    · rw [tensorDeg, Submodule.map_le_iff_le_comap]
      intro x hx
      rw [Submodule.mem_comap, LinearMap.mem_eqLocus]
      change tensorProjQ M N n (tensorMk _ _ x) = tensorMk _ _ x
      rw [tensorProjQ_tensorMk, GradedSuperspace.tensorProj_of_mem _ _ hx]
    · rw [tensorDeg, Submodule.map_le_iff_le_comap]
      intro x hx
      rw [Submodule.mem_comap, LinearMap.mem_ker]
      change tensorProjQ M N n (tensorMk _ _ x) = 0
      rw [tensorProjQ_tensorMk, GradedSuperspace.tensorProj_of_mem_ne _ _ hmn hx, tensorMk_zero]
  · change ⨆ n, (tensorDegK M N n).map _ = ⊤
    rw [← Submodule.map_iSup, GradedSuperspace.iSup_tensorDeg_eq_top, Submodule.map_top,
      LinearMap.range_eq_top]
    exact tensorMk_surjective _ _

set_option backward.isDefEq.respectTransparency false in
/-- **Brundan–Ellis, §6.** The graded balanced tensor product `M ⊗_B N` of graded
superbimodules: the balanced tensor product with `(M ⊗_B N)ₙ` the image of
`⨁_{r+s=n} Mᵣ ⊗ Nₛ`. -/
def tensor : GradedSuperBimodule 𝒢 𝒦 where
  toSuperBimodule := SuperBimodule.tensor M.toSuperBimodule N.toSuperBimodule
  deg := tensorDeg M N
  isInternal_deg := isInternal_tensorDeg M N
  odd_mem {n x} hx := by
    have h : tensorDeg M N n ≤ (tensorDeg M N n).comap
        (SuperBimodule.tensor M.toSuperBimodule N.toSuperBimodule).toSVec.odd := by
      rw [tensorDeg, Submodule.map_le_iff_le_comap]
      intro y hy
      rw [Submodule.mem_comap, Submodule.mem_comap]
      change tensorMk _ _ ((SVec.tensorObj M.toSuperBimodule.toSVec N.toSuperBimodule.toSVec).odd y) ∈ _
      exact Submodule.mem_map_of_mem
        ((M.toGradedSuperspace.tensorObj N.toGradedSuperspace).odd_mem hy)
    exact h hx
  lact_mem {n a} ha {m x} hx := by
    have h : tensorDeg M N m ≤ (tensorDeg M N (m + n)).comap
        (SVec.toLinearMap ((SuperBimodule.tensor M.toSuperBimodule N.toSuperBimodule).lact a)) := by
      rw [tensorDeg, tensorDeg, Submodule.map_le_iff_le_comap]
      intro y hy
      rw [Submodule.mem_comap, Submodule.mem_comap]
      change tensorMk _ _ (SVec.whiskerRight (M.toSuperBimodule.lact a) N.toSuperBimodule.toSVec y) ∈ _
      exact Submodule.mem_map_of_mem
        (GradedSuperspace.whiskerRight_mem_degHom (M.lact_mem_degHom ha) N.toGradedSuperspace m y hy)
    exact h hx
  ract_mem {n c} hc {m x} hx := by
    have h : tensorDeg M N m ≤ (tensorDeg M N (m + n)).comap
        (SVec.toLinearMap ((SuperBimodule.tensor M.toSuperBimodule N.toSuperBimodule).ract c)) := by
      rw [tensorDeg, tensorDeg, Submodule.map_le_iff_le_comap]
      intro y hy
      rw [Submodule.mem_comap, Submodule.mem_comap]
      change tensorMk _ _ ((tensorK M.toSuperBimodule N.toSuperBimodule).ract c y) ∈ _
      refine Submodule.mem_map_of_mem ?_
      refine (GradedSuperspace.tensorDeg_le_iff M.toGradedSuperspace N.toGradedSuperspace
        (S := (tensorDegK M N (m + n)).comap
          (SVec.toLinearMap ((tensorK M.toSuperBimodule N.toSuperBimodule).ract c)))).2
        (fun r s hrs v hv w hw => ?_) hy
      rw [Submodule.mem_comap]
      change v ⊗ₜ N.toSuperBimodule.ract c w ∈ _
      subst hrs
      rw [add_assoc]
      exact GradedSuperspace.tmul_mem_tensorDeg _ _ hv (N.ract_mem hc hw)
    exact h hx

@[simp] theorem tensor_toSuperBimodule :
    (M.tensor N).toSuperBimodule = SuperBimodule.tensor M.toSuperBimodule N.toSuperBimodule := rfl

@[simp] theorem tensor_deg (n : ℤ) : (M.tensor N).deg n = tensorDeg M N n := rfl

/-! ### The whiskerings, associator and unitors preserve degrees -/

variable {M N}

set_option backward.isDefEq.respectTransparency false in
theorem whiskerRight_mem_degHom {M M' : GradedSuperBimodule 𝒢 ℋ} {n : ℤ}
    {f : M.toSuperBimodule ⟶ M'.toSuperBimodule} (hf : f ∈ degHom M M' n)
    (N : GradedSuperBimodule ℋ 𝒦) :
    SuperBimodule.whiskerRight f N.toSuperBimodule ∈ degHom (M.tensor N) (M'.tensor N) n := by
  refine (mem_degHom_iff _).2 fun d x hx => ?_
  refine (tensorDeg_le_iff M N (S := ((M'.tensor N).deg (d + n)).comap
    (SVec.toLinearMap (SuperBimodule.whiskerRight f N.toSuperBimodule).1))).2
    (fun r s hrs m hm y hy => ?_) hx
  rw [Submodule.mem_comap]
  change btmul _ _ (f.1 m) y ∈ _
  subst hrs
  rw [add_right_comm]
  exact btmul_mem_tensorDeg M' N ((mem_degHom_iff _).1 hf r m hm) hy

set_option backward.isDefEq.respectTransparency false in
theorem whiskerLeft_mem_degHom (M : GradedSuperBimodule 𝒢 ℋ) {N N' : GradedSuperBimodule ℋ 𝒦}
    {n : ℤ} {g : N.toSuperBimodule ⟶ N'.toSuperBimodule} (hg : g ∈ degHom N N' n) :
    SuperBimodule.whiskerLeft M.toSuperBimodule g ∈ degHom (M.tensor N) (M.tensor N') n := by
  refine (mem_degHom_iff _).2 fun d x hx => ?_
  refine (tensorDeg_le_iff M N (S := ((M.tensor N').deg (d + n)).comap
    (SVec.toLinearMap (SuperBimodule.whiskerLeft M.toSuperBimodule g).1))).2
    (fun r s hrs m hm y hy => ?_) hx
  rw [Submodule.mem_comap]
  change tensorMk _ _ (SVec.whiskerLeft M.toSuperBimodule.toSVec g.1 (m ⊗ₜ y)) ∈ _
  subst hrs
  exact Submodule.mem_map_of_mem (GradedSuperspace.whiskerLeft_mem_degHom M.toGradedSuperspace
    (show g.1 ∈ GradedSuperspace.degHom N.toGradedSuperspace N'.toGradedSuperspace n from hg)
    (r + s) _ (GradedSuperspace.tmul_mem_tensorDeg _ _ hm hy))

set_option backward.isDefEq.respectTransparency false in
theorem whiskerRight_mem_hom {M M' : GradedSuperBimodule 𝒢 ℋ}
    {f : M.toSuperBimodule ⟶ M'.toSuperBimodule} (hf : f ∈ (family 𝒢 ℋ).hom M M')
    (N : GradedSuperBimodule ℋ 𝒦) :
    SuperBimodule.whiskerRight f N.toSuperBimodule ∈ (family 𝒢 𝒦).hom (M.tensor N) (M'.tensor N) := by
  refine (family 𝒢 ℋ).hom_induction hf
    (fun n f hf => (family 𝒢 𝒦).mem_hom_of_mem (whiskerRight_mem_degHom hf N)) ?_ ?_
  · rw [SuperBimodule.zero_whiskerRight]; exact Submodule.zero_mem _
  · intro f f' hf hf'
    rw [SuperBimodule.add_whiskerRight]; exact Submodule.add_mem _ hf hf'

set_option backward.isDefEq.respectTransparency false in
theorem whiskerLeft_mem_hom (M : GradedSuperBimodule 𝒢 ℋ) {N N' : GradedSuperBimodule ℋ 𝒦}
    {g : N.toSuperBimodule ⟶ N'.toSuperBimodule} (hg : g ∈ (family ℋ 𝒦).hom N N') :
    SuperBimodule.whiskerLeft M.toSuperBimodule g ∈ (family 𝒢 𝒦).hom (M.tensor N) (M.tensor N') := by
  refine (family ℋ 𝒦).hom_induction hg
    (fun n g hg => (family 𝒢 𝒦).mem_hom_of_mem (whiskerLeft_mem_degHom M hg)) ?_ ?_
  · rw [SuperBimodule.whiskerLeft_zero]; exact Submodule.zero_mem _
  · intro g g' hg hg'
    rw [SuperBimodule.whiskerLeft_add]; exact Submodule.add_mem _ hg hg'

variable (M N) (P : GradedSuperBimodule 𝒦 𝒟)

set_option backward.isDefEq.respectTransparency false in
theorem assoc_hom_mem_degHom :
    (SuperBimodule.assoc M.toSuperBimodule N.toSuperBimodule P.toSuperBimodule).hom ∈
      degHom ((M.tensor N).tensor P) (M.tensor (N.tensor P)) 0 := by
  refine (mem_degHom_iff _).2 fun d x hx => ?_
  refine (tensorDeg_le_iff (M.tensor N) P (S := ((M.tensor (N.tensor P)).deg (d + 0)).comap
    (SVec.toLinearMap (SuperBimodule.assoc M.toSuperBimodule N.toSuperBimodule P.toSuperBimodule).hom.1))).2
    (fun r s hrs y hy p hp => ?_) hx
  rw [Submodule.mem_comap]
  refine (tensorDeg_le_iff M N (S := ((M.tensor (N.tensor P)).deg (d + 0)).comap
    (SVec.toLinearMap (SuperBimodule.assoc M.toSuperBimodule N.toSuperBimodule P.toSuperBimodule).hom.1 ∘ₗ
      (btmulBi (SuperBimodule.tensor M.toSuperBimodule N.toSuperBimodule) P.toSuperBimodule).flip p))).2
    (fun a b hab m hm n hn => ?_) hy
  rw [Submodule.mem_comap]
  change (SuperBimodule.assoc M.toSuperBimodule N.toSuperBimodule P.toSuperBimodule).hom.1
    (btmul _ _ (btmul _ _ m n) p) ∈ _
  rw [assoc_hom_btmul]
  subst hrs hab
  rw [add_zero, add_assoc]
  exact btmul_mem_tensorDeg M (N.tensor P) hm (btmul_mem_tensorDeg N P hn hp)

set_option backward.isDefEq.respectTransparency false in
theorem assoc_inv_mem_degHom :
    (SuperBimodule.assoc M.toSuperBimodule N.toSuperBimodule P.toSuperBimodule).inv ∈
      degHom (M.tensor (N.tensor P)) ((M.tensor N).tensor P) 0 := by
  refine (mem_degHom_iff _).2 fun d x hx => ?_
  refine (tensorDeg_le_iff M (N.tensor P) (S := (((M.tensor N).tensor P).deg (d + 0)).comap
    (SVec.toLinearMap (SuperBimodule.assoc M.toSuperBimodule N.toSuperBimodule P.toSuperBimodule).inv.1))).2
    (fun r s hrs m hm y hy => ?_) hx
  rw [Submodule.mem_comap]
  refine (tensorDeg_le_iff N P (S := (((M.tensor N).tensor P).deg (d + 0)).comap
    (SVec.toLinearMap (SuperBimodule.assoc M.toSuperBimodule N.toSuperBimodule P.toSuperBimodule).inv.1 ∘ₗ
      btmulBi M.toSuperBimodule (SuperBimodule.tensor N.toSuperBimodule P.toSuperBimodule) m))).2
    (fun a b hab n hn p hp => ?_) hy
  rw [Submodule.mem_comap]
  change (SuperBimodule.assoc M.toSuperBimodule N.toSuperBimodule P.toSuperBimodule).inv.1
    (btmul _ _ m (btmul _ _ n p)) ∈ _
  rw [assoc_inv_btmul]
  subst hrs hab
  rw [add_zero, ← add_assoc]
  exact btmul_mem_tensorDeg (M.tensor N) P (btmul_mem_tensorDeg M N hm hn) hp

end GradedSuperBimodule

end Tensor

/-! ## The regular graded superbimodule and the unitors -/

section Regular

variable {A : Type u} [Ring A] [Algebra k A] {B : Type u} [Ring B] [Algebra k B]
  {𝒢 : GradedSuperalgebra k A} {ℋ : GradedSuperalgebra k B}

namespace GradedSuperBimodule

variable (𝒢) in
/-- The regular graded superbimodule `A`, with the grading of `A`. -/
def regular : GradedSuperBimodule 𝒢 𝒢 where
  toSuperBimodule := SuperBimodule.regular 𝒢.parity
  deg n := 𝒢.degree n
  isInternal_deg := DirectSum.Decomposition.isInternal 𝒢.degree
  odd_mem {n a} ha := by
    change Supercategory.proj k 1 (C := SuperalgebraCat 𝒢.parity) (X := SuperalgebraCat.star _)
      (Y := SuperalgebraCat.star _) (SuperalgebraCat.ofElem a) ∈ 𝒢.degree n
    rw [SuperalgebraCat.proj_eq_decompose]
    exact 𝒢.decompose_mem 1 ha
  lact_mem {n a} ha {m x} hx := by
    have h : a * (show A from x) ∈ 𝒢.degree (n + m) := SetLike.GradedMul.mul_mem ha hx
    rw [add_comm]; exact h
  ract_mem {n b} hb {m x} hx := by
    have h : (show A from x) * b ∈ 𝒢.degree (m + n) :=
      SetLike.GradedMul.mul_mem (R := A) hx hb
    exact h

@[simp] theorem regular_toSuperBimodule :
    (regular 𝒢).toSuperBimodule = SuperBimodule.regular 𝒢.parity := rfl

@[simp] theorem regular_deg (n : ℤ) : (regular 𝒢).deg n = 𝒢.degree n := rfl

variable (M : GradedSuperBimodule 𝒢 ℋ)

set_option backward.isDefEq.respectTransparency false in
theorem leftUnitor_hom_mem_degHom :
    (SuperBimodule.leftUnitor M.toSuperBimodule).hom ∈ degHom ((regular 𝒢).tensor M) M 0 := by
  refine (mem_degHom_iff _).2 fun d x hx => ?_
  refine (tensorDeg_le_iff (regular 𝒢) M (S := (M.deg (d + 0)).comap
    (SVec.toLinearMap (SuperBimodule.leftUnitor M.toSuperBimodule).hom.1))).2
    (fun r s hrs a ha m hm => ?_) hx
  rw [Submodule.mem_comap]
  change leftUnitorHom M.toSuperBimodule (btmul _ _ a m) ∈ _
  rw [leftUnitorHom_btmul]
  subst hrs
  rw [add_zero, add_comm]
  exact M.lact_mem ha hm

theorem leftUnitor_inv_mem_degHom :
    (SuperBimodule.leftUnitor M.toSuperBimodule).inv ∈ degHom M ((regular 𝒢).tensor M) 0 :=
  (mem_degHom_iff _).2 fun d m hm => by
    change btmul (SuperBimodule.regular 𝒢.parity) M.toSuperBimodule (1 : A) m ∈ _
    rw [add_zero]
    have := btmul_mem_tensorDeg (regular 𝒢) M (SetLike.GradedOne.one_mem : (1 : A) ∈ 𝒢.degree 0) hm
    rwa [zero_add] at this

set_option backward.isDefEq.respectTransparency false in
theorem rightUnitor_hom_mem_degHom :
    (SuperBimodule.rightUnitor M.toSuperBimodule).hom ∈ degHom (M.tensor (regular ℋ)) M 0 := by
  refine (mem_degHom_iff _).2 fun d x hx => ?_
  refine (tensorDeg_le_iff M (regular ℋ) (S := (M.deg (d + 0)).comap
    (SVec.toLinearMap (SuperBimodule.rightUnitor M.toSuperBimodule).hom.1))).2
    (fun r s hrs m hm b hb => ?_) hx
  rw [Submodule.mem_comap]
  change rightUnitorHom M.toSuperBimodule (btmul _ _ m b) ∈ _
  rw [rightUnitorHom_btmul]
  subst hrs
  rw [add_zero]
  exact M.ract_mem hb hm

theorem rightUnitor_inv_mem_degHom :
    (SuperBimodule.rightUnitor M.toSuperBimodule).inv ∈ degHom M (M.tensor (regular ℋ)) 0 :=
  (mem_degHom_iff _).2 fun d m hm => by
    change btmul M.toSuperBimodule (SuperBimodule.regular ℋ.parity) m (1 : B) ∈ _
    rw [add_zero]
    have := btmul_mem_tensorDeg M (regular ℋ) hm (SetLike.GradedOne.one_mem : (1 : B) ∈ ℋ.degree 0)
    rwa [add_zero] at this

end GradedSuperBimodule

end Regular

/-! ## The graded 2-supercategory `𝔊𝔖𝔅𝔦𝔪` -/

variable (k) in
/-- A graded superalgebra over `k`, bundled: a superalgebra (`SuperAlg k`) with a `ℤ`-grading
by sub-superspaces. -/
structure GSuperAlg extends SuperAlg k where
  /-- The `ℤ`-grading. -/
  degree : ℤ → Submodule k carrier
  [gradedDegree : GradedAlgebra degree]
  /-- Each homogeneous component is a sub-superspace. -/
  decompose_mem : ∀ {n : ℤ} {a : carrier} (p : ZMod 2), a ∈ degree n →
    (DirectSum.decompose grading a p : carrier) ∈ degree n

namespace GSuperAlg

attribute [instance] gradedDegree

instance : CoeSort (GSuperAlg k) (Type u) := ⟨fun A => A.carrier⟩

/-- The graded superalgebra structure of a bundled graded superalgebra. -/
def gsa (A : GSuperAlg k) : GradedSuperalgebra k A.carrier where
  parity := A.grading
  degree := A.degree
  decompose_mem := A.decompose_mem

@[simp] theorem gsa_parity (A : GSuperAlg k) : A.gsa.parity = A.grading := rfl

@[simp] theorem gsa_degree (A : GSuperAlg k) : A.gsa.degree = A.degree := rfl

open BicategoryStruct GradedSuperBimodule GradedSubcategory

/-- The horizontal composition data of `𝔊𝔖𝔅𝔦𝔪`: `Hom(A, B) := B-GSMod-A`, composition the
graded balanced tensor product (`M ≫ N := N ⊗_B M`), identities the regular graded
superbimodules, and the associators and unitors of the balanced tensor product. -/
instance instBicategoryStruct : BicategoryStruct.{u, u + 1} (GSuperAlg k) where
  Hom A B := GSMod B.gsa A.gsa
  id A := GSMod.of (regular A.gsa)
  comp M N := GSMod.of (N.as.tensor M.as)
  homCategory _ _ := inferInstance
  whiskerLeft M _ _ η := ⟨SuperBimodule.whiskerRight η.1 M.as.toSuperBimodule,
    whiskerRight_mem_hom η.2 M.as⟩
  whiskerRight η N := ⟨SuperBimodule.whiskerLeft N.as.toSuperBimodule η.1,
    whiskerLeft_mem_hom N.as η.2⟩
  associator M N P := isoMk
    (SuperBimodule.assoc P.as.toSuperBimodule N.as.toSuperBimodule M.as.toSuperBimodule).symm
    (assoc_inv_mem_degHom P.as N.as M.as) (assoc_hom_mem_degHom P.as N.as M.as)
  leftUnitor M := isoMk (SuperBimodule.rightUnitor M.as.toSuperBimodule)
    (rightUnitor_hom_mem_degHom M.as) (rightUnitor_inv_mem_degHom M.as)
  rightUnitor M := isoMk (SuperBimodule.leftUnitor M.as.toSuperBimodule)
    (leftUnitor_hom_mem_degHom M.as) (leftUnitor_inv_mem_degHom M.as)

instance (A B : GSuperAlg k) : Preadditive (A ⟶ B) :=
  inferInstanceAs (Preadditive (GSMod B.gsa A.gsa))

instance (A B : GSuperAlg k) : Linear k (A ⟶ B) :=
  inferInstanceAs (Linear k (GSMod B.gsa A.gsa))

instance (A B : GSuperAlg k) : Supercategory k (A ⟶ B) :=
  inferInstanceAs (Supercategory k (GSMod B.gsa A.gsa))

instance (A B : GSuperAlg k) : GradedSupercategory k (A ⟶ B) :=
  inferInstanceAs (GradedSupercategory k (GSMod B.gsa A.gsa))

theorem hom_def (A B : GSuperAlg k) : (A ⟶ B) = GSMod B.gsa A.gsa := rfl

theorem id_def (A : GSuperAlg k) : 𝟙 A = GSMod.of (regular A.gsa) := rfl

theorem comp_def {A B C : GSuperAlg k} (M : A ⟶ B) (N : B ⟶ C) :
    M ≫ N = GSMod.of (N.as.tensor M.as) := rfl

@[simp] theorem whiskerLeft_val {A B C : GSuperAlg k} (M : A ⟶ B) {N N' : B ⟶ C} (η : N ⟶ N') :
    (M ◁ η).1 = SuperBimodule.whiskerRight η.1 M.as.toSuperBimodule := rfl

@[simp] theorem whiskerRight_val {A B C : GSuperAlg k} {M M' : A ⟶ B} (η : M ⟶ M') (N : B ⟶ C) :
    (η ▷ N).1 = SuperBimodule.whiskerLeft N.as.toSuperBimodule η.1 := rfl

@[simp] theorem associator_hom_val {A B C D : GSuperAlg k} (M : A ⟶ B) (N : B ⟶ C) (P : C ⟶ D) :
    (associator M N P).hom.1 =
      (SuperBimodule.assoc P.as.toSuperBimodule N.as.toSuperBimodule M.as.toSuperBimodule).inv := rfl

@[simp] theorem associator_inv_val {A B C D : GSuperAlg k} (M : A ⟶ B) (N : B ⟶ C) (P : C ⟶ D) :
    (associator M N P).inv.1 =
      (SuperBimodule.assoc P.as.toSuperBimodule N.as.toSuperBimodule M.as.toSuperBimodule).hom := rfl

@[simp] theorem leftUnitor_hom_val {A B : GSuperAlg k} (M : A ⟶ B) :
    (leftUnitor M).hom.1 = (SuperBimodule.rightUnitor M.as.toSuperBimodule).hom := rfl

@[simp] theorem leftUnitor_inv_val {A B : GSuperAlg k} (M : A ⟶ B) :
    (leftUnitor M).inv.1 = (SuperBimodule.rightUnitor M.as.toSuperBimodule).inv := rfl

@[simp] theorem rightUnitor_hom_val {A B : GSuperAlg k} (M : A ⟶ B) :
    (rightUnitor M).hom.1 = (SuperBimodule.leftUnitor M.as.toSuperBimodule).hom := rfl

@[simp] theorem rightUnitor_inv_val {A B : GSuperAlg k} (M : A ⟶ B) :
    (rightUnitor M).inv.1 = (SuperBimodule.leftUnitor M.as.toSuperBimodule).inv := rfl

/-- **Brundan–Ellis, §6 (after Definition 6.2).** Graded superalgebras, graded superbimodules
and graded superbimodule homomorphisms form a 2-supercategory `𝔊𝔖𝔅𝔦𝔪`, with horizontal
composition the balanced tensor product; its axioms are those of `𝔖𝔅𝔦𝔪`. -/
instance instTwoSupercategory : TwoSupercategory k (GSuperAlg k) where
  whiskerLeft_id M N := Subtype.ext
    (TwoSupercategory.whiskerLeft_id (R := k) (B := SuperAlg k) M.as.toSuperBimodule N.as.toSuperBimodule)
  whiskerLeft_comp M _ _ _ η θ := Subtype.ext
    (TwoSupercategory.whiskerLeft_comp (R := k) (B := SuperAlg k) M.as.toSuperBimodule η.1 θ.1)
  id_whiskerLeft η := Subtype.ext (TwoSupercategory.id_whiskerLeft (R := k) (B := SuperAlg k) η.1)
  comp_whiskerLeft M N _ _ η := Subtype.ext
    (TwoSupercategory.comp_whiskerLeft (R := k) (B := SuperAlg k) M.as.toSuperBimodule
      N.as.toSuperBimodule η.1)
  id_whiskerRight M N := Subtype.ext
    (TwoSupercategory.id_whiskerRight (R := k) (B := SuperAlg k) M.as.toSuperBimodule N.as.toSuperBimodule)
  comp_whiskerRight η θ N := Subtype.ext
    (TwoSupercategory.comp_whiskerRight (R := k) (B := SuperAlg k) η.1 θ.1 N.as.toSuperBimodule)
  whiskerRight_id η := Subtype.ext (TwoSupercategory.whiskerRight_id (R := k) (B := SuperAlg k) η.1)
  whiskerRight_comp η N P := Subtype.ext
    (TwoSupercategory.whiskerRight_comp (R := k) (B := SuperAlg k) η.1 N.as.toSuperBimodule
      P.as.toSuperBimodule)
  whisker_assoc M _ _ η P := Subtype.ext
    (TwoSupercategory.whisker_assoc (R := k) (B := SuperAlg k) M.as.toSuperBimodule η.1
      P.as.toSuperBimodule)
  pentagon M N P Q := Subtype.ext
    (TwoSupercategory.pentagon (R := k) (B := SuperAlg k) M.as.toSuperBimodule N.as.toSuperBimodule
      P.as.toSuperBimodule Q.as.toSuperBimodule)
  triangle M N := Subtype.ext
    (TwoSupercategory.triangle (R := k) (B := SuperAlg k) M.as.toSuperBimodule N.as.toSuperBimodule)
  whiskerLeft_add M _ _ η θ := Subtype.ext
    (TwoSupercategory.whiskerLeft_add (R := k) (B := SuperAlg k) M.as.toSuperBimodule η.1 θ.1)
  add_whiskerRight η θ N := Subtype.ext
    (TwoSupercategory.add_whiskerRight (R := k) (B := SuperAlg k) η.1 θ.1 N.as.toSuperBimodule)
  whiskerLeft_smul M _ _ r η := Subtype.ext
    (TwoSupercategory.whiskerLeft_smul (B := SuperAlg k) M.as.toSuperBimodule r η.1)
  smul_whiskerRight r η N := Subtype.ext
    (TwoSupercategory.smul_whiskerRight (B := SuperAlg k) r η.1 N.as.toSuperBimodule)
  whiskerLeft_mem M _ _ _ _ hη :=
    TwoSupercategory.whiskerLeft_mem (R := k) (B := SuperAlg k) M.as.toSuperBimodule hη
  whiskerRight_mem N hη :=
    TwoSupercategory.whiskerRight_mem (R := k) (B := SuperAlg k) N.as.toSuperBimodule hη
  super_interchange hη hθ := Subtype.ext
    (TwoSupercategory.super_interchange (R := k) (B := SuperAlg k) hη hθ)
  associator_hom_mem M N P :=
    TwoSupercategory.associator_hom_mem (R := k) (B := SuperAlg k) M.as.toSuperBimodule
      N.as.toSuperBimodule P.as.toSuperBimodule
  leftUnitor_hom_mem M := TwoSupercategory.leftUnitor_hom_mem (R := k) (B := SuperAlg k) M.as.toSuperBimodule
  rightUnitor_hom_mem M :=
    TwoSupercategory.rightUnitor_hom_mem (R := k) (B := SuperAlg k) M.as.toSuperBimodule

/-- **Brundan–Ellis, §6 (after Definition 6.2).** `𝔊𝔖𝔅𝔦𝔪` is a graded 2-supercategory: the
whiskerings preserve degrees and the coherence maps have degree `0`. -/
instance instGradedTwoSupercategory : GradedTwoSupercategory k (GSuperAlg k) where
  whiskerLeft_mem_degree M _ _ _ _ hη := whiskerRight_mem_degHom hη M.as
  whiskerRight_mem_degree N hη := whiskerLeft_mem_degHom N.as hη
  associator_hom_mem_degree M N P := assoc_inv_mem_degHom P.as N.as M.as
  leftUnitor_hom_mem_degree M := rightUnitor_hom_mem_degHom M.as
  rightUnitor_hom_mem_degree M := leftUnitor_hom_mem_degHom M.as

/-- `𝔊𝔖𝔅𝔦𝔪` is a Π-2-supercategory, with `π_A := Π A` the parity shift of the regular graded
superbimodule and `ζ_A : Π A ⇒ A` the identity function (as `𝔖𝔅𝔦𝔪`). -/
instance instPiTwoSupercategory : PiTwoSupercategory k (GSuperAlg k) where
  pi A := GSMod.of (regular A.gsa).piObj
  ζ A := GSMod.ζIso (regular A.gsa)
  ζ_hom_mem A := GSMod.ζIso_hom_mem (regular A.gsa)

/-- `𝔊𝔖𝔅𝔦𝔪` is a graded `(Q, Π)`-2-supercategory, with `q_A`, `q_A⁻¹` the shifts of the regular
graded superbimodule, `σ_A`, `σ̄_A` the identity functions (even, of degrees `-1` and `1`),
`π_A` and `ζ_A` as above. This is the evident extension of the graded `(Q, Π)`-structure of
`A-GSMod-B`; it is not stated in the paper. -/
instance instQPiTwoSupercategory : QPiTwoSupercategory k (GSuperAlg k) where
  pi A := GSMod.of (regular A.gsa).piObj
  ζ A := GSMod.ζIso (regular A.gsa)
  ζ_hom_mem A := GSMod.ζIso_hom_mem (regular A.gsa)
  ζ_hom_mem_degree A := GSMod.ζIso_hom_mem_degree (regular A.gsa)
  q A := GSMod.of (GSMod.qObj (regular A.gsa))
  qinv A := GSMod.of (GSMod.qinvObj (regular A.gsa))
  σ A := GSMod.σIso (regular A.gsa)
  σbar A := GSMod.σbarIso (regular A.gsa)
  σ_hom_mem A := GSMod.σIso_hom_mem (regular A.gsa)
  σ_hom_mem_degree A := GSMod.σIso_hom_mem_degree (regular A.gsa)
  σbar_hom_mem A := GSMod.σbarIso_hom_mem (regular A.gsa)
  σbar_hom_mem_degree A := GSMod.σbarIso_hom_mem_degree (regular A.gsa)

end GSuperAlg

end StringDiagrams

end
