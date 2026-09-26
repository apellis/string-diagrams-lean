import StringDiagrams.Super.GSVec
import StringDiagrams.Super.GradedMonoidal
import StringDiagrams.Super.MonoidalPi
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.Algebra.Module.Submodule.Bilinear

/-!
# The graded monoidal supercategory of graded superspaces

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6 (before
Definition 6.1): the tensor product of graded superspaces, `(V ⊗ W)ₙ = ⨁_{r+s=n} Vᵣ ⊗ Wₛ`.

* `GradedSuperspace.tensorObj V W`: the tensor product of superspaces `V ⊗ W` (of
  `StringDiagrams.Super.SVec`, with the Koszul sign rule) with the grading
  `(V ⊗ W)ₙ = ⨁_{r+s=n} Vᵣ ⊗ Wₛ` (`GradedSuperspace.tensorDeg`). That this is a grading, i.e.
  that `V ⊗ W` is the internal direct sum of these submodules, is proved via the projections
  `V ⊗ W → V ⊗ W` onto `(V ⊗ W)ₙ` obtained from `V ⊗ W ≅ ⨁_{(r,s)} Vᵣ ⊗ Wₛ`
  (`GradedSuperspace.tensorProj`, `GradedSuperspace.isInternal_tensorDeg`).
* `GradedSuperspace.unit`: the unit `k`, in degree `0` and even parity.
* With the whiskerings, associator and unitors of `SVec k`, which preserve degrees,
  `GSVec k` is a monoidal supercategory (`GSVec.instMonoidalSupercategory`) and a graded
  monoidal supercategory (`GSVec.instGradedMonoidalSupercategory`); its underlying category
  `GradedSupercategory.GUnderlying k (GSVec k)` is the paper's monoidal category `GSVec̲` of
  graded superspaces and even linear maps of degree zero. The braiding is not formalized (nor
  is that of `SVec k`).
* `GSVec k` is a monoidal Π-supercategory with `π := Π k` and `ζ : Π k → k` the identity
  function (`GSVec.instMonoidalPiSupercategory`, the graded analogue of Example 1.13(i) for
  `A = k`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory GradedSupercategory TensorProduct

universe u

variable {k : Type u} [CommRing k]

namespace GradedSuperspace

variable (V W : GradedSuperspace k)

/-! ## The grading of `V ⊗ W` -/

/-- The submodule `Vᵣ ⊗ Wₛ` of `V ⊗ W`. -/
def tensorPiece (rs : ℤ × ℤ) : Submodule k (V.toSVec ⊗[k] W.toSVec) :=
  Submodule.map₂ (TensorProduct.mk k V.toSVec W.toSVec) (V.deg rs.1) (W.deg rs.2)

/-- The homogeneous component `(V ⊗ W)ₙ = ⨁_{r+s=n} Vᵣ ⊗ Wₛ`. -/
def tensorDeg (n : ℤ) : Submodule k (V.toSVec ⊗[k] W.toSVec) :=
  ⨆ (rs : ℤ × ℤ) (_ : rs.1 + rs.2 = n), V.tensorPiece W rs

theorem tmul_mem_tensorDeg {r s : ℤ} {v : V.toSVec} {w : W.toSVec} (hv : v ∈ V.deg r)
    (hw : w ∈ W.deg s) : v ⊗ₜ w ∈ V.tensorDeg W (r + s) :=
  Submodule.mem_iSup_of_mem (r, s)
    (Submodule.mem_iSup_of_mem rfl (Submodule.apply_mem_map₂ _ hv hw))

/-- `(V ⊗ W)ₙ` is spanned by the `v ⊗ w` with `v ∈ Vᵣ`, `w ∈ Wₛ`, `r + s = n`. -/
theorem tensorDeg_le_iff {n : ℤ} {S : Submodule k (V.toSVec ⊗[k] W.toSVec)} :
    V.tensorDeg W n ≤ S ↔
      ∀ (r s : ℤ), r + s = n → ∀ v ∈ V.deg r, ∀ w ∈ W.deg s, v ⊗ₜ w ∈ S :=
  ⟨fun h _ _ hrs _ hv _ hw => h (hrs ▸ tmul_mem_tensorDeg V W hv hw),
    fun h => iSup₂_le fun rs hrs => Submodule.map₂_le.2 fun v hv w hw => h rs.1 rs.2 hrs v hv w hw⟩

/-- The projection of `V ⊗ W` onto `(V ⊗ W)ₙ`, through `V ⊗ W ≅ ⨁_{(r,s)} Vᵣ ⊗ Wₛ`. -/
def tensorProj (n : ℤ) : V.toSVec ⊗[k] W.toSVec →ₗ[k] V.toSVec ⊗[k] W.toSVec :=
  letI := V.degreeDecomposition
  letI := W.degreeDecomposition
  DirectSum.toModule k (ℤ × ℤ) (V.toSVec ⊗[k] W.toSVec) (fun rs =>
      if rs.1 + rs.2 = n then TensorProduct.map (V.deg rs.1).subtype (W.deg rs.2).subtype else 0) ∘ₗ
    (TensorProduct.directSum k k (fun r => V.deg r) (fun s => W.deg s)).toLinearMap ∘ₗ
      TensorProduct.map (DirectSum.decomposeLinearEquiv V.deg).toLinearMap
        (DirectSum.decomposeLinearEquiv W.deg).toLinearMap

theorem tensorProj_tmul (n r s : ℤ) {v : V.toSVec} {w : W.toSVec} (hv : v ∈ V.deg r)
    (hw : w ∈ W.deg s) : V.tensorProj W n (v ⊗ₜ w) = if r + s = n then v ⊗ₜ w else 0 := by
  letI := V.degreeDecomposition
  letI := W.degreeDecomposition
  have hv' : DirectSum.decompose V.deg v = DirectSum.lof k ℤ (fun r => V.deg r) r ⟨v, hv⟩ :=
    DirectSum.decompose_of_mem V.deg hv
  have hw' : DirectSum.decompose W.deg w = DirectSum.lof k ℤ (fun s => W.deg s) s ⟨w, hw⟩ :=
    DirectSum.decompose_of_mem W.deg hw
  simp only [tensorProj, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, hv', hw', TensorProduct.directSum_lof_tmul_lof,
    DirectSum.toModule_lof]
  split_ifs
  · simp
  · rfl

theorem tensorPiece_le_eqLocus (n : ℤ) (rs : ℤ × ℤ) (h : rs.1 + rs.2 = n) :
    V.tensorPiece W rs ≤ LinearMap.eqLocus (V.tensorProj W n) LinearMap.id :=
  Submodule.map₂_le.2 fun v hv w hw => LinearMap.mem_eqLocus.2 (by
    rw [TensorProduct.mk_apply, tensorProj_tmul V W n rs.1 rs.2 hv hw, if_pos h]; rfl)

theorem tensorPiece_le_ker (n : ℤ) (rs : ℤ × ℤ) (h : rs.1 + rs.2 ≠ n) :
    V.tensorPiece W rs ≤ LinearMap.ker (V.tensorProj W n) :=
  Submodule.map₂_le.2 fun v hv w hw => LinearMap.mem_ker.2 (by
    rw [TensorProduct.mk_apply, tensorProj_tmul V W n rs.1 rs.2 hv hw, if_neg h])

theorem iSupIndep_tensorDeg : iSupIndep (V.tensorDeg W) :=
  iSupIndep_of_projections _ (V.tensorProj W)
    (fun n => iSup₂_le fun rs hrs => tensorPiece_le_eqLocus V W n rs hrs)
    (fun n _ hmn => iSup₂_le fun rs hrs =>
      tensorPiece_le_ker V W n rs fun h => hmn (hrs.symm.trans h))

theorem iSup_tensorDeg_eq_top : ⨆ n, V.tensorDeg W n = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine TensorProduct.induction_on x (Submodule.zero_mem _) (fun v w => ?_)
    (fun x y hx hy => Submodule.add_mem _ hx hy)
  refine V.induction_on_deg v (by rw [zero_tmul]; exact Submodule.zero_mem _) (fun r v hv => ?_)
    (fun v v' hv hv' => by rw [add_tmul]; exact Submodule.add_mem _ hv hv')
  refine W.induction_on_deg w (by rw [tmul_zero]; exact Submodule.zero_mem _) (fun s w hw => ?_)
    (fun w w' hw hw' => by rw [tmul_add]; exact Submodule.add_mem _ hw hw')
  exact Submodule.mem_iSup_of_mem (r + s) (tmul_mem_tensorDeg V W hv hw)

/-- `V ⊗ W = ⨁ₙ (V ⊗ W)ₙ`. -/
theorem isInternal_tensorDeg : DirectSum.IsInternal (V.tensorDeg W) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_tensorDeg V W, iSup_tensorDeg_eq_top V W⟩

theorem sgn_mem {b : ZMod 2} {n : ℤ} {v : V.toSVec} (hv : v ∈ V.deg n) : V.toSVec.sgn b v ∈ V.deg n := by
  rw [SVec.sgn_apply]
  exact Submodule.add_mem _ (V.proj_mem 0 hv) (Submodule.smul_mem _ _ (V.proj_mem 1 hv))

/-- **Brundan–Ellis, §6.** The tensor product of graded superspaces: the tensor product of
superspaces `V ⊗ W` with `(V ⊗ W)ₙ = ⨁_{r+s=n} Vᵣ ⊗ Wₛ`. -/
def tensorObj : GradedSuperspace k where
  toSVec := SVec.tensorObj V.toSVec W.toSVec
  deg := V.tensorDeg W
  isInternal_deg := V.isInternal_tensorDeg W
  odd_mem {n x} hx := by
    refine (tensorDeg_le_iff V W
      (S := (V.tensorDeg W n).comap (SVec.tensorObj V.toSVec W.toSVec).odd)).2
      (fun r s hrs v hv w hw => ?_) hx
    rw [Submodule.mem_comap, SVec.tensorObj_odd_tmul]
    subst hrs
    exact Submodule.add_mem _ (tmul_mem_tensorDeg V W (V.proj_mem 1 hv) (W.proj_mem 0 hw))
      (tmul_mem_tensorDeg V W (V.proj_mem 0 hv) (W.proj_mem 1 hw))

@[simp] theorem tensorObj_toSVec : (V.tensorObj W).toSVec = SVec.tensorObj V.toSVec W.toSVec := rfl

@[simp] theorem tensorObj_deg (n : ℤ) : (V.tensorObj W).deg n = V.tensorDeg W n := rfl

/-- The unit graded superspace `k`, in degree `0` and even parity. -/
def unit : GradedSuperspace k where
  toSVec := SVec.unit
  deg n := if n = 0 then ⊤ else ⊥
  isInternal_deg := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_def]
      intro i
      by_cases hi : i = 0
      · subst hi
        refine Disjoint.mono_right (iSup₂_le fun j hj => ?_) disjoint_bot_right
        rw [if_neg hj]
      · rw [if_neg hi]; exact disjoint_bot_left
    · exact le_antisymm le_top (le_iSup_of_le 0 (by rw [if_pos rfl]))
  odd_mem {n v} _ := by
    change (0 : k) ∈ _
    exact Submodule.zero_mem _

@[simp] theorem unit_toSVec : (unit : GradedSuperspace k).toSVec = SVec.unit := rfl

theorem unit_deg (n : ℤ) : (unit : GradedSuperspace k).deg n = if n = 0 then ⊤ else ⊥ := rfl

theorem mem_unit_deg_zero (r : (unit : GradedSuperspace k).toSVec) :
    r ∈ (unit : GradedSuperspace k).deg 0 := by
  rw [unit_deg, if_pos rfl]; trivial

theorem eq_zero_of_mem_unit_deg {n : ℤ} (hn : n ≠ 0) {r : (unit : GradedSuperspace k).toSVec}
    (hr : r ∈ (unit : GradedSuperspace k).deg n) : r = 0 := by
  rwa [unit_deg, if_neg hn, Submodule.mem_bot] at hr

/-! ## The whiskerings and coherence maps preserve degrees -/

variable {V W}

theorem whiskerLeft_mem_degHom (V : GradedSuperspace k) {W W' : GradedSuperspace k} {n : ℤ}
    {g : W.toSVec ⟶ W'.toSVec} (hg : g ∈ degHom W W' n) :
    SVec.whiskerLeft V.toSVec g ∈ degHom (V.tensorObj W) (V.tensorObj W') n := by
  intro m x hx
  refine (tensorDeg_le_iff V W
    (S := (V.tensorDeg W' (m + n)).comap (SVec.toLinearMap (SVec.whiskerLeft V.toSVec g)))).2
    (fun r s hrs v hv w hw => ?_) hx
  rw [Submodule.mem_comap]
  change (TensorProduct.map LinearMap.id (SVec.toLinearMap (SVec.homProj 0 g)) +
    TensorProduct.map (V.toSVec.sgn 1) (SVec.toLinearMap (SVec.homProj 1 g)) :
      V.toSVec ⊗[k] W.toSVec →ₗ[k] V.toSVec ⊗[k] W'.toSVec) (v ⊗ₜ w) ∈ _
  rw [LinearMap.add_apply, TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
  subst hrs
  rw [add_assoc]
  exact Submodule.add_mem _ (tmul_mem_tensorDeg V W' hv (homProj_mem_degHom 0 hg s w hw))
    (tmul_mem_tensorDeg V W' (V.sgn_mem hv) (homProj_mem_degHom 1 hg s w hw))

theorem whiskerRight_mem_degHom {V V' : GradedSuperspace k} {n : ℤ} {f : V.toSVec ⟶ V'.toSVec}
    (hf : f ∈ degHom V V' n) (W : GradedSuperspace k) :
    SVec.whiskerRight f W.toSVec ∈ degHom (V.tensorObj W) (V'.tensorObj W) n := by
  intro m x hx
  refine (tensorDeg_le_iff V W
    (S := (V'.tensorDeg W (m + n)).comap (SVec.toLinearMap (SVec.whiskerRight f W.toSVec)))).2
    (fun r s hrs v hv w hw => ?_) hx
  rw [Submodule.mem_comap]
  change f v ⊗ₜ w ∈ _
  subst hrs
  rw [add_right_comm]
  exact tmul_mem_tensorDeg V' W (hf r v hv) hw

theorem whiskerLeft_mem_hom (V : GradedSuperspace k) {W W' : GradedSuperspace k}
    {g : W.toSVec ⟶ W'.toSVec} (hg : g ∈ (family k).hom W W') :
    SVec.whiskerLeft V.toSVec g ∈ (family k).hom (V.tensorObj W) (V.tensorObj W') := by
  refine (family k).hom_induction hg
    (fun n g hg => (family k).mem_hom_of_mem (whiskerLeft_mem_degHom V hg)) ?_ ?_
  · rw [SVec.whiskerLeft_zero]; exact Submodule.zero_mem _
  · intro g g' hg hg'
    rw [SVec.whiskerLeft_add]; exact Submodule.add_mem _ hg hg'

theorem whiskerRight_mem_hom {V V' : GradedSuperspace k} {f : V.toSVec ⟶ V'.toSVec}
    (hf : f ∈ (family k).hom V V') (W : GradedSuperspace k) :
    SVec.whiskerRight f W.toSVec ∈ (family k).hom (V.tensorObj W) (V'.tensorObj W) := by
  refine (family k).hom_induction hf
    (fun n f hf => (family k).mem_hom_of_mem (whiskerRight_mem_degHom hf W)) ?_ ?_
  · rw [SVec.whiskerRight_zero]; exact Submodule.zero_mem _
  · intro f f' hf hf'
    rw [SVec.whiskerRight_add]; exact Submodule.add_mem _ hf hf'

theorem associator_hom_mem_degHom (U V W : GradedSuperspace k) :
    (SVec.associator U.toSVec V.toSVec W.toSVec).hom ∈
      degHom ((U.tensorObj V).tensorObj W) (U.tensorObj (V.tensorObj W)) 0 := by
  intro m x hx
  refine (tensorDeg_le_iff (U.tensorObj V) W
    (S := (U.tensorDeg (V.tensorObj W) (m + 0)).comap
      (SVec.toLinearMap (SVec.associator U.toSVec V.toSVec W.toSVec).hom))).2
    (fun r s hrs y hy w hw => ?_) hx
  refine (tensorDeg_le_iff U V
    (S := (U.tensorDeg (V.tensorObj W) (m + 0)).comap
      ((SVec.toLinearMap (SVec.associator U.toSVec V.toSVec W.toSVec).hom) ∘ₗ
        (TensorProduct.mk k _ W.toSVec).flip w))).2
    (fun a b hab u hu v hv => ?_) hy
  change (SVec.associator U.toSVec V.toSVec W.toSVec).hom ((u ⊗ₜ v) ⊗ₜ w) ∈
    U.tensorDeg (V.tensorObj W) (m + 0)
  change u ⊗ₜ (v ⊗ₜ w) ∈ _
  subst hrs hab
  rw [add_zero, add_assoc]
  exact tmul_mem_tensorDeg U (V.tensorObj W) hu (tmul_mem_tensorDeg V W hv hw)

theorem associator_inv_mem_degHom (U V W : GradedSuperspace k) :
    (SVec.associator U.toSVec V.toSVec W.toSVec).inv ∈
      degHom (U.tensorObj (V.tensorObj W)) ((U.tensorObj V).tensorObj W) 0 := by
  intro m x hx
  refine (tensorDeg_le_iff U (V.tensorObj W)
    (S := ((U.tensorObj V).tensorDeg W (m + 0)).comap
      (SVec.toLinearMap (SVec.associator U.toSVec V.toSVec W.toSVec).inv))).2
    (fun r s hrs u hu y hy => ?_) hx
  refine (tensorDeg_le_iff V W
    (S := ((U.tensorObj V).tensorDeg W (m + 0)).comap
      ((SVec.toLinearMap (SVec.associator U.toSVec V.toSVec W.toSVec).inv) ∘ₗ
        TensorProduct.mk k U.toSVec _ u))).2
    (fun a b hab v hv w hw => ?_) hy
  change (SVec.associator U.toSVec V.toSVec W.toSVec).inv (u ⊗ₜ (v ⊗ₜ w)) ∈
    (U.tensorObj V).tensorDeg W (m + 0)
  change (u ⊗ₜ v) ⊗ₜ w ∈ _
  subst hrs hab
  rw [add_zero, ← add_assoc]
  exact tmul_mem_tensorDeg (U.tensorObj V) W (tmul_mem_tensorDeg U V hu hv) hw

theorem leftUnitor_hom_mem_degHom (V : GradedSuperspace k) :
    (SVec.leftUnitor V.toSVec).hom ∈ degHom (unit.tensorObj V) V 0 := by
  intro m x hx
  refine (tensorDeg_le_iff unit V
    (S := (V.deg (m + 0)).comap (SVec.toLinearMap (SVec.leftUnitor V.toSVec).hom))).2
    (fun r s hrs c hc v hv => ?_) hx
  rw [Submodule.mem_comap]
  change TensorProduct.lid k V.toSVec (c ⊗ₜ v) ∈ _
  rw [TensorProduct.lid_tmul, add_zero]
  by_cases hr : r = 0
  · subst hr; rw [zero_add] at hrs; subst hrs; exact Submodule.smul_mem _ _ hv
  · rw [show (c • v : V.toSVec) = 0 by rw [eq_zero_of_mem_unit_deg hr hc]; exact zero_smul k v]
    exact Submodule.zero_mem _

theorem leftUnitor_inv_mem_degHom (V : GradedSuperspace k) :
    (SVec.leftUnitor V.toSVec).inv ∈ degHom V (unit.tensorObj V) 0 := fun m v hv => by
  change (TensorProduct.lid k V.toSVec).symm v ∈ _
  rw [TensorProduct.lid_symm_apply, add_zero]
  have := tmul_mem_tensorDeg unit V (mem_unit_deg_zero (1 : k)) hv
  rwa [zero_add] at this

theorem rightUnitor_hom_mem_degHom (V : GradedSuperspace k) :
    (SVec.rightUnitor V.toSVec).hom ∈ degHom (V.tensorObj unit) V 0 := by
  intro m x hx
  refine (tensorDeg_le_iff V unit
    (S := (V.deg (m + 0)).comap (SVec.toLinearMap (SVec.rightUnitor V.toSVec).hom))).2
    (fun r s hrs v hv c hc => ?_) hx
  rw [Submodule.mem_comap]
  change TensorProduct.rid k V.toSVec (v ⊗ₜ c) ∈ _
  rw [TensorProduct.rid_tmul, add_zero]
  by_cases hs : s = 0
  · subst hs; rw [add_zero] at hrs; subst hrs; exact Submodule.smul_mem _ _ hv
  · rw [show (c • v : V.toSVec) = 0 by rw [eq_zero_of_mem_unit_deg hs hc]; exact zero_smul k v]
    exact Submodule.zero_mem _

theorem rightUnitor_inv_mem_degHom (V : GradedSuperspace k) :
    (SVec.rightUnitor V.toSVec).inv ∈ degHom V (V.tensorObj unit) 0 := fun m v hv => by
  change (TensorProduct.rid k V.toSVec).symm v ∈ _
  rw [TensorProduct.rid_symm_apply, add_zero]
  have := tmul_mem_tensorDeg V unit hv (mem_unit_deg_zero (1 : k))
  rwa [add_zero] at this

end GradedSuperspace

/-! ## The monoidal supercategory `GSVec` -/

namespace GSVec

open GradedSuperspace GradedSubcategory

/-- The tensor product of objects of `GSVec k`. -/
abbrev tensorObj (V W : GSVec k) : GSVec k := of (V.as.tensorObj W.as)

/-- `1_V ⊗ g`. -/
def whiskerLeft (V : GSVec k) {W W' : GSVec k} (g : W ⟶ W') : tensorObj V W ⟶ tensorObj V W' :=
  ⟨SVec.whiskerLeft V.as.toSVec g.1, whiskerLeft_mem_hom V.as g.2⟩

/-- `f ⊗ 1_W`. -/
def whiskerRight {V V' : GSVec k} (f : V ⟶ V') (W : GSVec k) : tensorObj V W ⟶ tensorObj V' W :=
  ⟨SVec.whiskerRight f.1 W.as.toSVec, whiskerRight_mem_hom f.2 W.as⟩

/-- The unit object `k`. -/
abbrev unit : GSVec k := of GradedSuperspace.unit

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (GSVec k) where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorUnit := unit
  associator U V W := isoMk (SVec.associator U.as.toSVec V.as.toSVec W.as.toSVec)
    (associator_hom_mem_degHom U.as V.as W.as) (associator_inv_mem_degHom U.as V.as W.as)
  leftUnitor V := isoMk (SVec.leftUnitor V.as.toSVec) (leftUnitor_hom_mem_degHom V.as)
    (leftUnitor_inv_mem_degHom V.as)
  rightUnitor V := isoMk (SVec.rightUnitor V.as.toSVec) (rightUnitor_hom_mem_degHom V.as)
    (rightUnitor_inv_mem_degHom V.as)

theorem tensorObj_def (V W : GSVec k) : V ⊗ W = of (V.as.tensorObj W.as) := rfl

theorem tensorUnit_def : 𝟙_ (GSVec k) = of GradedSuperspace.unit := rfl

@[simp] theorem whiskerLeft_val (V : GSVec k) {W W' : GSVec k} (g : W ⟶ W') :
    (V ◁ g).1 = V.as.toSVec ◁ g.1 := rfl

@[simp] theorem whiskerRight_val {V V' : GSVec k} (f : V ⟶ V') (W : GSVec k) :
    (f ▷ W).1 = f.1 ▷ W.as.toSVec := rfl

@[simp] theorem associator_hom_val (U V W : GSVec k) :
    (α_ U V W).hom.1 = (α_ U.as.toSVec V.as.toSVec W.as.toSVec).hom := rfl

@[simp] theorem associator_inv_val (U V W : GSVec k) :
    (α_ U V W).inv.1 = (α_ U.as.toSVec V.as.toSVec W.as.toSVec).inv := rfl

@[simp] theorem leftUnitor_hom_val (V : GSVec k) : (λ_ V).hom.1 = (λ_ V.as.toSVec).hom := rfl

@[simp] theorem leftUnitor_inv_val (V : GSVec k) : (λ_ V).inv.1 = (λ_ V.as.toSVec).inv := rfl

@[simp] theorem rightUnitor_hom_val (V : GSVec k) : (ρ_ V).hom.1 = (ρ_ V.as.toSVec).hom := rfl

@[simp] theorem rightUnitor_inv_val (V : GSVec k) : (ρ_ V).inv.1 = (ρ_ V.as.toSVec).inv := rfl

@[simp] theorem tensorHom_val {V V' W W' : GSVec k} (f : V ⟶ V') (g : W ⟶ W') :
    (f ⊗ g).1 = f.1 ⊗ g.1 := rfl

/-- **Brundan–Ellis, §6.** `GSVec k` is a monoidal supercategory, with the tensor product,
whiskerings (with the Koszul sign rule), associator and unitors of `SVec k`. -/
instance instMonoidalSupercategory : MonoidalSupercategory k (GSVec k) where
  tensorHom_def _ _ := rfl
  whiskerLeft_id V W := Subtype.ext (MonoidalSupercategory.whiskerLeft_id (R := k) V.as.toSVec W.as.toSVec)
  id_whiskerRight V W := Subtype.ext (MonoidalSupercategory.id_whiskerRight (R := k) V.as.toSVec W.as.toSVec)
  whiskerLeft_comp V _ _ _ f g := Subtype.ext
    (MonoidalSupercategory.whiskerLeft_comp (R := k) V.as.toSVec f.1 g.1)
  comp_whiskerRight f g W := Subtype.ext
    (MonoidalSupercategory.comp_whiskerRight (R := k) f.1 g.1 W.as.toSVec)
  whiskerLeft_add V _ _ f g := Subtype.ext
    (MonoidalSupercategory.whiskerLeft_add (R := k) V.as.toSVec f.1 g.1)
  add_whiskerRight f g W := Subtype.ext
    (MonoidalSupercategory.add_whiskerRight (R := k) f.1 g.1 W.as.toSVec)
  whiskerLeft_smul V _ _ r f := Subtype.ext
    (MonoidalSupercategory.whiskerLeft_smul (R := k) V.as.toSVec r f.1)
  smul_whiskerRight r f W := Subtype.ext
    (MonoidalSupercategory.smul_whiskerRight (R := k) r f.1 W.as.toSVec)
  whiskerLeft_mem V _ _ _ _ hf :=
    MonoidalSupercategory.whiskerLeft_mem (R := k) (C := SVec k) V.as.toSVec hf
  whiskerRight_mem W hf :=
    MonoidalSupercategory.whiskerRight_mem (R := k) (C := SVec k) W.as.toSVec hf
  super_interchange hf hg := Subtype.ext
    (MonoidalSupercategory.super_interchange (R := k) (C := SVec k) hf hg)
  associator_naturality f₁ f₂ f₃ := Subtype.ext
    (MonoidalSupercategory.associator_naturality (R := k) (C := SVec k) f₁.1 f₂.1 f₃.1)
  leftUnitor_naturality f := Subtype.ext
    (MonoidalSupercategory.leftUnitor_naturality (R := k) (C := SVec k) f.1)
  rightUnitor_naturality f := Subtype.ext
    (MonoidalSupercategory.rightUnitor_naturality (R := k) (C := SVec k) f.1)
  pentagon U V W X := Subtype.ext
    (MonoidalSupercategory.pentagon (R := k) (C := SVec k) U.as.toSVec V.as.toSVec W.as.toSVec
      X.as.toSVec)
  triangle V W := Subtype.ext
    (MonoidalSupercategory.triangle (R := k) (C := SVec k) V.as.toSVec W.as.toSVec)
  associator_hom_mem U V W :=
    MonoidalSupercategory.associator_hom_mem (R := k) (C := SVec k) U.as.toSVec V.as.toSVec
      W.as.toSVec
  leftUnitor_hom_mem V := MonoidalSupercategory.leftUnitor_hom_mem (R := k) (C := SVec k) V.as.toSVec
  rightUnitor_hom_mem V :=
    MonoidalSupercategory.rightUnitor_hom_mem (R := k) (C := SVec k) V.as.toSVec

/-- **Brundan–Ellis, §6.** `GSVec k` is a graded monoidal supercategory: the tensor product of
morphisms adds degrees. -/
instance instGradedMonoidalSupercategory : GradedMonoidalSupercategory k (GSVec k) where
  whiskerLeft_mem_degree V _ _ _ _ hf := whiskerLeft_mem_degHom V.as hf
  whiskerRight_mem_degree W hf := whiskerRight_mem_degHom hf W.as
  associator_hom_mem_degree U V W := associator_hom_mem_degHom U.as V.as W.as
  leftUnitor_hom_mem_degree V := leftUnitor_hom_mem_degHom V.as
  rightUnitor_hom_mem_degree V := rightUnitor_hom_mem_degHom V.as

/-- **Brundan–Ellis, Example 1.13(i) (graded, for `A = k`).** `GSVec k` is a monoidal
Π-supercategory with `π := Π k` and `ζ : Π k → k` the identity function. -/
instance instMonoidalPiSupercategory : MonoidalPiSupercategory k (GSVec k) where
  pi := of GradedSuperspace.unit.piObj
  ζ := ζIso GradedSuperspace.unit
  ζ_hom_mem := ζIso_hom_mem GradedSuperspace.unit

end GSVec

end StringDiagrams

end
