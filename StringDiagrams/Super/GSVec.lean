import StringDiagrams.Super.GradedSub
import StringDiagrams.Super.SVec
import StringDiagrams.Super.QPi

/-!
# The graded (Q, Π)-supercategory of graded superspaces

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6: the
graded supercategory `GSVec` of graded superspaces (the third example after Definition 6.1)
and its graded `(Q, Π)`-structure (the example after Definition 6.4, for `A = B = k`).

A *graded superspace* is a `ℤ`-graded superspace `V = ⨁ₙ Vₙ = ⨁ₙ V_{n,0} ⊕ V_{n,1}`, the
`ℤ`- and `ℤ/2`-gradings being independent. We record it as a superspace `V : SVec k` with a
`ℤ`-grading by submodules `deg n` which are sub-superspaces, i.e. stable under the projection
onto the odd part (`StringDiagrams.GradedSuperspace`); then `V = ⨁_{(n,p)} V_{n,p}` with
`V_{n,p} = deg n ⊓ V.part p` (`GradedSuperspace.isInternal_bideg`).

The graded supercategory `GSVec k` has morphisms `Hom(V, W) = ⨁ₙ Hom(V, W)ₙ`, where
`Hom(V, W)ₙ` consists of the linear maps homogeneous of degree `n`, i.e. `f(Vₘ) ⊆ W_{m+n}` for
all `m` (`GradedSuperspace.degHom`); it is the graded subcategory (`GradedSubcategory`) of
`SVec k` determined by these (`GradedSuperspace.family`). The parity of a morphism is that of
its underlying linear map. The underlying category of the paper (even linear maps of degree
zero) is `GradedSupercategory.GUnderlying k (GSVec k)`.

## The (Q, Π)-structure

* `Π V` is `V` with the opposite parity and the same degrees (`GradedSuperspace.piObj`), and
  `ζ_V : Π V → V` is the identity function, odd of degree `0` (`GSVec.ζIso`), as in
  Example 1.8; this is `GSVec.instPiSupercategory`.
* `Q V` and `Q⁻¹ V` are the shifts `(Q V)ₙ = V_{n-1}`, `(Q⁻¹ V)ₙ = V_{n+1}`
  (`GradedSuperspace.shift`), and `σ_V : Q V → V`, `σ̄_V : Q⁻¹ V → V` are the identity functions,
  even of degrees `-1` and `1` (`GSVec.σIso`, `GSVec.σbarIso`); with these `GSVec k` is a
  graded `(Q, Π)`-supercategory (`GSVec.instQPiSupercategory`). On morphisms, `Π f`, `Q f`
  and `Q⁻¹ f` are `(-1)^{|f|} f`, `f` and `f` (`GSVec.pi_map_val`, `GSVec.Q_map_val`,
  `GSVec.Qinv_map_val`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe u

variable {k : Type u} [CommRing k]

/-- A graded superspace (Brundan–Ellis, §6): a superspace with a `ℤ`-grading by
sub-superspaces, i.e. submodules stable under the projection onto the odd part. -/
structure GradedSuperspace (k : Type u) [CommRing k] where
  /-- The underlying superspace. -/
  toSVec : SVec k
  /-- The homogeneous component of degree `n`. -/
  deg : ℤ → Submodule k toSVec
  /-- The module is the internal direct sum of its homogeneous components. -/
  isInternal_deg : DirectSum.IsInternal deg
  /-- Each homogeneous component is a sub-superspace. -/
  odd_mem : ∀ {n : ℤ} {v : toSVec}, v ∈ deg n → toSVec.odd v ∈ deg n

namespace GradedSuperspace

variable (V : GradedSuperspace k)

/-! ## Homogeneous components -/

theorem proj_mem (p : ZMod 2) {n : ℤ} {v : V.toSVec} (hv : v ∈ V.deg n) :
    V.toSVec.proj p v ∈ V.deg n := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SVec.proj_zero, LinearMap.sub_apply, LinearMap.id_apply]
    exact Submodule.sub_mem _ hv (V.odd_mem hv)
  · rw [SVec.proj_one]; exact V.odd_mem hv

/-- The decomposition of `V` into its homogeneous components. -/
def degreeDecomposition : DirectSum.Decomposition V.deg := V.isInternal_deg.chooseDecomposition

/-- The projection onto the component of degree `n`. -/
def dproj (n : ℤ) : V.toSVec →ₗ[k] V.toSVec :=
  letI := V.degreeDecomposition
  (V.deg n).subtype ∘ₗ (DirectSum.component k ℤ (fun m => V.deg m) n) ∘ₗ
    (DirectSum.decomposeLinearEquiv V.deg).toLinearMap

theorem dproj_of_mem {n : ℤ} {v : V.toSVec} (hv : v ∈ V.deg n) : V.dproj n v = v :=
  letI := V.degreeDecomposition
  DirectSum.decompose_of_mem_same _ hv

theorem dproj_of_mem_ne {m n : ℤ} {v : V.toSVec} (hv : v ∈ V.deg m) (h : m ≠ n) :
    V.dproj n v = 0 :=
  letI := V.degreeDecomposition
  DirectSum.decompose_of_mem_ne _ hv h

/-- Induction on vectors via homogeneous ones. -/
@[elab_as_elim]
theorem induction_on_deg {P : V.toSVec → Prop} (v : V.toSVec) (zero : P 0)
    (hom : ∀ (n : ℤ) (w : V.toSVec), w ∈ V.deg n → P w) (add : ∀ w w', P w → P w' → P (w + w')) :
    P v :=
  letI := V.degreeDecomposition
  DirectSum.Decomposition.inductionOn V.deg zero (fun w => hom _ _ w.2) add v

/-- The component `V_{n,p}` of degree `n` and parity `p`. -/
def bideg (np : ℤ × ZMod 2) : Submodule k V.toSVec := V.deg np.1 ⊓ V.toSVec.part np.2

/-- A graded superspace is the direct sum `⨁_{(n,p)} V_{n,p}` of its bihomogeneous
components: the `ℤ`- and `ℤ/2`-gradings are independent. -/
theorem isInternal_bideg : DirectSum.IsInternal V.bideg := by
  classical
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hpi : ∀ j : ℤ × ZMod 2, j ≠ i → ∀ y ∈ V.bideg j,
        V.toSVec.proj i.2 (V.dproj i.1 y) = 0 := by
      intro j hj y hy
      by_cases h1 : j.1 = i.1
      · have h2 : j.2 ≠ i.2 := fun h2 => hj (Prod.ext h1 h2)
        rw [V.dproj_of_mem (h1 ▸ hy.1), SVec.proj_apply_of_mem_part _ hy.2, if_neg (Ne.symm h2)]
      · rw [V.dproj_of_mem_ne hy.1 h1, map_zero]
    have h0 : V.toSVec.proj i.2 (V.dproj i.1 x) = 0 := by
      refine Submodule.iSup_induction (fun j : {j // j ≠ i} => V.bideg j)
        (motive := fun y => V.toSVec.proj i.2 (V.dproj i.1 y) = 0) ?_ ?_ ?_ ?_
      · simpa [iSup_subtype'] using hx'
      · intro j y hy; exact hpi j j.2 y hy
      · simp
      · intro y z hy hz; rw [map_add, map_add, hy, hz, add_zero]
    rwa [V.dproj_of_mem hx.1, (SVec.mem_part_iff _).1 hx.2] at h0
  · rw [eq_top_iff]
    intro v _
    refine V.induction_on_deg v (Submodule.zero_mem _) (fun n w hw => ?_)
      (fun w w' hw hw' => Submodule.add_mem _ hw hw')
    rw [← SVec.proj_apply_add V.toSVec w]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_iSup_of_mem (n, (0 : ZMod 2)) ⟨V.proj_mem 0 hw, SVec.proj_mem_part _ 0 _⟩
    · exact Submodule.mem_iSup_of_mem (n, (1 : ZMod 2)) ⟨V.proj_mem 1 hw, SVec.proj_mem_part _ 1 _⟩

/-! ## Homogeneous linear maps -/

variable {V} (W : GradedSuperspace k)

variable (V) in
/-- The linear maps homogeneous of degree `n`: `f(Vₘ) ⊆ W_{m+n}` for all `m`. -/
def degHom (n : ℤ) : Submodule k (V.toSVec ⟶ W.toSVec) where
  carrier := {f | ∀ (m : ℤ) (v : V.toSVec), v ∈ V.deg m → f v ∈ W.deg (m + n)}
  add_mem' {f g} hf hg m v hv := by
    rw [SVec.add_apply]; exact Submodule.add_mem _ (hf m v hv) (hg m v hv)
  zero_mem' m v _ := by rw [SVec.zero_apply]; exact Submodule.zero_mem _
  smul_mem' r f hf m v hv := by rw [SVec.smul_apply]; exact Submodule.smul_mem _ _ (hf m v hv)

theorem mem_degHom_iff {n : ℤ} {f : V.toSVec ⟶ W.toSVec} :
    f ∈ degHom V W n ↔ ∀ (m : ℤ) (v : V.toSVec), v ∈ V.deg m → f v ∈ W.deg (m + n) := Iff.rfl

theorem apply_mem_deg {n : ℤ} {f : V.toSVec ⟶ W.toSVec} (hf : f ∈ degHom V W n) {m : ℤ}
    {v : V.toSVec} (hv : v ∈ V.deg m) : f v ∈ W.deg (m + n) :=
  hf m v hv

variable {W}

/-- The parity components of a homogeneous linear map are homogeneous of the same degree. -/
theorem homProj_mem_degHom (p : ZMod 2) {n : ℤ} {f : V.toSVec ⟶ W.toSVec}
    (hf : f ∈ degHom V W n) : SVec.homProj p f ∈ degHom V W n := fun m v hv => by
  rw [SVec.homProj_apply]
  exact Submodule.add_mem _ (W.proj_mem _ (hf m _ (V.proj_mem 0 hv)))
    (W.proj_mem _ (hf m _ (V.proj_mem 1 hv)))

theorem proj_mem_degHom (p : ZMod 2) {n : ℤ} {f : V.toSVec ⟶ W.toSVec}
    (hf : f ∈ degHom V W n) : proj k p f ∈ degHom V W n := by
  rw [SVec.proj_eq_homProj]; exact homProj_mem_degHom p hf

/-- Evaluation at a vector, as a linear map on morphisms of `SVec k`. -/
def evalHom (v : V.toSVec) : (V.toSVec ⟶ W.toSVec) →ₗ[k] W.toSVec where
  toFun f := f v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (V W) in
/-- The homogeneous linear maps of distinct degrees are independent. -/
theorem iSupIndep_degHom : iSupIndep (degHom V W) := by
  refine iSupIndep_of_eval (degHom V W) (A := Σ m : ℤ, V.deg m) (N := fun _ => W.toSVec)
    (fun x => evalHom (x.2 : V.toSVec)) (fun x n => W.deg (x.1 + n))
    (fun x => W.isInternal_deg.submodule_iSupIndep.comp (add_right_injective x.1)) ?_ ?_
  · rintro ⟨m, v⟩ n f ⟨g, hg, rfl⟩
    exact hg m v v.2
  · intro f hf
    ext v
    rw [SVec.zero_apply]
    refine V.induction_on_deg v (map_zero f) (fun n w hw => hf ⟨n, ⟨w, hw⟩⟩)
      (fun w w' hw hw' => by rw [map_add, hw, hw', add_zero])

variable (k) in
/-- The graded hom family defining `GSVec k`: the homogeneous linear maps of each degree. -/
def family : GradedHomFamily k (SVec k) (GradedSuperspace k) where
  obj := toSVec
  deg := degHom
  proj_mem p hf := proj_mem_degHom p hf
  id_mem V m v hv := by rw [add_zero]; exact hv
  comp_mem {U V W a b f g} hf hg m v hv := by
    rw [SVec.comp_apply, ← add_assoc]; exact hg _ _ (hf m v hv)
  indep := iSupIndep_degHom

/-! ## Parity and degree shifts of graded superspaces -/

variable (V)

/-- `Π V`: the superspace `V` with the opposite parity, with the same degrees. -/
def piObj : GradedSuperspace k where
  toSVec := SVec.piObj V.toSVec
  deg := V.deg
  isInternal_deg := V.isInternal_deg
  odd_mem {n v} hv := by
    rw [show (SVec.piObj V.toSVec).odd v =
        (LinearMap.id - V.toSVec.odd : V.toSVec →ₗ[k] V.toSVec) v from rfl,
      LinearMap.sub_apply, LinearMap.id_apply]
    exact Submodule.sub_mem _ hv (V.odd_mem hv)

/-- The shift `(shift V a)ₙ = V_{n+a}` of the grading. -/
def shift (a : ℤ) : GradedSuperspace k where
  toSVec := V.toSVec
  deg n := V.deg (n + a)
  isInternal_deg := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨V.isInternal_deg.submodule_iSupIndep.comp (add_left_injective a), ?_⟩
    rw [(add_right_surjective a).iSup_comp V.deg]
    exact V.isInternal_deg.submodule_iSup_eq_top
  odd_mem hv := V.odd_mem hv

@[simp] theorem shift_toSVec (a : ℤ) : (V.shift a).toSVec = V.toSVec := rfl

@[simp] theorem shift_deg (a n : ℤ) : (V.shift a).deg n = V.deg (n + a) := rfl

@[simp] theorem piObj_deg (n : ℤ) : V.piObj.deg n = V.deg n := rfl

/-- A linear map homogeneous of degree `n` between `V` and `W` is homogeneous of degree `n`
between their shifts by `a`. -/
theorem mem_degHom_shift {a n : ℤ} {f : V.toSVec ⟶ W.toSVec} (hf : f ∈ degHom V W n) :
    f ∈ degHom (V.shift a) (W.shift a) n := fun m v hv => by
  rw [shift_deg, add_right_comm]; exact hf _ _ hv

end GradedSuperspace

/-! ## The graded supercategory `GSVec` -/

/-- **Brundan–Ellis, §6 (after Definition 6.1).** The graded supercategory `GSVec k` of graded
superspaces: `Hom(V, W) = ⨁ₙ Hom(V, W)ₙ`, with `Hom(V, W)ₙ` the linear maps homogeneous of
degree `n`. -/
abbrev GSVec (k : Type u) [CommRing k] := GradedSubcategory (GradedSuperspace.family k)

namespace GSVec

open GradedSuperspace GradedSubcategory

/-- A graded superspace, as an object of `GSVec k`. -/
abbrev of (V : GradedSuperspace k) : GSVec k := ⟨V⟩

theorem hom_def (V W : GSVec k) : (V ⟶ W) = ⨆ n, degHom V.as W.as n := rfl

theorem mem_degree_iff {V W : GSVec k} {n : ℤ} {f : V ⟶ W} :
    f ∈ GradedSupercategory.degree (R := k) V W n ↔
      ∀ (m : ℤ) (v : V.as.toSVec), v ∈ V.as.deg m → f.1 v ∈ W.as.deg (m + n) := Iff.rfl

theorem mem_parity_iff {V W : GSVec k} {p : ZMod 2} {f : V ⟶ W} :
    f ∈ parity (R := k) V W p ↔ f.1 ∈ SVec.parityHom V.as.toSVec W.as.toSVec p := Iff.rfl

/-! ### The parity shift `Π` (Example 1.8 with `A = B = k`) -/

/-- The odd isomorphism `ζ_V : Π V → V` of degree `0`, the identity function. -/
def ζIso (V : GradedSuperspace k) : of V.piObj ≅ of V :=
  isoMk (SVec.ζIso V.toSVec) (m := 0) (n := 0) (fun m v hv => by rw [add_zero]; exact hv)
    (fun m v hv => by rw [add_zero]; exact hv)

theorem ζIso_hom_mem (V : GradedSuperspace k) : (ζIso V).hom ∈ parity (R := k) _ _ 1 :=
  SVec.ζIso_hom_mem V.toSVec

theorem ζIso_hom_mem_degree (V : GradedSuperspace k) :
    (ζIso V).hom ∈ GradedSupercategory.degree (R := k) _ _ 0 := fun m v hv => by
  rw [add_zero]; exact hv

/-- **Brundan–Ellis, Example 1.8 (for `A = B = k`, graded).** `GSVec k` is a Π-supercategory,
with `ζ_V : Π V → V` the identity function. -/
instance instPiSupercategory : PiSupercategory k (GSVec k) :=
  PiSupercategory.ofIso (fun V => of V.as.piObj) (fun V => ζIso V.as) (fun V => ζIso_hom_mem V.as)

theorem pi_obj (V : GSVec k) : (PiSupercategory.pi (R := k)).obj V = of V.as.piObj := rfl

/-- `Π f = (-1)^{|f|} f` on the underlying linear maps. -/
theorem pi_map_val {V W : GSVec k} (f : V ⟶ W) :
    ((PiSupercategory.pi (R := k)).map f).1 = twist k 1 f.1 := by
  change ((ζIso V.as).hom ≫ twist k 1 f ≫ (ζIso W.as).inv).1 = _
  rw [comp_val, comp_val, twist_val]
  rfl

/-! ### The degree shifts `Q`, `Q⁻¹` (the example after Definition 6.4) -/

/-- `Q V`, with `(Q V)ₙ = V_{n-1}`. -/
abbrev qObj (V : GradedSuperspace k) : GradedSuperspace k := V.shift (-1)

/-- `Q⁻¹ V`, with `(Q⁻¹ V)ₙ = V_{n+1}`. -/
abbrev qinvObj (V : GradedSuperspace k) : GradedSuperspace k := V.shift 1

/-- The even isomorphism `σ_V : Q V → V` of degree `-1`, the identity function. -/
def σIso (V : GradedSuperspace k) : of (qObj V) ≅ of V :=
  isoMk (Iso.refl V.toSVec) (m := -1) (n := 1) (fun m v hv => hv)
    (fun m v hv => by rw [shift_deg, add_neg_cancel_right]; exact hv)

/-- The even isomorphism `σ̄_V : Q⁻¹ V → V` of degree `1`, the identity function. -/
def σbarIso (V : GradedSuperspace k) : of (qinvObj V) ≅ of V :=
  isoMk (Iso.refl V.toSVec) (m := 1) (n := -1) (fun m v hv => hv)
    (fun m v hv => by rw [shift_deg, neg_add_cancel_right]; exact hv)

theorem σIso_hom_mem (V : GradedSuperspace k) : (σIso V).hom ∈ parity (R := k) _ _ 0 :=
  mem_parity_iff.2 (id_mem V.toSVec)

theorem σIso_hom_mem_degree (V : GradedSuperspace k) :
    (σIso V).hom ∈ GradedSupercategory.degree (R := k) _ _ (-1) := fun _ _ hv => hv

theorem σbarIso_hom_mem (V : GradedSuperspace k) : (σbarIso V).hom ∈ parity (R := k) _ _ 0 :=
  mem_parity_iff.2 (id_mem V.toSVec)

theorem σbarIso_hom_mem_degree (V : GradedSuperspace k) :
    (σbarIso V).hom ∈ GradedSupercategory.degree (R := k) _ _ 1 := fun _ _ hv => hv

/-- **Brundan–Ellis, §6 (after Definition 6.4, for `A = B = k`).** `GSVec k` is a graded
`(Q, Π)`-supercategory, with `Q`, `Q⁻¹` the upward and downward shifts of the grading and
`σ`, `σ̄` induced by the identity functions. -/
instance instQPiSupercategory : QPiSupercategory k (GSVec k) :=
  QPiSupercategory.ofIso (fun V => ζIso_hom_mem_degree V.as) (fun V => of (qObj V.as))
    (fun V => σIso V.as) (fun V => σIso_hom_mem V.as) (fun V => σIso_hom_mem_degree V.as)
    (fun V => of (qinvObj V.as)) (fun V => σbarIso V.as) (fun V => σbarIso_hom_mem V.as)
    (fun V => σbarIso_hom_mem_degree V.as)

theorem Q_obj (V : GSVec k) : (QPiSupercategory.Q (R := k)).obj V = of (qObj V.as) := rfl

theorem Qinv_obj (V : GSVec k) : (QPiSupercategory.Qinv (R := k)).obj V = of (qinvObj V.as) := rfl

/-- `Q f = f` on the underlying linear maps. -/
theorem Q_map_val {V W : GSVec k} (f : V ⟶ W) : ((QPiSupercategory.Q (R := k)).map f).1 = f.1 := by
  change ((σIso V.as).hom ≫ f ≫ (σIso W.as).inv).1 = _
  rw [comp_val, comp_val]
  change 𝟙 V.as.toSVec ≫ f.1 ≫ 𝟙 W.as.toSVec = f.1
  rw [Category.id_comp]
  exact Category.comp_id f.1

/-- `Q⁻¹ f = f` on the underlying linear maps. -/
theorem Qinv_map_val {V W : GSVec k} (f : V ⟶ W) :
    ((QPiSupercategory.Qinv (R := k)).map f).1 = f.1 := by
  change ((σbarIso V.as).hom ≫ f ≫ (σbarIso W.as).inv).1 = _
  rw [comp_val, comp_val]
  change 𝟙 V.as.toSVec ≫ f.1 ≫ 𝟙 W.as.toSVec = f.1
  rw [Category.id_comp]
  exact Category.comp_id f.1

end GSVec

end StringDiagrams

end
