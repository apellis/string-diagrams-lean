import StringDiagrams.Super.GSVec
import StringDiagrams.Super.Superbimodule

/-!
# Graded superalgebras and the graded (Q, Π)-supercategory of graded superbimodules

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6: the
first two examples after Definition 6.1 (a graded superalgebra as a graded supercategory with
one object; the graded supercategory `A-GSMod-B` of graded `(A, B)`-superbimodules) and the
example after Definition 6.4 (`A-GSMod-B` as a graded `(Q, Π)`-supercategory).

* A *graded superalgebra* `A = ⨁ₙ Aₙ = ⨁ₙ A_{n,0} ⊕ A_{n,1}` is a superalgebra (a `k`-algebra
  with a `ℤ/2`-grading `parity`, Mathlib's `GradedAlgebra`) with a `ℤ`-grading `degree` (again
  a `GradedAlgebra`) whose components are sub-superspaces
  (`StringDiagrams.GradedSuperalgebra`); it is then a `ℤ × ℤ/2`-graded algebra
  (`GradedSuperalgebra.isInternal_bideg`, `GradedSuperalgebra.gradedAlgebraBideg`).
* `SuperalgebraCat.instGradedSupercategory`: a graded superalgebra is a graded supercategory
  with one object.
* A *graded `(A, B)`-superbimodule* `V = ⨁ₙ Vₙ = ⨁ₙ V_{n,0} ⊕ V_{n,1}` is an
  `(A, B)`-superbimodule (`SuperBimodule`, Example 1.2(iii)) with a `ℤ`-grading by
  sub-superspaces such that `Aₙ Vₘ ⊆ V_{m+n}` and `Vₘ Bₙ ⊆ V_{m+n}`
  (`StringDiagrams.GradedSuperBimodule`). The graded supercategory `GSMod 𝒢 ℋ` (the paper's
  `A-GSMod-B`) has morphisms `Hom(V, W) = ⨁ₙ Hom(V, W)ₙ`, with `Hom(V, W)ₙ` the superbimodule
  homomorphisms homogeneous of degree `n`, i.e. `f(Vₘ) ⊆ W_{m+n}` for all `m`
  (`GradedSuperBimodule.degHom`); it is the graded subcategory of `SuperBimodule` determined
  by these (`GradedSuperBimodule.family`).
* `GSMod 𝒢 ℋ` is a graded `(Q, Π)`-supercategory (`GSMod.instQPiSupercategory`): `Π` and `ζ`
  are as in Example 1.8 (`Π V` has the opposite parity, the actions `a · v · b := (-1)^{|a|} a v b`
  and the same degrees; `ζ_V : Π V → V` is the identity function), `Q` and `Q⁻¹` are the
  upward and downward shifts of the grading, `(Q V)ₙ = V_{n-1}`, `(Q⁻¹ V)ₙ = V_{n+1}`, and
  `σ`, `σ̄` are induced by the identity functions (`GSMod.σIso`, `GSMod.σbarIso`).

The paper obtains `GSVec` as `k-GSMod-k`; in the library `GSVec k` (`StringDiagrams.Super.GSVec`)
is built directly on `SVec k`, as `SVec k` is.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe u v v'

variable {k : Type u} [CommRing k] {A : Type v} [Ring A] [Algebra k A] {B : Type v'} [Ring B]
  [Algebra k B]

/-! ## Graded superalgebras -/

variable (k A) in
/-- A graded superalgebra (Brundan–Ellis, §6): a superalgebra `(A, parity)` with a `ℤ`-grading
`degree` making `A` a graded algebra, whose components are sub-superspaces, i.e. stable under
the parity projections. -/
structure GradedSuperalgebra where
  /-- The `ℤ/2`-grading. -/
  parity : ZMod 2 → Submodule k A
  /-- The `ℤ`-grading. -/
  degree : ℤ → Submodule k A
  [gradedParity : GradedAlgebra parity]
  [gradedDegree : GradedAlgebra degree]
  /-- Each homogeneous component is a sub-superspace. -/
  decompose_mem : ∀ {n : ℤ} {a : A} (p : ZMod 2), a ∈ degree n →
    (DirectSum.decompose parity a p : A) ∈ degree n

namespace GradedSuperalgebra

attribute [instance] gradedParity gradedDegree

variable (𝒢 : GradedSuperalgebra k A)

/-- The component `A_{n,p}` of degree `n` and parity `p`. -/
def bideg (np : ℤ × ZMod 2) : Submodule k A := 𝒢.degree np.1 ⊓ 𝒢.parity np.2

/-- A graded superalgebra is the direct sum `⨁_{(n,p)} A_{n,p}`: the `ℤ`- and
`ℤ/2`-gradings are independent. -/
theorem isInternal_bideg : DirectSum.IsInternal 𝒢.bideg :=
  isInternal_inf_of_decompose_mem 𝒢.degree 𝒢.parity fun _ p _ ha => 𝒢.decompose_mem p ha

instance : SetLike.GradedMonoid 𝒢.bideg where
  one_mem := ⟨SetLike.GradedOne.one_mem, SetLike.GradedOne.one_mem⟩
  mul_mem _ _ _ _ ha hb := ⟨SetLike.GradedMul.mul_mem ha.1 hb.1, SetLike.GradedMul.mul_mem ha.2 hb.2⟩

/-- A graded superalgebra is a `ℤ × ℤ/2`-graded algebra. -/
def gradedAlgebraBideg : GradedAlgebra 𝒢.bideg :=
  { (inferInstance : SetLike.GradedMonoid 𝒢.bideg), 𝒢.isInternal_bideg.chooseDecomposition with }

end GradedSuperalgebra

/-! ## A graded superalgebra as a graded supercategory with one object -/

namespace SuperalgebraCat

variable (𝒜 : ZMod 2 → Submodule k A) [GradedAlgebra 𝒜]

/-- The parity components of a morphism of `SuperalgebraCat 𝒜` are the homogeneous components
of the element of `A`. -/
theorem proj_eq_decompose (p : ZMod 2) {X Y : SuperalgebraCat 𝒜} (f : X ⟶ Y) :
    proj k p f = (DirectSum.decompose 𝒜 (toElem f) p : A) := by
  refine DirectSum.Decomposition.inductionOn 𝒜
    (motive := fun a => proj k p (ofElem a : X ⟶ Y) = (DirectSum.decompose 𝒜 a p : A)) ?_ ?_ ?_
    (toElem f)
  · change proj k p (ofElem (0 : A) : X ⟶ Y) = (DirectSum.decompose 𝒜 (0 : A) p : A)
    rw [DirectSum.decompose_zero, DirectSum.zero_apply, Submodule.coe_zero]
    exact map_zero _
  · intro q a
    by_cases h : q = p
    · subst h
      rw [proj_of_mem ((mem_parity_iff 𝒜 (f := (ofElem (a : A) : X ⟶ Y))).2 a.2),
        DirectSum.decompose_of_mem_same 𝒜 a.2]
      rfl
    · rw [proj_of_mem_ne ((mem_parity_iff 𝒜 (f := (ofElem (a : A) : X ⟶ Y))).2 a.2) h,
        DirectSum.decompose_of_mem_ne 𝒜 a.2 h]
  · intro a b ha hb
    rw [show (ofElem (a + b) : X ⟶ Y) = ofElem a + ofElem b from rfl, map_add, ha, hb,
      DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]

/-- **Brundan–Ellis, §6 (after Definition 6.1).** A graded superalgebra is a graded
supercategory with one object. -/
instance instGradedSupercategory (𝒢 : GradedSuperalgebra k A) :
    GradedSupercategory k (SuperalgebraCat 𝒢.parity) where
  degree _ _ n := 𝒢.degree n
  isInternal_degree _ _ := DirectSum.Decomposition.isInternal 𝒢.degree
  proj_mem_degree p hf := by
    rw [proj_eq_decompose]; exact 𝒢.decompose_mem p hf
  id_mem_degree _ := SetLike.GradedOne.one_mem
  comp_mem_degree hf hg := by
    rw [add_comm]; exact SetLike.GradedMul.mul_mem hg hf

theorem mem_degree_iff (𝒢 : GradedSuperalgebra k A) {X Y : SuperalgebraCat 𝒢.parity} {n : ℤ}
    {f : X ⟶ Y} : f ∈ GradedSupercategory.degree (R := k) X Y n ↔ toElem f ∈ 𝒢.degree n :=
  Iff.rfl

end SuperalgebraCat

/-! ## Graded superbimodules -/

namespace SuperBimodule

variable {𝒜 : ZMod 2 → Submodule k A} {ℬ : ZMod 2 → Submodule k B} [GradedAlgebra ℬ]

theorem proj_val (p : ZMod 2) {V W : SuperBimodule 𝒜 ℬ} (f : V ⟶ W) :
    (proj k p f).1 = proj k p f.1 := by
  have e : f = ⟨proj k p f.1, f.2.proj p⟩ + ⟨proj k (p + 1) f.1, f.2.proj (p + 1)⟩ :=
    Subtype.ext (proj_add_proj_add_one (R := k) p f.1).symm
  rw [proj_eq_of_add e (mem_parity_iff.2 (proj_mem p _)) (mem_parity_iff.2 (proj_mem _ _))]

end SuperBimodule

variable (𝒢 : GradedSuperalgebra k A) (ℋ : GradedSuperalgebra k B)

/-- A graded `(A, B)`-superbimodule (Brundan–Ellis, §6): an `(A, B)`-superbimodule with a
`ℤ`-grading by sub-superspaces such that `Aₙ Vₘ ⊆ V_{m+n}` and `Vₘ Bₙ ⊆ V_{m+n}`. -/
structure GradedSuperBimodule where
  /-- The underlying superbimodule. -/
  toSuperBimodule : SuperBimodule 𝒢.parity ℋ.parity
  /-- The homogeneous component of degree `n`. -/
  deg : ℤ → Submodule k toSuperBimodule.toSVec
  isInternal_deg : DirectSum.IsInternal deg
  /-- Each homogeneous component is a sub-superspace. -/
  odd_mem : ∀ {n : ℤ} {v : toSuperBimodule.toSVec}, v ∈ deg n → toSuperBimodule.toSVec.odd v ∈ deg n
  /-- `Aₙ Vₘ ⊆ V_{m+n}`. -/
  lact_mem : ∀ {n : ℤ} {a : A}, a ∈ 𝒢.degree n → ∀ {m : ℤ} {v : toSuperBimodule.toSVec},
    v ∈ deg m → toSuperBimodule.lact a v ∈ deg (m + n)
  /-- `Vₘ Bₙ ⊆ V_{m+n}`. -/
  ract_mem : ∀ {n : ℤ} {b : B}, b ∈ ℋ.degree n → ∀ {m : ℤ} {v : toSuperBimodule.toSVec},
    v ∈ deg m → toSuperBimodule.ract b v ∈ deg (m + n)

namespace GradedSuperBimodule

variable {𝒢 ℋ} (V : GradedSuperBimodule 𝒢 ℋ)

/-- The underlying graded superspace. -/
def toGradedSuperspace : GradedSuperspace k where
  toSVec := V.toSuperBimodule.toSVec
  deg := V.deg
  isInternal_deg := V.isInternal_deg
  odd_mem := V.odd_mem

@[simp] theorem toGradedSuperspace_toSVec : V.toGradedSuperspace.toSVec = V.toSuperBimodule.toSVec :=
  rfl

@[simp] theorem toGradedSuperspace_deg (n : ℤ) : V.toGradedSuperspace.deg n = V.deg n := rfl

/-- Left multiplication by `a ∈ Aₙ` is homogeneous of degree `n`. -/
theorem lact_mem_degHom {n : ℤ} {a : A} (ha : a ∈ 𝒢.degree n) :
    V.toSuperBimodule.lact a ∈ GradedSuperspace.degHom V.toGradedSuperspace V.toGradedSuperspace n :=
  fun _ _ hv => V.lact_mem ha hv

/-- Right multiplication by `b ∈ Bₙ` is homogeneous of degree `n`. -/
theorem ract_mem_degHom {n : ℤ} {b : B} (hb : b ∈ ℋ.degree n) :
    V.toSuperBimodule.ract b ∈ GradedSuperspace.degHom V.toGradedSuperspace V.toGradedSuperspace n :=
  fun _ _ hv => V.ract_mem hb hv

variable {V} (W : GradedSuperBimodule 𝒢 ℋ)

variable (V) in
/-- The superbimodule homomorphisms homogeneous of degree `n`: `f(Vₘ) ⊆ W_{m+n}` for all
`m`. -/
def degHom (n : ℤ) : Submodule k (V.toSuperBimodule ⟶ W.toSuperBimodule) :=
  (GradedSuperspace.degHom V.toGradedSuperspace W.toGradedSuperspace n).comap
    (SuperBimodule.homSubmodule _ _).subtype

theorem mem_degHom_iff {n : ℤ} {f : V.toSuperBimodule ⟶ W.toSuperBimodule} :
    f ∈ degHom V W n ↔
      ∀ (m : ℤ) (v : V.toSuperBimodule.toSVec), v ∈ V.deg m → f.1 v ∈ W.deg (m + n) :=
  Iff.rfl

variable {W}

variable (𝒢 ℋ) in
/-- The graded hom family defining `A-GSMod-B`: the superbimodule homomorphisms homogeneous of
each degree. -/
def family : GradedHomFamily k (SuperBimodule 𝒢.parity ℋ.parity) (GradedSuperBimodule 𝒢 ℋ) where
  obj := toSuperBimodule
  deg := degHom
  proj_mem {V W n f} p hf := by
    change (proj k p f).1 ∈ GradedSuperspace.degHom V.toGradedSuperspace W.toGradedSuperspace n
    rw [SuperBimodule.proj_val]
    exact GradedSuperspace.proj_mem_degHom p hf
  id_mem V := (GradedSuperspace.family k).id_mem V.toGradedSuperspace
  comp_mem hf hg := (GradedSuperspace.family k).comp_mem hf hg
  indep V W := iSupIndep_comap_of_injective
    (GradedSuperspace.iSupIndep_degHom V.toGradedSuperspace W.toGradedSuperspace) _
    Subtype.val_injective

/-! ### Parity and degree shifts -/

variable (V)

/-- `Π V` (Example 1.8): the superbimodule `Π V` of `SuperBimodule.piObj`, with the same
degrees. -/
def piObj : GradedSuperBimodule 𝒢 ℋ where
  toSuperBimodule := SuperBimodule.piObj V.toSuperBimodule
  deg := V.deg
  isInternal_deg := V.isInternal_deg
  odd_mem hv := V.toGradedSuperspace.piObj.odd_mem hv
  lact_mem {_ _} ha {_ _} hv :=
    (GradedSuperspace.family k).twist_mem 1 (V.lact_mem_degHom ha) _ _ hv
  ract_mem {_ _} hb {_ _} hv := V.ract_mem hb hv

/-- The shift `(shift V a)ₙ = V_{n+a}` of the grading. -/
def shift (a : ℤ) : GradedSuperBimodule 𝒢 ℋ where
  toSuperBimodule := V.toSuperBimodule
  deg n := V.deg (n + a)
  isInternal_deg := (V.toGradedSuperspace.shift a).isInternal_deg
  odd_mem hv := V.odd_mem hv
  lact_mem {_ _} ha {_ _} hv := by rw [add_right_comm]; exact V.lact_mem ha hv
  ract_mem {_ _} hb {_ _} hv := by rw [add_right_comm]; exact V.ract_mem hb hv

@[simp] theorem shift_deg (a n : ℤ) : (V.shift a).deg n = V.deg (n + a) := rfl

@[simp] theorem piObj_deg (n : ℤ) : V.piObj.deg n = V.deg n := rfl

end GradedSuperBimodule

/-! ## The graded (Q, Π)-supercategory `A-GSMod-B` -/

/-- **Brundan–Ellis, §6 (after Definition 6.1).** The graded supercategory `A-GSMod-B` of graded
`(A, B)`-superbimodules: `Hom(V, W) = ⨁ₙ Hom(V, W)ₙ`, with `Hom(V, W)ₙ` the superbimodule
homomorphisms homogeneous of degree `n`. -/
abbrev GSMod := GradedSubcategory (GradedSuperBimodule.family 𝒢 ℋ)

namespace GSMod

open GradedSuperBimodule GradedSubcategory

variable {𝒢 ℋ}

/-- A graded superbimodule, as an object of `A-GSMod-B`. -/
abbrev of (V : GradedSuperBimodule 𝒢 ℋ) : GSMod 𝒢 ℋ := ⟨V⟩

theorem mem_degree_iff {V W : GSMod 𝒢 ℋ} {n : ℤ} {f : V ⟶ W} :
    f ∈ GradedSupercategory.degree (R := k) V W n ↔
      ∀ (m : ℤ) (v : V.as.toSuperBimodule.toSVec), v ∈ V.as.deg m → f.1.1 v ∈ W.as.deg (m + n) :=
  Iff.rfl

theorem mem_parity_iff {V W : GSMod 𝒢 ℋ} {p : ZMod 2} {f : V ⟶ W} :
    f ∈ parity (R := k) V W p ↔
      f.1.1 ∈ SVec.parityHom V.as.toSuperBimodule.toSVec W.as.toSuperBimodule.toSVec p :=
  Iff.rfl

/-- The odd isomorphism `ζ_V : Π V → V` of degree `0`, the identity function (Example 1.8). -/
def ζIso (V : GradedSuperBimodule 𝒢 ℋ) : of V.piObj ≅ of V :=
  isoMk (SuperBimodule.ζIso V.toSuperBimodule) (m := 0) (n := 0)
    (fun m v hv => by rw [add_zero]; exact hv) (fun m v hv => by rw [add_zero]; exact hv)

theorem ζIso_hom_mem (V : GradedSuperBimodule 𝒢 ℋ) : (ζIso V).hom ∈ parity (R := k) _ _ 1 :=
  SuperBimodule.ζIso_hom_mem V.toSuperBimodule

theorem ζIso_hom_mem_degree (V : GradedSuperBimodule 𝒢 ℋ) :
    (ζIso V).hom ∈ GradedSupercategory.degree (R := k) _ _ 0 := fun m v hv => by
  rw [add_zero]; exact hv

/-- **Brundan–Ellis, Example 1.8 (graded).** `A-GSMod-B` is a Π-supercategory, with
`ζ_V : Π V → V` the identity function. -/
instance instPiSupercategory : PiSupercategory k (GSMod 𝒢 ℋ) :=
  PiSupercategory.ofIso (fun V => of V.as.piObj) (fun V => ζIso V.as) (fun V => ζIso_hom_mem V.as)

theorem pi_obj (V : GSMod 𝒢 ℋ) : (PiSupercategory.pi (R := k)).obj V = of V.as.piObj := rfl

/-- `Q V`, with `(Q V)ₙ = V_{n-1}`. -/
abbrev qObj (V : GradedSuperBimodule 𝒢 ℋ) : GradedSuperBimodule 𝒢 ℋ := V.shift (-1)

/-- `Q⁻¹ V`, with `(Q⁻¹ V)ₙ = V_{n+1}`. -/
abbrev qinvObj (V : GradedSuperBimodule 𝒢 ℋ) : GradedSuperBimodule 𝒢 ℋ := V.shift 1

/-- The even isomorphism `σ_V : Q V → V` of degree `-1`, the identity function. -/
def σIso (V : GradedSuperBimodule 𝒢 ℋ) : of (qObj V) ≅ of V :=
  isoMk (Iso.refl V.toSuperBimodule) (m := -1) (n := 1) (fun m v hv => hv)
    (fun m v hv => by change _ ∈ V.deg (m + 1 + -1); rw [add_neg_cancel_right]; exact hv)

/-- The even isomorphism `σ̄_V : Q⁻¹ V → V` of degree `1`, the identity function. -/
def σbarIso (V : GradedSuperBimodule 𝒢 ℋ) : of (qinvObj V) ≅ of V :=
  isoMk (Iso.refl V.toSuperBimodule) (m := 1) (n := -1) (fun m v hv => hv)
    (fun m v hv => by change _ ∈ V.deg (m + -1 + 1); rw [neg_add_cancel_right]; exact hv)

theorem σIso_hom_mem (V : GradedSuperBimodule 𝒢 ℋ) : (σIso V).hom ∈ parity (R := k) _ _ 0 :=
  GradedSubcategory.mem_parity_iff.2 (id_mem V.toSuperBimodule)

theorem σIso_hom_mem_degree (V : GradedSuperBimodule 𝒢 ℋ) :
    (σIso V).hom ∈ GradedSupercategory.degree (R := k) _ _ (-1) := fun _ _ hv => hv

theorem σbarIso_hom_mem (V : GradedSuperBimodule 𝒢 ℋ) :
    (σbarIso V).hom ∈ parity (R := k) _ _ 0 :=
  GradedSubcategory.mem_parity_iff.2 (id_mem V.toSuperBimodule)

theorem σbarIso_hom_mem_degree (V : GradedSuperBimodule 𝒢 ℋ) :
    (σbarIso V).hom ∈ GradedSupercategory.degree (R := k) _ _ 1 := fun _ _ hv => hv

/-- **Brundan–Ellis, §6 (after Definition 6.4).** `A-GSMod-B` is a graded
`(Q, Π)`-supercategory, with `Π`, `ζ` as in Example 1.8, `Q`, `Q⁻¹` the upward and downward
shifts of the grading, and `σ`, `σ̄` induced by the identity functions. -/
instance instQPiSupercategory : QPiSupercategory k (GSMod 𝒢 ℋ) :=
  QPiSupercategory.ofIso (fun V => ζIso_hom_mem_degree V.as) (fun V => of (qObj V.as))
    (fun V => σIso V.as) (fun V => σIso_hom_mem V.as) (fun V => σIso_hom_mem_degree V.as)
    (fun V => of (qinvObj V.as)) (fun V => σbarIso V.as) (fun V => σbarIso_hom_mem V.as)
    (fun V => σbarIso_hom_mem_degree V.as)

theorem Q_obj (V : GSMod 𝒢 ℋ) : (QPiSupercategory.Q (R := k)).obj V = of (qObj V.as) := rfl

theorem Qinv_obj (V : GSMod 𝒢 ℋ) : (QPiSupercategory.Qinv (R := k)).obj V = of (qinvObj V.as) :=
  rfl

/-- `Q f = f` on the underlying superbimodule homomorphisms. -/
theorem Q_map_val {V W : GSMod 𝒢 ℋ} (f : V ⟶ W) :
    ((QPiSupercategory.Q (R := k)).map f).1 = f.1 := by
  change ((σIso V.as).hom ≫ f ≫ (σIso W.as).inv).1 = _
  rw [comp_val, comp_val]
  change 𝟙 V.as.toSuperBimodule ≫ f.1 ≫ 𝟙 W.as.toSuperBimodule = f.1
  rw [Category.id_comp]
  exact Category.comp_id f.1

/-- `Q⁻¹ f = f` on the underlying superbimodule homomorphisms. -/
theorem Qinv_map_val {V W : GSMod 𝒢 ℋ} (f : V ⟶ W) :
    ((QPiSupercategory.Qinv (R := k)).map f).1 = f.1 := by
  change ((σbarIso V.as).hom ≫ f ≫ (σbarIso W.as).inv).1 = _
  rw [comp_val, comp_val]
  change 𝟙 V.as.toSuperBimodule ≫ f.1 ≫ 𝟙 W.as.toSuperBimodule = f.1
  rw [Category.id_comp]
  exact Category.comp_id f.1

end GSMod

end StringDiagrams

end
