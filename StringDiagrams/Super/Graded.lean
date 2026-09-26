import StringDiagrams.Super.Supernatural
import StringDiagrams.Super.Underlying

/-!
# Graded supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
§6, Definition 6.1.

A *graded superspace* is a `ℤ`-graded superspace `V = ⨁ₙ Vₙ = ⨁ₙ (V_{n,0} ⊕ V_{n,1})`, the
`ℤ`- and `ℤ/2`-gradings being independent. A *graded supercategory* is a category enriched in
the symmetric monoidal category `GSVec` of graded superspaces and degree-preserving even
linear maps.

## Encoding

As `StringDiagrams.Supercategory` unpacks `SVec`-enrichment, we unpack `GSVec`-enrichment on
top of a supercategory: `StringDiagrams.GradedSupercategory R C` adds submodules
`degree X Y n` of each morphism module such that

* the morphism module is the internal direct sum of the `degree X Y n` (`isInternal_degree`);
* each `degree X Y n` is a sub-superspace, i.e. stable under the parity projections
  (`proj_mem_degree`), so that `degree X Y n = V_{n,0} ⊕ V_{n,1}` with
  `V_{n,p} = degree X Y n ⊓ parity X Y p`;
* identities have degree `0` and composition adds degrees.

Together with the axioms of `Supercategory` (identities even, composition adds parities),
this says exactly that each morphism space is the bigraded module `⨁_{(n,p)} V_{n,p}`
(`GradedSupercategory.isInternal_bigrading`) and that composition is bihomogeneous, i.e.
the enriched definition.

## Main definitions

* `GradedSupercategory R C` (Definition 6.1), degree projections `dproj R n`.
* `GradedSupercategory.IsGradedSuperfunctor R F`: a superfunctor preserving degrees
  (Definition 6.1).
* `GradedSupercategory.IsGradedSupernatural R p n x`: a supernatural transformation
  homogeneous of parity `p` and degree `n` (Definition 6.1).
* `GradedSupercategory.GradedSuperNatTrans R F G`: a graded supernatural transformation, a
  finite sum of homogeneous ones (Definition 6.1).
* `GradedSupercategory.GradedSuperequivalence R F`: a graded superfunctor with a graded
  quasi-inverse and even unit and counit isomorphisms of degree zero;
  `GradedSuperequivalence.ofFullyFaithful`.
* `GradedSupercategory.DegreeZero R C`: the supercategory of morphisms of degree zero;
  the *underlying category* of the paper (even morphisms of degree zero) is
  `Underlying R (DegreeZero R C)` (`GradedSupercategory.GUnderlying`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ w₃ w₄ w₅ w₆

/-- A graded supercategory (Brundan–Ellis, Definition 6.1), in unpacked form: a
supercategory together with a `ℤ`-grading of each morphism module by sub-superspaces, with
identities of degree `0` and composition adding degrees. See the module documentation. -/
class GradedSupercategory (R : Type w) [CommRing R] (C : Type w₁) [Category.{w₂} C]
    [Preadditive C] [Linear R C] [Supercategory R C] where
  /-- The morphisms of degree `n`. -/
  degree : ∀ X Y : C, ℤ → Submodule R (X ⟶ Y)
  /-- Every morphism is uniquely a finite sum of homogeneous morphisms. -/
  isInternal_degree : ∀ X Y : C, DirectSum.IsInternal (degree X Y)
  /-- Each homogeneous component is a sub-superspace. -/
  proj_mem_degree : ∀ {X Y : C} {n : ℤ} {f : X ⟶ Y} (p : ZMod 2),
    f ∈ degree X Y n → proj R p f ∈ degree X Y n
  /-- Identities have degree zero. -/
  id_mem_degree : ∀ X : C, 𝟙 X ∈ degree X X 0
  /-- Composition adds degrees. -/
  comp_mem_degree : ∀ {X Y Z : C} {m n : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z},
    f ∈ degree X Y m → g ∈ degree Y Z n → f ≫ g ∈ degree X Z (m + n)

namespace GradedSupercategory

variable {R : Type w} [CommRing R]
  {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [Supercategory R C]
  [GradedSupercategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [GradedSupercategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [Supercategory R E]
  [GradedSupercategory R E]

/-! ## Degree projections -/

section Proj

variable (R) in
/-- The decomposition of a morphism module into homogeneous components. -/
def degreeDecomposition (X Y : C) : DirectSum.Decomposition (degree (R := R) X Y) :=
  (isInternal_degree X Y).chooseDecomposition

variable (R) in
/-- The degree-`n` component of morphisms `X ⟶ Y`. -/
def dproj (n : ℤ) {X Y : C} : (X ⟶ Y) →ₗ[R] (X ⟶ Y) :=
  letI := degreeDecomposition R X Y
  (degree (R := R) X Y n).subtype ∘ₗ
    (DirectSum.component R ℤ (fun m => degree (R := R) X Y m) n) ∘ₗ
      (DirectSum.decomposeLinearEquiv (degree (R := R) X Y)).toLinearMap

theorem dproj_apply (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    letI := degreeDecomposition R X Y
    dproj R n f = (DirectSum.decompose (degree (R := R) X Y) f n : X ⟶ Y) := rfl

theorem dproj_mem (n : ℤ) {X Y : C} (f : X ⟶ Y) : dproj R n f ∈ degree (R := R) X Y n :=
  letI := degreeDecomposition R X Y
  (DirectSum.decompose (degree (R := R) X Y) f n).2

theorem dproj_of_mem {n : ℤ} {X Y : C} {f : X ⟶ Y} (hf : f ∈ degree (R := R) X Y n) :
    dproj R n f = f :=
  letI := degreeDecomposition R X Y
  DirectSum.decompose_of_mem_same _ hf

theorem dproj_of_mem_ne {m n : ℤ} {X Y : C} {f : X ⟶ Y} (hf : f ∈ degree (R := R) X Y m)
    (h : m ≠ n) : dproj R n f = 0 :=
  letI := degreeDecomposition R X Y
  DirectSum.decompose_of_mem_ne _ hf h

/-- Induction on morphisms via homogeneous ones. -/
@[elab_as_elim]
theorem induction_on_degree {X Y : C} {P : (X ⟶ Y) → Prop} (f : X ⟶ Y) (zero : P 0)
    (hom : ∀ (n : ℤ) (g : X ⟶ Y), g ∈ degree (R := R) X Y n → P g)
    (add : ∀ g h, P g → P h → P (g + h)) : P f :=
  letI := degreeDecomposition R X Y
  DirectSum.Decomposition.inductionOn (degree (R := R) X Y) zero (fun g => hom _ _ g.2) add f

/-- A morphism all of whose components other than the degree-`n` one vanish has degree
`n`. -/
theorem mem_degree_of_dproj {n : ℤ} {X Y : C} {f : X ⟶ Y}
    (h : ∀ m, m ≠ n → dproj R m f = 0) : f ∈ degree (R := R) X Y n := by
  letI := degreeDecomposition R X Y
  have e : DirectSum.decompose (degree (R := R) X Y) f =
      DirectSum.of (fun m => degree (R := R) X Y m) n
        (DirectSum.decompose (degree (R := R) X Y) f n) := by
    ext m
    by_cases hm : m = n
    · subst hm; simp
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hm)]
      exact h m hm
  have := congrArg (DirectSum.decompose (degree (R := R) X Y)).symm e
  rw [Equiv.symm_apply_apply, DirectSum.decompose_symm_of] at this
  rw [this]; exact Submodule.coe_mem _

/-- The parity projections preserve the degree projections. -/
theorem proj_dproj (p : ZMod 2) (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    proj R p (dproj R n f) = dproj R n (proj R p f) := by
  refine induction_on_degree (R := R) f (by simp) (fun m g hg => ?_) (fun g h hg hh => ?_)
  · by_cases h : m = n
    · subst h
      rw [dproj_of_mem hg, dproj_of_mem (proj_mem_degree p hg)]
    · rw [dproj_of_mem_ne hg h, dproj_of_mem_ne (proj_mem_degree p hg) h, map_zero]
  · rw [map_add, map_add, hg, hh, map_add, map_add]

theorem twist_mem_degree (p : ZMod 2) {n : ℤ} {X Y : C} {f : X ⟶ Y}
    (hf : f ∈ degree (R := R) X Y n) : twist R p f ∈ degree (R := R) X Y n := by
  rw [twist_apply]
  exact Submodule.add_mem _ (proj_mem_degree 0 hf)
    (Submodule.smul_mem _ _ (proj_mem_degree 1 hf))

theorem zero_mem_degree {X Y : C} (n : ℤ) : (0 : X ⟶ Y) ∈ degree (R := R) X Y n :=
  Submodule.zero_mem _

/-- The inverse of an isomorphism of degree `n` has degree `-n`. -/
theorem inv_mem_degree {n : ℤ} {X Y : C} (e : X ≅ Y) (he : e.hom ∈ degree (R := R) X Y n) :
    e.inv ∈ degree (R := R) Y X (-n) := by
  apply mem_degree_of_dproj
  intro m hm
  have key : ∀ g : Y ⟶ X, ∀ k, dproj R (n + k) (e.hom ≫ g) = e.hom ≫ dproj R k g := by
    intro g k
    refine induction_on_degree (R := R) g (by simp) (fun j g hg => ?_) (fun g h hg hh => ?_)
    · by_cases hj : j = k
      · subst hj; rw [dproj_of_mem (comp_mem_degree he hg), dproj_of_mem hg]
      · rw [dproj_of_mem_ne (comp_mem_degree he hg) (fun h => hj (add_left_cancel h)),
          dproj_of_mem_ne hg hj, Limits.comp_zero]
    · rw [Preadditive.comp_add, map_add, hg, hh, map_add, Preadditive.comp_add]
  have h1 : e.hom ≫ dproj R m e.inv = 0 := by
    rw [← key, e.hom_inv_id, dproj_of_mem_ne (id_mem_degree X)]
    omega
  calc dproj R m e.inv = e.inv ≫ e.hom ≫ dproj R m e.inv := by
        rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    _ = 0 := by rw [h1, Limits.comp_zero]

/-- The morphisms of parity `p` and degree `n`. -/
def bidegree (X Y : C) (np : ℤ × ZMod 2) : Submodule R (X ⟶ Y) :=
  degree (R := R) X Y np.1 ⊓ parity (R := R) X Y np.2

/-- **Definition 6.1.** The encoding is that of `GSVec`-enrichment: each morphism module is
the internal direct sum of the bihomogeneous parts `V_{n,p} = degree n ⊓ parity p`. -/
theorem isInternal_bigrading (X Y : C) : DirectSum.IsInternal (bidegree (R := R) X Y) := by
  classical
  letI := degreeDecomposition R X Y
  letI := decomposition R X Y
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
  · -- independence, via the linear map `f ↦ proj_p (dproj_n f)` for each index
    rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hpi : ∀ j : ℤ × ZMod 2, j ≠ i → ∀ y ∈ bidegree (R := R) X Y j,
        proj R i.2 (dproj R i.1 y) = 0 := by
      intro j hj y hy
      by_cases h1 : j.1 = i.1
      · have h2 : j.2 ≠ i.2 := fun h2 => hj (Prod.ext h1 h2)
        rw [dproj_of_mem (h1 ▸ hy.1), proj_of_mem_ne hy.2 h2]
      · rw [dproj_of_mem_ne hy.1 h1, map_zero]
    have h0 : proj R i.2 (dproj R i.1 x) = 0 := by
      refine Submodule.iSup_induction (fun j : {j // j ≠ i} => bidegree (R := R) X Y j)
        (motive := fun y => proj R i.2 (dproj R i.1 y) = 0) ?_ ?_ ?_ ?_
      · simpa [iSup_subtype'] using hx'
      · intro j y hy; exact hpi j j.2 y hy
      · simp
      · intro y z hy hz; rw [map_add, map_add, hy, hz, add_zero]
    rwa [dproj_of_mem hx.1, proj_of_mem hx.2] at h0
  · rw [eq_top_iff]
    intro f _
    refine induction_on_degree (R := R) f (Submodule.zero_mem _) (fun n g hg => ?_)
      (fun g h hg hh => Submodule.add_mem _ hg hh)
    rw [← proj_add_proj (R := R) g]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_iSup_of_mem (n, (0 : ZMod 2)) ⟨proj_mem_degree 0 hg, proj_mem 0 g⟩
    · exact Submodule.mem_iSup_of_mem (n, (1 : ZMod 2)) ⟨proj_mem_degree 1 hg, proj_mem 1 g⟩

end Proj

/-! ## Graded superfunctors -/

section Functor

variable (R) in
/-- A graded superfunctor (Brundan–Ellis, Definition 6.1): a superfunctor preserving degrees
of morphisms. -/
class IsGradedSuperfunctor (F : C ⥤ D) [F.Additive] [F.Linear R] : Prop
    extends IsSuperfunctor R F where
  /-- `F` preserves degrees. -/
  map_mem_degree : ∀ {X Y : C} {n : ℤ} {f : X ⟶ Y}, f ∈ degree (R := R) X Y n →
    F.map f ∈ degree (R := R) (F.obj X) (F.obj Y) n

instance IsGradedSuperfunctor.id : IsGradedSuperfunctor R (𝟭 C) where
  map_mem_degree hf := hf

instance IsGradedSuperfunctor.comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [F.Linear R]
    [G.Additive] [G.Linear R] [IsGradedSuperfunctor R F] [IsGradedSuperfunctor R G] :
    IsGradedSuperfunctor R (F ⋙ G) where
  map_mem_degree hf := IsGradedSuperfunctor.map_mem_degree (R := R) (F := G)
    (IsGradedSuperfunctor.map_mem_degree (F := F) hf)

theorem map_mem_degree (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    {X Y : C} {n : ℤ} {f : X ⟶ Y} (hf : f ∈ degree (R := R) X Y n) :
    F.map f ∈ degree (R := R) (F.obj X) (F.obj Y) n :=
  IsGradedSuperfunctor.map_mem_degree hf

theorem map_dproj (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] (n : ℤ)
    {X Y : C} (f : X ⟶ Y) : F.map (dproj R n f) = dproj R n (F.map f) := by
  refine induction_on_degree (R := R) f (by simp) (fun m g hg => ?_) (fun g h hg hh => ?_)
  · by_cases h : m = n
    · subst h; rw [dproj_of_mem hg, dproj_of_mem (map_mem_degree F hg)]
    · rw [dproj_of_mem_ne hg h, dproj_of_mem_ne (map_mem_degree F hg) h, F.map_zero]
  · rw [map_add, F.map_add, hg, hh, F.map_add, map_add]

/-- Faithful graded superfunctors reflect degrees. -/
theorem mem_degree_of_map_mem (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    [F.Faithful] {X Y : C} {n : ℤ} {f : X ⟶ Y}
    (hf : F.map f ∈ degree (R := R) (F.obj X) (F.obj Y) n) : f ∈ degree (R := R) X Y n :=
  mem_degree_of_dproj fun m hm => F.map_injective (by
    rw [map_dproj, F.map_zero, dproj_of_mem_ne hf (Ne.symm hm)])

end Functor

/-! ## Homogeneous graded supernatural transformations -/

section NatTrans

variable (R) in
/-- A supernatural transformation homogeneous of parity `p` and of degree `n` (Brundan–Ellis,
Definition 6.1): every component `x X` has degree `n`. -/
structure IsGradedSupernatural (p : ZMod 2) (n : ℤ) {F G : C ⥤ D}
    (x : ∀ X, F.obj X ⟶ G.obj X) : Prop extends IsSupernatural R p x where
  mem_degree : ∀ X, x X ∈ degree (R := R) (F.obj X) (G.obj X) n

variable {F G H : C ⥤ D}

omit [GradedSupercategory R C] in
theorem isGradedSupernatural_id [F.Linear R] :
    IsGradedSupernatural R 0 0 fun X => 𝟙 (F.obj X) :=
  ⟨isSupernatural_id, fun _ => id_mem_degree _⟩

omit [GradedSupercategory R C] in
/-- Vertical composition adds parities and degrees. -/
theorem IsGradedSupernatural.comp [F.Additive] [G.Additive] [G.Linear R] [H.Additive]
    [H.Linear R] {p q : ZMod 2} {m n : ℤ} {x : ∀ X, F.obj X ⟶ G.obj X}
    {y : ∀ X, G.obj X ⟶ H.obj X} (hx : IsGradedSupernatural R p m x)
    (hy : IsGradedSupernatural R q n y) :
    IsGradedSupernatural R (p + q) (m + n) fun X => x X ≫ y X :=
  ⟨hx.toIsSupernatural.comp hy.toIsSupernatural,
    fun X => comp_mem_degree (hx.mem_degree X) (hy.mem_degree X)⟩

omit [GradedSupercategory R C] in
theorem IsGradedSupernatural.whiskerRight [F.Additive] [G.Additive] [G.Linear R] {p : ZMod 2}
    {n : ℤ} {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsGradedSupernatural R p n x) (K : D ⥤ E)
    [K.Additive] [K.Linear R] [IsGradedSuperfunctor R K] :
    IsGradedSupernatural R p n (F := F ⋙ K) (G := G ⋙ K) fun X => K.map (x X) :=
  ⟨hx.toIsSupernatural.whiskerRight K, fun X => map_mem_degree K (hx.mem_degree X)⟩

theorem IsGradedSupernatural.whiskerLeft {B : Type*} [Category B] [Preadditive B] [Linear R B]
    [Supercategory R B] [GradedSupercategory R B] {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsGradedSupernatural R p n x)
    (K : B ⥤ C) [K.Additive] [K.Linear R] [IsGradedSuperfunctor R K] :
    IsGradedSupernatural R p n (F := K ⋙ F) (G := K ⋙ G) fun X => x (K.obj X) :=
  ⟨hx.toIsSupernatural.whiskerLeft K, fun X => hx.mem_degree (K.obj X)⟩

omit [GradedSupercategory R C] in
theorem IsGradedSupernatural.neg {p : ZMod 2} {n : ℤ} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsGradedSupernatural R p n x) : IsGradedSupernatural R p n fun X => -x X :=
  ⟨⟨fun X => Submodule.neg_mem _ (hx.mem X), fun hf => by
      rw [Preadditive.comp_neg, hx.naturality hf, Preadditive.neg_comp, smul_neg]⟩,
    fun X => Submodule.neg_mem _ (hx.mem_degree X)⟩

variable (R) in
/-- A graded supernatural transformation `F ⇒ G` (Brundan–Ellis, Definition 6.1): an element
of `⨁ₙ Hom(F, G)ₙ`, where `Hom(F, G)ₙ` is the superspace of supernatural transformations
homogeneous of degree `n`. It is given by its bihomogeneous components `app n p`, finitely
many degrees being nonzero. -/
@[ext]
structure GradedSuperNatTrans (F G : C ⥤ D) where
  /-- The component of degree `n` and parity `p`. -/
  app : ℤ → ZMod 2 → ∀ X, F.obj X ⟶ G.obj X
  isGradedSupernatural : ∀ n p, IsGradedSupernatural R p n (app n p)
  /-- A finite set of degrees outside of which the components vanish. -/
  support : Finset ℤ
  app_eq_zero : ∀ n, n ∉ support → ∀ p, app n p = 0

/-- The morphism `x_X = ∑_{n,p} x_{X,n,p}`. -/
def GradedSuperNatTrans.total (x : GradedSuperNatTrans R F G) (X : C) : F.obj X ⟶ G.obj X :=
  ∑ n ∈ x.support, (x.app n 0 X + x.app n 1 X)

/-- A homogeneous supernatural transformation of parity `p` and degree `n` as a graded
supernatural transformation. -/
def IsGradedSupernatural.toGraded [DecidableEq ℤ] {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsGradedSupernatural R p n x) :
    GradedSuperNatTrans R F G where
  app m q := if m = n ∧ q = p then x else 0
  isGradedSupernatural m q := by
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact hx
    · exact ⟨⟨fun X => Submodule.zero_mem _, fun _ => by simp⟩, fun X => Submodule.zero_mem _⟩
  support := {n}
  app_eq_zero m hm q := by
    rw [Finset.mem_singleton] at hm
    simp [hm]

omit [GradedSupercategory R C] in
theorem IsGradedSupernatural.toGraded_total [DecidableEq ℤ] {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsGradedSupernatural R p n x) (X : C) :
    hx.toGraded.total X = x X := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [GradedSuperNatTrans.total, IsGradedSupernatural.toGraded]

end NatTrans

/-! ## Graded superequivalences -/

section Equivalence

variable (R) in
/-- A graded superequivalence: a graded superfunctor `F` with a graded quasi-inverse and even
unit and counit isomorphisms of degree zero. -/
structure GradedSuperequivalence (F : C ⥤ D) extends Superequivalence R F where
  [inverse_isGraded : IsGradedSuperfunctor R inverse]
  unitIso_mem_degree : ∀ X, unitIso.hom.app X ∈ degree (R := R) X (inverse.obj (F.obj X)) 0
  counitIso_mem_degree : ∀ Y, counitIso.hom.app Y ∈ degree (R := R) (F.obj (inverse.obj Y)) Y 0

attribute [instance] GradedSuperequivalence.inverse_isGraded

variable (R) in
/-- Every object of the target is isomorphic to an object in the image via an even
isomorphism of degree zero. -/
def GradedEvenlyDense (F : C ⥤ D) : Prop :=
  ∀ Y : D, ∃ (X : C) (e : F.obj X ≅ Y),
    e.hom ∈ parity (R := R) (F.obj X) Y 0 ∧ e.hom ∈ degree (R := R) (F.obj X) Y 0

theorem GradedSuperequivalence.gradedEvenlyDense {F : C ⥤ D} (e : GradedSuperequivalence R F) :
    GradedEvenlyDense R F := fun Y =>
  ⟨e.inverse.obj Y, e.counitIso.app Y, e.counitIso_mem Y, e.counitIso_mem_degree Y⟩

section OfFullyFaithful

variable (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] [F.Full] [F.Faithful]
  (hF : GradedEvenlyDense R F)

/-- The object chosen by graded even density. -/
def GradedEvenlyDense.obj (Y : D) : C := (hF Y).choose

/-- The isomorphism chosen by graded even density. -/
def GradedEvenlyDense.iso (Y : D) : F.obj (hF.obj F Y) ≅ Y := (hF Y).choose_spec.choose

omit [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] [F.Additive]
  [F.Linear R] [IsGradedSuperfunctor R F] [F.Full] [F.Faithful] in
theorem GradedEvenlyDense.iso_mem (Y : D) :
    (hF.iso F Y).hom ∈ parity (R := R) (F.obj (hF.obj F Y)) Y 0 :=
  (hF Y).choose_spec.choose_spec.1

omit [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] [F.Additive]
  [F.Linear R] [IsGradedSuperfunctor R F] [F.Full] [F.Faithful] in
theorem GradedEvenlyDense.iso_mem_degree (Y : D) :
    (hF.iso F Y).hom ∈ degree (R := R) (F.obj (hF.obj F Y)) Y 0 :=
  (hF Y).choose_spec.choose_spec.2

/-- The quasi-inverse of a full, faithful, gradedly evenly dense graded superfunctor. -/
@[simps]
def GradedEvenlyDense.inverse : D ⥤ C where
  obj := hF.obj F
  map {Y Y'} g := F.preimage ((hF.iso F Y).hom ≫ g ≫ (hF.iso F Y').inv)
  map_id Y := F.map_injective (by simp)
  map_comp f g := F.map_injective (by simp)

instance GradedEvenlyDense.inverse_additive : (hF.inverse F).Additive where
  map_add := F.map_injective (by simp)

instance GradedEvenlyDense.inverse_linear : (hF.inverse F).Linear R where
  map_smul _ _ := F.map_injective (by simp [F.map_smul])

instance GradedEvenlyDense.inverse_isGraded : IsGradedSuperfunctor R (hF.inverse F) where
  map_mem {Y Y' p g} hg := by
    apply mem_of_map_mem F
    rw [GradedEvenlyDense.inverse_map, F.map_preimage]
    have := comp_mem (comp_mem (hF.iso_mem F Y) hg) (inv_mem _ (hF.iso_mem F Y'))
    simpa using this
  map_mem_degree {Y Y' n g} hg := by
    apply mem_degree_of_map_mem F
    rw [GradedEvenlyDense.inverse_map, F.map_preimage]
    have := comp_mem_degree (comp_mem_degree (hF.iso_mem_degree F Y) hg)
      (inv_mem_degree _ (hF.iso_mem_degree F Y'))
    simpa using this

/-- A full, faithful graded superfunctor that is evenly dense in degree zero is a graded
superequivalence. -/
def GradedSuperequivalence.ofFullyFaithful : GradedSuperequivalence R F where
  inverse := hF.inverse F
  unitIso := NatIso.ofComponents (fun X => F.preimageIso (hF.iso F (F.obj X)).symm)
    (fun f => F.map_injective (by simp))
  counitIso := NatIso.ofComponents (fun Y => hF.iso F Y) (fun g => by simp)
  unitIso_mem X := by
    apply mem_of_map_mem F
    simpa using inv_mem _ (hF.iso_mem F (F.obj X))
  counitIso_mem Y := hF.iso_mem F Y
  unitIso_mem_degree X := by
    apply mem_degree_of_map_mem F
    simpa using inv_mem_degree _ (hF.iso_mem_degree F (F.obj X))
  counitIso_mem_degree Y := hF.iso_mem_degree F Y

end OfFullyFaithful

end Equivalence

/-! ## Morphisms of degree zero and the underlying category -/

section DegreeZero

/-- The supercategory with the objects of a graded supercategory and its morphisms of degree
zero. -/
@[ext]
structure DegreeZero (R : Type w) (C : Type w₁) where
  /-- The object of `C`. -/
  obj : C

namespace DegreeZero

instance : Category (DegreeZero R C) where
  Hom X Y := degree (R := R) X.obj Y.obj 0
  id X := ⟨𝟙 X.obj, id_mem_degree X.obj⟩
  comp f g := ⟨f.1 ≫ g.1, by simpa using comp_mem_degree f.2 g.2⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

@[ext] theorem hom_ext {X Y : DegreeZero R C} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

@[simp] theorem id_val (X : DegreeZero R C) : (𝟙 X : X ⟶ X).1 = 𝟙 X.obj := rfl

@[simp] theorem comp_val {X Y Z : DegreeZero R C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

instance : Preadditive (DegreeZero R C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (degree (R := R) X.obj Y.obj 0))
  add_comp _ _ _ f f' g := Subtype.ext (Preadditive.add_comp _ _ _ f.1 f'.1 g.1)
  comp_add _ _ _ f g g' := Subtype.ext (Preadditive.comp_add _ _ _ f.1 g.1 g'.1)

instance : Linear R (DegreeZero R C) where
  homModule X Y := inferInstanceAs (Module R (degree (R := R) X.obj Y.obj 0))
  smul_comp _ _ _ r f g := Subtype.ext (Linear.smul_comp _ _ _ r f.1 g.1)
  comp_smul _ _ _ f r g := Subtype.ext (Linear.comp_smul _ _ _ f.1 r g.1)

@[simp] theorem add_val {X Y : DegreeZero R C} (f g : X ⟶ Y) : (f + g).1 = f.1 + g.1 := rfl

@[simp] theorem neg_val {X Y : DegreeZero R C} (f : X ⟶ Y) : (-f).1 = -f.1 := rfl

@[simp] theorem zero_val {X Y : DegreeZero R C} : (0 : X ⟶ Y).1 = 0 := rfl

@[simp] theorem sub_val {X Y : DegreeZero R C} (f g : X ⟶ Y) : (f - g).1 = f.1 - g.1 := rfl

@[simp] theorem smul_val {X Y : DegreeZero R C} (r : R) (f : X ⟶ Y) : (r • f).1 = r • f.1 :=
  rfl

/-- The parities of morphisms of degree zero. -/
def parityZ (X Y : DegreeZero R C) (p : ZMod 2) : Submodule R (X ⟶ Y) :=
  (parity (R := R) X.obj Y.obj p).comap (degree (R := R) X.obj Y.obj 0).subtype

theorem mem_parityZ {X Y : DegreeZero R C} {p : ZMod 2} {f : X ⟶ Y} :
    f ∈ parityZ X Y p ↔ f.1 ∈ parity (R := R) X.obj Y.obj p := Iff.rfl

/-- The morphisms of degree zero form a supercategory. -/
instance : Supercategory R (DegreeZero R C) where
  parity := parityZ
  isInternal X Y := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro f h0 h1
      have := proj_of_mem (R := R) (mem_parityZ.1 h0)
      rw [proj_of_mem_ne (mem_parityZ.1 h1) (by decide)] at this
      exact Subtype.ext this.symm
    · rw [codisjoint_iff, eq_top_iff]
      intro f _
      have e : f = ⟨proj R 0 f.1, proj_mem_degree 0 f.2⟩ + ⟨proj R 1 f.1, proj_mem_degree 1 f.2⟩ :=
        Subtype.ext (proj_add_proj (R := R) f.1).symm
      rw [e]
      exact Submodule.add_mem_sup (mem_parityZ.2 (proj_mem 0 _)) (mem_parityZ.2 (proj_mem 1 _))
  id_mem X := mem_parityZ.2 (id_mem X.obj)
  comp_mem hf hg := mem_parityZ.2 (comp_mem (mem_parityZ.1 hf) (mem_parityZ.1 hg))

theorem mem_parity_iff {X Y : DegreeZero R C} {p : ZMod 2} {f : X ⟶ Y} :
    f ∈ parity (R := R) X Y p ↔ f.1 ∈ parity (R := R) X.obj Y.obj p := Iff.rfl

theorem proj_val (p : ZMod 2) {X Y : DegreeZero R C} (f : X ⟶ Y) :
    (proj R p f).1 = proj R p f.1 := by
  have e : f = ⟨proj R p f.1, proj_mem_degree p f.2⟩ +
      ⟨proj R (p + 1) f.1, proj_mem_degree (p + 1) f.2⟩ :=
    Subtype.ext (proj_add_proj_add_one (R := R) p f.1).symm
  rw [proj_eq_of_add e (mem_parity_iff.2 (proj_mem p _)) (mem_parity_iff.2 (proj_mem _ _))]

theorem twist_val (p : ZMod 2) {X Y : DegreeZero R C} (f : X ⟶ Y) :
    (twist R p f).1 = twist R p f.1 := by
  rw [twist_apply, twist_apply]
  simp [proj_val]

variable (R C) in
/-- The inclusion of the morphisms of degree zero. -/
@[simps]
def ι : DegreeZero R C ⥤ C where
  obj X := X.obj
  map f := f.1

instance : (ι R C).Additive where
instance : (ι R C).Linear R where
instance : IsSuperfunctor R (ι R C) where
  map_mem hf := hf
instance : (ι R C).Faithful where
  map_injective h := Subtype.ext h

/-- A homogeneous isomorphism of degree zero gives an isomorphism of `DegreeZero R C`. -/
@[simps]
def isoMk {X Y : C} (e : X ≅ Y) (he : e.hom ∈ degree (R := R) X Y 0) :
    (⟨X⟩ : DegreeZero R C) ≅ ⟨Y⟩ where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, by simpa using inv_mem_degree e he⟩
  hom_inv_id := Subtype.ext e.hom_inv_id
  inv_hom_id := Subtype.ext e.inv_hom_id

/-- The restriction of a graded superfunctor to morphisms of degree zero. -/
@[simps]
def map (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    DegreeZero R C ⥤ DegreeZero R D where
  obj X := ⟨F.obj X.obj⟩
  map f := ⟨F.map f.1, map_mem_degree F f.2⟩
  map_id X := Subtype.ext (F.map_id X.obj)
  map_comp f g := Subtype.ext (F.map_comp f.1 g.1)

instance (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    (map (R := R) F).Additive where
  map_add := Subtype.ext F.map_add

instance (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    (map (R := R) F).Linear R where
  map_smul f r := Subtype.ext (Functor.Linear.map_smul (F := F) f.1 r)

instance (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    IsSuperfunctor R (map (R := R) F) where
  map_mem hf := Supercategory.map_mem (R := R) F hf

/-- A supernatural transformation of degree zero, restricted to morphisms of degree zero. -/
theorem isSupernatural_map {F G : C ⥤ D} [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G] {p : ZMod 2}
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsGradedSupernatural R p 0 x) :
    IsSupernatural R p (F := map (R := R) F) (G := map (R := R) G)
      fun X => (⟨x X.obj, hx.mem_degree X.obj⟩ : (map (R := R) F).obj X ⟶ (map (R := R) G).obj X) where
  mem X := hx.mem X.obj
  naturality hf := Subtype.ext (hx.naturality hf)

end DegreeZero

variable (R C) in
/-- The underlying category of a graded supercategory (Brundan–Ellis, §6, after
Definition 6.1): the same objects, with only the even morphisms of degree zero. -/
abbrev GUnderlying := Underlying R (DegreeZero R C)

end DegreeZero

end GradedSupercategory

end StringDiagrams

end
