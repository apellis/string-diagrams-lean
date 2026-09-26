import StringDiagrams.Super.Graded
import Mathlib.Algebra.Module.Submodule.EqLocus

/-!
# Graded subcategories of a supercategory

A construction used for the examples of graded supercategories of J. Brundan, A. P. Ellis,
*Monoidal supercategories*, arXiv:1603.05928v3, §6 (after Definition 6.1): `GSVec`, the
graded supercategory `A-GSMod-B` of graded superbimodules, and the graded supercategory
`ℋom(A, B)` of graded superfunctors. In each of these the morphism space `Hom(V, W)` is defined
as a direct sum `⨁ₙ Hom(V, W)ₙ`, where `Hom(V, W)ₙ` is a submodule of the morphisms
`V → W` of an ambient supercategory (all linear maps, all superbimodule homomorphisms, all
supernatural transformations): the morphisms homogeneous of degree `n`.

`StringDiagrams.GradedHomFamily R C J` records such data: objects `obj : J → C` of an ambient
supercategory `C`, submodules `deg i j n` of the ambient morphism modules, stable under the
parity projections, containing the identities in degree `0`, closed under composition with
degrees adding, and *independent* (a finite sum of homogeneous morphisms of distinct degrees
vanishes only if each does). The graded supercategory `GradedSubcategory 𝒟` has objects `J`
and morphisms `⨁ₙ deg i j n`, realized as the submodule `⨆ₙ deg i j n` of the ambient
morphisms (`GradedHomFamily.hom`).

## Main definitions

* `GradedHomFamily`, `GradedHomFamily.hom`, `GradedHomFamily.hom_induction`.
* `GradedSubcategory 𝒟`, with instances `Category`, `Preadditive`, `Linear R`,
  `Supercategory R` and `GradedSupercategory R`; the faithful superfunctor
  `GradedSubcategory.ι` to the ambient supercategory; `GradedSubcategory.homMk`,
  `GradedSubcategory.isoMk`.
* `iSupIndep_of_eval`: a criterion for the independence of a family of submodules, by
  evaluation into modules with independent families; `iSupIndep_of_projections`: independence
  from a family of projections; `iSupIndep_comap_of_injective`.
* `isInternal_inf_of_decompose_mem`: two gradings of a module, the components of the first
  being stable under the projections of the second, form a bigrading.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ u

/-! ## Independence criteria -/

section Indep

variable {R : Type w} [CommRing R]

/-- A family of submodules is independent if it is so after an injective linear map. -/
theorem iSupIndep_comap_of_injective {ι : Type*} {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {p : ι → Submodule R N} (hp : iSupIndep p) (f : M →ₗ[R] N)
    (hf : Function.Injective f) : iSupIndep fun i => (p i).comap f := by
  rw [iSupIndep_def] at hp ⊢
  intro i
  refine Disjoint.mono_right (iSup₂_le fun j hj => Submodule.comap_mono
    (le_iSup₂ (f := fun j _ => p j) j hj)) ?_
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have h := Submodule.disjoint_def.1 (hp i) (f x) hx hx'
  exact hf (h.trans (map_zero f).symm)

/-- A family of submodules `deg n` of `M` is independent if there are linear maps
`ev a : M → N a` which are jointly injective, and independent families `E a n` of submodules
of `N a` with `ev a (deg n) ⊆ E a n`. -/
theorem iSupIndep_of_eval {ι : Type*} {M : Type*} [AddCommGroup M] [Module R M]
    (deg : ι → Submodule R M) {A : Type*} {N : A → Type*} [∀ a, AddCommGroup (N a)]
    [∀ a, Module R (N a)] (ev : ∀ a, M →ₗ[R] N a) (E : ∀ a, ι → Submodule R (N a))
    (hE : ∀ a, iSupIndep (E a)) (hdeg : ∀ a n, (deg n).map (ev a) ≤ E a n)
    (hinj : ∀ x : M, (∀ a, ev a x = 0) → x = 0) : iSupIndep deg := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  refine hinj x fun a => ?_
  have h1 : ev a x ∈ E a i := hdeg a i ⟨x, hx, rfl⟩
  have h2 : ev a x ∈ ⨆ (j) (_ : j ≠ i), E a j := by
    have : (⨆ (j) (_ : j ≠ i), deg j).map (ev a) ≤ ⨆ (j) (_ : j ≠ i), E a j := by
      rw [Submodule.map_iSup]
      refine iSup_mono fun j => ?_
      rw [Submodule.map_iSup]
      exact iSup_mono fun hj => hdeg a j
    exact this ⟨x, hx', rfl⟩
  exact Submodule.disjoint_def.1 (iSupIndep_def.1 (hE a) i) _ h1 h2

/-- A family of submodules `P i` is independent if there are linear maps `π i` which are the
identity on `P i` and vanish on `P j` for `j ≠ i`. -/
theorem iSupIndep_of_projections {ι M : Type*} [AddCommGroup M] [Module R M]
    (P : ι → Submodule R M) (π : ι → M →ₗ[R] M)
    (h_same : ∀ i, P i ≤ LinearMap.eqLocus (π i) LinearMap.id)
    (h_ne : ∀ i j, j ≠ i → P j ≤ LinearMap.ker (π i)) : iSupIndep P := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have h1 : π i x = x := LinearMap.mem_eqLocus.1 (h_same i hx)
  have h2 : π i x = 0 :=
    LinearMap.mem_ker.1 ((iSup₂_le fun j hj => h_ne i j hj : (⨆ (j) (_ : j ≠ i), P j) ≤ _) hx')
  rw [← h1, h2]

/-- Two decompositions `𝒜`, `ℬ` of a module such that each `𝒜 i` is stable under the
projections onto the `ℬ j` form a bigrading: the module is the internal direct sum of the
`𝒜 i ⊓ ℬ j`. -/
theorem isInternal_inf_of_decompose_mem {ι κ M : Type*} [AddCommGroup M] [Module R M]
    [DecidableEq ι] [DecidableEq κ] (𝒜 : ι → Submodule R M) (ℬ : κ → Submodule R M)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ]
    (h : ∀ (i : ι) (j : κ) {m : M}, m ∈ 𝒜 i → (DirectSum.decompose ℬ m j : M) ∈ 𝒜 i) :
    DirectSum.IsInternal fun ij : ι × κ => 𝒜 ij.1 ⊓ ℬ ij.2 := by
  classical
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    let φ : M →ₗ[R] M := (ℬ i.2).subtype ∘ₗ (DirectSum.component R κ (fun j => ℬ j) i.2) ∘ₗ
      (DirectSum.decomposeLinearEquiv ℬ).toLinearMap ∘ₗ (𝒜 i.1).subtype ∘ₗ
        (DirectSum.component R ι (fun i => 𝒜 i) i.1) ∘ₗ (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap
    have hφ : ∀ y, φ y = (DirectSum.decompose ℬ (DirectSum.decompose 𝒜 y i.1 : M) i.2 : M) :=
      fun y => rfl
    have hpi : ∀ j : ι × κ, j ≠ i → ∀ y ∈ 𝒜 j.1 ⊓ ℬ j.2, φ y = 0 := by
      intro j hj y hy
      rw [hφ]
      by_cases h1 : j.1 = i.1
      · have h2 : j.2 ≠ i.2 := fun h2 => hj (Prod.ext h1 h2)
        rw [DirectSum.decompose_of_mem_same 𝒜 (h1 ▸ hy.1), DirectSum.decompose_of_mem_ne ℬ hy.2 h2]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 hy.1 h1]
        simp
    have h0 : φ x = 0 := by
      refine Submodule.iSup_induction (fun j : {j // j ≠ i} => 𝒜 j.1.1 ⊓ ℬ j.1.2)
        (motive := fun y => φ y = 0) ?_ ?_ ?_ ?_
      · simpa [iSup_subtype'] using hx'
      · intro j y hy; exact hpi j j.2 y hy
      · simp
      · intro y z hy hz; rw [map_add, hy, hz, add_zero]
    rwa [hφ, DirectSum.decompose_of_mem_same 𝒜 hx.1, DirectSum.decompose_of_mem_same ℬ hx.2] at h0
  · rw [eq_top_iff]
    intro v _
    refine DirectSum.Decomposition.inductionOn 𝒜
      (motive := fun v => v ∈ ⨆ ij : ι × κ, 𝒜 ij.1 ⊓ ℬ ij.2) (Submodule.zero_mem _)
      (fun {i} w => ?_) (fun w w' hw hw' => Submodule.add_mem _ hw hw') v
    rw [← DirectSum.sum_support_decompose ℬ (w : M)]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.mem_iSup_of_mem (i, j) ⟨h i j w.2, Submodule.coe_mem _⟩

end Indep

/-! ## Graded hom families -/

variable (R : Type w) [CommRing R] (C : Type w₁) [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C]

/-- The data of a graded supercategory inside a supercategory `C`: objects `obj i`, and
submodules `deg i j n` of the ambient morphisms (the morphisms homogeneous of degree `n`)
which are stable under the parity projections, contain the identities in degree `0`, are
closed under composition with degrees adding, and are independent. -/
structure GradedHomFamily (J : Type u) where
  /-- The underlying objects of the ambient supercategory. -/
  obj : J → C
  /-- The morphisms homogeneous of degree `n`. -/
  deg : ∀ i j : J, ℤ → Submodule R (obj i ⟶ obj j)
  /-- Homogeneous morphisms have homogeneous parity components. -/
  proj_mem : ∀ {i j : J} {n : ℤ} {f : obj i ⟶ obj j} (p : ZMod 2), f ∈ deg i j n →
    proj R p f ∈ deg i j n
  /-- Identities have degree zero. -/
  id_mem : ∀ i : J, 𝟙 (obj i) ∈ deg i i 0
  /-- Composition adds degrees. -/
  comp_mem : ∀ {i j k : J} {m n : ℤ} {f : obj i ⟶ obj j} {g : obj j ⟶ obj k},
    f ∈ deg i j m → g ∈ deg j k n → f ≫ g ∈ deg i k (m + n)
  /-- A finite sum of homogeneous morphisms of distinct degrees vanishes only if each does. -/
  indep : ∀ i j : J, iSupIndep (deg i j)

namespace GradedHomFamily

variable {R C} {J : Type u} (𝒟 : GradedHomFamily R C J)

/-- The morphism module `⨁ₙ Hom(i, j)ₙ`, as the submodule `⨆ₙ deg i j n` of the ambient
morphisms. -/
def hom (i j : J) : Submodule R (𝒟.obj i ⟶ 𝒟.obj j) := ⨆ n, 𝒟.deg i j n

theorem mem_hom_of_mem {i j : J} {n : ℤ} {f : 𝒟.obj i ⟶ 𝒟.obj j} (hf : f ∈ 𝒟.deg i j n) :
    f ∈ 𝒟.hom i j :=
  Submodule.mem_iSup_of_mem n hf

/-- Induction on morphisms of `⨁ₙ Hom(i, j)ₙ` via homogeneous ones. -/
@[elab_as_elim]
theorem hom_induction {i j : J} {motive : (𝒟.obj i ⟶ 𝒟.obj j) → Prop} {f : 𝒟.obj i ⟶ 𝒟.obj j}
    (hf : f ∈ 𝒟.hom i j) (mem : ∀ (n : ℤ) (g : 𝒟.obj i ⟶ 𝒟.obj j), g ∈ 𝒟.deg i j n → motive g)
    (zero : motive 0) (add : ∀ g h, motive g → motive h → motive (g + h)) : motive f :=
  Submodule.iSup_induction (𝒟.deg i j) (motive := motive) hf mem zero add

theorem id_mem_hom (i : J) : 𝟙 (𝒟.obj i) ∈ 𝒟.hom i i :=
  𝒟.mem_hom_of_mem (𝒟.id_mem i)

theorem comp_mem_hom {i j k : J} {f : 𝒟.obj i ⟶ 𝒟.obj j} {g : 𝒟.obj j ⟶ 𝒟.obj k}
    (hf : f ∈ 𝒟.hom i j) (hg : g ∈ 𝒟.hom j k) : f ≫ g ∈ 𝒟.hom i k := by
  refine 𝒟.hom_induction hf (fun m f hf => ?_) (by simp) (fun f f' h h' => ?_)
  · refine 𝒟.hom_induction hg (fun n g hg => 𝒟.mem_hom_of_mem (𝒟.comp_mem hf hg)) (by simp)
      (fun g g' h h' => ?_)
    rw [Preadditive.comp_add]; exact Submodule.add_mem _ h h'
  · rw [Preadditive.add_comp]; exact Submodule.add_mem _ h h'

theorem proj_mem_hom (p : ZMod 2) {i j : J} {f : 𝒟.obj i ⟶ 𝒟.obj j} (hf : f ∈ 𝒟.hom i j) :
    proj R p f ∈ 𝒟.hom i j := by
  refine 𝒟.hom_induction hf (fun n g hg => 𝒟.mem_hom_of_mem (𝒟.proj_mem p hg)) (by simp)
    (fun g g' h h' => ?_)
  rw [map_add]; exact Submodule.add_mem _ h h'

theorem twist_mem (p : ZMod 2) {i j : J} {n : ℤ} {f : 𝒟.obj i ⟶ 𝒟.obj j}
    (hf : f ∈ 𝒟.deg i j n) : twist R p f ∈ 𝒟.deg i j n := by
  rw [twist_apply]
  exact Submodule.add_mem _ (𝒟.proj_mem 0 hf) (Submodule.smul_mem _ _ (𝒟.proj_mem 1 hf))

end GradedHomFamily

/-! ## The graded subcategory -/

variable {R C} in
/-- The graded supercategory determined by a graded hom family: its objects are `J`, and its
morphisms `i ⟶ j` are the elements of `⨆ₙ deg i j n`. -/
@[ext]
structure GradedSubcategory {J : Type u} (𝒟 : GradedHomFamily R C J) where
  /-- The underlying index. -/
  as : J

namespace GradedSubcategory

variable {R C} {J : Type u} {𝒟 : GradedHomFamily R C J}

instance : Category (GradedSubcategory 𝒟) where
  Hom X Y := 𝒟.hom X.as Y.as
  id X := ⟨𝟙 _, 𝒟.id_mem_hom X.as⟩
  comp f g := ⟨f.1 ≫ g.1, 𝒟.comp_mem_hom f.2 g.2⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

@[ext] theorem hom_ext {X Y : GradedSubcategory 𝒟} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

@[simp] theorem id_val (X : GradedSubcategory 𝒟) : (𝟙 X : X ⟶ X).1 = 𝟙 (𝒟.obj X.as) := rfl

@[simp] theorem comp_val {X Y Z : GradedSubcategory 𝒟} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

instance : Preadditive (GradedSubcategory 𝒟) where
  homGroup X Y := inferInstanceAs (AddCommGroup (𝒟.hom X.as Y.as))
  add_comp _ _ _ f f' g := Subtype.ext (Preadditive.add_comp _ _ _ f.1 f'.1 g.1)
  comp_add _ _ _ f g g' := Subtype.ext (Preadditive.comp_add _ _ _ f.1 g.1 g'.1)

instance : Linear R (GradedSubcategory 𝒟) where
  homModule X Y := inferInstanceAs (Module R (𝒟.hom X.as Y.as))
  smul_comp _ _ _ r f g := Subtype.ext (Linear.smul_comp _ _ _ r f.1 g.1)
  comp_smul _ _ _ f r g := Subtype.ext (Linear.comp_smul _ _ _ f.1 r g.1)

@[simp] theorem add_val {X Y : GradedSubcategory 𝒟} (f g : X ⟶ Y) : (f + g).1 = f.1 + g.1 := rfl

@[simp] theorem neg_val {X Y : GradedSubcategory 𝒟} (f : X ⟶ Y) : (-f).1 = -f.1 := rfl

@[simp] theorem zero_val {X Y : GradedSubcategory 𝒟} : (0 : X ⟶ Y).1 = 0 := rfl

@[simp] theorem sub_val {X Y : GradedSubcategory 𝒟} (f g : X ⟶ Y) : (f - g).1 = f.1 - g.1 := rfl

@[simp] theorem smul_val {X Y : GradedSubcategory 𝒟} (r : R) (f : X ⟶ Y) :
    (r • f).1 = r • f.1 := rfl

/-- The parities of morphisms: those of the ambient supercategory. -/
def parityHom (X Y : GradedSubcategory 𝒟) (p : ZMod 2) : Submodule R (X ⟶ Y) :=
  (parity (R := R) (𝒟.obj X.as) (𝒟.obj Y.as) p).comap (𝒟.hom X.as Y.as).subtype

theorem mem_parityHom {X Y : GradedSubcategory 𝒟} {p : ZMod 2} {f : X ⟶ Y} :
    f ∈ parityHom X Y p ↔ f.1 ∈ parity (R := R) (𝒟.obj X.as) (𝒟.obj Y.as) p := Iff.rfl

instance : Supercategory R (GradedSubcategory 𝒟) where
  parity := parityHom
  isInternal X Y := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro f h0 h1
      have := proj_of_mem (R := R) (mem_parityHom.1 h0)
      rw [proj_of_mem_ne (mem_parityHom.1 h1) (by decide)] at this
      exact Subtype.ext this.symm
    · rw [codisjoint_iff, eq_top_iff]
      intro f _
      have e : f = ⟨proj R 0 f.1, 𝒟.proj_mem_hom 0 f.2⟩ + ⟨proj R 1 f.1, 𝒟.proj_mem_hom 1 f.2⟩ :=
        Subtype.ext (proj_add_proj (R := R) f.1).symm
      rw [e]
      exact Submodule.add_mem_sup (mem_parityHom.2 (proj_mem 0 _)) (mem_parityHom.2 (proj_mem 1 _))
  id_mem X := mem_parityHom.2 (id_mem (𝒟.obj X.as))
  comp_mem hf hg := mem_parityHom.2 (comp_mem (mem_parityHom.1 hf) (mem_parityHom.1 hg))

theorem mem_parity_iff {X Y : GradedSubcategory 𝒟} {p : ZMod 2} {f : X ⟶ Y} :
    f ∈ parity (R := R) X Y p ↔ f.1 ∈ parity (R := R) (𝒟.obj X.as) (𝒟.obj Y.as) p := Iff.rfl

theorem proj_val (p : ZMod 2) {X Y : GradedSubcategory 𝒟} (f : X ⟶ Y) :
    (proj R p f).1 = proj R p f.1 := by
  have e : f = ⟨proj R p f.1, 𝒟.proj_mem_hom p f.2⟩ +
      ⟨proj R (p + 1) f.1, 𝒟.proj_mem_hom (p + 1) f.2⟩ :=
    Subtype.ext (proj_add_proj_add_one (R := R) p f.1).symm
  rw [proj_eq_of_add e (mem_parity_iff.2 (proj_mem p _)) (mem_parity_iff.2 (proj_mem _ _))]

theorem twist_val (p : ZMod 2) {X Y : GradedSubcategory 𝒟} (f : X ⟶ Y) :
    (twist R p f).1 = twist R p f.1 := by
  rw [twist_apply, twist_apply]
  simp [proj_val]

/-- The degrees of morphisms. -/
def degreeHom (X Y : GradedSubcategory 𝒟) (n : ℤ) : Submodule R (X ⟶ Y) :=
  (𝒟.deg X.as Y.as n).comap (𝒟.hom X.as Y.as).subtype

theorem mem_degreeHom {X Y : GradedSubcategory 𝒟} {n : ℤ} {f : X ⟶ Y} :
    f ∈ degreeHom X Y n ↔ f.1 ∈ 𝒟.deg X.as Y.as n := Iff.rfl

/-- A graded hom family defines a graded supercategory. -/
instance : GradedSupercategory R (GradedSubcategory 𝒟) where
  degree := degreeHom
  isInternal_degree X Y := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨iSupIndep_comap_of_injective (𝒟.indep X.as Y.as) _ Subtype.val_injective, ?_⟩
    rw [eq_top_iff]
    rintro ⟨f, hf⟩ -
    refine Submodule.iSup_induction' (𝒟.deg X.as Y.as)
      (motive := fun g hg => (⟨g, hg⟩ : 𝒟.hom X.as Y.as) ∈ ⨆ n, degreeHom X Y n)
      (fun n g hg => Submodule.mem_iSup_of_mem n (mem_degreeHom.2 hg)) (Submodule.zero_mem _)
      (fun g h hg hh ihg ihh => Submodule.add_mem _ ihg ihh) hf
  proj_mem_degree p hf := by
    rw [mem_degreeHom, proj_val]
    exact 𝒟.proj_mem p (mem_degreeHom.1 hf)
  id_mem_degree X := mem_degreeHom.2 (𝒟.id_mem X.as)
  comp_mem_degree hf hg := mem_degreeHom.2 (𝒟.comp_mem (mem_degreeHom.1 hf) (mem_degreeHom.1 hg))

theorem mem_degree_iff {X Y : GradedSubcategory 𝒟} {n : ℤ} {f : X ⟶ Y} :
    f ∈ GradedSupercategory.degree (R := R) X Y n ↔ f.1 ∈ 𝒟.deg X.as Y.as n := Iff.rfl

/-- The morphism given by a homogeneous ambient morphism. -/
def homMk {X Y : GradedSubcategory 𝒟} {n : ℤ} (f : 𝒟.obj X.as ⟶ 𝒟.obj Y.as)
    (hf : f ∈ 𝒟.deg X.as Y.as n) : X ⟶ Y :=
  ⟨f, 𝒟.mem_hom_of_mem hf⟩

@[simp] theorem homMk_val {X Y : GradedSubcategory 𝒟} {n : ℤ} (f : 𝒟.obj X.as ⟶ 𝒟.obj Y.as)
    (hf : f ∈ 𝒟.deg X.as Y.as n) : (homMk f hf).1 = f := rfl

theorem homMk_mem_degree {X Y : GradedSubcategory 𝒟} {n : ℤ} (f : 𝒟.obj X.as ⟶ 𝒟.obj Y.as)
    (hf : f ∈ 𝒟.deg X.as Y.as n) : homMk f hf ∈ GradedSupercategory.degree (R := R) X Y n :=
  hf

/-- An isomorphism of the ambient supercategory whose components are homogeneous gives an
isomorphism of the graded subcategory. -/
@[simps]
def isoMk {i j : J} (e : 𝒟.obj i ≅ 𝒟.obj j) {m n : ℤ} (he : e.hom ∈ 𝒟.deg i j m)
    (he' : e.inv ∈ 𝒟.deg j i n) : (⟨i⟩ : GradedSubcategory 𝒟) ≅ ⟨j⟩ where
  hom := homMk e.hom he
  inv := homMk e.inv he'
  hom_inv_id := Subtype.ext e.hom_inv_id
  inv_hom_id := Subtype.ext e.inv_hom_id

variable (𝒟) in
/-- The faithful superfunctor to the ambient supercategory. -/
@[simps]
def ι : GradedSubcategory 𝒟 ⥤ C where
  obj X := 𝒟.obj X.as
  map f := f.1

instance : (ι 𝒟).Additive where
instance : (ι 𝒟).Linear R where
instance : IsSuperfunctor R (ι 𝒟) where
  map_mem hf := hf
instance : (ι 𝒟).Faithful where
  map_injective h := Subtype.ext h

end GradedSubcategory

end StringDiagrams

end
