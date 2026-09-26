import StringDiagrams.Examples.OddTemperleyLieb.Splitting
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective

/-!
# Semisimple abelian categories from orthogonal Schur objects

Used for J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Example
1.17(ii) and Theorem 1.18 = Theorem A.3 ("`SKar(STL(δ))` is a semisimple Abelian category").

## Von Neumann regular morphisms

A morphism `f` of a preadditive category is *(von Neumann) regular* if `f ≫ g ≫ f = f` for some
`g` (`IsVNRegular`). If every morphism is regular and idempotents split, then every morphism has
a (split) kernel and cokernel, every monomorphism is a kernel and every epimorphism is a
cokernel, so a category with finite products of this kind is abelian (`abelianOfVNRegular`).

## Orthogonal Schur generators

Let `𝒞` be a `k`-linear category (`k` a field) with binary biproducts and a zero object, and let
`S : ι → 𝒞` be a family of objects. `OrthogonalSchurGenerators k S` says that each `S i` is a
nonzero Schur object (`End(S i) = k`), that `Hom(S i, S j) = 0` for `i ≠ j`, and that every
object of `𝒞` is isomorphic to a finite biproduct `bsum L` of objects of the family. Then

* morphisms out of `bsum L` are determined by, and can be prescribed through, the linear maps
  they induce on the `Hom(S i, -)` (`hom_ext_of_gen`, `exists_hom_of_gen`);
* every morphism is regular (`isVNRegular_of_gen`), so if `𝒞` is idempotent complete it is
  abelian (`abelianOfOrthogonalSchurGenerators`);
* each `S i` is a simple object (`simple_of_gen`), every object is a finite biproduct of simple
  objects (`exists_iso_bsum_simple`), every simple object is isomorphic to some `S i`
  (`exists_iso_of_simple`), and `S i ≇ S j` for `i ≠ j` (`isEmpty_iso_of_ne`).

This is the precise sense in which the categories of Example 1.17(ii) and Theorem A.3 are
"semisimple abelian categories": abelian, with every object a finite direct sum of simple objects,
and with the given family as a complete set of pairwise non-isomorphic simple objects. The
hypothesis that `𝒞` is idempotent complete is automatic for abelian categories, and holds for the
Karoubi envelopes to which the result is applied here.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Limits OddTemperleyLieb

universe w v u

/-! ## Von Neumann regular morphisms -/

section Regular

variable {𝒞 : Type u} [Category.{v} 𝒞] [Preadditive 𝒞]

/-- A morphism `f` is *(von Neumann) regular* if `f ≫ g ≫ f = f` for some `g`. -/
def IsVNRegular {X Y : 𝒞} (f : X ⟶ Y) : Prop := ∃ g : Y ⟶ X, f ≫ g ≫ f = f

namespace IsVNRegular

variable {X Y : 𝒞} {f : X ⟶ Y}

omit [Preadditive 𝒞] in
/-- A regular monomorphism is a split monomorphism. -/
theorem comp_eq_id_of_mono {g : Y ⟶ X} (h : f ≫ g ≫ f = f) [Mono f] : f ≫ g = 𝟙 X := by
  rw [← cancel_mono f, Category.assoc, h, Category.id_comp]

omit [Preadditive 𝒞] in
/-- A regular epimorphism is a split epimorphism. -/
theorem comp_eq_id_of_epi {g : Y ⟶ X} (h : f ≫ g ≫ f = f) [Epi f] : g ≫ f = 𝟙 Y := by
  rw [← cancel_epi f, h, Category.comp_id]

/-- `𝟙 X - f ≫ g` is an idempotent. -/
theorem idem_left {g : Y ⟶ X} (h : f ≫ g ≫ f = f) :
    (𝟙 X - f ≫ g) ≫ (𝟙 X - f ≫ g) = 𝟙 X - f ≫ g := by
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [← Category.assoc g f, ← Category.assoc f, h]
  abel

/-- `𝟙 Y - g ≫ f` is an idempotent. -/
theorem idem_right {g : Y ⟶ X} (h : f ≫ g ≫ f = f) :
    (𝟙 Y - g ≫ f) ≫ (𝟙 Y - g ≫ f) = 𝟙 Y - g ≫ f := by
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [h]
  abel

/-- The splitting of the idempotent `𝟙 X - f ≫ g` is a kernel of `f`. -/
def kernelIsLimit {g : Y ⟶ X} (h : f ≫ g ≫ f = f) {K : 𝒞} (i : K ⟶ X) (r : X ⟶ K)
    (hir : i ≫ r = 𝟙 K) (hri : r ≫ i = 𝟙 X - f ≫ g) :
    IsLimit (KernelFork.ofι i (show i ≫ f = 0 by
      have : i = i ≫ (𝟙 X - f ≫ g) := by rw [← hri, ← Category.assoc, hir, Category.id_comp]
      rw [this, Category.assoc, Preadditive.sub_comp, Category.id_comp, Category.assoc, h,
        sub_self, comp_zero])) :=
  KernelFork.IsLimit.ofι i _ (fun {_} k _ => k ≫ r)
    (fun {_} k hk => by
      rw [Category.assoc, hri, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hk,
        zero_comp, sub_zero])
    (fun {_} k _ m hm => by show m = k ≫ r; rw [← hm, Category.assoc, hir, Category.comp_id])

/-- The splitting of the idempotent `𝟙 Y - g ≫ f` is a cokernel of `f`. -/
def cokernelIsColimit {g : Y ⟶ X} (h : f ≫ g ≫ f = f) {C : 𝒞} (i : C ⟶ Y) (r : Y ⟶ C)
    (hir : i ≫ r = 𝟙 C) (hri : r ≫ i = 𝟙 Y - g ≫ f) :
    IsColimit (CokernelCofork.ofπ r (show f ≫ r = 0 by
      have : f ≫ r ≫ i = 0 := by
        rw [hri, Preadditive.comp_sub, Category.comp_id, h, sub_self]
      rw [← Category.comp_id (f ≫ r), ← hir, ← Category.assoc, Category.assoc f, this,
        zero_comp])) :=
  CokernelCofork.IsColimit.ofπ r _ (fun {_} k _ => i ≫ k)
    (fun {_} k hk => by
      rw [← Category.assoc, hri, Preadditive.sub_comp, Category.id_comp, Category.assoc, hk,
        comp_zero, sub_zero])
    (fun {_} k _ m hm => by show m = i ≫ k; rw [← hm, ← Category.assoc, hir, Category.id_comp])

/-- A regular monomorphism is the kernel of `𝟙 Y - g ≫ f`. -/
def normalMono {g : Y ⟶ X} (h : f ≫ g ≫ f = f) [Mono f] : NormalMono f where
  Z := Y
  g := 𝟙 Y - g ≫ f
  w := by rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, comp_eq_id_of_mono h,
    Category.id_comp, sub_self]
  isLimit :=
    KernelFork.IsLimit.ofι f _ (fun {_} k _ => k ≫ g)
      (fun {_} k hk => by
        rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hk
        rw [Category.assoc, ← hk])
      (fun {_} k _ m hm => by
        show m = k ≫ g
        rw [← hm, Category.assoc, comp_eq_id_of_mono h, Category.comp_id])

/-- A regular epimorphism is the cokernel of `𝟙 X - f ≫ g`. -/
def normalEpi {g : Y ⟶ X} (h : f ≫ g ≫ f = f) [Epi f] : NormalEpi f where
  W := X
  g := 𝟙 X - f ≫ g
  w := by rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, comp_eq_id_of_epi h,
    Category.comp_id, sub_self]
  isColimit :=
    CokernelCofork.IsColimit.ofπ f _ (fun {_} k _ => g ≫ k)
      (fun {_} k hk => by
        rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero] at hk
        rw [← Category.assoc, ← hk])
      (fun {_} k _ m hm => by
        show m = g ≫ k
        rw [← hm, ← Category.assoc, comp_eq_id_of_epi h, Category.id_comp])

end IsVNRegular

variable (𝒞) in
/-- If every morphism is regular and idempotents split, kernels exist. -/
theorem hasKernels_of_isVNRegular [IsIdempotentComplete 𝒞]
    (H : ∀ {X Y : 𝒞} (f : X ⟶ Y), IsVNRegular f) : HasKernels 𝒞 where
  has_limit f := by
    obtain ⟨g, hg⟩ := H f
    obtain ⟨K, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split _ _ (IsVNRegular.idem_left hg)
    exact HasLimit.mk ⟨_, IsVNRegular.kernelIsLimit hg i r hir hri⟩

variable (𝒞) in
/-- If every morphism is regular and idempotents split, cokernels exist. -/
theorem hasCokernels_of_isVNRegular [IsIdempotentComplete 𝒞]
    (H : ∀ {X Y : 𝒞} (f : X ⟶ Y), IsVNRegular f) : HasCokernels 𝒞 where
  has_colimit f := by
    obtain ⟨g, hg⟩ := H f
    obtain ⟨C, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split _ _ (IsVNRegular.idem_right hg)
    exact HasColimit.mk ⟨_, IsVNRegular.cokernelIsColimit hg i r hir hri⟩

variable (𝒞) in
theorem isNormalMonoCategory_of_isVNRegular (H : ∀ {X Y : 𝒞} (f : X ⟶ Y), IsVNRegular f) :
    IsNormalMonoCategory 𝒞 where
  normalMonoOfMono f _ := by
    obtain ⟨g, hg⟩ := H f
    exact ⟨IsVNRegular.normalMono hg⟩

variable (𝒞) in
theorem isNormalEpiCategory_of_isVNRegular (H : ∀ {X Y : 𝒞} (f : X ⟶ Y), IsVNRegular f) :
    IsNormalEpiCategory 𝒞 where
  normalEpiOfEpi f _ := by
    obtain ⟨g, hg⟩ := H f
    exact ⟨IsVNRegular.normalEpi hg⟩

variable (𝒞) in
/-- **A preadditive category with finite products in which idempotents split and every morphism
is von Neumann regular is abelian.** -/
def abelianOfVNRegular [HasFiniteProducts 𝒞] [IsIdempotentComplete 𝒞]
    (H : ∀ {X Y : 𝒞} (f : X ⟶ Y), IsVNRegular f) : Abelian 𝒞 :=
  letI := hasKernels_of_isVNRegular 𝒞 H
  letI := hasCokernels_of_isVNRegular 𝒞 H
  letI := isNormalMonoCategory_of_isVNRegular 𝒞 H
  letI := isNormalEpiCategory_of_isVNRegular 𝒞 H
  Abelian.mk

end Regular

/-! ## Generalized inverses of linear maps -/

/-- Over a field, every linear map `φ` has a generalized inverse `ψ`: `φ ∘ ψ ∘ φ = φ`. -/
theorem LinearMap.exists_comp_comp_eq_self {k : Type w} [Field k] {V W : Type*} [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module k W] (φ : V →ₗ[k] W) :
    ∃ ψ : W →ₗ[k] V, φ ∘ₗ ψ ∘ₗ φ = φ := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective φ.rangeRestrict
    (LinearMap.range_rangeRestrict φ)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range φ).subtype
    (Submodule.ker_subtype _)
  refine ⟨s ∘ₗ r, ?_⟩
  apply LinearMap.ext
  intro v
  have h1 : ∀ x : LinearMap.range φ, φ (s x) = x := fun x =>
    congrArg Subtype.val (congrArg (fun F => F x) hs)
  have h2 : ∀ x : LinearMap.range φ, r (x : W) = x := fun x => congrArg (fun F => F x) hr
  simp only [LinearMap.comp_apply]
  rw [h1]
  change ((r ((φ.rangeRestrict v : LinearMap.range φ) : W)) : W) =
    ((φ.rangeRestrict v : LinearMap.range φ) : W)
  rw [h2]

/-! ## Orthogonal Schur generators -/

section Schur

variable {𝒞 : Type u} [Category.{v} 𝒞] [Preadditive 𝒞] [HasBinaryBiproducts 𝒞] [HasZeroObject 𝒞]
  (k : Type w) [Field k] [Linear k 𝒞] {ι : Type*} (S : ι → 𝒞)

/-- A family `S` of objects of a `k`-linear category is a family of *orthogonal Schur
generators* if each `S i` is a nonzero object with `End(S i) = k`, `Hom(S i, S j) = 0` for
`i ≠ j`, and every object is isomorphic to a finite biproduct of objects of the family. -/
structure OrthogonalSchurGenerators : Prop where
  schur : ∀ i, IsSchur (k := k) (S i)
  id_ne_zero : ∀ i, 𝟙 (S i) ≠ 0
  hom_eq_zero : ∀ {i j : ι}, i ≠ j → ∀ f : S i ⟶ S j, f = 0
  exists_iso_bsum : ∀ X : 𝒞, ∃ L : List 𝒞, (∀ P ∈ L, ∃ i, P = S i) ∧ Nonempty (X ≅ bsum L)

namespace OrthogonalSchurGenerators

variable {k S} (hS : OrthogonalSchurGenerators k S)
include hS

/-- A family of linear maps `Hom(S i, X) → Hom(S i, Y)` commutes with precomposition by the
morphisms between the objects `S i`. -/
theorem comp_apply_eq {X Y : 𝒞} (φ : ∀ i, (S i ⟶ X) →ₗ[k] (S i ⟶ Y)) {i j : ι}
    (u : S i ⟶ S j) (v : S j ⟶ X) : u ≫ φ j v = φ i (u ≫ v) := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨c, rfl⟩ := hS.schur i u
    rw [Linear.smul_comp, Category.id_comp, Linear.smul_comp, Category.id_comp, map_smul]
  · rw [hS.hom_eq_zero hij u, zero_comp, zero_comp, map_zero]

omit hS [Field k] [Linear k 𝒞] in
/-- Morphisms out of a biproduct of generators are determined by the maps they induce on the
`Hom(S i, -)`. -/
theorem hom_ext_bsum {Y : 𝒞} (L : List 𝒞) (hL : ∀ P ∈ L, ∃ i, P = S i) {f f' : bsum L ⟶ Y}
    (h : ∀ i (u : S i ⟶ bsum L), u ≫ f = u ≫ f') : f = f' := by
  induction L with
  | nil => exact (isZero_zero 𝒞).eq_of_src f f'
  | cons P L ih =>
    obtain ⟨j, rfl⟩ := hL P (by simp)
    apply biprod.hom_ext'
    · exact h j biprod.inl
    · exact ih (fun Q hQ => hL Q (by simp [hQ])) fun i u => by
        rw [← Category.assoc, ← Category.assoc]; exact h i (u ≫ biprod.inr)

/-- Morphisms are determined by the maps they induce on the `Hom(S i, -)`. -/
theorem hom_ext_of_gen {X Y : 𝒞} {f f' : X ⟶ Y}
    (h : ∀ i (u : S i ⟶ X), u ≫ f = u ≫ f') : f = f' := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hS.exists_iso_bsum X
  rw [← cancel_epi e.inv]
  exact hom_ext_bsum L hL fun i u => by
    rw [← Category.assoc, ← Category.assoc]; exact h i (u ≫ e.inv)

/-- Every family of linear maps `Hom(S i, bsum L) → Hom(S i, Y)` is induced by a morphism. -/
theorem exists_hom_bsum {Y : 𝒞} (L : List 𝒞) (hL : ∀ P ∈ L, ∃ i, P = S i)
    (φ : ∀ i, (S i ⟶ bsum L) →ₗ[k] (S i ⟶ Y)) :
    ∃ f : bsum L ⟶ Y, ∀ i (u : S i ⟶ bsum L), u ≫ f = φ i u := by
  induction L with
  | nil =>
    refine ⟨0, fun i u => ?_⟩
    rw [(isZero_zero 𝒞).eq_of_tgt u 0, zero_comp, map_zero]
  | cons P L ih =>
    obtain ⟨j, rfl⟩ := hL P (by simp)
    obtain ⟨f₂, hf₂⟩ := ih (fun Q hQ => hL Q (by simp [hQ]))
      (fun i => (φ i) ∘ₗ Linear.rightComp k (S i) biprod.inr)
    refine ⟨biprod.desc (φ j biprod.inl) f₂, fun i u => ?_⟩
    have hu : u ≫ biprod.fst ≫ biprod.inl + u ≫ biprod.snd ≫ biprod.inr = u := by
      rw [← Preadditive.comp_add, biprod.total]; exact Category.comp_id u
    have h1 : (u ≫ biprod.fst ≫ biprod.inl) ≫ biprod.desc (φ j biprod.inl) f₂ =
        φ i (u ≫ biprod.fst ≫ biprod.inl) := by
      rw [Category.assoc, Category.assoc, biprod.inl_desc, ← Category.assoc, hS.comp_apply_eq φ,
        Category.assoc]
    have h2 : (u ≫ biprod.snd ≫ biprod.inr) ≫ biprod.desc (φ j biprod.inl) f₂ =
        φ i (u ≫ biprod.snd ≫ biprod.inr) := by
      rw [Category.assoc, Category.assoc, biprod.inr_desc, ← Category.assoc, hf₂ i]
      change φ i ((u ≫ biprod.snd) ≫ biprod.inr) = _
      rw [Category.assoc]
    rw [← hu, map_add, Preadditive.add_comp, h1, h2]

/-- Every family of linear maps `Hom(S i, X) → Hom(S i, Y)` is induced by a morphism. -/
theorem exists_hom_of_gen {X Y : 𝒞} (φ : ∀ i, (S i ⟶ X) →ₗ[k] (S i ⟶ Y)) :
    ∃ f : X ⟶ Y, ∀ i (u : S i ⟶ X), u ≫ f = φ i u := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hS.exists_iso_bsum X
  obtain ⟨f₀, hf₀⟩ := hS.exists_hom_bsum L hL fun i => (φ i) ∘ₗ Linear.rightComp k (S i) e.inv
  refine ⟨e.hom ≫ f₀, fun i u => ?_⟩
  rw [← Category.assoc, hf₀]
  change φ i ((u ≫ e.hom) ≫ e.inv) = φ i u
  rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- **Every morphism is von Neumann regular.** -/
theorem isVNRegular_of_gen {X Y : 𝒞} (f : X ⟶ Y) : IsVNRegular f := by
  choose ψ hψ using fun i => LinearMap.exists_comp_comp_eq_self (Linear.rightComp k (S i) f)
  obtain ⟨g, hg⟩ := hS.exists_hom_of_gen ψ
  refine ⟨g, hS.hom_ext_of_gen fun i u => ?_⟩
  have h := congrArg (fun F => F u) (hψ i)
  simp only [LinearMap.comp_apply, Linear.rightComp_apply] at h
  rw [← Category.assoc, ← Category.assoc, hg]
  exact h

/-- **A `k`-linear idempotent complete category with orthogonal Schur generators is abelian.** -/
def abelian [IsIdempotentComplete 𝒞] : Abelian 𝒞 :=
  haveI : HasFiniteProducts 𝒞 := hasFiniteProducts_of_has_binary_and_terminal
  abelianOfVNRegular 𝒞 fun f => hS.isVNRegular_of_gen f

/-- **The generators are simple objects.** -/
theorem simple (i : ι) : Simple (S i) where
  mono_isIso_iff_nonzero {Y} f _ := by
    constructor
    · rintro ⟨g, -, hgf⟩ h0
      rw [h0, comp_zero] at hgf
      exact hS.id_ne_zero i hgf.symm
    · intro hf
      obtain ⟨g, hg⟩ := hS.isVNRegular_of_gen f
      have hfg : f ≫ g = 𝟙 Y := IsVNRegular.comp_eq_id_of_mono hg
      obtain ⟨c, hc⟩ := hS.schur i (g ≫ f)
      have hidem : (g ≫ f) ≫ (g ≫ f) = g ≫ f := by
        rw [Category.assoc, ← Category.assoc f, hfg, Category.id_comp]
      rw [hc, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at hidem
      have hcc : c * c = c := by
        by_contra hne
        have : (c * c - c) • 𝟙 (S i) = 0 := by rw [sub_smul, hidem, sub_self]
        exact hS.id_ne_zero i ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne))
      have hc1 : c = 1 := by
        have : c * (c - 1) = 0 := by rw [mul_sub, hcc, mul_one, sub_self]
        rcases mul_eq_zero.mp this with h0 | h1
        · exfalso
          apply hf
          rw [← hg, hc, h0, zero_smul, comp_zero]
        · exact sub_eq_zero.mp h1
      exact ⟨g, hfg, by rw [hc, hc1, one_smul]⟩

/-- Every object is a finite biproduct of simple objects. -/
theorem exists_iso_bsum_simple (X : 𝒞) :
    ∃ L : List 𝒞, (∀ P ∈ L, Simple P) ∧ Nonempty (X ≅ bsum L) := by
  obtain ⟨L, hL, e⟩ := hS.exists_iso_bsum X
  refine ⟨L, fun P hP => ?_, e⟩
  obtain ⟨i, rfl⟩ := hL P hP
  exact hS.simple i

/-- Every simple object is isomorphic to one of the generators. -/
theorem exists_iso_of_simple (X : 𝒞) [Simple X] : ∃ i, Nonempty (X ≅ S i) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hS.exists_iso_bsum X
  cases L with
  | nil => exact absurd (IsZero.of_iso (isZero_zero 𝒞) e) (Simple.not_isZero X)
  | cons P L =>
    obtain ⟨i, rfl⟩ := hL P (by simp)
    refine ⟨i, ?_⟩
    rcases (indecomposable_of_simple X).2 _ _ e with h | h
    · exfalso
      exact hS.id_ne_zero i (h.eq_of_src _ _)
    · exact ⟨e ≪≫ (isoBiprodZero h).symm⟩

/-- Distinct generators are not isomorphic. -/
theorem isEmpty_iso_of_ne {i j : ι} (h : i ≠ j) : IsEmpty (S i ≅ S j) :=
  ⟨fun e => hS.id_ne_zero i (by rw [← e.hom_inv_id, hS.hom_eq_zero h e.hom, zero_comp])⟩

end OrthogonalSchurGenerators

end Schur

end StringDiagrams

end
