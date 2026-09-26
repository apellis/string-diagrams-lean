import StringDiagrams.Super.SKar
import StringDiagrams.Super.Superbimodule
import StringDiagrams.Super.Parity
import Mathlib.Algebra.BigOperators.Pi

/-!
# The super Karoubi envelope of a superalgebra

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 1.17(i).

Let `A` be a superalgebra, viewed as a supercategory with one object `⋆` (`SuperalgebraCat 𝒜`).
An object of `SKar(A) = Kar(Mat_(A̲_π))` is a pair `(M, p)` of a tuple `M = (Π^{aᵢ} ⋆)ᵢ` and an
even idempotent matrix `p` with entries in `A`. The functor `Hom_{A_π}(⋆, -)` sends `(M, p)` to
the right `A`-supermodule `p(⊕ᵢ Π^{aᵢ} A)`, where an element `v = (vᵢ)ᵢ` has parity `q` if
`vᵢ ∈ A_{q + aᵢ}` for all `i`, `A` acts by right multiplication, and a matrix `f` acts by
`(f v)ⱼ = ∑ᵢ fᵢⱼ vᵢ`. Right `A`-supermodules are `(k, A)`-superbimodules
(`StringDiagrams.SuperBimodule`), and even homomorphisms are the morphisms of the underlying
category.

## Main results

* `SKarAlg.toMod : SKar(A) ⥤ (k-SMod-A)̲`, additive, faithful and full
  (`SKarAlg.toMod_faithful`, `SKarAlg.toMod_full`).
* Its essential image is the class of finitely generated projective supermodules, i.e. even
  direct summands of finite free supermodules `⊕ᵢ Π^{aᵢ} A` (`SKarAlg.IsFGProjective`):
  `SKarAlg.isFGProjective_toMod_obj` and `SKarAlg.exists_iso_toMod_obj`. Hence `SKar(A)` is
  equivalent to the category of finitely generated projective `A`-supermodules and even
  homomorphisms.

The identification of `K₀(SKar(A))` with the split Grothendieck group of `A` (the last sentence
of Example 1.17(i)) is not formalized: the full subcategory of finitely generated projective
supermodules is not given its additive structure here.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Limits Idempotents Supercategory

universe u

namespace SKarAlg

variable {k : Type u} [CommRing k] {A : Type u} [Ring A] [Algebra k A]
  {𝒜 : ZMod 2 → Submodule k A} [GradedAlgebra 𝒜]

variable (𝒜) in
/-- The underlying category `A̲_π` of the Π-envelope of `A`. -/
abbrev D : Type := Underlying k (Envelope k (SuperalgebraCat 𝒜))

/-- The parity `a` of an object `Πᵃ ⋆` of `A̲_π`. -/
abbrev par (X : D 𝒜) : ZMod 2 := X.obj.par

/-- The element of `A` underlying a morphism of `A̲_π`. -/
def elem {X Y : D 𝒜} (f : X ⟶ Y) : A := SuperalgebraCat.toElem (Envelope.toHom f.1)

@[simp] theorem elem_comp {X Y Z : D 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) :
    elem (f ≫ g) = elem g * elem f := rfl

@[simp] theorem elem_id (X : D 𝒜) : elem (𝟙 X) = 1 := rfl

@[simp] theorem elem_add {X Y : D 𝒜} (f g : X ⟶ Y) : elem (f + g) = elem f + elem g := rfl

@[simp] theorem elem_zero {X Y : D 𝒜} : elem (0 : X ⟶ Y) = 0 := rfl

variable (𝒜) in
/-- `elem` as an additive map. -/
def elemHom (X Y : D 𝒜) : (X ⟶ Y) →+ A where
  toFun := elem
  map_zero' := rfl
  map_add' _ _ := rfl

theorem elem_sum {X Y : D 𝒜} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    elem (∑ i ∈ s, f i) = ∑ i ∈ s, elem (f i) :=
  map_sum (elemHom 𝒜 X Y) f s

theorem elem_mem {X Y : D 𝒜} (f : X ⟶ Y) : elem f ∈ 𝒜 (par X + par Y) := by
  have hf := f.2
  rw [Envelope.mem_parity_iff, zero_add] at hf
  exact hf

theorem hom_ext {X Y : D 𝒜} {f g : X ⟶ Y} (h : elem f = elem g) : f = g := Subtype.ext h

/-- The morphism `Πᵃ ⋆ ⟶ Πᵇ ⋆` given by an element of `A_{a + b}`. -/
def ofElem {X Y : D 𝒜} {r : A} (h : r ∈ 𝒜 (par X + par Y)) : X ⟶ Y :=
  ⟨Envelope.ofHom (SuperalgebraCat.ofElem r), by
    rw [Envelope.mem_parity_iff, zero_add]; exact h⟩

@[simp] theorem elem_ofElem {X Y : D 𝒜} {r : A} (h : r ∈ 𝒜 (par X + par Y)) :
    elem (ofElem h) = r := rfl

theorem elem_eqToHom {X Y : D 𝒜} (h : X = Y) : elem (eqToHom h) = 1 := by
  subst h; rfl

/-! ## Parity components in `A` -/

variable (𝒜) in
/-- The parity projection `A → A_p`. -/
def aproj (p : ZMod 2) : A →ₗ[k] A :=
  Supercategory.proj k p (C := SuperalgebraCat 𝒜) (X := SuperalgebraCat.star 𝒜)
    (Y := SuperalgebraCat.star 𝒜)

theorem aproj_mem (p : ZMod 2) (r : A) : aproj 𝒜 p r ∈ 𝒜 p :=
  proj_mem (R := k) p (C := SuperalgebraCat 𝒜) (X := SuperalgebraCat.star 𝒜)
    (Y := SuperalgebraCat.star 𝒜) r

theorem aproj_of_mem {p : ZMod 2} {r : A} (h : r ∈ 𝒜 p) : aproj 𝒜 p r = r :=
  proj_of_mem (R := k) (C := SuperalgebraCat 𝒜) (X := SuperalgebraCat.star 𝒜)
    (Y := SuperalgebraCat.star 𝒜) h

theorem aproj_of_mem_ne {p q : ZMod 2} {r : A} (h : r ∈ 𝒜 q) (hpq : q ≠ p) : aproj 𝒜 p r = 0 :=
  proj_of_mem_ne (R := k) (C := SuperalgebraCat 𝒜) (X := SuperalgebraCat.star 𝒜)
    (Y := SuperalgebraCat.star 𝒜) h hpq

theorem aproj_add_aproj (r : A) : aproj 𝒜 0 r + aproj 𝒜 1 r = r :=
  proj_add_proj (R := k) (C := SuperalgebraCat 𝒜) (X := SuperalgebraCat.star 𝒜)
    (Y := SuperalgebraCat.star 𝒜) r

theorem aproj_aproj (p : ZMod 2) (r : A) : aproj 𝒜 p (aproj 𝒜 p r) = aproj 𝒜 p r :=
  aproj_of_mem (aproj_mem p r)

theorem aproj_aproj_of_ne {p q : ZMod 2} (h : q ≠ p) (r : A) : aproj 𝒜 p (aproj 𝒜 q r) = 0 :=
  aproj_of_mem_ne (aproj_mem q r) h

theorem aproj_add_aproj' (q : ZMod 2) (r : A) : aproj 𝒜 q r + aproj 𝒜 (1 + q) r = r := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · exact aproj_add_aproj r
  · rw [add_comm, show (1 : ZMod 2) + 1 = 0 from rfl]; exact aproj_add_aproj r

/-! ## The free supermodules `⊕ᵢ Π^{aᵢ} A` -/

variable (𝒜) in
/-- The superspace `⊕ᵢ Π^{aᵢ} A = Hom_{A_π}(⋆, (Π^{aᵢ} ⋆)ᵢ)`: `v` has parity `q` if
`vᵢ ∈ A_{q + aᵢ}` for all `i`. -/
abbrev freeObj (M : Mat_ (D 𝒜)) : SVec k where
  carrier := M.ι → A
  odd := LinearMap.pi fun i => aproj 𝒜 (1 + par (M.X i)) ∘ₗ LinearMap.proj i
  odd_comp_odd := by
    ext v i
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, LinearMap.coe_proj,
      Function.eval]
    exact aproj_aproj _ _

theorem freeObj_proj_apply (M : Mat_ (D 𝒜)) (q : ZMod 2) (v : M.ι → A) (i : M.ι) :
    (freeObj 𝒜 M).proj q v i = aproj 𝒜 (q + par (M.X i)) (v i) := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [SVec.proj_zero, LinearMap.sub_apply, LinearMap.id_apply, zero_add]
    change v i - aproj 𝒜 (1 + par (M.X i)) (v i) = _
    rw [sub_eq_iff_eq_add]
    exact (aproj_add_aproj' (par (M.X i)) (v i)).symm
  · rw [SVec.proj_one]; rfl

theorem mem_freeObj_part_iff (M : Mat_ (D 𝒜)) {q : ZMod 2} {v : M.ι → A} :
    v ∈ (freeObj 𝒜 M).part q ↔ ∀ i, v i ∈ 𝒜 (q + par (M.X i)) := by
  rw [SVec.mem_part_iff]
  constructor
  · intro h i
    rw [← h, freeObj_proj_apply]; exact aproj_mem _ _
  · intro h
    funext i
    change (freeObj 𝒜 M).proj q v i = v i
    rw [freeObj_proj_apply, aproj_of_mem (h i)]

/-- The right action of `a ∈ A` on `⊕ᵢ Π^{aᵢ} A`. -/
def rmul (M : Mat_ (D 𝒜)) (a : A) : freeObj 𝒜 M ⟶ freeObj 𝒜 M :=
  SVec.ofHom
    { toFun := fun v i => v i * a
      map_add' := fun v w => by funext i; exact add_mul _ _ _
      map_smul' := fun r v => by funext i; exact smul_mul_assoc r (v i) a }

@[simp] theorem rmul_apply (M : Mat_ (D 𝒜)) (a : A) (v : M.ι → A) (i : M.ι) :
    rmul M a v i = v i * a := rfl

theorem rmul_mem (M : Mat_ (D 𝒜)) {p : ZMod 2} {a : A} (ha : a ∈ 𝒜 p) :
    rmul M a ∈ SVec.parityHom (freeObj 𝒜 M) (freeObj 𝒜 M) p := by
  refine SVec.mem_parityHom_of_apply_mem fun q v hv => ?_
  rw [mem_freeObj_part_iff] at hv ⊢
  intro i
  rw [show q + p + par (M.X i) = q + par (M.X i) + p by abel]
  exact SetLike.GradedMul.mul_mem (hv i) ha

/-- The matrix `(fᵢⱼ)` of a morphism of the additive envelope acts by `(f v)ⱼ = ∑ᵢ fᵢⱼ vᵢ`. -/
def matHom {M N : Mat_ (D 𝒜)} (f : M ⟶ N) : freeObj 𝒜 M ⟶ freeObj 𝒜 N :=
  SVec.ofHom
    { toFun := fun v j => ∑ i, elem (f i j) * v i
      map_add' := fun v w => by funext j; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r v => by funext j; simp [Finset.smul_sum, mul_smul_comm] }

theorem matHom_apply {M N : Mat_ (D 𝒜)} (f : M ⟶ N) (v : M.ι → A) (j : N.ι) :
    matHom f v j = ∑ i, elem (f i j) * v i := rfl

theorem matHom_comp {M N P : Mat_ (D 𝒜)} (f : M ⟶ N) (g : N ⟶ P) :
    matHom (f ≫ g) = matHom f ≫ matHom g := by
  refine SVec.hom_ext fun v => funext fun l => ?_
  change ∑ i, elem ((f ≫ g) i l) * v i = ∑ j, elem (g j l) * ∑ i, elem (f i j) * v i
  simp only [CategoryTheory.Mat_.comp_apply, elem_sum, elem_comp, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem matHom_id (M : Mat_ (D 𝒜)) : matHom (𝟙 M) = 𝟙 (freeObj 𝒜 M) := by
  classical
  refine SVec.hom_ext fun v => funext fun j => ?_
  change ∑ i, elem ((𝟙 M : M ⟶ M) i j) * v i = v j
  rw [Finset.sum_eq_single j]
  · rw [CategoryTheory.Mat_.id_apply_self, elem_id, one_mul]
  · intro i _ hij; rw [CategoryTheory.Mat_.id_apply_of_ne _ _ _ hij, elem_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem matHom_add {M N : Mat_ (D 𝒜)} (f g : M ⟶ N) : matHom (f + g) = matHom f + matHom g := by
  refine SVec.hom_ext fun v => funext fun j => ?_
  change ∑ i, elem ((f + g) i j) * v i = ∑ i, elem (f i j) * v i + ∑ i, elem (g i j) * v i
  simp [add_mul, Finset.sum_add_distrib]

theorem matHom_mem {M N : Mat_ (D 𝒜)} (f : M ⟶ N) :
    matHom f ∈ SVec.parityHom (freeObj 𝒜 M) (freeObj 𝒜 N) 0 := by
  refine SVec.mem_parityHom_of_apply_mem fun q v hv => ?_
  simp only [add_zero]
  rw [mem_freeObj_part_iff] at hv ⊢
  intro j
  refine Submodule.sum_mem _ fun i _ => ?_
  have := SetLike.GradedMul.mul_mem (elem_mem (f i j)) (hv i)
  have key : ∀ a b q : ZMod 2, a + b + (q + a) = q + b := by decide
  rwa [key] at this

theorem matHom_rmul {M N : Mat_ (D 𝒜)} (f : M ⟶ N) (a : A) (v : M.ι → A) :
    matHom f (rmul M a v) = rmul N a (matHom f v) := by
  funext j
  change ∑ i, elem (f i j) * (v i * a) = (∑ i, elem (f i j) * v i) * a
  rw [Finset.sum_mul]
  simp only [mul_assoc]

theorem matHom_injective {M N : Mat_ (D 𝒜)} {f g : M ⟶ N} (h : matHom f = matHom g) : f = g := by
  classical
  refine CategoryTheory.Mat_.hom_ext _ _ fun i j => hom_ext ?_
  have := congrArg (fun φ : freeObj 𝒜 M ⟶ freeObj 𝒜 N => φ (Pi.single i 1) j) h
  change ∑ i', elem (f i' j) * (Pi.single i (1 : A) : M.ι → A) i' =
    ∑ i', elem (g i' j) * (Pi.single i (1 : A) : M.ι → A) i' at this
  simpa [Pi.single_apply] using this

theorem matHom_odd {M N : Mat_ (D 𝒜)} (f : M ⟶ N) (v : M.ι → A) :
    matHom f ((freeObj 𝒜 M).odd v) = (freeObj 𝒜 N).odd (matHom f v) := by
  have h := SVec.apply_proj_of_mem (matHom_mem f) 1 v
  simp only [add_zero] at h
  rwa [SVec.proj_one, SVec.proj_one] at h

/-! ## The supermodules `p(⊕ᵢ Π^{aᵢ} A)` -/

/-- The image of an idempotent matrix. -/
def imgSubmodule (P : SKar k (SuperalgebraCat 𝒜)) : Submodule k (P.X.ι → A) :=
  LinearMap.range (SVec.toLinearMap (matHom P.p))

theorem mem_imgSubmodule {P : SKar k (SuperalgebraCat 𝒜)} {v : P.X.ι → A} :
    v ∈ imgSubmodule P ↔ matHom P.p v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    change matHom P.p (matHom P.p w) = matHom P.p w
    rw [← SVec.comp_apply, ← matHom_comp, P.idem]
  · intro h; exact ⟨v, h⟩

theorem matHom_p_mem (P : SKar k (SuperalgebraCat 𝒜)) (v : P.X.ι → A) :
    matHom P.p v ∈ imgSubmodule P := ⟨v, rfl⟩

theorem odd_mem_imgSubmodule (P : SKar k (SuperalgebraCat 𝒜)) :
    ∀ v ∈ imgSubmodule P, (freeObj 𝒜 P.X).odd v ∈ imgSubmodule P := by
  intro v hv
  rw [mem_imgSubmodule] at hv ⊢
  rw [matHom_odd, hv]

theorem rmul_mem_imgSubmodule (P : SKar k (SuperalgebraCat 𝒜)) (a : A) :
    ∀ v ∈ imgSubmodule P, rmul P.X a v ∈ imgSubmodule P := by
  intro v hv
  rw [mem_imgSubmodule] at hv ⊢
  rw [matHom_rmul, hv]

/-- The superspace `p(⊕ᵢ Π^{aᵢ} A)`. -/
abbrev imgObj (P : SKar k (SuperalgebraCat 𝒜)) : SVec k :=
  SVec.sub (freeObj 𝒜 P.X) (imgSubmodule P) (odd_mem_imgSubmodule P)

/-- The right action of `A` on `p(⊕ᵢ Π^{aᵢ} A)`. -/
def ractHom (P : SKar k (SuperalgebraCat 𝒜)) : A →ₗ[k] (imgObj P ⟶ imgObj P) where
  toFun a := SVec.restrictHom (rmul P.X a) (rmul_mem_imgSubmodule P a)
  map_add' a b := SVec.hom_ext fun v => Subtype.ext (funext fun i => mul_add (v.1 i) a b)
  map_smul' r a := SVec.hom_ext fun v => Subtype.ext (funext fun i => mul_smul_comm r (v.1 i) a)

theorem ractHom_apply (P : SKar k (SuperalgebraCat 𝒜)) (a : A) (v : imgSubmodule P) (i : P.X.ι) :
    (ractHom P a v).1 i = v.1 i * a := rfl

/-- **Brundan–Ellis, Example 1.17(i).** The right `A`-supermodule `p(⊕ᵢ Π^{aᵢ} A)`, as a
`(k, A)`-superbimodule. -/
abbrev toModObj (P : SKar k (SuperalgebraCat 𝒜)) : SuperBimodule (trivialGrading k) 𝒜 where
  toSVec := imgObj P
  lact := LinearMap.toSpanSingleton k _ (𝟙 (imgObj P))
  ract := ractHom P
  lact_one := one_smul k _
  lact_mul r r' := by
    simp only [LinearMap.toSpanSingleton_apply, Linear.smul_comp, Linear.comp_smul,
      Category.comp_id, smul_smul, mul_comm r r']
  ract_one := SVec.hom_ext fun v => Subtype.ext (funext fun i => mul_one (v.1 i))
  ract_mul b b' := SVec.hom_ext fun v => Subtype.ext (funext fun i => (mul_assoc (v.1 i) b b').symm)
  lact_ract r b := by
    simp only [LinearMap.toSpanSingleton_apply, Linear.smul_comp, Linear.comp_smul,
      Category.comp_id, Category.id_comp]
  lact_mem p r hr := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact Submodule.smul_mem _ r (id_mem _)
    · rw [trivialGrading_one, Submodule.mem_bot] at hr
      rw [hr, LinearMap.toSpanSingleton_apply, zero_smul]
      exact Submodule.zero_mem _
  ract_mem p b hb := SVec.restrictHom_mem (rmul_mem P.X hb) (rmul_mem_imgSubmodule P b)

theorem matHom_mem_imgSubmodule {P Q : SKar k (SuperalgebraCat 𝒜)} (f : P ⟶ Q) :
    ∀ v ∈ imgSubmodule P, matHom f.f v ∈ imgSubmodule Q := fun v _ => by
  rw [mem_imgSubmodule, ← SVec.comp_apply, ← matHom_comp, Idempotents.Karoubi.comp_p]

theorem isHom_matHom {P Q : SKar k (SuperalgebraCat 𝒜)} (f : P ⟶ Q) :
    SuperBimodule.IsHom (toModObj P) (toModObj Q)
      (SVec.restrictHom (matHom f.f) (matHom_mem_imgSubmodule f)) := by
  refine ⟨fun p r _ => ?_, fun b => ?_⟩
  · rw [twist_of_mem p (SVec.restrictHom_mem (matHom_mem f.f) (matHom_mem_imgSubmodule f)),
      mul_zero, sign_zero, one_smul]
    simp only [LinearMap.toSpanSingleton_apply, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id]
  · exact SVec.hom_ext fun v => Subtype.ext (by
      change matHom f.f (rmul P.X b v.1) = rmul Q.X b (matHom f.f v.1)
      exact matHom_rmul f.f b v.1)

/-- The homomorphism `p(⊕ Π^{aᵢ} A) → q(⊕ Π^{bⱼ} A)` of a morphism of `SKar(A)`. -/
def toModHom {P Q : SKar k (SuperalgebraCat 𝒜)} (f : P ⟶ Q) : toModObj P ⟶ toModObj Q :=
  ⟨_, isHom_matHom f⟩

theorem toModHom_mem {P Q : SKar k (SuperalgebraCat 𝒜)} (f : P ⟶ Q) :
    toModHom f ∈ parity (R := k) (toModObj P) (toModObj Q) 0 :=
  SVec.restrictHom_mem (matHom_mem f.f) (matHom_mem_imgSubmodule f)

variable (𝒜) in
/-- **Brundan–Ellis, Example 1.17(i).** The functor `SKar(A) ⥤ (k-SMod-A)̲`,
`(M, p) ↦ p(⊕ᵢ Π^{aᵢ} A)`. -/
def toMod : SKar k (SuperalgebraCat 𝒜) ⥤ Underlying k (SuperBimodule (trivialGrading k) 𝒜) where
  obj P := ⟨toModObj P⟩
  map f := ⟨toModHom f, toModHom_mem f⟩
  map_id P := Underlying.hom_ext (SuperBimodule.hom_ext (SVec.hom_ext fun v => Subtype.ext (by
    change matHom P.p v.1 = v.1
    exact mem_imgSubmodule.1 v.2)))
  map_comp f g := Underlying.hom_ext (SuperBimodule.hom_ext (SVec.hom_ext fun v =>
    Subtype.ext (by
      change matHom (f.f ≫ g.f) v.1 = matHom g.f (matHom f.f v.1)
      rw [matHom_comp]; rfl)))

theorem toMod_map_apply {P Q : SKar k (SuperalgebraCat 𝒜)} (f : P ⟶ Q) (v : imgSubmodule P) :
    (((toMod 𝒜).map f).1.1 v).1 = matHom f.f v.1 := rfl

instance : (toMod 𝒜).Additive where
  map_add {P Q f g} := Underlying.hom_ext (SuperBimodule.hom_ext (SVec.hom_ext fun v =>
    Subtype.ext (by
      change matHom (f.f + g.f) v.1 = matHom f.f v.1 + matHom g.f v.1
      rw [matHom_add]; rfl)))

/-! ## Full faithfulness -/

/-- **Example 1.17(i).** The functor `SKar(A) ⥤ (k-SMod-A)̲` is faithful. -/
instance toMod_faithful : (toMod 𝒜).Faithful where
  map_injective {P Q f g} h := by
    apply Idempotents.Karoubi.hom_ext
    apply matHom_injective
    refine SVec.hom_ext fun v => ?_
    have := congrArg (fun φ : (toMod 𝒜).obj P ⟶ (toMod 𝒜).obj Q =>
      (φ.1.1 ⟨matHom P.p v, matHom_p_mem P v⟩).1) h
    simp only [toMod_map_apply] at this
    rw [← Idempotents.Karoubi.p_comp f, ← Idempotents.Karoubi.p_comp g, matHom_comp, matHom_comp,
      SVec.comp_apply, SVec.comp_apply]
    exact this

section Full

open scoped Classical

variable {P Q : SKar k (SuperalgebraCat 𝒜)} (g : (toMod 𝒜).obj P ⟶ (toMod 𝒜).obj Q)

/-- The map `v ↦ g(p v)`. -/
def fullMap (v : P.X.ι → A) : Q.X.ι → A := (g.1.1 ⟨matHom P.p v, matHom_p_mem P v⟩).1

theorem fullMap_add (v w : P.X.ι → A) : fullMap g (v + w) = fullMap g v + fullMap g w := by
  have e : (⟨matHom P.p (v + w), matHom_p_mem P _⟩ : imgSubmodule P) =
      ⟨matHom P.p v, matHom_p_mem P _⟩ + ⟨matHom P.p w, matHom_p_mem P _⟩ :=
    Subtype.ext (map_add (SVec.toLinearMap (matHom P.p)) v w)
  simp only [fullMap]
  rw [e, map_add]
  rfl

theorem fullMap_zero : fullMap g 0 = 0 := by
  have e : (⟨matHom P.p 0, matHom_p_mem P 0⟩ : imgSubmodule P) = 0 :=
    Subtype.ext (map_zero (SVec.toLinearMap (matHom P.p)))
  simp only [fullMap]
  rw [e, map_zero]
  rfl

theorem fullMap_sum {ι : Type*} (s : Finset ι) (v : ι → P.X.ι → A) :
    fullMap g (∑ i ∈ s, v i) = ∑ i ∈ s, fullMap g (v i) := by
  induction s using Finset.induction_on with
  | empty => simp [fullMap_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fullMap_add, ih]

/-- `v ↦ g(p v)` is right `A`-linear. -/
theorem fullMap_rmul (a : A) (v : P.X.ι → A) :
    fullMap g (rmul P.X a v) = rmul Q.X a (fullMap g v) := by
  have h := congrArg (fun φ => (φ ⟨matHom P.p v, matHom_p_mem P v⟩).1) (g.1.2.2 a)
  change (g.1.1 ⟨rmul P.X a (matHom P.p v), _⟩).1 = rmul Q.X a (fullMap g v) at h
  rw [fullMap, ← h]
  congr 2
  exact Subtype.ext (matHom_rmul P.p a v)

theorem single_mem_part (i : P.X.ι) :
    (Pi.single i 1 : P.X.ι → A) ∈ (freeObj 𝒜 P.X).part (par (P.X.X i)) := by
  rw [mem_freeObj_part_iff]
  intro i'
  rw [Pi.single_apply]
  split_ifs with h
  · subst h; rw [zmod2_add_self]; exact SetLike.GradedOne.one_mem
  · exact Submodule.zero_mem _

theorem fullMap_single_mem (i : P.X.ι) (j : Q.X.ι) :
    fullMap g (Pi.single i 1) j ∈ 𝒜 (par (P.X.X i) + par (Q.X.X j)) := by
  have h2 := SVec.apply_mem_part (matHom_mem P.p) (single_mem_part i)
  simp only [add_zero] at h2
  have h3 : (⟨matHom P.p (Pi.single i 1), matHom_p_mem P _⟩ : imgSubmodule P) ∈
      (imgObj P).part (par (P.X.X i)) := (SVec.mem_sub_part_iff _ _ _).2 h2
  have h4 := SVec.apply_mem_part (SuperBimodule.mem_parity_iff.1 g.2) h3
  simp only [add_zero] at h4
  have h5 := (SVec.mem_sub_part_iff _ _ _).1 h4
  rw [mem_freeObj_part_iff] at h5
  exact h5 j

/-- The matrix with entries `g(p eᵢ)ⱼ`. -/
def fullMatrix : P.X ⟶ Q.X := fun i j => ofElem (fullMap_single_mem g i j)

theorem matHom_fullMatrix (v : P.X.ι → A) : matHom (fullMatrix g) v = fullMap g v := by
  have hv : v = ∑ i, rmul P.X (v i) (Pi.single i 1) := by
    funext i'
    rw [Finset.sum_apply]
    change v i' = ∑ c, (Pi.single c (1 : A) : P.X.ι → A) i' * v c
    simp [Pi.single_apply]
  conv_rhs => rw [hv, fullMap_sum]
  funext j
  rw [Finset.sum_apply]
  change ∑ i, elem (fullMatrix g i j) * v i = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fullMap_rmul]
  rfl

theorem fullMap_p (v : P.X.ι → A) : fullMap g (matHom P.p v) = fullMap g v := by
  simp only [fullMap]
  congr 3
  exact mem_imgSubmodule.1 (matHom_p_mem P v)

theorem q_fullMap (v : P.X.ι → A) : matHom Q.p (fullMap g v) = fullMap g v :=
  mem_imgSubmodule.1 (g.1.1 ⟨matHom P.p v, matHom_p_mem P v⟩).2

/-- The preimage of `g` in `SKar(A)`. -/
def fullHom : P ⟶ Q :=
  ⟨fullMatrix g, by
    apply matHom_injective
    refine SVec.hom_ext fun v => ?_
    rw [matHom_comp, matHom_comp, SVec.comp_apply, SVec.comp_apply, matHom_fullMatrix,
      matHom_fullMatrix, fullMap_p, q_fullMap]⟩

theorem toMod_map_fullHom : (toMod 𝒜).map (fullHom g) = g := by
  refine Underlying.hom_ext (SuperBimodule.hom_ext (SVec.hom_ext fun w => Subtype.ext ?_))
  change matHom (fullMatrix g) w.1 = (g.1.1 w).1
  rw [matHom_fullMatrix, fullMap]
  congr 2
  exact Subtype.ext (mem_imgSubmodule.1 w.2)

end Full

/-- **Example 1.17(i).** The functor `SKar(A) ⥤ (k-SMod-A)̲` is full. -/
instance toMod_full : (toMod 𝒜).Full where
  map_surjective g := ⟨fullHom g, toMod_map_fullHom g⟩

/-! ## The essential image: finitely generated projective supermodules -/

variable (𝒜) in
/-- The finite free supermodule `⊕ᵢ Π^{aᵢ} A` (the image of the identity matrix, which is all
of `⊕ᵢ Π^{aᵢ} A`: `imgSubmodule_toKaroubi`). -/
abbrev freeMod (M : Mat_ (D 𝒜)) : SuperBimodule (trivialGrading k) 𝒜 :=
  toModObj ((toKaroubi _).obj M)

theorem imgSubmodule_toKaroubi (M : Mat_ (D 𝒜)) : imgSubmodule ((toKaroubi _).obj M) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [mem_imgSubmodule]
  change matHom (𝟙 M) v = v
  rw [matHom_id]; rfl

/-- A supermodule is finitely generated projective if it is an even direct summand of a finite
free supermodule `⊕ᵢ Π^{aᵢ} A`. -/
def IsFGProjective (V : SuperBimodule (trivialGrading k) 𝒜) : Prop :=
  ∃ (M : Mat_ (D 𝒜)) (i : (⟨V⟩ : Underlying k (SuperBimodule (trivialGrading k) 𝒜)) ⟶
      ⟨freeMod 𝒜 M⟩) (r : (⟨freeMod 𝒜 M⟩ : Underlying k (SuperBimodule (trivialGrading k) 𝒜)) ⟶
      ⟨V⟩), i ≫ r = 𝟙 _

/-- **Example 1.17(i).** The supermodules `p(⊕ᵢ Π^{aᵢ} A)` are finitely generated projective. -/
theorem isFGProjective_toMod_obj (P : SKar k (SuperalgebraCat 𝒜)) :
    IsFGProjective ((toMod 𝒜).obj P).obj :=
  ⟨P.X, (toMod 𝒜).map (Karoubi.decompId_i P), (toMod 𝒜).map (Karoubi.decompId_p P), by
    rw [← Functor.map_comp, ← Karoubi.decompId, CategoryTheory.Functor.map_id]⟩

/-- **Example 1.17(i).** Every finitely generated projective supermodule is evenly isomorphic to
`p(⊕ᵢ Π^{aᵢ} A)` for an object `(M, p)` of `SKar(A)`. Together with `toMod_full` and
`toMod_faithful`, `SKar(A)` is equivalent to the category of finitely generated projective
`A`-supermodules and even homomorphisms. -/
theorem exists_iso_toMod_obj {V : SuperBimodule (trivialGrading k) 𝒜} (hV : IsFGProjective V) :
    ∃ P : SKar k (SuperalgebraCat 𝒜), Nonempty ((toMod 𝒜).obj P ≅ ⟨V⟩) := by
  obtain ⟨M, i, r, h⟩ := hV
  let ε : (toKaroubi _).obj M ⟶ (toKaroubi _).obj M := (toMod 𝒜).preimage (r ≫ i)
  have hε : (toMod 𝒜).map ε = r ≫ i := (toMod 𝒜).map_preimage _
  have hεε : ε ≫ ε = ε := (toMod 𝒜).map_injective (by
    rw [Functor.map_comp, hε, Category.assoc, reassoc_of% h])
  have idem : ε.f ≫ ε.f = ε.f := congrArg Idempotents.Karoubi.Hom.f hεε
  let P : SKar k (SuperalgebraCat 𝒜) := ⟨M, ε.f, idem⟩
  let a : P ⟶ (toKaroubi _).obj M := ⟨ε.f, by
    rw [Idempotents.Karoubi.comp_p]; exact idem.symm⟩
  let b : (toKaroubi _).obj M ⟶ P := ⟨ε.f, by
    rw [← Category.assoc, Idempotents.Karoubi.p_comp]; exact idem.symm⟩
  have hab : a ≫ ε ≫ b = 𝟙 P := Idempotents.Karoubi.hom_ext _ _ (by
    change ε.f ≫ ε.f ≫ ε.f = ε.f; rw [idem, idem])
  have hba : b ≫ a = ε := Idempotents.Karoubi.hom_ext _ _ idem
  refine ⟨P, ⟨Iso.mk ((toMod 𝒜).map a ≫ r) (i ≫ (toMod 𝒜).map b) ?_ ?_⟩⟩
  · rw [Category.assoc, ← Category.assoc r, ← hε, ← Functor.map_comp, ← Functor.map_comp, hab,
      CategoryTheory.Functor.map_id]
  · rw [Category.assoc, ← Category.assoc ((toMod 𝒜).map b), ← Functor.map_comp, hba, hε,
      ← Category.assoc, ← Category.assoc, h, Category.id_comp, h]

end SKarAlg

end StringDiagrams
