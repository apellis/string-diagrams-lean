import StringDiagrams.Super.SKarMonoidal
import StringDiagrams.Super.Superalgebra
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The super Karoubi envelope of `I`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 1.17(ii).

Let `I` be the supercategory with one object and endomorphisms `k` (`UnitSupercat k`). An object
of `SKar(I) = Kar(Mat_(I̲_π))` is a pair `(M, p)` of a tuple `M = (Π^{aᵢ} ⋆)ᵢ` and an even
idempotent matrix `p` of scalars. We construct the functor
`SKarUnit.toSVec : SKar(I) ⥤ SVec̲` (to superspaces and even linear maps) sending `(M, p)` to
the image of `p` acting on the superspace `⊕ᵢ Π^{aᵢ} k`, and prove:

* it is additive, faithful and full (`SKarUnit.toSVec_faithful`, `SKarUnit.toSVec_full`), and
  over a field every finite-dimensional superspace is evenly isomorphic to an object in its image
  (`SKarUnit.exists_iso_toSVec_obj`): `SKar(I)` is equivalent to `SVec_fd`;
* over a field, `K₀(SKar(I)) ≅ Zπ`, `[V] ↦ dim V₀ + (dim V₁) π`, compatibly with the
  action of `π` (`SKarUnit.K₀Equiv`, `SKarUnit.K₀Equiv_π_smul`).

The monoidal structure of the equivalence (the paper states a monoidal equivalence) is not
formalized.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Limits Idempotents Supercategory Matrix

universe u

namespace SKarUnit

variable {k : Type u} [CommRing k]

/-- The underlying category `I̲_π` of the Π-envelope of `I`. -/
abbrev D (k : Type u) [CommRing k] : Type := Underlying k (Envelope k (UnitSupercat k))

/-- The parity `a` of an object `Πᵃ ⋆` of `I̲_π`. -/
abbrev par (X : D k) : ZMod 2 := X.obj.par

/-- The scalar underlying a morphism of `I̲_π`. -/
def scal {X Y : D k} (f : X ⟶ Y) : k := SuperalgebraCat.toElem (Envelope.toHom f.1)

@[simp] theorem scal_comp {X Y Z : D k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    scal (f ≫ g) = scal g * scal f := rfl

@[simp] theorem scal_id (X : D k) : scal (𝟙 X) = 1 := rfl

@[simp] theorem scal_add {X Y : D k} (f g : X ⟶ Y) : scal (f + g) = scal f + scal g := rfl

@[simp] theorem scal_zero {X Y : D k} : scal (0 : X ⟶ Y) = 0 := rfl

/-- `scal` as an additive map. -/
def scalHom (X Y : D k) : (X ⟶ Y) →+ k where
  toFun := scal
  map_zero' := rfl
  map_add' _ _ := rfl

theorem scal_sum {X Y : D k} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    scal (∑ i ∈ s, f i) = ∑ i ∈ s, scal (f i) :=
  map_sum (scalHom X Y) f s

theorem scal_eq_zero_of_ne {X Y : D k} (f : X ⟶ Y) (h : par X ≠ par Y) : scal f = 0 := by
  have hf := f.2
  rw [Envelope.mem_parity_iff, zero_add,
    show X.obj.par + Y.obj.par = 1 by
      rcases parity_eq_zero_or_one X.obj.par with h1 | h1 <;>
        rcases parity_eq_zero_or_one Y.obj.par with h2 | h2 <;> simp_all] at hf
  exact UnitSupercat.eq_zero_of_mem_parity_one hf

theorem hom_ext {X Y : D k} {f g : X ⟶ Y} (h : scal f = scal g) : f = g := Subtype.ext h

/-- The morphism `Πᵃ ⋆ ⟶ Πᵃ ⋆` given by a scalar. -/
def ofScal {X Y : D k} (h : par X = par Y) (r : k) : X ⟶ Y :=
  ⟨Envelope.ofHom (SuperalgebraCat.ofElem r), by
    rw [Envelope.mem_parity_iff, zero_add, show X.obj.par = Y.obj.par from h, zmod2_add_self]
    exact UnitSupercat.mem_parity_zero _⟩

@[simp] theorem scal_ofScal {X Y : D k} (h : par X = par Y) (r : k) : scal (ofScal h r) = r :=
  rfl

theorem scal_eqToHom {X Y : D k} (h : X = Y) : scal (eqToHom h) = 1 := by
  subst h; rfl

/-! ## The superspaces `⊕ᵢ Π^{aᵢ} k` -/

/-- The superspace `⊕ᵢ Π^{aᵢ} k` of an object `(Π^{aᵢ} ⋆)ᵢ` of the additive envelope. -/
abbrev freeObj (M : Mat_ (D k)) : SVec k where
  carrier := M.ι → k
  odd := LinearMap.pi fun i => if par (M.X i) = 1 then LinearMap.proj i else 0
  odd_comp_odd := by
    ext v i
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply]
    split_ifs <;> simp_all

theorem freeObj_odd_apply (M : Mat_ (D k)) (v : M.ι → k) (i : M.ι) :
    (freeObj M).odd v i = if par (M.X i) = 1 then v i else 0 := by
  simp only [freeObj, LinearMap.pi_apply]
  split_ifs <;> rfl

theorem freeObj_proj_apply (M : Mat_ (D k)) (q : ZMod 2) (v : M.ι → k) (i : M.ι) :
    (freeObj M).proj q v i = if par (M.X i) = q then v i else 0 := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [SVec.proj_zero, LinearMap.sub_apply, LinearMap.id_apply]
    change v i - (freeObj M).odd v i = _
    rw [freeObj_odd_apply]
    rcases parity_eq_zero_or_one (par (M.X i)) with h | h <;> simp [h]
  · rw [SVec.proj_one]; exact freeObj_odd_apply M v i

theorem mem_freeObj_part_iff (M : Mat_ (D k)) {q : ZMod 2} {v : M.ι → k} :
    v ∈ (freeObj M).part q ↔ ∀ i, par (M.X i) ≠ q → v i = 0 := by
  rw [SVec.mem_part_iff]
  constructor
  · intro h i hi
    rw [← h, freeObj_proj_apply, if_neg hi]
  · intro h
    funext i
    change (freeObj M).proj q v i = v i
    rw [freeObj_proj_apply]
    split_ifs with hi
    · rfl
    · exact (h i hi).symm

/-! ## Matrices of scalars -/

/-- The matrix of scalars of a morphism of the additive envelope. -/
def scalMat {M N : Mat_ (D k)} (f : M ⟶ N) : Matrix M.ι N.ι k := fun i j => scal (f i j)

theorem scalMat_comp {M N P : Mat_ (D k)} (f : M ⟶ N) (g : N ⟶ P) :
    scalMat (f ≫ g) = scalMat f * scalMat g := by
  ext i l
  simp only [scalMat, CategoryTheory.Mat_.comp_apply, scal_sum, scal_comp, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

open scoped Classical in
theorem scalMat_id (M : Mat_ (D k)) : scalMat (𝟙 M) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [scalMat, CategoryTheory.Mat_.id_apply_self]
  · rw [Matrix.one_apply_ne h, scalMat, CategoryTheory.Mat_.id_apply_of_ne _ _ _ h, scal_zero]

theorem scalMat_add {M N : Mat_ (D k)} (f g : M ⟶ N) : scalMat (f + g) = scalMat f + scalMat g :=
  rfl

theorem scalMat_injective {M N : Mat_ (D k)} : Function.Injective (scalMat (M := M) (N := N)) :=
  fun _ _ h => CategoryTheory.Mat_.hom_ext _ _ fun i j => hom_ext (congrFun (congrFun h i) j)

theorem scalMat_eq_zero_of_ne {M N : Mat_ (D k)} (f : M ⟶ N) {i : M.ι} {j : N.ι}
    (h : par (M.X i) ≠ par (N.X j)) : scalMat f i j = 0 :=
  scal_eq_zero_of_ne _ h

/-- The linear map `⊕ Π^{aᵢ} k → ⊕ Π^{bⱼ} k` of a matrix morphism: `v ↦ v · f`. -/
def matHom {M N : Mat_ (D k)} (f : M ⟶ N) : freeObj M ⟶ freeObj N :=
  SVec.ofHom (scalMat f).vecMulLinear

@[simp] theorem matHom_apply {M N : Mat_ (D k)} (f : M ⟶ N) (v : M.ι → k) :
    matHom f v = v ᵥ* scalMat f := rfl

theorem matHom_comp {M N P : Mat_ (D k)} (f : M ⟶ N) (g : N ⟶ P) :
    matHom (f ≫ g) = matHom f ≫ matHom g := by
  ext v j
  show (v ᵥ* scalMat (f ≫ g)) j = ((v ᵥ* scalMat f) ᵥ* scalMat g) j
  rw [scalMat_comp, Matrix.vecMul_vecMul]

open scoped Classical in
theorem matHom_id (M : Mat_ (D k)) : matHom (𝟙 M) = 𝟙 (freeObj M) := by
  ext v j
  show (v ᵥ* scalMat (𝟙 M)) j = v j
  rw [scalMat_id, Matrix.vecMul_one]

theorem matHom_mem {M N : Mat_ (D k)} (f : M ⟶ N) :
    matHom f ∈ SVec.parityHom (freeObj M) (freeObj N) 0 := by
  refine SVec.mem_parityHom_of_apply_mem fun q v hv => ?_
  simp only [add_zero]
  rw [mem_freeObj_part_iff] at hv ⊢
  intro j hj
  rw [matHom_apply, Matrix.vecMul, dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : par (M.X i) = q
  · rw [scalMat_eq_zero_of_ne f (by rw [hi]; exact Ne.symm hj), mul_zero]
  · rw [hv i hi, zero_mul]

theorem matHom_injective {M N : Mat_ (D k)} {f g : M ⟶ N} (h : matHom f = matHom g) : f = g := by
  classical
  apply scalMat_injective
  ext i j
  have := congrArg (fun φ : freeObj M ⟶ freeObj N => φ (Pi.single i 1) j) h
  change (Pi.single i 1 ᵥ* scalMat f) j = (Pi.single i 1 ᵥ* scalMat g) j at this
  simpa [Matrix.single_vecMul] using this

theorem matHom_odd {M N : Mat_ (D k)} (f : M ⟶ N) (v : M.ι → k) :
    matHom f ((freeObj M).odd v) = (freeObj N).odd (matHom f v) := by
  have h := SVec.apply_proj_of_mem (matHom_mem f) 1 v
  simp only [add_zero] at h
  rwa [SVec.proj_one, SVec.proj_one] at h

/-! ## The functor `SKar(I) ⥤ SVec̲` -/

/-- The image of an idempotent matrix. -/
def imgSubmodule (P : SKar k (UnitSupercat k)) : Submodule k (P.X.ι → k) :=
  LinearMap.range (SVec.toLinearMap (matHom P.p))

theorem mem_imgSubmodule {P : SKar k (UnitSupercat k)} {v : P.X.ι → k} :
    v ∈ imgSubmodule P ↔ matHom P.p v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    change matHom P.p (matHom P.p w) = matHom P.p w
    rw [← SVec.comp_apply, ← matHom_comp, P.idem]
  · intro h; exact ⟨v, h⟩

theorem odd_mem_imgSubmodule (P : SKar k (UnitSupercat k)) :
    ∀ v ∈ imgSubmodule P, (freeObj P.X).odd v ∈ imgSubmodule P := by
  intro v hv
  rw [mem_imgSubmodule] at hv ⊢
  rw [matHom_odd, hv]

/-- The superspace `(M, p) ↦ p(⊕ᵢ Π^{aᵢ} k)`. -/
abbrev imgObj (P : SKar k (UnitSupercat k)) : SVec k :=
  SVec.sub (freeObj P.X) (imgSubmodule P) (odd_mem_imgSubmodule P)

theorem matHom_mem_imgSubmodule {P Q : SKar k (UnitSupercat k)} (f : P ⟶ Q) :
    ∀ v ∈ imgSubmodule P, matHom f.f v ∈ imgSubmodule Q := by
  intro v _
  rw [mem_imgSubmodule, ← SVec.comp_apply, ← matHom_comp, Idempotents.Karoubi.comp_p]

/-- The even linear map `p(⊕ Π^{aᵢ} k) → q(⊕ Π^{bⱼ} k)` of a morphism of `SKar(I)`. -/
def imgHom {P Q : SKar k (UnitSupercat k)} (f : P ⟶ Q) : imgObj P ⟶ imgObj Q :=
  SVec.restrictHom (matHom f.f) (matHom_mem_imgSubmodule f)

@[simp] theorem imgHom_apply {P Q : SKar k (UnitSupercat k)} (f : P ⟶ Q) (v : imgSubmodule P) :
    ((imgHom f v : imgSubmodule Q) : Q.X.ι → k) = matHom f.f v := rfl

theorem imgHom_mem {P Q : SKar k (UnitSupercat k)} (f : P ⟶ Q) :
    imgHom f ∈ SVec.parityHom (imgObj P) (imgObj Q) 0 :=
  SVec.restrictHom_mem (matHom_mem f.f) _

variable (k) in
/-- **Brundan–Ellis, Example 1.17(ii).** The functor `SKar(I) ⥤ SVec̲`,
`(M, p) ↦ p(⊕ᵢ Π^{aᵢ} k)`. -/
def toSVec : SKar k (UnitSupercat k) ⥤ Underlying k (SVec k) where
  obj P := ⟨imgObj P⟩
  map f := ⟨imgHom f, imgHom_mem f⟩
  map_id P := Underlying.hom_ext (SVec.hom_ext fun v => Subtype.ext (by
    change matHom P.p v = v
    exact mem_imgSubmodule.1 v.2))
  map_comp f g := Underlying.hom_ext (SVec.hom_ext fun v => Subtype.ext (by
    change matHom (f.f ≫ g.f) v = matHom g.f (matHom f.f v)
    rw [matHom_comp]; rfl))

@[simp] theorem toSVec_obj (P : SKar k (UnitSupercat k)) : ((toSVec k).obj P).obj = imgObj P := rfl

theorem toSVec_map_apply {P Q : SKar k (UnitSupercat k)} (f : P ⟶ Q) (v : imgSubmodule P) :
    (((toSVec k).map f).1 v).1 = matHom f.f v.1 := rfl

instance : (toSVec k).Additive where
  map_add {P Q f g} := Underlying.hom_ext (SVec.hom_ext fun v => Subtype.ext (by
    change v.1 ᵥ* scalMat (f.f + g.f) = (v.1 ᵥ* scalMat f.f) + (v.1 ᵥ* scalMat g.f)
    rw [scalMat_add, Matrix.vecMul_add]))

/-! ## Full faithfulness -/

theorem matHom_p_mem (P : SKar k (UnitSupercat k)) (v : P.X.ι → k) :
    matHom P.p v ∈ imgSubmodule P := ⟨v, rfl⟩

/-- **Example 1.17(ii).** The functor `SKar(I) ⥤ SVec̲` is faithful. -/
instance toSVec_faithful : (toSVec k).Faithful where
  map_injective {P Q f g} h := by
    apply Idempotents.Karoubi.hom_ext
    apply matHom_injective
    refine SVec.hom_ext fun v => ?_
    have := congrArg (fun φ : (toSVec k).obj P ⟶ (toSVec k).obj Q =>
      (φ.1 ⟨matHom P.p v, matHom_p_mem P v⟩).1) h
    simp only [toSVec_map_apply] at this
    rw [← Idempotents.Karoubi.p_comp f, ← Idempotents.Karoubi.p_comp g, matHom_comp, matHom_comp,
      SVec.comp_apply, SVec.comp_apply]
    exact this

section Full

open scoped Classical

variable {P Q : SKar k (UnitSupercat k)} (g : (toSVec k).obj P ⟶ (toSVec k).obj Q)

/-- The linear map `⊕ Π^{aᵢ} k → ⊕ Π^{bⱼ} k` given by `v ↦ g(p v)`. -/
def fullMap : (P.X.ι → k) →ₗ[k] (Q.X.ι → k) :=
  (imgSubmodule Q).subtype ∘ₗ SVec.toLinearMap g.1 ∘ₗ
    (SVec.toLinearMap (matHom P.p)).codRestrict (imgSubmodule P) (matHom_p_mem P)

theorem fullMap_apply (v : P.X.ι → k) :
    fullMap g v = (g.1 ⟨matHom P.p v, matHom_p_mem P v⟩).1 := rfl

theorem fullMap_eq_zero_of_ne {i : P.X.ι} {j : Q.X.ι} (h : par (P.X.X i) ≠ par (Q.X.X j)) :
    fullMap g (Pi.single i 1) j = 0 := by
  have h1 : (Pi.single i 1 : P.X.ι → k) ∈ (freeObj P.X).part (par (P.X.X i)) := by
    rw [mem_freeObj_part_iff]
    intro i' hi'
    rw [Pi.single_apply, if_neg]
    rintro rfl; exact hi' rfl
  have h2 := SVec.apply_mem_part (matHom_mem P.p) h1
  simp only [add_zero] at h2
  have h3 : (⟨matHom P.p (Pi.single i 1), matHom_p_mem P _⟩ : imgSubmodule P) ∈
      (imgObj P).part (par (P.X.X i)) := (SVec.mem_sub_part_iff _ _ _).2 h2
  have h4 := SVec.apply_mem_part g.2 h3
  simp only [add_zero] at h4
  have h5 := (SVec.mem_sub_part_iff _ _ _).1 h4
  rw [mem_freeObj_part_iff] at h5
  exact h5 j (Ne.symm h)

/-- The matrix morphism with entries `g(p eᵢ)ⱼ`. -/
def fullMatrix : P.X ⟶ Q.X := fun i j =>
  if h : par (P.X.X i) = par (Q.X.X j) then ofScal h (fullMap g (Pi.single i 1) j) else 0

theorem scalMat_fullMatrix : scalMat (fullMatrix g) = fun i j => fullMap g (Pi.single i 1) j := by
  ext i j
  simp only [scalMat, fullMatrix]
  split_ifs with h
  · rfl
  · rw [scal_zero, fullMap_eq_zero_of_ne g h]

theorem matHom_fullMatrix (v : P.X.ι → k) : matHom (fullMatrix g) v = fullMap g v := by
  change v ᵥ* scalMat (fullMatrix g) = _
  rw [scalMat_fullMatrix]
  conv_rhs => rw [pi_eq_sum_univ v]
  ext j
  simp only [Matrix.vecMul, dotProduct, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : (Pi.single x 1 : P.X.ι → k) = fun j => if x = j then 1 else 0 := by
    funext j'; rw [Pi.single_apply]; simp [eq_comm]
  rw [this]

theorem fullMap_p (v : P.X.ι → k) : fullMap g (matHom P.p v) = fullMap g v := by
  rw [fullMap_apply, fullMap_apply]
  congr 3
  exact mem_imgSubmodule.1 (matHom_p_mem P v)

theorem q_fullMap (v : P.X.ι → k) : matHom Q.p (fullMap g v) = fullMap g v :=
  mem_imgSubmodule.1 (g.1 ⟨matHom P.p v, matHom_p_mem P v⟩).2

/-- The preimage of `g` in `SKar(I)`. -/
def fullHom : P ⟶ Q :=
  ⟨fullMatrix g, by
    apply matHom_injective
    refine SVec.hom_ext fun v => ?_
    rw [matHom_comp, matHom_comp, SVec.comp_apply, SVec.comp_apply, matHom_fullMatrix,
      matHom_fullMatrix, fullMap_p, q_fullMap]⟩

theorem toSVec_map_fullHom : (toSVec k).map (fullHom g) = g := by
  refine Underlying.hom_ext (SVec.hom_ext fun w => Subtype.ext ?_)
  change matHom (fullMatrix g) w.1 = (g.1 w).1
  rw [matHom_fullMatrix, fullMap_apply]
  congr 2
  exact Subtype.ext (mem_imgSubmodule.1 w.2)

end Full

/-- **Example 1.17(ii).** The functor `SKar(I) ⥤ SVec̲` is full. -/
instance toSVec_full : (toSVec k).Full where
  map_surjective g := ⟨fullHom g, toSVec_map_fullHom g⟩

end SKarUnit

end StringDiagrams
