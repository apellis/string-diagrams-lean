import StringDiagrams.Super.SKarMonoidal
import StringDiagrams.Super.Superalgebra
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

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
* over a field, `K₀(SKar(I)) ≅ Zπ` as `Zπ`-algebras, with inverse
  `[V] ↦ dim V₀ + (dim V₁) π` (`SKarUnit.K₀AlgEquiv`, `SKarUnit.K₀AlgEquiv_symm_mk`); the
  dimension map intertwines `[V] ↦ [Π V]` with multiplication by `π`
  (`SKarUnit.K₀Dim_piInvolution`).

The classification of objects up to isomorphism by their dimensions is
`SKarUnit.nonempty_iso_of_dim_eq`; that `SKar(I)` is a semisimple abelian category with the two
simple objects `k` and `Π k` is proved in `StringDiagrams.Super.SKarUnitAbelian`; the
compatibility of the equivalence with the monoidal structures (the paper states a monoidal
equivalence) is proved in `StringDiagrams.Super.SKarUnitMonoidal`.
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

/-- An isomorphism of `SVec̲`, as an even isomorphism of superspaces. -/
def svecIso {V W : Underlying k (SVec k)} (e : V ≅ W) : V.obj ≅ W.obj where
  hom := e.hom.1
  inv := e.inv.1
  hom_inv_id := congrArg Subtype.val e.hom_inv_id
  inv_hom_id := congrArg Subtype.val e.inv_hom_id

theorem toSVec_map_comp_val {P Q R : SKar k (UnitSupercat k)} (f : P ⟶ Q) (g : Q ⟶ R) :
    ((toSVec k).map (f ≫ g)).1 = ((toSVec k).map f).1 ≫ ((toSVec k).map g).1 :=
  congrArg Subtype.val ((toSVec k).map_comp f g)

theorem toSVec_map_id_val (P : SKar k (UnitSupercat k)) :
    ((toSVec k).map (𝟙 P)).1 = 𝟙 (imgObj P) :=
  congrArg Subtype.val ((toSVec k).map_id P)

theorem toSVec_map_add_val {P Q : SKar k (UnitSupercat k)} (f g : P ⟶ Q) :
    ((toSVec k).map (f + g)).1 = ((toSVec k).map f).1 + ((toSVec k).map g).1 :=
  congrArg Subtype.val ((toSVec k).map_add)

/-- `Π` on `I̲_π` does not change scalars. -/
theorem scal_pi {X Y : D k} (f : X ⟶ Y) : scal ((PiCategory.pi (R := k)).map f) = scal f := by
  change SuperalgebraCat.toElem (Envelope.toHom ((PiSupercategory.pi (R := k)).map f.1)) = scal f
  rw [Envelope.toHom_pi_map, twist_of_mem 1 (UnitSupercat.mem_parity_zero _), mul_zero,
    sign_zero, one_smul]
  by_cases h : par X = par Y
  · change SuperalgebraCat.toElem (sign k (X.obj.par + Y.obj.par) • Envelope.toHom f.1) = scal f
    rw [show X.obj.par = Y.obj.par from h, zmod2_add_self, sign_zero, one_smul]; rfl
  · change sign k (X.obj.par + Y.obj.par) * scal f = scal f
    rw [scal_eq_zero_of_ne f h, mul_zero]

theorem scalMat_pi {M N : Mat_ (D k)} (f : M ⟶ N) :
    scalMat ((PiCategory.pi (R := k)).map f) = scalMat f := by
  ext i j
  exact scal_pi (f i j)

theorem imgSubmodule_eq (P : SKar k (UnitSupercat k)) :
    imgSubmodule P = LinearMap.range (scalMat P.p).vecMulLinear := rfl

theorem pi_obj_p (P : SKar k (UnitSupercat k)) :
    ((PiCategory.pi (R := k)).obj P).p = (PiCategory.pi (R := k)).map P.p := rfl

theorem imgSubmodule_pi (P : SKar k (UnitSupercat k)) :
    imgSubmodule ((PiCategory.pi (R := k)).obj P) = imgSubmodule P := by
  rw [imgSubmodule_eq, imgSubmodule_eq, pi_obj_p, scalMat_pi]

/-- The object `(Π^{aᵢ + 1} ⋆)ᵢ`. -/
abbrev shiftMat (M : Mat_ (D k)) : Mat_ (D k) := ⟨M.ι, fun i => ⟨⟨par (M.X i) + 1, ()⟩⟩⟩

theorem pi_obj_mat (M : Mat_ (D k)) : (PiCategory.pi (R := k)).obj M = shiftMat M := rfl

theorem mem_freeObj_shiftMat_part_iff (M : Mat_ (D k)) {q : ZMod 2} {v : M.ι → k} :
    v ∈ (freeObj (shiftMat M)).part q ↔ v ∈ (freeObj M).part (q + 1) := by
  rw [mem_freeObj_part_iff, mem_freeObj_part_iff]
  refine forall_congr' fun i => imp_congr_left ?_
  change par (M.X i) + 1 ≠ q ↔ _
  rcases parity_eq_zero_or_one (par (M.X i)) with h | h <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;> simp [h]

/-! ## Dimensions -/

section Field

variable {K : Type u} [Field K]

instance (P : SKar K (UnitSupercat K)) (q : ZMod 2) : Module.Finite K ((imgObj P).part q) :=
  inferInstance

instance (P : SKar K (UnitSupercat K)) (q : ZMod 2) :
    Module.Finite K (((toSVec K).obj P).obj.part q) :=
  inferInstanceAs (Module.Finite K ((imgObj P).part q))

/-- The dimension of the component of parity `q` of `p(⊕ᵢ Π^{aᵢ} K)`. -/
def dim (P : SKar K (UnitSupercat K)) (q : ZMod 2) : ℕ := Module.finrank K ((imgObj P).part q)

theorem dim_eq_of_iso {P Q : SKar K (UnitSupercat K)} (e : P ≅ Q) (q : ZMod 2) :
    dim P q = dim Q q :=
  (SVec.partEquivOfIso (svecIso ((toSVec K).mapIso e)) ((toSVec K).map e.hom).2 q).finrank_eq

theorem dim_biprod (P Q : SKar K (UnitSupercat K)) (q : ZMod 2) :
    dim (P ⊞ Q) q = dim P q + dim Q q := by
  have hmap : ∀ {A B C : SKar K (UnitSupercat K)} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C),
      f ≫ g = h → ((toSVec K).map f).1 ≫ ((toSVec K).map g).1 = ((toSVec K).map h).1 := by
    intro A B C f g h e; rw [← toSVec_map_comp_val, e]
  exact SVec.finrank_part_of_biprod ((toSVec K).map biprod.inl).1 ((toSVec K).map biprod.inr).1
    ((toSVec K).map biprod.fst).1 ((toSVec K).map biprod.snd).1
    ((toSVec K).map _).2 ((toSVec K).map _).2 ((toSVec K).map _).2 ((toSVec K).map _).2
    (by rw [hmap _ _ _ biprod.inl_fst, CategoryTheory.Functor.map_id]; rfl)
    (by rw [hmap _ _ _ biprod.inr_snd, CategoryTheory.Functor.map_id]; rfl)
    (by rw [hmap _ _ _ biprod.inl_snd, Functor.map_zero]; rfl)
    (by rw [hmap _ _ _ biprod.inr_fst, Functor.map_zero]; rfl)
    (by
      rw [← toSVec_map_comp_val, ← toSVec_map_comp_val, ← toSVec_map_add_val, biprod.total,
        toSVec_map_id_val]
      rfl)
    q

/-- The dimension as the rank of a submodule of `⊕ᵢ Π^{aᵢ} K`. -/
theorem dim_eq_finrank (P : SKar K (UnitSupercat K)) (q : ZMod 2) :
    dim P q = Module.finrank K ↥(imgSubmodule P ⊓ (freeObj P.X).part q) := by
  refine LinearEquiv.finrank_eq
    { toFun := fun w => ⟨w.1.1, w.1.2, (SVec.mem_sub_part_iff (freeObj P.X) (imgSubmodule P)
        (odd_mem_imgSubmodule P)).1 w.2⟩
      invFun := fun w => ⟨⟨w.1, w.2.1⟩, (SVec.mem_sub_part_iff (freeObj P.X) (imgSubmodule P)
        (odd_mem_imgSubmodule P)).2 w.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem freeObj_part_pi (P : SKar K (UnitSupercat K)) (q : ZMod 2) :
    (freeObj ((PiCategory.pi (R := K)).obj P).X).part q = (freeObj P.X).part (q + 1) := by
  ext v
  exact mem_freeObj_shiftMat_part_iff P.X

theorem dim_pi (P : SKar K (UnitSupercat K)) (q : ZMod 2) :
    dim ((PiCategory.pi (R := K)).obj P) q = dim P (q + 1) := by
  rw [dim_eq_finrank, dim_eq_finrank]
  have h : imgSubmodule ((PiCategory.pi (R := K)).obj P) ⊓
      (freeObj ((PiCategory.pi (R := K)).obj P).X).part q =
        imgSubmodule P ⊓ (freeObj P.X).part (q + 1) := by
    rw [imgSubmodule_pi, freeObj_part_pi]
  exact congrArg (fun S : Submodule K (P.X.ι → K) => Module.finrank K S) h

/-- The dimensions of the objects `(M, 1)`. -/
theorem dim_toKaroubi (M : Mat_ (D K)) (q : ZMod 2) :
    dim ((toKaroubi _).obj M) q = Fintype.card {i // par (M.X i) = q} := by
  classical
  rw [← Module.finrank_fintype_fun_eq_card (R := K)]
  have hall : ∀ v : M.ι → K, v ∈ imgSubmodule ((toKaroubi _).obj M) := fun v =>
    mem_imgSubmodule.2 (by
      change matHom (𝟙 M) v = v
      rw [matHom_id]; rfl)
  refine LinearEquiv.finrank_eq
    { toFun := fun w i => w.1.1 i.1
      invFun := fun u => ⟨⟨fun i => if h : par (M.X i) = q then u ⟨i, h⟩ else 0, hall _⟩,
        (SVec.mem_sub_part_iff _ _ _).2 ((mem_freeObj_part_iff M).2 fun i hi => dif_neg hi)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun w => ?_
      right_inv := fun u => ?_ }
  · apply Subtype.ext; apply Subtype.ext
    funext i
    dsimp only
    split_ifs with h
    · rfl
    · exact ((mem_freeObj_part_iff M).1 ((SVec.mem_sub_part_iff _ _ _).1 w.2) i h).symm
  · funext i
    exact dif_pos i.2

variable (K) in
/-- The object `Πᵃ ⋆` of `SKar(I)`. -/
def obj (a : ZMod 2) : SKar K (UnitSupercat K) :=
  (toKaroubi _).obj ((CategoryTheory.Mat_.embedding _).obj (⟨⟨a, ()⟩⟩ : D K))

theorem dim_obj (a q : ZMod 2) : dim (obj K a) q = if a = q then 1 else 0 := by
  rw [obj, dim_toKaroubi]
  split_ifs with h
  · subst h
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨PUnit.unit, rfl⟩, fun _ => Subtype.ext rfl⟩
  · rw [Fintype.card_eq_zero_iff]; exact ⟨fun i => h i.2⟩

/-! ## The Grothendieck group -/

/-- `dim V₀ + (dim V₁) π ∈ Zπ`. -/
def dimZπ (P : SKar K (UnitSupercat K)) : Zπ := (dim P 0 : Zπ) + (dim P 1 : Zπ) * Zπ.π

variable (K) in
/-- The homomorphism `K₀(SKar(I)) → Zπ`, `[V] ↦ dim V₀ + (dim V₁) π`. -/
def K₀Dim : K₀ (SKar K (UnitSupercat K)) →+ Zπ :=
  K₀.lift dimZπ (fun P Q e => by simp only [dimZπ, dim_eq_of_iso e])
    (fun P Q => by simp only [dimZπ, dim_biprod]; push_cast; ring)

@[simp] theorem K₀Dim_mk (P : SKar K (UnitSupercat K)) : K₀Dim K (K₀.mk P) = dimZπ P :=
  K₀.lift_mk _ _ _ P

theorem K₀Dim_obj_zero : K₀Dim K (K₀.mk (obj K 0)) = 1 := by
  rw [K₀Dim_mk, dimZπ, dim_obj, dim_obj]
  simp

theorem K₀Dim_obj_one : K₀Dim K (K₀.mk (obj K 1)) = Zπ.π := by
  rw [K₀Dim_mk, dimZπ, dim_obj, dim_obj]
  simp

theorem K₀Dim_surjective : Function.Surjective (K₀Dim K) := by
  intro z
  obtain ⟨a, b, rfl⟩ := Zπ.exists_eq_add_mul_π z
  refine ⟨a • K₀.mk (obj K 0) + b • K₀.mk (obj K 1), ?_⟩
  rw [map_add, map_zsmul, map_zsmul, K₀Dim_obj_zero, K₀Dim_obj_one, zsmul_eq_mul, zsmul_eq_mul,
    mul_one]

/-- Objects of `SKar(I)` with the same dimensions are isomorphic. -/
theorem nonempty_iso_of_dim_eq {P Q : SKar K (UnitSupercat K)} (h₀ : dim P 0 = dim Q 0)
    (h₁ : dim P 1 = dim Q 1) : Nonempty (P ≅ Q) := by
  let e := SVec.isoOfPartEquiv (V := ((toSVec K).obj P).obj) (W := ((toSVec K).obj Q).obj)
    (LinearEquiv.ofFinrankEq _ _ h₀) (LinearEquiv.ofFinrankEq _ _ h₁)
  exact ⟨(toSVec K).preimageIso (Underlying.isoMk e (SVec.isoOfPartEquiv_hom_mem _ _))⟩

theorem K₀Dim_injective : Function.Injective (K₀Dim K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨P, Q, rfl⟩ := K₀.exists_eq_mk_sub_mk x
  rw [map_sub, K₀Dim_mk, K₀Dim_mk, sub_eq_zero, dimZπ, dimZπ] at hx
  have hx' : ((dim P 0 : ℤ) : Zπ) + ((dim P 1 : ℤ) : Zπ) * Zπ.π =
      ((dim Q 0 : ℤ) : Zπ) + ((dim Q 1 : ℤ) : Zπ) * Zπ.π := by
    simpa only [Int.cast_natCast] using hx
  obtain ⟨h₀, h₁⟩ := Zπ.add_mul_π_injective hx'
  obtain ⟨e⟩ := nonempty_iso_of_dim_eq (Int.ofNat_inj.1 h₀) (Int.ofNat_inj.1 h₁)
  rw [K₀.mk_eq_mk_of_iso e, sub_self]

theorem K₀Dim_piInvolution (x : K₀ (SKar K (UnitSupercat K))) :
    K₀Dim K (K₀.piInvolution K _ x) = Zπ.π * K₀Dim K x := by
  induction x using K₀.induction_on with
  | mk P =>
    rw [K₀.piInvolution_mk, K₀Dim_mk, K₀Dim_mk, dimZπ, dimZπ, dim_pi, dim_pi]
    rw [show (0 : ZMod 2) + 1 = 1 from rfl, show (1 : ZMod 2) + 1 = 0 from rfl]
    rw [mul_add, ← mul_assoc, mul_comm Zπ.π (dim P 1 : Zπ), mul_assoc, Zπ.π_mul_π]
    ring
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]
  | neg x hx => rw [map_neg, map_neg, hx, map_neg]; ring

theorem one_eq_mk_obj_zero : (1 : K₀ (SKar K (UnitSupercat K))) = K₀.mk (obj K 0) := rfl

theorem K₀Dim_one : K₀Dim K 1 = 1 := by rw [one_eq_mk_obj_zero, K₀Dim_obj_zero]

/-- `K₀(SKar(I)) → Zπ` is `Zπ`-linear for the `Zπ`-algebra structure of §1.5. -/
theorem K₀Dim_smul (c : Zπ) (x : K₀ (SKar K (UnitSupercat K))) :
    K₀Dim K (c • x) = c * K₀Dim K x := by
  obtain ⟨a, b, rfl⟩ := Zπ.exists_eq_add_mul_π c
  rw [add_smul, MulAction.mul_smul, SKar.π_smul_eq, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul,
    map_add, map_zsmul, map_zsmul, K₀Dim_piInvolution, zsmul_eq_mul, zsmul_eq_mul]
  ring

theorem K₀Dim_algebraMap (c : Zπ) : K₀Dim K (algebraMap Zπ _ c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, K₀Dim_smul, K₀Dim_one, mul_one]

/-- **Brundan–Ellis, Example 1.17(ii).** Over a field, `K₀(SKar(I)) ≅ Zπ` as `Zπ`-algebras;
the inverse is `[V] ↦ dim V₀ + (dim V₁) π` (`K₀AlgEquiv_symm_apply`). -/
def K₀AlgEquiv : Zπ ≃ₐ[Zπ] K₀ (SKar K (UnitSupercat K)) :=
  AlgEquiv.ofBijective (Algebra.ofId Zπ _)
    ⟨fun c c' h => by
      have := congrArg (K₀Dim K) h
      simpa only [Algebra.ofId_apply, K₀Dim_algebraMap] using this,
    fun x => ⟨K₀Dim K x, K₀Dim_injective (by rw [Algebra.ofId_apply, K₀Dim_algebraMap])⟩⟩

theorem K₀AlgEquiv_symm_apply (x : K₀ (SKar K (UnitSupercat K))) :
    (K₀AlgEquiv (K := K)).symm x = K₀Dim K x := by
  rw [AlgEquiv.symm_apply_eq]
  exact K₀Dim_injective (by
    change K₀Dim K x = K₀Dim K (algebraMap Zπ _ (K₀Dim K x))
    rw [K₀Dim_algebraMap])

theorem K₀AlgEquiv_symm_mk (P : SKar K (UnitSupercat K)) :
    (K₀AlgEquiv (K := K)).symm (K₀.mk P) =
      (dim P 0 : Zπ) + (dim P 1 : Zπ) * Zπ.π := by
  rw [K₀AlgEquiv_symm_apply, K₀Dim_mk, dimZπ]

/-! ## Essential surjectivity onto `SVec_fd` -/

/-- The object `(Π⁰ ⋆)^m ⊕ (Π¹ ⋆)^n` of the additive envelope. -/
def sumMat (m n : ℕ) : Mat_ (D K) :=
  ⟨Fin m ⊕ Fin n, Sum.elim (fun _ => ⟨⟨0, ()⟩⟩) (fun _ => ⟨⟨1, ()⟩⟩)⟩

theorem card_sumMat_zero (m n : ℕ) :
    Fintype.card {i // par ((sumMat (K := K) m n).X i) = 0} = m := by
  refine (Fintype.card_congr
    { toFun := fun i => match i with
        | ⟨.inl a, _⟩ => a
        | ⟨.inr _, h⟩ => (fun h' : (1 : ZMod 2) = 0 => absurd h' (by decide)) h
      invFun := fun a => ⟨.inl a, rfl⟩
      left_inv := fun i => ?_
      right_inv := fun _ => rfl }).trans (Fintype.card_fin m)
  rcases i with ⟨i | i, h⟩
  · rfl
  · exact (fun h' : (1 : ZMod 2) = 0 => absurd h' (by decide)) h

theorem card_sumMat_one (m n : ℕ) :
    Fintype.card {i // par ((sumMat (K := K) m n).X i) = 1} = n := by
  refine (Fintype.card_congr
    { toFun := fun i => match i with
        | ⟨.inr a, _⟩ => a
        | ⟨.inl _, h⟩ => (fun h' : (0 : ZMod 2) = 1 => absurd h' (by decide)) h
      invFun := fun a => ⟨.inr a, rfl⟩
      left_inv := fun i => ?_
      right_inv := fun _ => rfl }).trans (Fintype.card_fin n)
  rcases i with ⟨i | i, h⟩
  · exact (fun h' : (0 : ZMod 2) = 1 => absurd h' (by decide)) h
  · rfl

/-- **Brundan–Ellis, Example 1.17(ii).** Every finite-dimensional superspace is evenly
isomorphic to the image of an object of `SKar(I)`: together with `toSVec_full` and
`toSVec_faithful`, `SKar(I)` is equivalent to `SVec_fd`. -/
theorem exists_iso_toSVec_obj (V : SVec K) [FiniteDimensional K V] :
    ∃ P : SKar K (UnitSupercat K), Nonempty ((toSVec K).obj P ≅ ⟨V⟩) := by
  refine ⟨(toKaroubi _).obj (sumMat (Module.finrank K (V.part 0)) (Module.finrank K (V.part 1))),
    ⟨Underlying.isoMk (SVec.isoOfPartEquiv (LinearEquiv.ofFinrankEq _ _ ?_)
      (LinearEquiv.ofFinrankEq _ _ ?_)) (SVec.isoOfPartEquiv_hom_mem _ _)⟩⟩
  · exact (dim_toKaroubi _ 0).trans (card_sumMat_zero _ _)
  · exact (dim_toKaroubi _ 1).trans (card_sumMat_one _ _)

/-- The image of every object of `SKar(I)` is finite-dimensional. -/
instance (P : SKar K (UnitSupercat K)) : FiniteDimensional K ((toSVec K).obj P).obj :=
  inferInstanceAs (FiniteDimensional K (imgSubmodule P))

end Field

end SKarUnit

end StringDiagrams
