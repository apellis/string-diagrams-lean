import StringDiagrams.Super.SKarUnit
import StringDiagrams.Super.Semisimple

/-!
# `SKar(I)` is a semisimple abelian category (Example 1.17(ii))

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 1.17(ii): over a field `K`, the super Karoubi envelope `SKar(I)` of the unit
supercategory "is a semisimple Abelian category with just two isomorphism classes of irreducible
objects represented by `k` and `Πk`".

The objects `Πᵃ ⋆` (`SKarUnit.obj K a`, `a ∈ ℤ/2`), which correspond to the superspaces `K` and
`ΠK` under `SKarUnit.toSVec`, are orthogonal Schur generators of `SKar(I)`
(`SKarUnit.orthogonalSchurGenerators_obj`): their endomorphism algebras are `K`, there are no
nonzero morphisms between them, and every object is isomorphic to `(Π⁰ ⋆)^m ⊕ (Π¹ ⋆)^n` with
`(m, n)` its even and odd dimensions (`SKarUnit.exists_iso_bsum_obj`). Hence, by
`StringDiagrams.Super.Semisimple`:

* `SKarUnit.abelian`: `SKar(I)` is an abelian category;
* `SKarUnit.simple_obj`: `Π⁰ ⋆` and `Π¹ ⋆` are simple;
* `SKarUnit.exists_iso_bsum_simple`: every object is a finite biproduct of simple objects;
* `SKarUnit.exists_iso_obj_of_simple`, `SKarUnit.isEmpty_iso_obj_zero_one`: `Π⁰ ⋆` and `Π¹ ⋆`
  form a complete set of pairwise non-isomorphic simple objects.
-/

noncomputable section

namespace StringDiagrams.SKarUnit

open CategoryTheory Limits Idempotents OddTemperleyLieb ZeroObject Supercategory

universe u

variable {K : Type u} [Field K]

/-! ## The generators `Π⁰ ⋆`, `Π¹ ⋆` -/

theorem obj_p (a : ZMod 2) :
    (obj K a).p = 𝟙 ((CategoryTheory.Mat_.embedding _).obj (⟨⟨a, ()⟩⟩ : D K)) := rfl

/-- `End(Πᵃ ⋆) = K`. -/
theorem isSchur_obj (a : ZMod 2) : IsSchur (k := K) (obj K a) := by
  intro f
  refine ⟨scal (f.f PUnit.unit PUnit.unit), ?_⟩
  apply Karoubi.hom_ext
  apply CategoryTheory.Mat_.hom_ext
  rintro ⟨⟩ ⟨⟩
  apply hom_ext
  rw [Karoubi.smul_f, Karoubi.id_f, obj_p, Mat_.smul_apply, CategoryTheory.Mat_.id_apply_self]
  change _ = scal (f.f PUnit.unit PUnit.unit) * scal (𝟙 _)
  rw [scal_id, mul_one]

/-- `Πᵃ ⋆ ≠ 0`. -/
theorem id_obj_ne_zero (a : ZMod 2) : 𝟙 (obj K a) ≠ 0 := by
  intro h
  have := congrArg (fun φ : obj K a ⟶ obj K a => scal (φ.f PUnit.unit PUnit.unit)) h
  simp only [Karoubi.id_f, obj_p, CategoryTheory.Mat_.id_apply_self, scal_id] at this
  exact one_ne_zero (this.trans rfl)

/-- `Hom(Πᵃ ⋆, Πᵇ ⋆) = 0` for `a ≠ b`. -/
theorem hom_obj_eq_zero {a b : ZMod 2} (h : a ≠ b) (f : obj K a ⟶ obj K b) : f = 0 := by
  apply Karoubi.hom_ext
  apply CategoryTheory.Mat_.hom_ext
  rintro ⟨⟩ ⟨⟩
  apply hom_ext
  rw [scal_eq_zero_of_ne _ h]
  rfl

/-! ## Dimensions of biproducts -/

theorem dim_of_isZero {P : SKar K (UnitSupercat K)} (hP : IsZero P) (q : ZMod 2) : dim P q = 0 := by
  have hz : IsZero ((0 : SKar K (UnitSupercat K)) ⊞ 0) := by
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext <;> exact (isZero_zero _).eq_of_tgt _ _
  have h1 := dim_biprod (0 : SKar K (UnitSupercat K)) 0 q
  rw [dim_eq_of_iso (hz.iso (isZero_zero _)) q] at h1
  rw [dim_eq_of_iso (hP.iso (isZero_zero _)) q]
  omega

theorem dim_bsum (L : List (SKar K (UnitSupercat K))) (q : ZMod 2) :
    dim (bsum L) q = (L.map fun P => dim P q).sum := by
  induction L with
  | nil => exact dim_of_isZero (isZero_zero _) q
  | cons P L ih => rw [bsum_cons, dim_biprod, ih, List.map_cons, List.sum_cons]

/-- The object `(Π⁰ ⋆)^m ⊕ (Π¹ ⋆)^n`, as an iterated biproduct. -/
def sumList (m n : ℕ) : List (SKar K (UnitSupercat K)) :=
  List.replicate m (obj K 0) ++ List.replicate n (obj K 1)

theorem dim_bsum_sumList (m n : ℕ) (q : ZMod 2) :
    dim (bsum (sumList (K := K) m n)) q = if q = 0 then m else n := by
  rw [dim_bsum, sumList, List.map_append, List.sum_append, List.map_replicate, List.map_replicate,
    List.sum_replicate, List.sum_replicate, dim_obj, dim_obj]
  rcases parity_eq_zero_or_one q with rfl | rfl <;> simp

/-- **Example 1.17(ii).** Every object of `SKar(I)` is isomorphic to `(Π⁰ ⋆)^m ⊕ (Π¹ ⋆)^n`,
where `m` and `n` are its even and odd dimensions. -/
theorem exists_iso_bsum_obj (P : SKar K (UnitSupercat K)) :
    Nonempty (P ≅ bsum (sumList (dim P 0) (dim P 1))) :=
  nonempty_iso_of_dim_eq (by rw [dim_bsum_sumList]; rfl) (by rw [dim_bsum_sumList]; rfl)

/-- **Example 1.17(ii).** `Π⁰ ⋆` and `Π¹ ⋆` are orthogonal Schur generators of `SKar(I)`. -/
theorem orthogonalSchurGenerators_obj : OrthogonalSchurGenerators K (obj K) where
  schur := isSchur_obj
  id_ne_zero := id_obj_ne_zero
  hom_eq_zero h := hom_obj_eq_zero h
  exists_iso_bsum P :=
    ⟨sumList (dim P 0) (dim P 1), fun Q hQ => by
      rcases List.mem_append.mp hQ with h | h
      · exact ⟨0, (List.eq_of_mem_replicate h)⟩
      · exact ⟨1, (List.eq_of_mem_replicate h)⟩,
      exists_iso_bsum_obj P⟩

/-! ## Semisimplicity -/

/-- **Brundan–Ellis, Example 1.17(ii).** `SKar(I)` is an abelian category. -/
instance abelian : Abelian (SKar K (UnitSupercat K)) :=
  (orthogonalSchurGenerators_obj (K := K)).abelian

/-- **Example 1.17(ii).** The objects `Π⁰ ⋆` and `Π¹ ⋆` (corresponding to `K` and `ΠK`) are
simple. -/
theorem simple_obj (a : ZMod 2) : Simple (obj K a) :=
  (orthogonalSchurGenerators_obj (K := K)).simple a

/-- **Example 1.17(ii) (semisimplicity).** Every object of `SKar(I)` is isomorphic to a finite
biproduct of simple objects. -/
theorem exists_iso_bsum_simple (P : SKar K (UnitSupercat K)) :
    ∃ L : List (SKar K (UnitSupercat K)), (∀ Q ∈ L, Simple Q) ∧ Nonempty (P ≅ bsum L) :=
  (orthogonalSchurGenerators_obj (K := K)).exists_iso_bsum_simple P

/-- **Example 1.17(ii).** Every simple object of `SKar(I)` is isomorphic to `Π⁰ ⋆` or `Π¹ ⋆`. -/
theorem exists_iso_obj_of_simple (P : SKar K (UnitSupercat K)) [Simple P] :
    ∃ a, Nonempty (P ≅ obj K a) :=
  (orthogonalSchurGenerators_obj (K := K)).exists_iso_of_simple P

/-- **Example 1.17(ii).** `Π⁰ ⋆` and `Π¹ ⋆` are not isomorphic. -/
theorem isEmpty_iso_obj_zero_one : IsEmpty (obj K 0 ≅ obj K 1) :=
  (orthogonalSchurGenerators_obj (K := K)).isEmpty_iso_of_ne (by decide)

end StringDiagrams.SKarUnit

end
