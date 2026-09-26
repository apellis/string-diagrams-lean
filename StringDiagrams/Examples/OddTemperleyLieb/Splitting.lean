import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Splitting retracts of sums of Schur objects

A general lemma used for Theorem A.3 of J. Brundan, A. P. Ellis, *Monoidal supercategories*,
arXiv:1603.05928v3.

Let `𝒞` be a `k`-linear category (`k` a field) with binary biproducts and a zero object, which is
idempotent complete. Call an object `P` *Schur* if every endomorphism of `P` is a scalar
multiple of `1_P`. For a list `L` of objects, `bsum L` is their iterated biproduct.

* `retract_bsum_of_sum_eq_id`: an object `A` with morphisms `a_j : A → Y_j`, `b_j : Y_j → A` and
  `Σ_j a_j ≫ b_j = 1_A` is a retract of `bsum [Y_j]`.
* `iso_bsum_of_sum_eq_id`: if moreover `b_i ≫ a_j = δ_{ij}`, then `A ≅ bsum [Y_j]`.
* `iso_bsum_of_retract` (**splitting**): a retract of an iterated biproduct of Schur objects is
  isomorphic to the iterated biproduct of a sublist.

Together with the computation of the endomorphisms of the Jones–Wenzl objects, this shows that
every object of the super Karoubi envelope of `STL(δ)` is a finite direct sum of the simple
objects `(f_n)^a_a`.
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory Limits

variable {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [HasBinaryBiproducts 𝒞] [HasZeroObject 𝒞]

open ZeroObject

/-- The iterated biproduct of a list of objects. -/
def bsum : List 𝒞 → 𝒞
  | [] => 0
  | X :: l => X ⊞ bsum l

@[simp] theorem bsum_nil : bsum ([] : List 𝒞) = 0 := rfl

@[simp] theorem bsum_cons (X : 𝒞) (l : List 𝒞) : bsum (X :: l) = (X ⊞ bsum l) := rfl

/-- `bsum (l₁ ++ l₂) ≅ bsum l₁ ⊞ bsum l₂`. -/
def bsumAppendIso : (l₁ l₂ : List 𝒞) → (bsum (l₁ ++ l₂) ≅ bsum l₁ ⊞ bsum l₂)
  | [], _ => isoZeroBiprod (isZero_zero 𝒞)
  | X :: l₁, l₂ => biprod.mapIso (Iso.refl X) (bsumAppendIso l₁ l₂) ≪≫ (biprod.associator _ _ _).symm

/-- A list of objects with maps to and from `A`. -/
structure Piece (A : 𝒞) where
  /-- The object. -/
  obj : 𝒞
  /-- The map from `A`. -/
  a : A ⟶ obj
  /-- The map to `A`. -/
  b : obj ⟶ A

/-- The map `A → bsum`. -/
def toBsum {A : 𝒞} : (l : List (Piece A)) → (A ⟶ bsum (l.map Piece.obj))
  | [] => 0
  | p :: l => biprod.lift p.a (toBsum l)

/-- The map `bsum → A`. -/
def fromBsum {A : 𝒞} : (l : List (Piece A)) → (bsum (l.map Piece.obj) ⟶ A)
  | [] => 0
  | p :: l => biprod.desc p.b (fromBsum l)

theorem toBsum_comp_fromBsum {A : 𝒞} (l : List (Piece A)) :
    toBsum l ≫ fromBsum l = (l.map fun p => p.a ≫ p.b).sum := by
  induction l with
  | nil => simp [toBsum, fromBsum]
  | cons p l ih => simp [toBsum, fromBsum, ih]

/-- A resolution of the identity exhibits a retract of a sum. -/
theorem retract_bsum_of_sum_eq_id {A : 𝒞} (l : List (Piece A))
    (h : (l.map fun p => p.a ≫ p.b).sum = 𝟙 A) : toBsum l ≫ fromBsum l = 𝟙 A := by
  rw [toBsum_comp_fromBsum, h]

/-- Pairwise orthogonality of a list of pieces. -/
def Orthogonal {A : 𝒞} : List (Piece A) → Prop
  | [] => True
  | p :: l => p.b ≫ p.a = 𝟙 _ ∧ (∀ q ∈ l, p.b ≫ q.a = 0 ∧ q.b ≫ p.a = 0) ∧ Orthogonal l

theorem fromBsum_comp_toBsum {A : 𝒞} (l : List (Piece A)) (h : Orthogonal l) :
    fromBsum l ≫ toBsum l = 𝟙 _ := by
  induction l with
  | nil => exact (isZero_zero 𝒞).eq_of_src _ _
  | cons p l ih =>
    obtain ⟨h1, h2, h3⟩ := h
    have e1 : p.b ≫ toBsum l = 0 := by
      clear ih h3
      induction l with
      | nil => simp [toBsum]
      | cons q l ih' =>
        refine biprod.hom_ext _ _ ?_ ?_
        · simp [toBsum, (h2 q (by simp)).1]
        · simpa [toBsum] using ih' fun r hr => h2 r (by simp [hr])
    have e2 : fromBsum l ≫ p.a = 0 := by
      clear ih h3 e1
      induction l with
      | nil => simp [fromBsum]
      | cons q l ih' =>
        refine biprod.hom_ext' _ _ ?_ ?_
        · simp [fromBsum, (h2 q (by simp)).2]
        · simpa [fromBsum] using ih' fun r hr => h2 r (by simp [hr])
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_
    · simp [toBsum, fromBsum, h1]
    · simp [toBsum, fromBsum, e1]
    · simp [toBsum, fromBsum, e2]
    · simp [toBsum, fromBsum, ih h3]

/-- A resolution of the identity by orthogonal pieces exhibits an isomorphism with a sum. -/
def isoBsum {A : 𝒞} (l : List (Piece A)) (h : (l.map fun p => p.a ≫ p.b).sum = 𝟙 A)
    (ho : Orthogonal l) : A ≅ bsum (l.map Piece.obj) where
  hom := toBsum l
  inv := fromBsum l
  hom_inv_id := retract_bsum_of_sum_eq_id l h
  inv_hom_id := fromBsum_comp_toBsum l ho

/-! ## Splitting -/

variable {k : Type*} [Field k] [Linear k 𝒞] [IsIdempotentComplete 𝒞]

/-- An object whose endomorphisms are scalars. -/
def IsSchur (P : 𝒞) : Prop := ∀ f : P ⟶ P, ∃ c : k, f = c • 𝟙 P

/-- **Splitting.** A retract of an iterated biproduct of Schur objects is isomorphic to the
iterated biproduct of a sublist. -/
theorem iso_bsum_of_retract (L : List 𝒞) (hL : ∀ P ∈ L, IsSchur (k := k) P) :
    ∀ (Z : 𝒞) (σ : Z ⟶ bsum L) (τ : bsum L ⟶ Z), σ ≫ τ = 𝟙 Z →
      ∃ L' : List 𝒞, L'.Sublist L ∧ Nonempty (Z ≅ bsum L') := by
  induction L with
  | nil =>
    intro Z σ τ h
    refine ⟨[], List.Sublist.slnil, ⟨?_⟩⟩
    have hZ : IsZero Z := by
      rw [IsZero.iff_id_eq_zero, ← h, (isZero_zero 𝒞).eq_of_tgt σ 0, Limits.zero_comp]
    exact hZ.isoZero
  | cons P L ih =>
    intro Z σ τ h
    have hP := hL P (by simp)
    obtain ⟨c, hc⟩ := hP (biprod.inl ≫ τ ≫ σ ≫ biprod.fst)
    by_cases hc0 : c = 0
    · -- `P` does not occur: `Z` is a retract of the rest
      set x : Z ⟶ Z := σ ≫ biprod.fst ≫ biprod.inl ≫ τ
      have hx : x ≫ x = 0 := by
        simp only [x, Category.assoc]
        rw [← Category.assoc biprod.inl τ, ← Category.assoc (biprod.inl ≫ τ) σ,
          ← Category.assoc ((biprod.inl ≫ τ) ≫ σ), show ((biprod.inl ≫ τ) ≫ σ) ≫ biprod.fst =
            biprod.inl ≫ τ ≫ σ ≫ biprod.fst by simp only [Category.assoc], hc, hc0]
        simp
      obtain ⟨L', hL', ⟨e⟩⟩ := ih (fun Q hQ => hL Q (by simp [hQ])) Z (σ ≫ biprod.snd)
        (biprod.inr ≫ τ ≫ (𝟙 Z + x)) (by
          have t : biprod.snd ≫ biprod.inr = 𝟙 (P ⊞ bsum L) - biprod.fst ≫ biprod.inl := by
            rw [← biprod.total]; abel
          have hστx : σ ≫ τ ≫ x = x := by rw [← Category.assoc, h, Category.id_comp]
          have e2 : σ ≫ biprod.fst ≫ biprod.inl ≫ τ ≫ x = x ≫ x := by simp [x]
          have hx' : σ ≫ biprod.fst ≫ biprod.inl ≫ τ = x := rfl
          simp only [Category.assoc]
          rw [← Category.assoc biprod.snd biprod.inr, t]
          simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
            Preadditive.comp_add, Category.comp_id, Category.assoc]
          rw [h, hστx, e2, hx', hx]
          abel)
      exact ⟨L', hL'.cons P, ⟨e⟩⟩
    · -- `P` splits off
      set s : P ⟶ Z := biprod.inl ≫ τ
      set r : Z ⟶ P := c⁻¹ • (σ ≫ biprod.fst)
      have hsr : s ≫ r = 𝟙 P := by
        simp only [s, r, Linear.comp_smul, Category.assoc]
        rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      have hq : (𝟙 Z - r ≫ s) ≫ (𝟙 Z - r ≫ s) = 𝟙 Z - r ≫ s := by
        simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
          Category.comp_id, Category.assoc]
        rw [← Category.assoc s r, hsr, Category.id_comp]
        abel
      obtain ⟨Z', i', e', hie, hei⟩ := IsIdempotentComplete.idempotents_split Z _ hq
      have hse : s ≫ e' = 0 := by
        have : s ≫ e' ≫ i' = 0 := by
          rw [hei, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hsr,
            Category.id_comp, sub_self]
        rw [← Category.comp_id (s ≫ e'), ← hie]
        simp only [Category.assoc] at this ⊢
        rw [← Category.assoc e' i' e', ← Category.assoc s (e' ≫ i') e', this, Limits.zero_comp]
      have hir : i' ≫ r = 0 := by
        have : i' ≫ e' ≫ i' ≫ r = 0 := by
          rw [← Category.assoc e' i' r, hei, Preadditive.sub_comp, Category.id_comp,
            Category.assoc, hsr, Category.comp_id, sub_self, Limits.comp_zero]
        rwa [← Category.assoc i' e', hie, Category.id_comp] at this
      -- `Z'` is a retract of the rest
      obtain ⟨L', hL', ⟨e⟩⟩ := ih (fun Q hQ => hL Q (by simp [hQ])) Z'
        (i' ≫ σ ≫ biprod.snd) (biprod.inr ≫ τ ≫ e') (by
          have t : biprod.snd ≫ biprod.inr = 𝟙 (P ⊞ bsum L) - biprod.fst ≫ biprod.inl := by
            rw [← biprod.total]; abel
          have hστ' : σ ≫ τ ≫ e' = e' := by rw [← Category.assoc, h, Category.id_comp]
          have e3 : σ ≫ biprod.fst ≫ biprod.inl ≫ τ ≫ e' = 0 := by
            have : (biprod.inl : P ⟶ P ⊞ bsum L) ≫ τ ≫ e' = 0 := by
              rw [← Category.assoc]; exact hse
            rw [this, Limits.comp_zero, Limits.comp_zero]
          simp only [Category.assoc]
          rw [← Category.assoc biprod.snd biprod.inr, t]
          simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
            Category.assoc]
          rw [hστ', e3, hie, Limits.comp_zero, sub_zero])
      refine ⟨P :: L', hL'.cons₂ P, ⟨?_⟩⟩
      have hmid : biprod.desc s i' ≫ biprod.lift r e' = 𝟙 (P ⊞ Z') := by
        refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_
        · simp [hsr]
        · simp [hse]
        · simp [hir]
        · simp [hie]
      have hmid' : biprod.lift r e' ≫ biprod.desc s i' = 𝟙 Z := by
        rw [biprod.lift_desc, hei]; abel
      let e₁ : Z ≅ P ⊞ Z' := ⟨biprod.lift r e', biprod.desc s i', hmid', hmid⟩
      exact e₁ ≪≫ biprod.mapIso (Iso.refl P) e

end StringDiagrams.OddTemperleyLieb

end
