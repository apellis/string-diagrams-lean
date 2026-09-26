import StringDiagrams.Examples.OddTemperleyLieb.Canonical
import StringDiagrams.Examples.OddTemperleyLieb.Representation
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Linear independence of the canonical cup diagrams

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, proof of
Theorem A.2 (linear independence).

Apply the representation `G` of Lemma A.1 (`Rep.rep q`) to the canonical cup diagram of a
crossingless matching `s` of `N` points and evaluate at `1`: this gives a vector
`v_s ∈ V^{⊗N}`, whose coefficient at the basis vector `v_t` (`t` a word) is nonzero only if
`t ≤ s` in the dominance order of Dyck sequences, and whose coefficient at `v_s` itself is a
unit (`canonVec_triangular`; it is `±(-q)^{N/2}`). The paper applies `G` to caps and evaluates
on `v_t`; using cups and reading coefficients is the same triangularity argument in the dual
form. Linear independence follows (`linearIndependent_canon`), for any commutative ring `R` and
any unit `q`, with `δ = -(q - q⁻¹)`.

With the spanning result `span_canon` this gives the basis of `Hom(0, N)` indexed by the
crossingless matchings of `N` points (`basisCanon`).
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory
open TemperleyLieb.Rep (Word ins del ext ext_apply_of_length length_del length_ins)
open Rep (rep delta psign cupCoeff rep_cup_apply)

variable {R : Type*} [CommRing R] (q : Rˣ)

/-- The vector `v_s = G(canon s)(1) ∈ V^{⊗n}`, as a function on words. -/
def canonVec (n : ℕ) (w : List (Fin 2)) : Word (strands n).word.length → R :=
  ((rep R q).map (canon R (delta q) n w)).hom (fun _ => 1)

theorem canonVec_zero (w : List (Fin 2)) (t : Word (strands 0).word.length) :
    canonVec q 0 w t = 1 := by
  simp [canonVec, canon_zero]

theorem canonVec_succ_succ {n : ℕ} (w : List (Fin 2)) (h : firstPair w ≤ n)
    (t : Word (strands (n + 2)).word.length) :
    canonVec q (n + 2) w t = psign R (firstPair w) t.1 *
      (cupCoeff R q (t.1.getD (firstPair w) 0) (t.1.getD (firstPair w + 1) 0) *
        ext R _ (canonVec q n (del (firstPair w) w)) (del (firstPair w) t.1)) := by
  rw [canonVec, canon_succ_succ, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    rep_cup_apply h]
  rfl

theorem isUnit_psign (p : ℕ) (w : List (Fin 2)) : IsUnit (psign R p w) :=
  (isUnit_neg_one (α := R)).pow _

theorem step_add_of_cupCoeff_ne_zero {a b : Fin 2} (h : cupCoeff R q a b ≠ 0) :
    step a + step b = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all

/-- **Triangularity.** The coefficient of `v_t` in `v_s` vanishes unless `t ≤ s`, and the
coefficient of `v_s` is a unit. -/
theorem canonVec_triangular (n : ℕ) : ∀ (w : List (Fin 2)), IsDyck w →
    ∀ (hl : w.length = (strands n).word.length),
    (∀ t : Word (strands n).word.length, canonVec q n w t ≠ 0 → dle t.1 w) ∧
      IsUnit (canonVec q n w ⟨w, hl⟩) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hl
  simp only [strands_word_length] at hl
  rcases eq_or_ne w [] with rfl | hne
  · obtain rfl : n = 0 := by simpa using hl.symm
    refine ⟨fun t _ => ?_, by rw [canonVec_zero]; exact isUnit_one⟩
    obtain ⟨t, ht⟩ := t
    obtain rfl : t = [] := by simpa [strands] using ht
    exact dle_refl _
  obtain ⟨r, hr⟩ := dyck_decomp hw hne
  generalize hp : firstPair w = p at hr
  have hlr : p + 2 + r.length = n := by rw [← hl, hr]; simp; omega
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨p + r.length, by omega⟩
  have hw0 : IsDyck (List.replicate p 0 ++ r) := by
    have := hw.del_pair (p := p) (by omega)
      (by rw [hr]; simp [getD_rep_add p 0 0 (0 :: 1 :: r)])
      (by rw [hr]; simp [getD_rep_add p 1 0 (0 :: 1 :: r)])
    rwa [hr, del_rep] at this
  have hd : del p w = List.replicate p 0 ++ r := by rw [hr, del_rep]
  have hl0 : (List.replicate p (0 : Fin 2) ++ r).length = (strands n).word.length := by
    simp; omega
  obtain ⟨ih1, ih2⟩ := ih n (by omega) _ hw0 hl0
  have hins : w = ins p 0 1 (List.replicate p 0 ++ r) := by rw [hr, ins_rep]
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [canonVec_succ_succ q w (by omega), hp, hd] at ht
    obtain ⟨t, htl⟩ := t
    dsimp only at ht ⊢
    simp only [strands_word_length] at htl
    have h1 : cupCoeff R q (t.getD p 0) (t.getD (p + 1) 0) ≠ 0 := fun h => ht (by
      rw [h, zero_mul, mul_zero])
    have h2 : ext R _ (canonVec q n (List.replicate p 0 ++ r)) (del p t) ≠ 0 :=
      fun h => ht (by rw [h, mul_zero, mul_zero])
    have hdl : (del p t).length = (strands n).word.length := by
      have := length_del (p := p) (w := t) (by omega); simp; omega
    rw [ext_apply_of_length R _ hdl] at h2
    have := ih1 _ h2
    rw [← ins_getD_del (p := p) (w := t) (by omega), hins]
    exact dle_ins this (by rw [hdl]; simp; omega) (by simp)
      (step_add_of_cupCoeff_ne_zero q h1)
  · rw [canonVec_succ_succ q w (by omega)]
    dsimp only
    rw [hp, hd]
    have g0 : w.getD p 0 = 0 := by rw [hr]; simp [getD_rep_add p 0 0 (0 :: 1 :: r)]
    have g1 : w.getD (p + 1) 0 = 1 := by rw [hr]; simp [getD_rep_add p 1 0 (0 :: 1 :: r)]
    rw [g0, g1, Rep.cupCoeff_01, ext_apply_of_length R _ hl0]
    exact (isUnit_psign p w).mul ((Units.isUnit q).neg.mul ih2)

/-- A potential for the dominance order: the sum of the partial sums. -/
def potential (N : ℕ) (w : List (Fin 2)) : ℤ := ∑ k ∈ Finset.range (N + 1), bal (w.take k)

theorem eq_of_dle_of_potential {t w : List (Fin 2)} (h : dle t w) (hl : t.length = w.length)
    (hp : potential w.length t = potential w.length w) : t = w := by
  refine dle_antisymm h (fun k => ?_) hl
  have hk : ∀ k ∈ Finset.range (w.length + 1), bal (t.take k) = bal (w.take k) :=
    (Finset.sum_eq_sum_iff_of_le (fun k _ => h k)).mp hp
  rcases le_or_lt k w.length with hkl | hkl
  · exact (hk k (Finset.mem_range.mpr (by omega))).ge
  · have := hk w.length (Finset.mem_range.mpr (by omega))
    rw [List.take_of_length_le (by omega : w.length ≤ k),
      List.take_of_length_le (by omega : t.length ≤ k)]
    rw [List.take_of_length_le (by omega : t.length ≤ w.length), List.take_length] at this
    exact this.ge

theorem potential_le_of_dle {t w : List (Fin 2)} (h : dle t w) (N : ℕ) :
    potential N t ≤ potential N w :=
  Finset.sum_le_sum fun k _ => h k

/-- **Linear independence (Theorem A.2 for `m = 0`).** For any unit `q` of a commutative ring
`R`, the canonical cup diagrams of the crossingless matchings of `N` points are linearly
independent in `Hom(0, N)` of `STL(δ)`, `δ = -(q - q⁻¹)`. -/
theorem linearIndependent_canon (N : ℕ) :
    LinearIndependent R (fun w : DyckSeq N => canon R (delta q) N w.1) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have hne : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, by simp [hi, hgi]⟩
  obtain ⟨w, hw, hmax⟩ := (s.filter fun j => g j ≠ 0).exists_max_image
    (fun j => potential N j.1) hne
  simp only [Finset.mem_filter] at hw
  have hl : w.1.length = (strands N).word.length := by simp [w.2.2]
  let evl : (X R (delta q) 0 ⟶ X R (delta q) N) →ₗ[R] R :=
    { toFun := fun x => ((rep R q).map x).hom (fun _ => 1) ⟨w.1, hl⟩
      map_add' := fun x y => by simp [Functor.map_add]; rfl
      map_smul' := fun r x => by simp [Functor.map_smul]; rfl }
  have key := congrArg evl hsum
  rw [map_sum, map_zero] at key
  simp only [map_smul, smul_eq_mul] at key
  rw [Finset.sum_eq_single_of_mem w hw.1] at key
  · have hu := (canonVec_triangular q N w.1 w.2.1 hl).2
    exact hw.2 ((hu.mul_left_eq_zero).mp key)
  · intro j hj hjw
    by_cases hgj : g j = 0
    · rw [hgj, zero_mul]
    · have hv : evl (canon R (delta q) N j.1) = canonVec q N j.1 ⟨w.1, hl⟩ := rfl
      rw [hv]
      refine by_contra fun hne' => ?_
      have hd := (canonVec_triangular q N j.1 j.2.1 (by simp [j.2.2])).1 _
        (right_ne_zero_of_mul hne')
      have h1 := hmax j (by simp [hj, hgj])
      have h2 := potential_le_of_dle hd N
      have heq : w.1 = j.1 := eq_of_dle_of_potential hd (by rw [w.2.2, j.2.2])
        (by rw [j.2.2]; simp only at h1 h2; omega)
      exact hjw (Subtype.ext heq).symm

/-- **Theorem A.2 for `m = 0`.** The canonical cup diagrams of the crossingless matchings of `N`
points form a basis of `Hom(0, N)` in `STL(δ)`, `δ = -(q - q⁻¹)`, for any unit `q` of a
commutative ring. -/
def basisCanon (N : ℕ) : Basis (DyckSeq N) R (X R (delta q) 0 ⟶ X R (delta q) N) :=
  Basis.mk (linearIndependent_canon q N) (by rw [span_canon])

@[simp] theorem basisCanon_apply (N : ℕ) (w : DyckSeq N) :
    basisCanon q N w = canon R (delta q) N w.1 := Basis.mk_apply _ _ _

end StringDiagrams.OddTemperleyLieb

end
