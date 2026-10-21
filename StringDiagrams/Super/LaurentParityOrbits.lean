/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.LaurentBasis

/-!
# Parity-compatible representatives of grading-shift orbits

For the corrected first preliminary fact of BE2 §11, parity acts on the
integer-shift orbits of indecomposables. A fixed orbit cannot carry a nonzero
integer twist: squaring parity would give a nonzero shift stabilizer. Thus one
can choose representatives compatibly with parity, without introducing powers
of q in its action on the Laurent basis.
-/

noncomputable section
namespace StringDiagrams.LaurentBasis
variable {ι : Type*} [AddAction ℤ ι]
  (σ : ι → ι) (hσ : Function.Involutive σ)
  (hc : ∀ (n : ℤ) (i : ι), σ (n +ᵥ i) = n +ᵥ σ i)
  (hf : ∀ (i : ι) (n : ℤ), n +ᵥ i = i → n = 0)

include hσ hc hf in
/-- An involution commuting with a free integer action has no twisted fixed points. -/
theorem parity_shift_rigid (i : ι) (n : ℤ) (h : σ i = n +ᵥ i) : n = 0 := by
  have hn : (n + n) +ᵥ i = i := by
    rw [add_vadd, ← h, ← hc, ← h, hσ]
  have := hf i (n + n) hn
  omega

/-- The induced parity involution on integer-shift orbits. -/
def orbitParity : Orbit (ι := ι) → Orbit (ι := ι) :=
  Quotient.map σ (by
    rintro i j ⟨n, hn⟩
    exact ⟨n, (hc n j).symm.trans (congrArg σ hn)⟩)

include hσ in
/-- Parity still squares to the identity after quotienting integer shifts. -/
theorem orbitParity_involutive : Function.Involutive (orbitParity σ hc) := by
  intro o
  induction o using Quotient.inductionOn with
  | h i => change Quotient.mk _ (σ (σ i)) = Quotient.mk _ i; rw [hσ]

include hσ hf in
/-- A parity-fixed shift orbit consists of parity-fixed representatives. -/
theorem orbitParity_fixed_iff (i : ι) :
    orbitParity σ hc (Quotient.mk _ i) = Quotient.mk _ i ↔ σ i = i := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Quotient.exact h
    have hz := parity_shift_rigid σ hσ hc hf i n hn.symm
    simpa only [hz, zero_vadd] using hn.symm
  · intro h
    change Quotient.mk _ (σ i) = Quotient.mk _ i
    rw [h]

section Ordered
variable [LinearOrder (Orbit (ι := ι))]

/-- Choose the representative on the smaller parity orbit; transport it on its partner. -/
def paritySection (o : Orbit (ι := ι)) : ι :=
  if orbitParity σ hc o < o then σ (orbitParity σ hc o).out else o.out

include hσ in
/-- The chosen representative has the prescribed integer-shift orbit. -/
theorem paritySection_spec (o : Orbit (ι := ι)) :
    Quotient.mk (AddAction.orbitRel ℤ ι) (paritySection σ hc o) = o := by
  classical
  unfold paritySection
  split_ifs
  · change orbitParity σ hc (Quotient.mk _ (orbitParity σ hc o).out) = o
    rw [Quotient.out_eq, orbitParity_involutive σ hσ hc]
  · exact Quotient.out_eq o

include hσ hf in
/-- The section is equivariant for parity, including fixed orbits. -/
theorem paritySection_parity (o : Orbit (ι := ι)) :
    paritySection σ hc (orbitParity σ hc o) = σ (paritySection σ hc o) := by
  classical
  have hs := orbitParity_involutive σ hσ hc
  rcases lt_trichotomy o (orbitParity σ hc o) with h | h | h
  · simp only [paritySection, hs o]
    rw [ite_eq_left h, ite_eq_right (not_lt_of_gt h)]
  · have hfix : σ o.out = o.out := by
      apply (orbitParity_fixed_iff σ hσ hc hf o.out).1
      rw [Quotient.out_eq, ← h]
    simp only [paritySection, ← h, lt_self_iff_false, ↓reduceIte, hfix]
  · simp only [paritySection, hs o]
    rw [ite_eq_right (not_lt_of_gt h), ite_eq_left h, hσ]

end Ordered
end StringDiagrams.LaurentBasis
