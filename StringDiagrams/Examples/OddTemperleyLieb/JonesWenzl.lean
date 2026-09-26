import StringDiagrams.Examples.OddTemperleyLieb.RightWhisker
import StringDiagrams.Examples.OddTemperleyLieb.Basis
import StringDiagrams.Examples.OddTemperleyLieb.QuantumIntegers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Super Jones–Wenzl projectors

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, proof of Theorem A.3
(first paragraph).

Over a field `k` with `q ∈ k^×` not a root of unity and `δ = -[2] = -(q - q⁻¹)`, the super
Jones–Wenzl projectors `f_n ∈ End(n)` are defined by `f_0 = 1` (and `f_1 = 1`) and
`f_{n+1} = f_n ⊗ 1 + ([n]/[n+1]) (f_n ⊗ 1) ∘ (cup ∘ cap on the last two strands) ∘ (f_n ⊗ 1)`
(`jw`; in diagrammatic order the middle factor is `cap_{n-1} ≫ cup_{n-1}` on `n + 1` strands).

* `jw_mem_evenSpan`: `f_n` is even;
* `jw_partialTrace` (the "easy but crucial inductive calculation"): closing the last strand of
  `f_{n+1}` gives `-([n+2]/[n+1]) f_n`;
* `jw_idem`: `f_n` is an idempotent;
* `jw_comp_cap`, `cup_comp_jw`: composing `f_n` on top of a cap, or below a cup, gives zero;
* `jw_comp_wR1`, `wR1_comp_jw`: `f_{n+1}` absorbs `f_n ⊗ 1`;
* `jw_ne_zero`: `f_n ≠ 0`.
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory
open Rep (delta)

variable {k : Type*} [Field k] (q : kˣ)

/-- The coefficient `[n]/[n+1]` of the recursion. -/
def jwCoeff (n : ℕ) : k := qint q n / qint q (n + 1)

local notation "δq" => delta q

/-- The super Jones–Wenzl projectors. -/
def jw : (n : ℕ) → (X k δq n ⟶ X k δq n)
  | 0 => 𝟙 _
  | 1 => 𝟙 _
  | n + 2 => wR1 k δq (jw (n + 1)) + jwCoeff q (n + 1) •
      (wR1 k δq (jw (n + 1)) ≫ cap k δq n n ≫ cup k δq n n ≫ wR1 k δq (jw (n + 1)))

theorem jw_zero : jw q 0 = 𝟙 _ := by rw [jw]

theorem jw_one : jw q 1 = 𝟙 _ := by rw [jw]

theorem jw_succ_succ (n : ℕ) : jw q (n + 2) = wR1 k δq (jw q (n + 1)) + jwCoeff q (n + 1) •
    (wR1 k δq (jw q (n + 1)) ≫ cap k δq n n ≫ cup k δq n n ≫ wR1 k δq (jw q (n + 1))) := by
  rw [jw]

/-- The projector `f_1 = 1` is `f_0 ⊗ 1` (the recursion at `n = 0`, where `[0] = 0`). -/
theorem jw_one_eq : jw q 1 = wR1 k δq (jw q 0) := by rw [jw_one, jw_zero, wR1_id]

/-- `f_n` is even. -/
theorem jw_mem_evenSpan (n : ℕ) : jw q n ∈ evenSpan k δq n n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n, ih with
  | 0, _ => rw [jw_zero]; exact id_mem_evenSpan 0
  | 1, _ => rw [jw_one]; exact id_mem_evenSpan 1
  | n + 2, ih =>
    rw [jw_succ_succ]
    have h1 := wR1_mem_evenSpan (ih (n + 1) (by omega))
    have hcc : cap k δq n n ≫ cup k δq n n ∈ evenSpan k δq (n + 2) (n + 2) := by
      have := evW_mem_evenSpan (R := k) (δ := δq) (a := n + 2) (u := [.cap n, .cup n])
        (b := n + 2) ⟨by omega, by simp⟩ (by simp) (by simp)
      simpa using this
    have h2 := comp_mem_evenSpan (comp_mem_evenSpan h1 hcc) h1
    simp only [Category.assoc] at h2
    exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2)

/-! ## The inductive properties -/

/-- `f_{m+1}` absorbs `f_m ⊗ 1`, given that `f_m` is idempotent. -/
theorem jw_absorb (m : ℕ) (hI : jw q m ≫ jw q m = jw q m) :
    jw q (m + 1) ≫ wR1 k δq (jw q m) = jw q (m + 1) ∧
      wR1 k δq (jw q m) ≫ jw q (m + 1) = jw q (m + 1) := by
  match m, hI with
  | 0, _ => simp [jw_one, jw_zero, wR1_id]
  | m + 1, hI =>
    have hw : wR1 k δq (jw q (m + 1)) ≫ wR1 k δq (jw q (m + 1)) = wR1 k δq (jw q (m + 1)) := by
      rw [← wR1_comp, hI]
    rw [jw_succ_succ]
    constructor
    · simp only [Preadditive.add_comp, Linear.smul_comp, Category.assoc, hw]
    · simp only [Preadditive.comp_add, Linear.comp_smul, ← Category.assoc, hw]

theorem delta_eq : δq = -qint q 2 := by rw [qint_two]

/-- **The partial trace.** Closing the last strand of `f_{m+1}` gives `-([m+2]/[m+1]) f_m`. -/
theorem jw_partialTrace (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (m : ℕ)
    (hI : jw q m ≫ jw q m = jw q m) :
    cup k δq m m ≫ wR1 k δq (jw q (m + 1)) ≫ cap k δq m m =
      -(qint q (m + 2) / qint q (m + 1)) • jw q m := by
  match m, hI with
  | 0, _ =>
    rw [jw_one, wR1_id, Category.id_comp, loop_at le_rfl, jw_zero, delta_eq]
    simp
  | m + 1, hI =>
    have hf := jw_mem_evenSpan q (m + 1)
    have hne : qint q (m + 2) ≠ 0 := qint_ne_zero hq (by omega)
    have t1 : cup k δq (m + 1) (m + 1) ≫ wR1 k δq (wR1 k δq (jw q (m + 1))) ≫
        cap k δq (m + 1) (m + 1) = δq • jw q (m + 1) := by
      rw [← Category.assoc, ← comp_cup_right hf, Category.assoc, loop_at le_rfl,
        Linear.comp_smul, Category.comp_id]
    have t2 : cup k δq (m + 1) (m + 1) ≫ wR1 k δq (wR1 k δq (jw q (m + 1))) ≫
        cap k δq (m + 1) m ≫ cup k δq (m + 1) m ≫ wR1 k δq (wR1 k δq (jw q (m + 1))) ≫
          cap k δq (m + 1) (m + 1) = -jw q (m + 1) := by
      rw [wR2_comp_cap_right hf, ← Category.assoc (cup k δq (m + 1) (m + 1)),
        ← comp_cup_right hf]
      simp only [Category.assoc]
      rw [← Category.assoc (cup k δq (m + 1) (m + 1)) (cap k δq (m + 1) m), zigzagA_at le_rfl,
        Category.id_comp, ← Category.assoc (cup k δq (m + 1) m) (cap k δq (m + 1) (m + 1)),
        zigzagB_at le_rfl, Preadditive.neg_comp, Category.id_comp, Preadditive.comp_neg, hI]
    have hexp : wR1 k δq (jw q (m + 2)) = wR1 k δq (wR1 k δq (jw q (m + 1))) +
        jwCoeff q (m + 1) • (wR1 k δq (wR1 k δq (jw q (m + 1))) ≫ cap k δq (m + 1) m ≫
          cup k δq (m + 1) m ≫ wR1 k δq (wR1 k δq (jw q (m + 1)))) := by
      rw [jw_succ_succ, wR1_add, wR1_smul, wR1_comp, wR1_comp, wR1_comp, wR1_cap le_rfl,
        wR1_cup le_rfl]
    rw [hexp, Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul]
    simp only [Category.assoc]
    rw [t1, t2, smul_neg, ← sub_eq_add_neg, ← sub_smul]
    congr 1
    have h2 := qint_mul_two q (m + 1)
    rw [delta_eq, jwCoeff]
    field_simp
    linear_combination -h2

/-- The top cap and the bottom cup are killed by `f_{m+2}`. -/
theorem jw_top (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (m : ℕ)
    (hT : cup k δq m m ≫ wR1 k δq (jw q (m + 1)) ≫ cap k δq m m =
      -(qint q (m + 2) / qint q (m + 1)) • jw q m)
    (hA : jw q (m + 1) ≫ wR1 k δq (jw q m) = jw q (m + 1) ∧
      wR1 k δq (jw q m) ≫ jw q (m + 1) = jw q (m + 1)) :
    jw q (m + 2) ≫ cap k δq m m = 0 ∧ cup k δq m m ≫ jw q (m + 2) = 0 := by
  have hg := jw_mem_evenSpan q m
  have hc : jwCoeff q (m + 1) * (qint q (m + 2) / qint q (m + 1)) = 1 := by
    have h1 := qint_ne_zero hq (show 0 < m + 1 by omega)
    have h2 := qint_ne_zero hq (show 0 < m + 2 by omega)
    rw [jwCoeff, show m + 1 + 1 = m + 2 from rfl]
    field_simp
  have hw : wR1 k δq (jw q (m + 1)) ≫ wR1 k δq (wR1 k δq (jw q m)) = wR1 k δq (jw q (m + 1)) := by
    rw [← wR1_comp, hA.1]
  have hw' : wR1 k δq (wR1 k δq (jw q m)) ≫ wR1 k δq (jw q (m + 1)) = wR1 k δq (jw q (m + 1)) := by
    rw [← wR1_comp, hA.2]
  rw [jw_succ_succ]
  constructor
  · rw [Preadditive.add_comp, Linear.smul_comp]
    simp only [Category.assoc]
    rw [hT, Linear.comp_smul, Linear.comp_smul, smul_smul, mul_neg, hc,
      ← wR2_comp_cap_right hg, ← Category.assoc, hw]
    simp
  · rw [Preadditive.comp_add, Linear.comp_smul]
    have e : cup k δq m m ≫ wR1 k δq (jw q (m + 1)) ≫ cap k δq m m ≫ cup k δq m m ≫
        wR1 k δq (jw q (m + 1)) = (cup k δq m m ≫ wR1 k δq (jw q (m + 1)) ≫ cap k δq m m) ≫
          cup k δq m m ≫ wR1 k δq (jw q (m + 1)) := by simp only [Category.assoc]
    rw [e, hT, Linear.smul_comp, smul_smul, mul_neg, hc, ← Category.assoc, comp_cup_right hg,
      Category.assoc, hw']
    simp

/-- Caps and cups not at the top position are killed by induction. -/
theorem jw_low (m : ℕ)
    (hC : ∀ i ≤ m, jw q (m + 2) ≫ cap k δq m i = 0 ∧ cup k δq m i ≫ jw q (m + 2) = 0)
    {i : ℕ} (hi : i ≤ m) :
    jw q (m + 3) ≫ cap k δq (m + 1) i = 0 ∧ cup k δq (m + 1) i ≫ jw q (m + 3) = 0 := by
  have e1 : wR1 k δq (jw q (m + 2)) ≫ cap k δq (m + 1) i = 0 := by
    rw [← wR1_cap hi, ← wR1_comp, (hC i hi).1, wR1_zero]
  have e2 : cup k δq (m + 1) i ≫ wR1 k δq (jw q (m + 2)) = 0 := by
    rw [← wR1_cup hi, ← wR1_comp, (hC i hi).2, wR1_zero]
  rw [jw_succ_succ]
  constructor
  · simp only [Preadditive.add_comp, Linear.smul_comp, Category.assoc, e1, Limits.comp_zero,
      smul_zero, add_zero]
  · simp only [Preadditive.comp_add, Linear.comp_smul, ← Category.assoc, e2, Limits.zero_comp,
      smul_zero, add_zero]

/-- Idempotence of `f_{m+2}` from absorption and the top cap. -/
theorem jw_idem_of (m : ℕ)
    (hA : jw q (m + 2) ≫ wR1 k δq (jw q (m + 1)) = jw q (m + 2))
    (hC : jw q (m + 2) ≫ cap k δq m m = 0) :
    jw q (m + 2) ≫ jw q (m + 2) = jw q (m + 2) := by
  nth_rewrite 2 [jw_succ_succ]
  rw [Preadditive.comp_add, Linear.comp_smul, ← Category.assoc, hA, ← Category.assoc, hC]
  simp

/-- All the properties, by induction. -/
theorem jw_spec (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (m : ℕ) :
    jw q m ≫ jw q m = jw q m ∧ jw q (m + 1) ≫ jw q (m + 1) = jw q (m + 1) ∧
      (∀ i ≤ m, jw q (m + 2) ≫ cap k δq m i = 0 ∧ cup k δq m i ≫ jw q (m + 2) = 0) := by
  induction m with
  | zero =>
    have hI0 : jw q 0 ≫ jw q 0 = jw q 0 := by rw [jw_zero, Category.comp_id]
    have hI1 : jw q 1 ≫ jw q 1 = jw q 1 := by rw [jw_one, Category.comp_id]
    refine ⟨hI0, hI1, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    exact jw_top q hq 0 (jw_partialTrace q hq 0 hI0) (jw_absorb q 0 hI0)
  | succ m ih =>
    obtain ⟨hI0, hI1, hC⟩ := ih
    have hA1 := jw_absorb q (m + 1) hI1
    have hT1 := jw_partialTrace q hq (m + 1) hI1
    have hC1 : ∀ i ≤ m + 1, jw q (m + 3) ≫ cap k δq (m + 1) i = 0 ∧
        cup k δq (m + 1) i ≫ jw q (m + 3) = 0 := by
      intro i hi
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · exact jw_low q m hC (by omega)
      · obtain rfl : i = m + 1 := by omega
        exact jw_top q hq (m + 1) hT1 hA1
    refine ⟨hI1, ?_, hC1⟩
    exact jw_idem_of q m (jw_absorb q (m + 1) hI1).1 (jw_top q hq m (jw_partialTrace q hq m hI0)
      (jw_absorb q m hI0)).1

variable {q}

/-- `f_n` is an idempotent. -/
theorem jw_idem (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (n : ℕ) : jw q n ≫ jw q n = jw q n :=
  (jw_spec q hq n).1

/-- `f_{m+2}` composed on top of any cap is zero. -/
theorem jw_comp_cap (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) {m i : ℕ} (hi : i ≤ m) :
    jw q (m + 2) ≫ cap k δq m i = 0 := ((jw_spec q hq m).2.2 i hi).1

/-- Any cup composed on top of `f_{m+2}` is zero. -/
theorem cup_comp_jw (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) {m i : ℕ} (hi : i ≤ m) :
    cup k δq m i ≫ jw q (m + 2) = 0 := ((jw_spec q hq m).2.2 i hi).2

/-- `f_{m+1}` absorbs `f_m ⊗ 1`. -/
theorem jw_comp_wR1 (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (m : ℕ) :
    jw q (m + 1) ≫ wR1 k δq (jw q m) = jw q (m + 1) := (jw_absorb q m (jw_idem hq m)).1

theorem wR1_comp_jw (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (m : ℕ) :
    wR1 k δq (jw q m) ≫ jw q (m + 1) = jw q (m + 1) := (jw_absorb q m (jw_idem hq m)).2

/-- **The partial trace** (Theorem A.3, first paragraph). -/
theorem jw_partial_trace (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (m : ℕ) :
    cup k δq m m ≫ wR1 k δq (jw q (m + 1)) ≫ cap k δq m m =
      -(qint q (m + 2) / qint q (m + 1)) • jw q m :=
  jw_partialTrace q hq m (jw_idem hq m)

/-- The identity of the unit object is non-zero. -/
theorem id_X_zero_ne_zero : 𝟙 (X k δq 0) ≠ 0 := by
  have := (basisCanon q 0).ne_zero ⟨[], isDyck_nil, rfl⟩
  rwa [basisCanon_apply, canon_zero] at this

/-- `f_n ≠ 0`. -/
theorem jw_ne_zero (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (n : ℕ) : jw q n ≠ 0 := by
  induction n with
  | zero => rw [jw_zero]; exact id_X_zero_ne_zero
  | succ n ih =>
    intro h
    have := jw_partial_trace hq n
    rw [h, wR1_zero, Limits.zero_comp, Limits.comp_zero, eq_comm, smul_eq_zero] at this
    rcases this with h1 | h1
    · rw [neg_eq_zero, div_eq_zero_iff] at h1
      rcases h1 with h1 | h1
      · exact qint_ne_zero hq (by omega) h1
      · exact qint_ne_zero hq (by omega) h1
    · exact ih h1

end StringDiagrams.OddTemperleyLieb

end
