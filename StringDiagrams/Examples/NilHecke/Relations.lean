import StringDiagrams.Examples.NilHecke.Basic

/-!
# The nilHecke relations at symbolic width

For every width `n` and every admissible position, the dots `x n i` and crossings `ψ n i`
of `NH R` satisfy the nilHecke relations (KL I, arXiv:0803.4121v2, §2.2 Example 3, p. 10;
indices shifted to start at `0`, products are composition of operators):

* `ψ_mul_ψ`: `ψ_i ψ_i = 0`;
* `ψ_braid`: `ψ_i ψ_{i+1} ψ_i = ψ_{i+1} ψ_i ψ_{i+1}`;
* `x_mul_ψ_sub_ψ_mul_x`: `x_i ψ_i - ψ_i x_{i+1} = 1`;
* `ψ_mul_x_sub_x_mul_ψ`: `ψ_i x_i - x_{i+1} ψ_i = 1`;
* `x_mul_x_comm`, `x_mul_ψ_comm`, `ψ_mul_ψ_comm`: far commutativity.

Each is obtained by whiskering a defining relation (or an instance of the interchange law)
to the symbolic position; no case analysis on `n` is involved.
-/

noncomputable section

namespace StringDiagrams.NilHecke

open CategoryTheory

variable (R : Type*) [CommRing R]

/-- Words in the single colour are determined by their length. -/
@[simp] theorem word_eq_iff {l₁ l₂ : List sig.Colour} : l₁ = l₂ ↔ l₁.length = l₂.length :=
  ⟨congrArg List.length, list_punit_ext⟩

/-- `i` strands, used to whisker on the left. -/
def shift (i : ℕ) : Obj sig := ⟨(), List.replicate i ()⟩

theorem whisker_strands {w i n : ℕ} (h : i + w ≤ n) :
    (strands w).whisker (shift i) (List.replicate (n - i - w) ()) = strands n :=
  obj_ext (by simp [strands, shift, Obj.whisker]; omega)

/-- A defining relation, transported to position `i` in width `n`. -/
theorem relation_at (r : Rel) {n i : ℕ} (h : i + r.width ≤ n) :
    (pres R).lin (LinDiagram.cast (LinDiagram.whisker (relation R r) (shift i)
      (List.replicate (n - i - r.width) ()) (Obj.whiskerOK_of_subsingleton _ _ _))
      (whisker_strands h) (whisker_strands h)) = 0 :=
  (pres R).lin_rel_cast r (shift i) _ _ _ _

/-- The interchange law for generators `g` (at position `i`) and `h` (at position `j`,
to the right of `g`) in width `n`. -/
theorem interchange_at (g h : Gen) {n i j : ℕ} (hij : i + g.arity ≤ j) (hn : j + h.arity ≤ n) :
    (pres R).diag (dlay (n := n) (i := i) (g := g) (by omega)) ≫
        (pres R).diag (dlay (n := n) (i := j) (g := h) hn) =
      (pres R).diag (dlay (n := n) (i := j) (g := h) hn) ≫
        (pres R).diag (dlay (n := n) (i := i) (g := g) (by omega)) := by
  let x : InterchangeData sig := ⟨(), g, List.replicate (j - i - g.arity) (), h⟩
  have hx : x.Valid := InterchangeData.valid_of_subsingleton x
  have hd : x.dom.whisker (shift i) (List.replicate (n - j - h.arity) ()) = strands n :=
    obj_ext (by simp [x, InterchangeData.dom, shift, strands, sig]; omega)
  have hc : x.cod.whisker (shift i) (List.replicate (n - j - h.arity) ()) = strands n :=
    obj_ext (by simp [x, InterchangeData.cod, shift, strands, sig]; omega)
  have key := (pres R).diag_interchange x hx (shift i) _
    (Obj.whiskerOK_of_subsingleton _ _ _) hd hc
  have hs : ((x.sign : ℤ) : R) = 1 := by simp [x, InterchangeData.sign, sig]
  rw [hs, one_smul] at key
  rw [← Presentation.diag_comp, ← Presentation.diag_comp]
  convert key using 1 <;> apply Presentation.diag_eq_of_layers_eq <;>
    simp [x, dlay, lay, shift, Layer.whisker, InterchangeData.ghDiagram,
      InterchangeData.hgDiagram, InterchangeData.gh₁, InterchangeData.gh₂,
      InterchangeData.hg₁, InterchangeData.hg₂, sig] <;> omega

theorem x_def {n i : ℕ} (h : i < n) : x R n i = (pres R).diag (dlay (g := .dot) h) := dif_pos h

theorem ψ_def {n i : ℕ} (h : i + 1 < n) : ψ R n i = (pres R).diag (dlay (g := .cross) h) :=
  dif_pos h

theorem x_of_le {n i : ℕ} (h : n ≤ i) : x R n i = 0 := dif_neg (by omega)

theorem ψ_of_le {n i : ℕ} (h : n ≤ i + 1) : ψ R n i = 0 := dif_neg (by omega)

/-! ## Defining relations -/

theorem ψ_mul_ψ (n i : ℕ) : ψ R n i * ψ R n i = 0 := by
  by_cases h : i + 1 < n
  · have key := relation_at R .crossSq (n := n) (i := i) (by simp [Rel.width]; omega)
    rw [show relation R .crossSq = LinDiagram.of _ from rfl, LinDiagram.whisker_of,
      LinDiagram.cast_of, Presentation.lin_of] at key
    rw [ψ_def R h, End.mul_def, ← Presentation.diag_comp, ← key]
    apply Presentation.diag_eq_of_layers_eq
    simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width]
  · rw [ψ_of_le R (by omega), mul_zero]

theorem ψ_braid (n i : ℕ) :
    ψ R n i * ψ R n (i + 1) * ψ R n i = ψ R n (i + 1) * ψ R n i * ψ R n (i + 1) := by
  by_cases h : i + 2 < n
  · have key := relation_at R .braid (n := n) (i := i) (by simp [Rel.width]; omega)
    rw [show relation R .braid = LinDiagram.of _ - LinDiagram.of _ from rfl,
      LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.whisker_of, LinDiagram.cast_sub,
      LinDiagram.cast_of, LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_of,
      Presentation.lin_of, sub_eq_zero] at key
    rw [ψ_def R (show i + 1 < n by omega), ψ_def R h]
    simp only [End.mul_def, ← Presentation.diag_comp]
    convert key using 1 <;> apply Presentation.diag_eq_of_layers_eq <;>
      simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width] <;> omega
  · by_cases h' : i + 1 < n
    · rw [ψ_of_le R (n := n) (i := i + 1) (by omega)]; simp
    · rw [ψ_of_le R (n := n) (i := i) (by omega)]; simp

theorem x_mul_ψ_sub_ψ_mul_x {n i : ℕ} (h : i + 1 < n) :
    x R n i * ψ R n i - ψ R n i * x R n (i + 1) = 1 := by
  have key := relation_at R .slideA (n := n) (i := i) (by simp [Rel.width]; omega)
  rw [show relation R .slideA = LinDiagram.of _ - LinDiagram.of _ - LinDiagram.of _ from rfl,
    LinDiagram.whisker_sub, LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.whisker_of,
    LinDiagram.whisker_of, LinDiagram.cast_sub, LinDiagram.cast_sub, LinDiagram.cast_of,
    LinDiagram.cast_of, LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_sub,
    Presentation.lin_of, Presentation.lin_of, Presentation.lin_of, sub_eq_zero] at key
  rw [x_def R (show i < n by omega), x_def R h, ψ_def R h]
  simp only [End.mul_def, ← Presentation.diag_comp, End.one_def]
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1 <;> apply Presentation.diag_eq_of_layers_eq <;>
      simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width]
    all_goals omega
  · refine Eq.trans ?_ ((pres R).diag_id _)
    apply Presentation.diag_eq_of_layers_eq
    simp

theorem ψ_mul_x_sub_x_mul_ψ {n i : ℕ} (h : i + 1 < n) :
    ψ R n i * x R n i - x R n (i + 1) * ψ R n i = 1 := by
  have key := relation_at R .slideB (n := n) (i := i) (by simp [Rel.width]; omega)
  rw [show relation R .slideB = LinDiagram.of _ - LinDiagram.of _ - LinDiagram.of _ from rfl,
    LinDiagram.whisker_sub, LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.whisker_of,
    LinDiagram.whisker_of, LinDiagram.cast_sub, LinDiagram.cast_sub, LinDiagram.cast_of,
    LinDiagram.cast_of, LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_sub,
    Presentation.lin_of, Presentation.lin_of, Presentation.lin_of, sub_eq_zero] at key
  rw [x_def R (show i < n by omega), x_def R h, ψ_def R h]
  simp only [End.mul_def, ← Presentation.diag_comp, End.one_def]
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1 <;> apply Presentation.diag_eq_of_layers_eq <;>
      simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width]
    all_goals omega
  · refine Eq.trans ?_ ((pres R).diag_id _)
    apply Presentation.diag_eq_of_layers_eq
    simp

/-! ## Far commutativity -/

theorem x_mul_x_comm (n i j : ℕ) : x R n i * x R n j = x R n j * x R n i := by
  wlog hij : i < j generalizing i j
  · rcases Nat.lt_or_ge j i with h | h
    · exact (this j i h).symm
    · rw [show i = j by omega]
  by_cases hj : j < n
  · rw [x_def R (show i < n by omega), x_def R hj, End.mul_def, End.mul_def]
    exact (interchange_at R .dot .dot (n := n) hij hj).symm
  · rw [x_of_le R (show n ≤ j by omega)]; simp

theorem x_mul_ψ_comm {n i j : ℕ} (h : j ≠ i) (h' : j ≠ i + 1) :
    x R n j * ψ R n i = ψ R n i * x R n j := by
  rcases Nat.lt_or_ge j i with hji | hji
  · by_cases hi : i + 1 < n
    · rw [x_def R (show j < n by omega), ψ_def R hi, End.mul_def, End.mul_def]
      exact (interchange_at R .dot .cross (n := n) hji hi).symm
    · rw [ψ_of_le R (show n ≤ i + 1 by omega)]; simp
  · by_cases hj : j < n
    · rw [x_def R hj, ψ_def R (show i + 1 < n by omega), End.mul_def, End.mul_def]
      exact interchange_at R .cross .dot (n := n) (show i + 2 ≤ j by omega) hj
    · rw [x_of_le R (show n ≤ j by omega)]; simp

theorem ψ_mul_ψ_comm {n i j : ℕ} (h : i + 1 < j) : ψ R n i * ψ R n j = ψ R n j * ψ R n i := by
  by_cases hj : j + 1 < n
  · rw [ψ_def R (show i + 1 < n by omega), ψ_def R hj, End.mul_def, End.mul_def]
    exact (interchange_at R .cross .cross (n := n) (show i + 2 ≤ j by omega) hj).symm
  · rw [ψ_of_le R (show n ≤ j + 1 by omega)]; simp

end StringDiagrams.NilHecke

end
