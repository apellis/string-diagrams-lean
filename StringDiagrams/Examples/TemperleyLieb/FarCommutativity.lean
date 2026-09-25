import StringDiagrams.Examples.TemperleyLieb
import StringDiagrams.Interchange

/-!
# Far commutativity in the Temperley–Lieb algebras

For every width, the Temperley–Lieb generators commute when they are at least two strands
apart: `e_i e_j = e_j e_i` for `i + 2 ≤ j` (`e_mul_e_comm`), with no range hypothesis since
`e m i = 0` for `i > m`.

The proof uses the interchange law for the width-changing generators. For a cup or a cap `g`
to the left of a cup or a cap `h`, the two orders of the layers agree
(`cap_cap_interchange`, `cup_cup_interchange`, `cap_cup_interchange`, `cup_cap_interchange`),
where the position of `h` shifts by `2` when it passes below a cap or above a cup on its left.
Each is an instance of `Presentation.diag_swap_layers`, transported to symbolic positions and
widths by `diag_eq_of_swap`.
-/

noncomputable section

namespace StringDiagrams.TemperleyLieb

open CategoryTheory

variable {R : Type*} [CommRing R] (δ : R)

/-- The interchange law of `pres R δ` for two diagrams with the layers of the two sides of an
interchange: `L` (on the left) below `M` (on the right), and `M` below `L`. -/
theorem diag_eq_of_swap {a b : Obj sig} {f f' : a ⟶ b} (L M : Layer sig)
    (hf : Diagram.layers f = [L.wr M.dom.word, M.wl L.cod])
    (hf' : Diagram.layers f' = [M.wl L.dom, L.wr M.cod.word]) :
    (pres R δ).diag f = (pres R δ).diag f' := by
  have hc := Diagram.chain f
  rw [hf] at hc
  obtain ⟨-, ha, -, -, hb⟩ := hc
  rw [Layer.wr_dom] at ha
  rw [chain_nil, Layer.wl_cod] at hb
  subst ha hb
  have key := (pres R δ).diag_swap_layers L M
  simp only [Diagram.oddCountList, sig, Bool.false_eq_true, decide_false, List.filter_cons,
    List.filter_nil, ite_false, List.length_nil, mul_zero, pow_zero, one_smul] at key
  exact (Presentation.diag_eq_of_layers_eq _ (by rw [hf]; rfl)).trans
    (key.trans (Presentation.diag_eq_of_layers_eq _ (by rw [hf']; rfl)))

/-- A layer with `l` strands on the left and `r` on the right. -/
abbrev gl (l : ℕ) (g : Gen) (r : ℕ) : Layer sig := ⟨(), List.replicate l (), g, List.replicate r ()⟩

/-- Two caps: `cap_j` then `cap_i` equals `cap_i` then `cap_{j-2}`, for `i + 2 ≤ j`. -/
@[reassoc]
theorem cap_cap_interchange {n i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n + 2) :
    (pres R δ).diag (dcap (m := n + 2) (i := j) hj) ≫ (pres R δ).diag (dcap (m := n) (i := i) (by omega)) =
      (pres R δ).diag (dcap (m := n + 2) (i := i) (by omega)) ≫
        (pres R δ).diag (dcap (m := n) (i := j - 2) (by omega)) := by
  rw [← Presentation.diag_comp, ← Presentation.diag_comp]
  symm
  apply diag_eq_of_swap δ (gl i .cap 0) (gl (j - 2 - i) .cap (n + 2 - j)) <;>
    simp [dcap, lay, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig] <;> omega

/-- Two cups: `cup_{j-2}` then `cup_i` equals `cup_i` then `cup_j`, for `i + 2 ≤ j`. -/
@[reassoc]
theorem cup_cup_interchange {n i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n + 2) :
    (pres R δ).diag (dcup (m := n) (i := j - 2) (by omega)) ≫
        (pres R δ).diag (dcup (m := n + 2) (i := i) (by omega)) =
      (pres R δ).diag (dcup (m := n) (i := i) (by omega)) ≫
        (pres R δ).diag (dcup (m := n + 2) (i := j) hj) := by
  rw [← Presentation.diag_comp, ← Presentation.diag_comp]
  symm
  apply diag_eq_of_swap δ (gl i .cup 0) (gl (j - 2 - i) .cup (n + 2 - j)) <;>
    simp [dcup, lay, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig] <;> omega

/-- A cup on the right passing a cap on the left: `cup_j` then `cap_i` equals `cap_i` then
`cup_{j-2}`, for `i + 2 ≤ j`. -/
@[reassoc]
theorem cap_cup_interchange {n i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n + 2) :
    (pres R δ).diag (dcup (m := n + 2) (i := j) hj) ≫
        (pres R δ).diag (dcap (m := n + 2) (i := i) (by omega)) =
      (pres R δ).diag (dcap (m := n) (i := i) (by omega)) ≫
        (pres R δ).diag (dcup (m := n) (i := j - 2) (by omega)) := by
  rw [← Presentation.diag_comp, ← Presentation.diag_comp]
  symm
  apply diag_eq_of_swap δ (gl i .cap 0) (gl (j - 2 - i) .cup (n + 2 - j)) <;>
    simp [dcup, dcap, lay, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig] <;> omega

/-- A cap on the right passing a cup on the left: `cap_{j-2}` then `cup_i` equals `cup_i` then
`cap_j`, for `i + 2 ≤ j`. -/
@[reassoc]
theorem cup_cap_interchange {n i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n + 2) :
    (pres R δ).diag (dcap (m := n) (i := j - 2) (by omega)) ≫
        (pres R δ).diag (dcup (m := n) (i := i) (by omega)) =
      (pres R δ).diag (dcup (m := n + 2) (i := i) (by omega)) ≫
        (pres R δ).diag (dcap (m := n + 2) (i := j) hj) := by
  rw [← Presentation.diag_comp, ← Presentation.diag_comp]
  symm
  apply diag_eq_of_swap δ (gl i .cup 0) (gl (j - 2 - i) .cap (n + 2 - j)) <;>
    simp [dcup, dcap, lay, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig] <;> omega

/-- Far commutativity: `e_i e_j = e_j e_i` for `i + 2 ≤ j`, in every width. -/
theorem e_mul_e_comm {m i j : ℕ} (hij : i + 2 ≤ j) : e δ m i * e δ m j = e δ m j * e δ m i := by
  by_cases hj : j ≤ m
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    rw [e_def δ (show i ≤ n + 2 by omega), e_def δ hj, End.mul_def, End.mul_def]
    simp only [Category.assoc]
    rw [cap_cup_interchange_assoc δ hij hj, cap_cap_interchange_assoc δ hij hj,
      cup_cup_interchange δ hij hj, cup_cap_interchange_assoc δ hij hj]
  · simp [e, hj]

/-- Far commutativity: `e_i e_j = e_j e_i` whenever `i` and `j` differ by at least `2`. -/
theorem e_mul_e_comm_of_far {m i j : ℕ} (h : i + 2 ≤ j ∨ j + 2 ≤ i) :
    e δ m i * e δ m j = e δ m j * e δ m i := by
  rcases h with h | h
  · exact e_mul_e_comm δ h
  · exact (e_mul_e_comm δ h).symm

end StringDiagrams.TemperleyLieb

end
