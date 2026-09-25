import StringDiagrams.Grading
import StringDiagrams.Examples.NilHecke.Basic
import StringDiagrams.Examples.TemperleyLieb

/-!
# Examples of graded presentations

* The nilHecke presentation is homogeneous for the grading with a dot in degree `2` and a
  crossing in degree `-2` (KL I, arXiv:0803.4121v2, §2.1: `deg(x) = 2`, `deg(∂) = -2` in the
  one-colour case). Consequently `NH_n` is a `ℤ`-graded `R`-algebra
  (`NilHecke.gradedAlgebra`), with `x n i` of degree `2` and `ψ n i` of degree `-2`.
* The Temperley–Lieb presentation is homogeneous for the grading with a cup in degree `t` and
  a cap in degree `-t`, for every `t : ℤ` (the zigzag relations force the degrees of cup and cap
  to be opposite). The generators `e m i` have degree `0`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

/-! ## The nilHecke algebras -/

namespace NilHecke

/-- The grading of the nilHecke signature: a dot has degree `2`, a crossing degree `-2`. -/
def deg : Gen → ℤ
  | .dot => 2
  | .cross => -2

@[simp] theorem degree_dlay {n i : ℕ} {g : Gen} (h : i + g.arity ≤ n) :
    Diagram.degree (S := sig) deg (dlay h) = deg g := by
  simp [dlay, lay]

variable (R : Type*) [CommRing R]

/-- The nilHecke presentation is homogeneous. -/
theorem pres_isHomogeneous : (pres R).IsHomogeneous (S := sig) deg := by
  intro r
  cases r with
  | crossSq => exact ⟨-4, LinDiagram.of_mem_homDeg' (by simp [deg])⟩
  | braid =>
    exact ⟨-6, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' (by simp [deg]))
      (LinDiagram.of_mem_homDeg' (by simp [deg]))⟩
  | slideA =>
    exact ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' (by simp [deg]))
      (LinDiagram.of_mem_homDeg' (by simp [deg])))
      (LinDiagram.of_mem_homDeg' (Diagram.degree_id _ _))⟩
  | slideB =>
    exact ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' (by simp [deg]))
      (LinDiagram.of_mem_homDeg' (by simp [deg])))
      (LinDiagram.of_mem_homDeg' (Diagram.degree_id _ _))⟩

/-- A dot has degree `2`. -/
theorem x_mem_endDeg (n i : ℕ) : x R n i ∈ (pres R).endDeg deg (strands n) 2 := by
  unfold x
  split_ifs with h
  · exact Presentation.diag_mem_homDeg' (by simp [deg])
  · exact Submodule.zero_mem _

/-- A crossing has degree `-2`. -/
theorem ψ_mem_endDeg (n i : ℕ) : ψ R n i ∈ (pres R).endDeg deg (strands n) (-2) := by
  unfold ψ
  split_ifs with h
  · exact Presentation.diag_mem_homDeg' (by simp [deg])
  · exact Submodule.zero_mem _

/-- The nilHecke algebra `NH_n = End (NH.obj R n)` is a `ℤ`-graded `R`-algebra. -/
def gradedAlgebra (n : ℕ) : GradedAlgebra ((pres R).endDeg deg (strands n)) :=
  (pres R).gradedAlgebra (pres_isHomogeneous R) (strands n)

/-- Every Hom-space of the nilHecke category is the direct sum of its homogeneous parts. -/
theorem isInternal_homDeg (a b : Obj sig) :
    DirectSum.IsInternal ((pres R).homDeg deg a b) :=
  (pres R).isInternal_homDeg (pres_isHomogeneous R) a b

end NilHecke

/-! ## The Temperley–Lieb category -/

namespace TemperleyLieb

/-- The grading of the Temperley–Lieb signature with a cup in degree `t` and a cap in degree
`-t`. -/
def deg (t : ℤ) : Gen → ℤ
  | .cup => t
  | .cap => -t

@[simp] theorem degree_dcup (t : ℤ) {m i : ℕ} (h : i ≤ m) :
    Diagram.degree (S := sig) (deg t) (dcup h) = t := by
  simp [dcup, lay, deg]

@[simp] theorem degree_dcap (t : ℤ) {m i : ℕ} (h : i ≤ m) :
    Diagram.degree (S := sig) (deg t) (dcap h) = -t := by
  simp [dcap, lay, deg]

variable {R : Type*} [CommRing R] (δ : R)

/-- The Temperley–Lieb presentation is homogeneous for every grading `deg t`. -/
theorem pres_isHomogeneous (t : ℤ) : (pres R δ).IsHomogeneous (S := sig) (deg t) := by
  intro r
  refine ⟨0, ?_⟩
  cases r with
  | loop =>
    exact Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' (by simp))
      (Submodule.smul_mem _ _ (LinDiagram.of_mem_homDeg' (Diagram.degree_id _ _)))
  | zigzagA =>
    exact Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' (by simp))
      (LinDiagram.of_mem_homDeg' (Diagram.degree_id _ _))
  | zigzagB =>
    exact Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' (by simp))
      (LinDiagram.of_mem_homDeg' (Diagram.degree_id _ _))

/-- A cup has degree `t`. -/
theorem diag_dcup_mem_homDeg (t : ℤ) {m i : ℕ} (h : i ≤ m) :
    (pres R δ).diag (dcup h) ∈ (pres R δ).homDeg (deg t) (strands m) (strands (m + 2)) t :=
  Presentation.diag_mem_homDeg' (degree_dcup t h)

/-- A cap has degree `-t`. -/
theorem diag_dcap_mem_homDeg (t : ℤ) {m i : ℕ} (h : i ≤ m) :
    (pres R δ).diag (dcap h) ∈ (pres R δ).homDeg (deg t) (strands (m + 2)) (strands m) (-t) :=
  Presentation.diag_mem_homDeg' (degree_dcap t h)

/-- The Temperley–Lieb generators have degree `0`. -/
theorem e_mem_endDeg (t : ℤ) (m i : ℕ) :
    e δ m i ∈ (pres R δ).endDeg (deg t) (strands (m + 2)) 0 := by
  unfold e
  split_ifs with h
  · have :=
      Presentation.comp_mem_homDeg (diag_dcap_mem_homDeg δ t h) (diag_dcup_mem_homDeg δ t h)
    rwa [neg_add_cancel] at this
  · exact Submodule.zero_mem _

end TemperleyLieb

end StringDiagrams

end
