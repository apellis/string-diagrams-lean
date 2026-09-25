import StringDiagrams.Examples.NilHecke.Relations
import StringDiagrams.Monoidal

/-!
# The nilHecke category is monoidal

The nilHecke signature is monoidal and even, so `NH R` is a strict monoidal `R`-linear
category (`StringDiagrams.Presentation.instMonoidalCategory`). The tensor product of objects
adds numbers of strands (`NH.obj_tensor`), and whiskering a dot by a strand on the right
(left) puts the dot on the leftmost (a shifted) strand of the wider object
(`x_whiskerRight`, `whiskerLeft_x`). As an illustration, commutativity of dots on
neighbouring strands in `NH_2` follows from the interchange law of the monoidal structure
(`x_mul_x_comm_two`).
-/

noncomputable section

namespace StringDiagrams.NilHecke

open CategoryTheory MonoidalCategory

instance : Inhabited sig.Region := ⟨()⟩

instance : sig.IsEven := ⟨fun _ => rfl⟩

variable (R : Type*) [CommRing R]

example : MonoidalCategory (NH R) := inferInstance
example : MonoidalLinear R (NH R) := inferInstance

/-- Tensor product of objects adds numbers of strands. -/
theorem NH.obj_tensor (m n : ℕ) : NH.obj R m ⊗ NH.obj R n = NH.obj R (m + n) := by
  rw [NH.obj, NH.obj, Presentation.obj_tensor]
  congr 1
  exact obj_ext (by simp [strands, Obj.tensor])

/-- The unit object is the empty object. -/
theorem NH.obj_zero : 𝟙_ (NH R) = NH.obj R 0 := rfl

/-- A dot on one strand, followed by a strand on the right, is a dot on strand `0` of `2`. -/
theorem x_whiskerRight : x R 1 0 ▷ NH.obj R 1 = x R 2 0 := by
  rw [x_def R (show 0 < 1 by omega), x_def R (show 0 < 2 by omega),
    Presentation.diag_whiskerRight]
  apply Presentation.diag_eq_of_layers_eq
  rfl

/-- A strand, followed by a dot on one strand, is a dot on strand `1` of `2`. -/
theorem whiskerLeft_x : NH.obj R 1 ◁ x R 1 0 = x R 2 1 := by
  rw [x_def R (show 0 < 1 by omega), x_def R (show 1 < 2 by omega),
    Presentation.diag_whiskerLeft]
  apply Presentation.diag_eq_of_layers_eq
  rfl

/-- Right whiskering of a dot at symbolic width. -/
theorem x_whiskerRight_strands {n i : ℕ} (h : i < n) (m : ℕ) :
    x R n i ▷ NH.obj R m = eqToHom (NH.obj_tensor R n m) ≫ x R (n + m) i ≫
      eqToHom (NH.obj_tensor R n m).symm := by
  rw [x_def R h, x_def R (show i < n + m by omega), Presentation.diag_whiskerRight]
  simp only [NH.obj, (pres R).eqToHom_obj, ← Presentation.diag_comp]
  apply Presentation.diag_eq_of_layers_eq
  simp only [Diagram.layers_whiskerR, Diagram.layers_comp, Diagram.layers_eqToHom, dlay,
    Diagram.layers_layer, List.map_cons, List.map_nil, List.nil_append, List.append_nil,
    List.cons.injEq, and_true]
  exact layer_ext (by simp [lay, Layer.wr]) rfl
    (by simp [lay, Layer.wr, strands, Gen.arity]; omega)

/-- Dots on neighbouring strands commute, from the interchange law of the monoidal
structure. -/
theorem x_mul_x_comm_two : x R 2 0 * x R 2 1 = x R 2 1 * x R 2 0 := by
  rw [← x_whiskerRight, ← whiskerLeft_x, End.mul_def, End.mul_def]
  exact (whisker_exchange _ _).trans rfl

end StringDiagrams.NilHecke

end
