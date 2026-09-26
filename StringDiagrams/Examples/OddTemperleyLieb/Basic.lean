import StringDiagrams.Super.Presented

/-!
# The odd Temperley–Lieb supercategory

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Example 1.17(iii)
and Appendix A.

For `δ` in the ground ring, the odd Temperley–Lieb supercategory `STL(δ)` is the strict
monoidal supercategory with one generating object and two *odd* generating morphisms, a cup
`1 → · ⊗ ·` and a cap `· ⊗ · → 1`, subject to the relations (read from the pictures of the
paper; `f ≫ g` is `f` below `g`, and a generator at position `i` has `i` strands to its left)

* `cap ∘ (1 ⊗ cup) = 1`, i.e. `cup₁ ≫ cap₀ = 1` on one strand (`zigzagA`);
* `(1 ⊗ cap) ∘ (cup ⊗ 1) = ε`, i.e. `cup₀ ≫ cap₁ = -1` on one strand (`zigzagB`), where
  `ε = -1` as in Appendix A;
* `cap ∘ cup = δ` (`loop`).

All relations are parity-homogeneous (`isParityHomogeneous`), so the presented category is a
strict monoidal supercategory (`monoidalSupercategory`, `Presentation.isStrict`).

The object with `n` strands is `X R δ n` (the `n`-fold tensor power of the generating object,
`X_tensor`), and `e_n` is its identity. Cups and caps at symbolic positions and widths are
`cup R δ n i : X n ⟶ X (n + 2)` and `cap R δ n i : X (n + 2) ⟶ X n` (zero when the position is
out of range); the relations at every position are `zigzagA_at`, `zigzagB_at`, `loop_at`, and
the super interchange law for two generators at disjoint positions gives the four
anticommutation rules `cup_cup`, `cap_cap`, `cup_cap`, `cap_cup` (both generators are odd,
so the Koszul sign is `-1`).
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory MonoidalCategory

/-- The generators: a cup and a cap. -/
inductive Gen
  | cup
  | cap
  deriving DecidableEq

/-- One region, one colour; the cup and the cap are odd. -/
def sig : Signature where
  Region := Unit
  Colour := Unit
  colourSrc _ := ()
  colourTgt _ := ()
  Gen := Gen
  dom
    | .cup => []
    | .cap => [(), ()]
  cod
    | .cup => [(), ()]
    | .cap => []
  left _ := ()
  right _ := ()
  odd _ := true

instance : Subsingleton sig.Region := inferInstanceAs (Subsingleton Unit)

instance : Inhabited sig.Region := inferInstanceAs (Inhabited Unit)

/-- `n` strands. -/
def strands (n : ℕ) : Obj sig := ⟨(), List.replicate n ()⟩

theorem list_unit_ext {l₁ l₂ : List Unit} (h : l₁.length = l₂.length) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a l ih => cases l₂ with
    | nil => simp at h
    | cons b l₂ => rw [ih (by simpa using h)]

@[simp] theorem list_unit_eq_iff {l₁ l₂ : List Unit} : l₁ = l₂ ↔ l₁.length = l₂.length :=
  ⟨congrArg List.length, list_unit_ext⟩

theorem obj_ext {a b : Obj sig} (h : a.word.length = b.word.length) : a = b :=
  Obj.ext (Subsingleton.elim (α := Unit) _ _) (list_unit_ext h)

@[simp] theorem strands_word_length (n : ℕ) : (strands n).word.length = n := by
  simp [strands]

/-- Every object is a number of strands. -/
theorem eq_strands (a : Obj sig) : a = strands a.word.length := obj_ext (by simp)

/-- The generator `g` with `l` strands to its left and `r` strands to its right. -/
abbrev gl (l : ℕ) (g : Gen) (r : ℕ) : Layer sig := ⟨(), List.replicate l (), g, List.replicate r ()⟩

/-- A cup at position `i`, from `m` to `m + 2` strands. -/
def dcup {m i : ℕ} (h : i ≤ m) : strands m ⟶ strands (m + 2) :=
  Diagram.layer (gl i .cup (m - i)) (Layer.valid_of_subsingleton _)
    (obj_ext (by simp [Layer.dom, strands, sig]; omega))
    (obj_ext (by simp [Layer.cod, strands, sig]; omega))

/-- A cap at position `i`, from `m + 2` to `m` strands. -/
def dcap {m i : ℕ} (h : i ≤ m) : strands (m + 2) ⟶ strands m :=
  Diagram.layer (gl i .cap (m - i)) (Layer.valid_of_subsingleton _)
    (obj_ext (by simp [Layer.dom, strands, sig]; omega))
    (obj_ext (by simp [Layer.cod, strands, sig]; omega))

/-- The relations. -/
inductive Rel
  | zigzagA
  | zigzagB
  | loop

/-- Number of strands of a relation (at the top and at the bottom). -/
def Rel.width : Rel → ℕ
  | .zigzagA => 1
  | .zigzagB => 1
  | .loop => 0

variable (R : Type*) [CommRing R] (δ : R)

open LinDiagram in
/-- The relations of Example 1.17(iii), each written as `lhs - rhs` (`f ≫ g` is `f` below
`g`), with `ε = -1`:
* `zigzagA`: `cup₁ ≫ cap₀ - 1` on one strand;
* `zigzagB`: `cup₀ ≫ cap₁ - ε = cup₀ ≫ cap₁ + 1` on one strand;
* `loop`: `cup ≫ cap - δ`. -/
def relation : (r : Rel) → LinDiagram R (strands r.width) (strands r.width)
  | .zigzagA => of (dcup (m := 1) (i := 1) le_rfl ≫ dcap (m := 1) (i := 0) zero_le_one) -
      of (𝟙 _)
  | .zigzagB => of (dcup (m := 1) (i := 0) zero_le_one ≫ dcap (m := 1) (i := 1) le_rfl) +
      of (𝟙 _)
  | .loop => of (dcup (m := 0) (i := 0) le_rfl ≫ dcap (m := 0) (i := 0) le_rfl) - δ • of (𝟙 _)

/-- The odd Temperley–Lieb supercategory `STL(δ)`, as a presentation. -/
def pres : Presentation sig R where
  Rel := Rel
  dom r := strands r.width
  cod r := strands r.width
  rel := relation R δ

/-- The relations are homogeneous for the parity. -/
theorem isParityHomogeneous : (pres R δ).IsParityHomogeneous := by
  intro r
  cases r
  · refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.of_mem_homDeg' ?_)⟩
    all_goals first | exact Diagram.degree_id _ _ |
      (simp [dcup, dcap, Presentation.parityDeg, sig]; try decide)
  · refine ⟨0, Submodule.add_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.of_mem_homDeg' ?_)⟩
    all_goals first | exact Diagram.degree_id _ _ |
      (simp [dcup, dcap, Presentation.parityDeg, sig]; try decide)
  · refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_)
      (Submodule.smul_mem _ _ (LinDiagram.of_mem_homDeg' ?_))⟩
    all_goals first | exact Diagram.degree_id _ _ |
      (simp [dcup, dcap, Presentation.parityDeg, sig]; try decide)

/-- The odd Temperley–Lieb category. -/
abbrev STL : Type _ := (pres R δ).Presented

/-- The supercategory structure of `STL(δ)`: the parity of a diagram is its number of
generators modulo `2`. -/
abbrev supercategory : Supercategory R (STL R δ) :=
  (pres R δ).supercategory (isParityHomogeneous R δ)

/-- **Example 1.17(iii).** `STL(δ)` is a monoidal supercategory (strict, by
`Presentation.isStrict`). -/
theorem monoidalSupercategory :
    letI := supercategory R δ
    MonoidalSupercategory R (STL R δ) :=
  (pres R δ).monoidalSupercategory (isParityHomogeneous R δ)

example : MonoidalSupercategory.IsStrict (STL R δ) := Presentation.isStrict _

/-- The object `n`: `n` strands, the `n`-fold tensor power of the generating object. -/
abbrev X (n : ℕ) : STL R δ := (pres R δ).obj (strands n)

/-- Tensor product of objects adds numbers of strands; in particular `X n` is the `n`-fold
tensor power of the generating object `X 1`. -/
theorem X_tensor (m n : ℕ) : X R δ m ⊗ X R δ n = X R δ (m + n) := by
  rw [Presentation.obj_tensor]
  exact congrArg _ (obj_ext (by simp [strands, Obj.tensor]))

/-- The unit object is `X 0`. -/
theorem X_zero : 𝟙_ (STL R δ) = X R δ 0 := rfl

/-- The identity `e_n` of `n`. -/
abbrev e (n : ℕ) : X R δ n ⟶ X R δ n := 𝟙 _

/-- Retyping along an equality of numbers of strands. -/
abbrev tr {m n : ℕ} (h : m = n) : X R δ m ⟶ X R δ n := eqToHom (by rw [h])

/-! ## Generators at symbolic positions -/

variable {R δ}

/-- `i` strands, used to whisker on the left. -/
def shift (i : ℕ) : Obj sig := ⟨(), List.replicate i ()⟩

theorem whisk_eq {w i k n : ℕ} (h : i + w + k = n) :
    (strands w).whisker (shift i) (List.replicate k ()) = strands n :=
  obj_ext (by simp [strands, shift, Obj.whisker]; omega)

/-- A relation whiskered by `i` strands on the left and `k` on the right, retyped. -/
theorem relation_at (r : Rel) (i k : ℕ) {a b : Obj sig}
    (ha : (strands r.width).whisker (shift i) (List.replicate k ()) = a)
    (hb : (strands r.width).whisker (shift i) (List.replicate k ()) = b) :
    (pres R δ).lin (LinDiagram.cast (LinDiagram.whisker (relation R δ r) (shift i)
      (List.replicate k ()) (Obj.whiskerOK_of_subsingleton _ _ _)) ha hb) = 0 :=
  (pres R δ).lin_rel_cast r (shift i) _ _ ha hb

variable (R δ)

/-- A cup at position `i` on `n` strands (zero if `i > n`). -/
def cup (n i : ℕ) : X R δ n ⟶ X R δ (n + 2) :=
  if h : i ≤ n then (pres R δ).diag (dcup h) else 0

/-- A cap at position `i` on `n + 2` strands (zero if `i > n`). -/
def cap (n i : ℕ) : X R δ (n + 2) ⟶ X R δ n :=
  if h : i ≤ n then (pres R δ).diag (dcap h) else 0

variable {R δ}

theorem cup_def {n i : ℕ} (h : i ≤ n) : cup R δ n i = (pres R δ).diag (dcup h) := dif_pos h

theorem cap_def {n i : ℕ} (h : i ≤ n) : cap R δ n i = (pres R δ).diag (dcap h) := dif_pos h

theorem cup_of_lt {n i : ℕ} (h : n < i) : cup R δ n i = 0 := dif_neg (by omega)

theorem cap_of_lt {n i : ℕ} (h : n < i) : cap R δ n i = 0 := dif_neg (by omega)

/-! ## The relations at symbolic positions -/

/-- `cup_{i+1} ≫ cap_i = 1`. -/
theorem zigzagA_at {n i : ℕ} (h : i + 1 ≤ n) : cup R δ n (i + 1) ≫ cap R δ n i = 𝟙 _ := by
  have key := relation_at (R := R) (δ := δ) .zigzagA i (n - i - 1) (a := strands n)
    (b := strands n) (whisk_eq (by simp [Rel.width]; omega))
    (whisk_eq (by simp [Rel.width]; omega))
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.cast_sub,
    LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_of, sub_eq_zero] at key
  rw [cup_def h, cap_def (by omega), ← Presentation.diag_comp, ← (pres R δ).diag_id]
  refine Eq.trans ?_ (key.trans ?_) <;> apply Presentation.diag_eq_of_layers_eq
  · simp [dcup, dcap, shift, Layer.whisker, Rel.width, sig]; try omega
  · rfl

/-- `cup_i ≫ cap_{i+1} = ε = -1`. -/
theorem zigzagB_at {n i : ℕ} (h : i + 1 ≤ n) : cup R δ n i ≫ cap R δ n (i + 1) = -𝟙 _ := by
  have key := relation_at (R := R) (δ := δ) .zigzagB i (n - i - 1) (a := strands n)
    (b := strands n) (whisk_eq (by simp [Rel.width]; omega))
    (whisk_eq (by simp [Rel.width]; omega))
  simp only [relation, LinDiagram.whisker_add, LinDiagram.whisker_of, LinDiagram.cast_add,
    LinDiagram.cast_of, Presentation.lin_add, Presentation.lin_of, add_eq_zero_iff_eq_neg] at key
  rw [cup_def (by omega), cap_def h, ← Presentation.diag_comp, ← (pres R δ).diag_id]
  refine Eq.trans ?_ (key.trans (congrArg _ ?_)) <;> apply Presentation.diag_eq_of_layers_eq
  · simp [dcup, dcap, shift, Layer.whisker, Rel.width, sig]; try omega
  · rfl

/-- `cup_i ≫ cap_i = δ`. -/
theorem loop_at {n i : ℕ} (h : i ≤ n) : cup R δ n i ≫ cap R δ n i = δ • 𝟙 _ := by
  have key := relation_at (R := R) (δ := δ) .loop i (n - i) (a := strands n)
    (b := strands n) (whisk_eq (by simp [Rel.width]; omega))
    (whisk_eq (by simp [Rel.width]; omega))
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_smul, LinDiagram.whisker_of,
    LinDiagram.cast_sub, LinDiagram.cast_smul, LinDiagram.cast_of, Presentation.lin_sub,
    Presentation.lin_smul, Presentation.lin_of, sub_eq_zero] at key
  rw [cup_def h, cap_def h, ← Presentation.diag_comp, ← (pres R δ).diag_id]
  refine Eq.trans ?_ (key.trans ?_)
  · apply Presentation.diag_eq_of_layers_eq
    simp [dcup, dcap, shift, Layer.whisker, Rel.width, sig]; try omega
  · congr 1

/-! ## The super interchange law for the generators -/

/-- The interchange law for two layers, with its Koszul sign. -/
theorem diag_eq_of_swap {a b : Obj sig} {f f' : a ⟶ b} (L M : Layer sig)
    (hf : Diagram.layers f = [L.wr M.dom.word, M.wl L.cod])
    (hf' : Diagram.layers f' = [M.wl L.dom, L.wr M.cod.word]) :
    (pres R δ).diag f =
      ((-1 : ℤ) ^ (Diagram.oddCountList [L] * Diagram.oddCountList [M])) •
        (pres R δ).diag f' := by
  have hc := Diagram.chain f
  rw [hf] at hc
  obtain ⟨-, ha, -, -, hb⟩ := hc
  rw [Layer.wr_dom] at ha
  rw [chain_nil, Layer.wl_cod] at hb
  subst ha hb
  exact (Presentation.diag_eq_of_layers_eq _ (by rw [hf]; rfl)).trans
    (((pres R δ).diag_swap_layers L M).trans
      (congrArg _ (Presentation.diag_eq_of_layers_eq _ (by rw [hf']; rfl))))

/-- Two caps anticommute: `cap_j ≫ cap_i = -(cap_i ≫ cap_{j-2})` for `i + 2 ≤ j`. -/
theorem cap_cap {n i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n + 2) :
    cap R δ (n + 2) j ≫ cap R δ n i = -(cap R δ (n + 2) i ≫ cap R δ n (j - 2)) := by
  rw [cap_def hj, cap_def (show i ≤ n by omega), cap_def (show i ≤ n + 2 by omega),
    cap_def (show j - 2 ≤ n by omega)]
  have key := diag_eq_of_swap (R := R) (δ := δ)
    (f := dcap (m := n + 2) (i := i) (by omega) ≫ dcap (m := n) (i := j - 2) (by omega))
    (f' := dcap (m := n + 2) (i := j) hj ≫ dcap (m := n) (i := i) (by omega))
    (gl i .cap 0) (gl (j - 2 - i) .cap (n + 2 - j))
    (by simp [dcap, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
    (by simp [dcap, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
  simp [Diagram.oddCountList, sig] at key
  rw [key, neg_neg]

/-- Two cups anticommute: `cup_{j-2} ≫ cup_i = -(cup_i ≫ cup_j)` for `i + 2 ≤ j`. -/
theorem cup_cup {n i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n + 2) :
    cup R δ n (j - 2) ≫ cup R δ (n + 2) i = -(cup R δ n i ≫ cup R δ (n + 2) j) := by
  rw [cup_def (show j - 2 ≤ n by omega), cup_def (show i ≤ n + 2 by omega),
    cup_def (show i ≤ n by omega), cup_def hj]
  have key := diag_eq_of_swap (R := R) (δ := δ)
    (f := dcup (m := n) (i := i) (by omega) ≫ dcup (m := n + 2) (i := j) hj)
    (f' := dcup (m := n) (i := j - 2) (by omega) ≫ dcup (m := n + 2) (i := i) (by omega))
    (gl i .cup 0) (gl (j - 2 - i) .cup (n + 2 - j))
    (by simp [dcup, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
    (by simp [dcup, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
  simp [Diagram.oddCountList, sig] at key
  rw [key, neg_neg]

/-- A cup on the left and a cap on the right anticommute:
`cup_i ≫ cap_j = -(cap_{j-2} ≫ cup_i)` for `i + 2 ≤ j`. -/
theorem cup_cap {n i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n + 2) :
    cup R δ (n + 2) i ≫ cap R δ (n + 2) j = -(cap R δ n (j - 2) ≫ cup R δ n i) := by
  rw [cup_def (show i ≤ n + 2 by omega), cap_def hj, cap_def (show j - 2 ≤ n by omega),
    cup_def (show i ≤ n by omega)]
  have key := diag_eq_of_swap (R := R) (δ := δ)
    (f := dcup (m := n + 2) (i := i) (by omega) ≫ dcap (m := n + 2) (i := j) hj)
    (f' := dcap (m := n) (i := j - 2) (by omega) ≫ dcup (m := n) (i := i) (by omega))
    (gl i .cup 0) (gl (j - 2 - i) .cap (n + 2 - j))
    (by simp [dcup, dcap, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
    (by simp [dcup, dcap, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
  simp [Diagram.oddCountList, sig] at key
  exact key

/-- A cap on the left and a cup on the right anticommute:
`cup_j ≫ cap_i = -(cap_i ≫ cup_{j-2})` for `i + 2 ≤ j`. -/
theorem cap_cup {n i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n + 2) :
    cup R δ (n + 2) j ≫ cap R δ (n + 2) i = -(cap R δ n i ≫ cup R δ n (j - 2)) := by
  rw [cup_def hj, cap_def (show i ≤ n + 2 by omega), cap_def (show i ≤ n by omega),
    cup_def (show j - 2 ≤ n by omega)]
  have key := diag_eq_of_swap (R := R) (δ := δ)
    (f := dcap (m := n) (i := i) (by omega) ≫ dcup (m := n) (i := j - 2) (by omega))
    (f' := dcup (m := n + 2) (i := j) hj ≫ dcap (m := n + 2) (i := i) (by omega))
    (gl i .cap 0) (gl (j - 2 - i) .cup (n + 2 - j))
    (by simp [dcup, dcap, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
    (by simp [dcup, dcap, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
  simp [Diagram.oddCountList, sig] at key
  rw [key, neg_neg]

end StringDiagrams.OddTemperleyLieb

end
