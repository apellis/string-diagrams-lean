import StringDiagrams.Super.Presented

/-!
# The odd Brauer supercategory

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Example 1.5(iii)
(introduced by Kujawa and Tharp as the *marked Brauer category*).

The odd Brauer supercategory `SB` is the strict monoidal supercategory with one generating
object, an even generating morphism `s : · ⊗ · → · ⊗ ·` (the crossing), and two odd
generating morphisms `cup : 1 → · ⊗ ·` and `cap : · ⊗ · → 1`, subject to the relations
(read from the pictures of Example 1.5(iii); `f ≫ g` is `f` below `g`, and a generator at
position `i` has `i` strands to its left)

* `s ≫ s = 1` (`crossSq`);
* `s₀ ≫ s₁ ≫ s₀ = s₁ ≫ s₀ ≫ s₁` on three strands (`braid`);
* `cap ∘ (1 ⊗ cup) = 1`, i.e. `cup₁ ≫ cap₀ = 1` on one strand (`zigzagA`);
* `(1 ⊗ cap) ∘ (cup ⊗ 1) = -1`, i.e. `cup₀ ≫ cap₁ = -1` on one strand (`zigzagB`);
* a strand slides through a cup: `cup₀ ≫ s₁ = cup₁ ≫ s₀` from one to three strands
  (`slide`);
* `cup ≫ s = cup` (`crossCup`).

All relations are parity-homogeneous (`isParityHomogeneous`), so the presented category is a
strict monoidal supercategory (`monoidalSupercategory`).

## The stated consequences

Using the relations and the super interchange law, the paper checks that
`s ≫ cap = -cap` (`cross_comp_cap`), hence the bubble `cup ≫ cap` equals minus itself
(`bubble_eq_neg`), i.e. `2 • bubble = 0` (`two_smul_bubble`), and the bubble vanishes when
`2` is invertible in the ground ring (`bubble_eq_zero`); the paper writes this as
`bubble = ½ (cap ∘ s ∘ cup) - ½ (cap ∘ s ∘ cup) = 0`, which requires `2` to be invertible.
Over an arbitrary commutative ring only `2 • bubble = 0` is proved here.

The derivation of `s ≫ cap = -cap` rotates both legs of the cap: writing `Z` for the
composite `cup₀ ≫ cup₁ ≫ cap₃ ≫ cap₂` on two strands, `Z = -1` by two applications of
`zigzagB` and one odd interchange; then `Z ≫ s ≫ cap` is computed by moving `s` and `cap`
below the caps of `Z` and applying `slide` twice, `crossCup`, `zigzagA` and `zigzagB`.

No nondegeneracy statement (e.g. that the identity morphisms are non-zero) is proved in this
file.
-/

noncomputable section

namespace StringDiagrams.OddBrauer

open CategoryTheory

/-- The generators: a crossing, a cup and a cap. -/
inductive Gen
  | cross
  | cup
  | cap
  deriving DecidableEq

/-- One region, one colour; the crossing is even, the cup and the cap are odd. -/
def sig : Signature where
  Region := Unit
  Colour := Unit
  colourSrc _ := ()
  colourTgt _ := ()
  Gen := Gen
  dom
    | .cross => [(), ()]
    | .cup => []
    | .cap => [(), ()]
  cod
    | .cross => [(), ()]
    | .cup => [(), ()]
    | .cap => []
  left _ := ()
  right _ := ()
  odd
    | .cross => false
    | .cup => true
    | .cap => true

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

/-- A crossing of the strands `i` and `i + 1` of `n`. -/
def dcross {n i : ℕ} (h : i + 2 ≤ n) : strands n ⟶ strands n :=
  Diagram.layer (gl i .cross (n - i - 2)) (Layer.valid_of_subsingleton _)
    (obj_ext (by simp [Layer.dom, strands, sig]; omega))
    (obj_ext (by simp [Layer.cod, strands, sig]; omega))

/-- The relations. -/
inductive Rel
  | crossSq
  | braid
  | zigzagA
  | zigzagB
  | slide
  | crossCup

/-- Number of strands at the bottom of a relation. -/
def Rel.dom : Rel → ℕ
  | .crossSq => 2
  | .braid => 3
  | .zigzagA => 1
  | .zigzagB => 1
  | .slide => 1
  | .crossCup => 0

/-- Number of strands at the top of a relation. -/
def Rel.cod : Rel → ℕ
  | .crossSq => 2
  | .braid => 3
  | .zigzagA => 1
  | .zigzagB => 1
  | .slide => 3
  | .crossCup => 2

variable (R : Type*) [CommRing R]

open LinDiagram in
/-- The relations of Example 1.5(iii), each written as `lhs - rhs` (`f ≫ g` is `f` below
`g`). -/
def relation : (r : Rel) → LinDiagram R (strands r.dom) (strands r.cod)
  | .crossSq => of (dcross (n := 2) (i := 0) le_rfl ≫ dcross (n := 2) (i := 0) le_rfl) -
      of (𝟙 _)
  | .braid => of (dcross (n := 3) (i := 0) (by norm_num) ≫ dcross (n := 3) (i := 1) le_rfl ≫
        dcross (n := 3) (i := 0) (by norm_num)) -
      of (dcross (n := 3) (i := 1) le_rfl ≫ dcross (n := 3) (i := 0) (by norm_num) ≫
        dcross (n := 3) (i := 1) le_rfl)
  | .zigzagA => of (dcup (m := 1) (i := 1) le_rfl ≫ dcap (m := 1) (i := 0) zero_le_one) -
      of (𝟙 _)
  | .zigzagB => of (dcup (m := 1) (i := 0) zero_le_one ≫ dcap (m := 1) (i := 1) le_rfl) +
      of (𝟙 _)
  | .slide => of (dcup (m := 1) (i := 0) zero_le_one ≫ dcross (n := 3) (i := 1) le_rfl) -
      of (dcup (m := 1) (i := 1) le_rfl ≫ dcross (n := 3) (i := 0) (by norm_num))
  | .crossCup => of (dcup (m := 0) (i := 0) le_rfl ≫ dcross (n := 2) (i := 0) le_rfl) -
      of (dcup (m := 0) (i := 0) le_rfl)

/-- The odd Brauer supercategory, as a presentation. -/
def pres : Presentation sig R where
  Rel := Rel
  dom r := strands r.dom
  cod r := strands r.cod
  rel := relation R

/-- The relations are homogeneous for the parity. -/
theorem isParityHomogeneous : (pres R).IsParityHomogeneous := by
  intro r
  cases r
  · refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.of_mem_homDeg' ?_)⟩
    all_goals first | exact Diagram.degree_id _ _ | simp [dcross, Presentation.parityDeg, sig]
  · refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.of_mem_homDeg' ?_)⟩
    all_goals first | exact Diagram.degree_id _ _ | simp [dcross, Presentation.parityDeg, sig]
  · refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.of_mem_homDeg' ?_)⟩
    all_goals first | exact Diagram.degree_id _ _ | (simp [dcup, dcap, Presentation.parityDeg, sig]; try decide)
  · refine ⟨0, Submodule.add_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.of_mem_homDeg' ?_)⟩
    all_goals first | exact Diagram.degree_id _ _ | (simp [dcup, dcap, Presentation.parityDeg, sig]; try decide)
  · refine ⟨1, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.of_mem_homDeg' ?_)⟩
    all_goals simp [dcup, dcross, Presentation.parityDeg, sig]
  · refine ⟨1, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.of_mem_homDeg' ?_)⟩
    all_goals simp [dcup, dcross, Presentation.parityDeg, sig]

/-- The odd Brauer supercategory is a monoidal supercategory (strict, by
`Presentation.isStrict`). -/
theorem monoidalSupercategory :
    letI := (pres R).supercategory (isParityHomogeneous R)
    MonoidalSupercategory R (pres R).Presented :=
  (pres R).monoidalSupercategory (isParityHomogeneous R)

/-! ## Generators at symbolic positions -/

variable {R}

/-- `i` strands, used to whisker on the left. -/
def shift (i : ℕ) : Obj sig := ⟨(), List.replicate i ()⟩

theorem whisk_eq {w i k n : ℕ} (h : i + w + k = n) :
    (strands w).whisker (shift i) (List.replicate k ()) = strands n :=
  obj_ext (by simp [strands, shift, Obj.whisker]; omega)

/-- A relation whiskered by `i` strands on the left and `k` on the right, retyped. -/
theorem relation_at (r : Rel) (i k : ℕ) {a b : Obj sig}
    (ha : (strands r.dom).whisker (shift i) (List.replicate k ()) = a)
    (hb : (strands r.cod).whisker (shift i) (List.replicate k ()) = b) :
    (pres R).lin (LinDiagram.cast (LinDiagram.whisker (relation R r) (shift i)
      (List.replicate k ()) (Obj.whiskerOK_of_subsingleton _ _ _)) ha hb) = 0 :=
  (pres R).lin_rel_cast r (shift i) _ _ ha hb

variable (R)

/-- A cup at position `i` on `n` strands (zero if `i > n`). -/
def cup (n i : ℕ) : (pres R).obj (strands n) ⟶ (pres R).obj (strands (n + 2)) :=
  if h : i ≤ n then (pres R).diag (dcup h) else 0

/-- A cap at position `i` on `n + 2` strands (zero if `i > n`). -/
def cap (n i : ℕ) : (pres R).obj (strands (n + 2)) ⟶ (pres R).obj (strands n) :=
  if h : i ≤ n then (pres R).diag (dcap h) else 0

/-- The crossing of the strands `i`, `i + 1` of `n` (zero if `i + 2 > n`). -/
def cross (n i : ℕ) : (pres R).obj (strands n) ⟶ (pres R).obj (strands n) :=
  if h : i + 2 ≤ n then (pres R).diag (dcross h) else 0

variable {R}

theorem cup_def {n i : ℕ} (h : i ≤ n) : cup R n i = (pres R).diag (dcup h) := dif_pos h

theorem cap_def {n i : ℕ} (h : i ≤ n) : cap R n i = (pres R).diag (dcap h) := dif_pos h

theorem cross_def {n i : ℕ} (h : i + 2 ≤ n) : cross R n i = (pres R).diag (dcross h) := dif_pos h

/-! ## The relations at symbolic positions -/

/-- `cup_{i+1} ≫ cap_i = 1`. -/
theorem zigzagA_at {n i : ℕ} (h : i + 1 ≤ n) : cup R n (i + 1) ≫ cap R n i = 𝟙 _ := by
  have key := relation_at (R := R) .zigzagA i (n - i - 1) (a := strands n) (b := strands n)
    (whisk_eq (by simp [Rel.dom]; omega)) (whisk_eq (by simp [Rel.cod]; omega))
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.cast_sub,
    LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_of, sub_eq_zero] at key
  rw [cup_def h, cap_def (by omega), ← Presentation.diag_comp, ← (pres R).diag_id]
  refine Eq.trans ?_ (key.trans ?_) <;> apply Presentation.diag_eq_of_layers_eq
  · simp [dcup, dcap, shift, Layer.whisker, Rel.dom, sig]; try omega
  · rfl

/-- `cup_i ≫ cap_{i+1} = -1`. -/
theorem zigzagB_at {n i : ℕ} (h : i + 1 ≤ n) : cup R n i ≫ cap R n (i + 1) = -𝟙 _ := by
  have key := relation_at (R := R) .zigzagB i (n - i - 1) (a := strands n) (b := strands n)
    (whisk_eq (by simp [Rel.dom]; omega)) (whisk_eq (by simp [Rel.cod]; omega))
  simp only [relation, LinDiagram.whisker_add, LinDiagram.whisker_of, LinDiagram.cast_add,
    LinDiagram.cast_of, Presentation.lin_add, Presentation.lin_of, add_eq_zero_iff_eq_neg] at key
  rw [cup_def (by omega), cap_def h, ← Presentation.diag_comp, ← (pres R).diag_id]
  refine Eq.trans ?_ (key.trans (congrArg _ ?_)) <;> apply Presentation.diag_eq_of_layers_eq
  · simp [dcup, dcap, shift, Layer.whisker, Rel.dom, sig]; try omega
  · rfl

/-- A strand slides through a cup: `cup_i ≫ s_{i+1} = cup_{i+1} ≫ s_i`. -/
theorem slide_at {n i : ℕ} (h : i + 1 ≤ n) :
    cup R n i ≫ cross R (n + 2) (i + 1) = cup R n (i + 1) ≫ cross R (n + 2) i := by
  have key := relation_at (R := R) .slide i (n - i - 1) (a := strands n) (b := strands (n + 2))
    (whisk_eq (by simp [Rel.dom]; omega)) (whisk_eq (by simp [Rel.cod]; omega))
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.cast_sub,
    LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_of, sub_eq_zero] at key
  rw [cup_def (by omega), cup_def h, cross_def (by omega), cross_def (by omega),
    ← Presentation.diag_comp, ← Presentation.diag_comp]
  refine Eq.trans ?_ (key.trans ?_) <;> apply Presentation.diag_eq_of_layers_eq
  · simp [dcup, dcross, shift, Layer.whisker, Rel.dom, sig]; try omega
  · simp [dcup, dcross, shift, Layer.whisker, Rel.dom, sig]; try omega

/-- `cup ≫ s = cup`. -/
theorem crossCup_at {n i : ℕ} (h : i ≤ n) : cup R n i ≫ cross R (n + 2) i = cup R n i := by
  have key := relation_at (R := R) .crossCup i (n - i - 0) (a := strands n) (b := strands (n + 2))
    (whisk_eq (by simp [Rel.dom]; omega)) (whisk_eq (by simp [Rel.cod]; omega))
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.cast_sub,
    LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_of, sub_eq_zero] at key
  rw [cup_def h, cross_def (by omega), ← Presentation.diag_comp]
  refine Eq.trans ?_ (key.trans ?_) <;> apply Presentation.diag_eq_of_layers_eq
  · simp [dcup, dcross, shift, Layer.whisker, Rel.dom, sig]; try omega
  · simp [dcup, dcross, shift, Layer.whisker, Rel.dom, sig]; try omega

/-- `s ≫ s = 1`. -/
theorem crossSq_at {n i : ℕ} (h : i + 2 ≤ n) : cross R n i ≫ cross R n i = 𝟙 _ := by
  have key := relation_at (R := R) .crossSq i (n - i - 2) (a := strands n) (b := strands n)
    (whisk_eq (by simp [Rel.dom]; omega)) (whisk_eq (by simp [Rel.cod]; omega))
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.cast_sub,
    LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_of, sub_eq_zero] at key
  rw [cross_def h, ← Presentation.diag_comp, ← (pres R).diag_id]
  refine Eq.trans ?_ (key.trans ?_) <;> apply Presentation.diag_eq_of_layers_eq
  · simp [dcross, shift, Layer.whisker, Rel.dom, sig]; try omega
  · rfl

/-! ## The super interchange law for the generators -/

/-- The interchange law for two layers, with its Koszul sign. -/
theorem diag_eq_of_swap {a b : Obj sig} {f f' : a ⟶ b} (L M : Layer sig)
    (hf : Diagram.layers f = [L.wr M.dom.word, M.wl L.cod])
    (hf' : Diagram.layers f' = [M.wl L.dom, L.wr M.cod.word]) :
    (pres R).diag f =
      ((-1 : ℤ) ^ (Diagram.oddCountList [L] * Diagram.oddCountList [M])) • (pres R).diag f' := by
  have hc := Diagram.chain f
  rw [hf] at hc
  obtain ⟨-, ha, -, -, hb⟩ := hc
  rw [Layer.wr_dom] at ha
  rw [chain_nil, Layer.wl_cod] at hb
  subst ha hb
  exact (Presentation.diag_eq_of_layers_eq _ (by rw [hf]; rfl)).trans
    (((pres R).diag_swap_layers L M).trans
      (congrArg _ (Presentation.diag_eq_of_layers_eq _ (by rw [hf']; rfl))))

/-- Two caps anticommute: `cap_j ≫ cap_i = -(cap_i ≫ cap_{j-2})` for `i + 2 ≤ j`. -/
theorem cap_cap {n i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n + 2) :
    cap R (n + 2) j ≫ cap R n i = -(cap R (n + 2) i ≫ cap R n (j - 2)) := by
  rw [cap_def hj, cap_def (show i ≤ n by omega), cap_def (show i ≤ n + 2 by omega),
    cap_def (show j - 2 ≤ n by omega)]
  have key := diag_eq_of_swap (R := R)
    (f := dcap (m := n + 2) (i := i) (by omega) ≫ dcap (m := n) (i := j - 2) (by omega))
    (f' := dcap (m := n + 2) (i := j) hj ≫ dcap (m := n) (i := i) (by omega))
    (gl i .cap 0) (gl (j - 2 - i) .cap (n + 2 - j))
    (by simp [dcap, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
    (by simp [dcap, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
  simp [Diagram.oddCountList, sig] at key
  rw [key, neg_neg]

/-- Two cups anticommute: `cup_{j-2} ≫ cup_i = -(cup_i ≫ cup_j)` for `i + 2 ≤ j`. -/
theorem cup_cup {n i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n + 2) :
    cup R n (j - 2) ≫ cup R (n + 2) i = -(cup R n i ≫ cup R (n + 2) j) := by
  rw [cup_def (show j - 2 ≤ n by omega), cup_def (show i ≤ n + 2 by omega),
    cup_def (show i ≤ n by omega), cup_def hj]
  have key := diag_eq_of_swap (R := R)
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
    cup R (n + 2) i ≫ cap R (n + 2) j = -(cap R n (j - 2) ≫ cup R n i) := by
  rw [cup_def (show i ≤ n + 2 by omega), cap_def hj, cap_def (show j - 2 ≤ n by omega),
    cup_def (show i ≤ n by omega)]
  have key := diag_eq_of_swap (R := R)
    (f := dcup (m := n + 2) (i := i) (by omega) ≫ dcap (m := n + 2) (i := j) hj)
    (f' := dcap (m := n) (i := j - 2) (by omega) ≫ dcup (m := n) (i := i) (by omega))
    (gl i .cup 0) (gl (j - 2 - i) .cap (n + 2 - j))
    (by simp [dcup, dcap, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
    (by simp [dcup, dcap, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
  simp [Diagram.oddCountList, sig] at key
  exact key

/-- A cap on the right commutes with a crossing on the left:
`cap_j ≫ s_i = s_i ≫ cap_j` for `i + 2 ≤ j`. -/
theorem cap_cross {n i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n) :
    cap R n j ≫ cross R n i = cross R (n + 2) i ≫ cap R n j := by
  rw [cap_def hj, cross_def (show i + 2 ≤ n by omega), cross_def (show i + 2 ≤ n + 2 by omega)]
  have key := diag_eq_of_swap (R := R)
    (f := dcross (n := n + 2) (i := i) (by omega) ≫ dcap (m := n) (i := j) hj)
    (f' := dcap (m := n) (i := j) hj ≫ dcross (n := n) (i := i) (by omega))
    (gl i .cross 0) (gl (j - 2 - i) .cap (n - j))
    (by simp [dcap, dcross, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
    (by simp [dcap, dcross, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
  simp [Diagram.oddCountList, sig] at key
  exact key.symm

/-- A crossing on the right commutes with a cap on the left:
`s_{i+2} ≫ cap_j = cap_j ≫ s_i` for `j ≤ i`. -/
theorem cross_cap {n i j : ℕ} (hji : j ≤ i) (hi : i + 2 ≤ n) :
    cross R (n + 2) (i + 2) ≫ cap R n j = cap R n j ≫ cross R n i := by
  rw [cap_def (show j ≤ n by omega), cross_def hi, cross_def (show i + 2 + 2 ≤ n + 2 by omega)]
  have key := diag_eq_of_swap (R := R)
    (f := dcap (m := n) (i := j) (by omega) ≫ dcross (n := n) (i := i) hi)
    (f' := dcross (n := n + 2) (i := i + 2) (by omega) ≫ dcap (m := n) (i := j) (by omega))
    (gl j .cap 0) (gl (i - j) .cross (n - i - 2))
    (by simp [dcap, dcross, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
    (by simp [dcap, dcross, Layer.wr, Layer.wl, Layer.dom, Layer.cod, sig]; omega)
  simp [Diagram.oddCountList, sig] at key
  exact key.symm

/-! ## The computation of Example 1.5(iii) -/

/-- The composite `Z = cup₀ ≫ cup₁ ≫ cap₃ ≫ cap₂` on two strands is `-1`. -/
theorem zigzag_two : cup R 2 0 ≫ cup R 4 1 ≫ cap R 4 3 ≫ cap R 2 2 = -𝟙 _ := by
  have e1 : cup R 4 1 ≫ cap R 4 3 = -(cap R 2 1 ≫ cup R 2 1) :=
    cup_cap (n := 2) (i := 1) (j := 3) (by norm_num) (by norm_num)
  have e2 : cup R 2 0 ≫ cap R 2 1 = -𝟙 _ := zigzagB_at (n := 2) (i := 0) (by norm_num)
  have e3 : cup R 2 1 ≫ cap R 2 2 = -𝟙 _ := zigzagB_at (n := 2) (i := 1) (by norm_num)
  rw [reassoc_of% e1]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc, e3,
    Category.comp_id, neg_neg]
  rw [e2]

/-- The rotated cap relation `cup₀ ≫ cup₁ ≫ s₀ ≫ cap₀ = -cup₀` from two to four strands. -/
theorem rotate_crossCup : cup R 2 0 ≫ cup R 4 1 ≫ cross R 6 0 ≫ cap R 4 0 = -cup R 2 0 := by
  have f1 : cup R 4 1 ≫ cross R 6 0 = cup R 4 0 ≫ cross R 6 1 :=
    (slide_at (n := 4) (i := 0) (by norm_num)).symm
  have f2 : cup R 2 0 ≫ cup R 4 0 = -(cup R 2 0 ≫ cup R 4 2) :=
    cup_cup (n := 2) (i := 0) (j := 2) (by norm_num) (by norm_num)
  have f3 : cup R 4 2 ≫ cross R 6 1 = cup R 4 1 ≫ cross R 6 2 :=
    (slide_at (n := 4) (i := 1) (by norm_num)).symm
  have f4 : cross R 6 2 ≫ cap R 4 0 = cap R 4 0 ≫ cross R 4 0 :=
    cross_cap (n := 4) (i := 0) (j := 0) le_rfl (by norm_num)
  have f5 : cup R 4 1 ≫ cap R 4 0 = 𝟙 _ := zigzagA_at (n := 4) (i := 0) (by norm_num)
  have f6 : cup R 2 0 ≫ cross R 4 0 = cup R 2 0 := crossCup_at (n := 2) (i := 0) (by norm_num)
  rw [reassoc_of% f1, reassoc_of% f2]
  simp only [Preadditive.neg_comp, Category.assoc]
  rw [reassoc_of% f3, f4, reassoc_of% f5, f6]

/-- **Example 1.5(iii)**: a cap on top of a crossing is minus the cap, `s ≫ cap = -cap`. -/
theorem cross_comp_cap : cross R 2 0 ≫ cap R 0 0 = -cap R 0 0 := by
  have g1 : cap R 2 2 ≫ cross R 2 0 = cross R 4 0 ≫ cap R 2 2 :=
    cap_cross (n := 2) (i := 0) (j := 2) le_rfl le_rfl
  have g2 : cap R 4 3 ≫ cross R 4 0 = cross R 6 0 ≫ cap R 4 3 :=
    cap_cross (n := 4) (i := 0) (j := 3) (by norm_num) (by norm_num)
  have g3 : cap R 2 2 ≫ cap R 0 0 = -(cap R 2 0 ≫ cap R 0 0) :=
    cap_cap (n := 0) (i := 0) (j := 2) le_rfl le_rfl
  have g4 : cap R 4 3 ≫ cap R 2 0 = -(cap R 4 0 ≫ cap R 2 1) :=
    cap_cap (n := 2) (i := 0) (j := 3) (by norm_num) (by norm_num)
  have g5 : cup R 2 0 ≫ cap R 2 1 = -𝟙 _ := zigzagB_at (n := 2) (i := 0) (by norm_num)
  have key : (cup R 2 0 ≫ cup R 4 1 ≫ cap R 4 3 ≫ cap R 2 2) ≫ cross R 2 0 ≫ cap R 0 0 =
      cap R 0 0 := by
    simp only [Category.assoc]
    rw [reassoc_of% g1, reassoc_of% g2, g3]
    simp only [Preadditive.comp_neg, Category.assoc]
    rw [reassoc_of% g4]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, neg_neg, Category.assoc]
    rw [reassoc_of% (rotate_crossCup (R := R))]
    simp only [Preadditive.neg_comp, Category.assoc]
    rw [reassoc_of% g5]
    simp
  rw [zigzag_two] at key
  simpa using congrArg Neg.neg key

/-- The bubble `cup ≫ cap`. -/
def bubble : End ((pres R).obj (strands 0)) := cup R 0 0 ≫ cap R 0 0

/-- The bubble equals minus itself. -/
theorem bubble_eq_neg : bubble (R := R) = -bubble := by
  have h : cup R 0 0 ≫ cross R 2 0 = cup R 0 0 := crossCup_at (n := 0) (i := 0) le_rfl
  calc bubble (R := R) = (cup R 0 0 ≫ cross R 2 0) ≫ cap R 0 0 := by rw [h]; rfl
    _ = -bubble := by rw [Category.assoc, cross_comp_cap, Preadditive.comp_neg]; rfl

/-- Twice the bubble is zero, over any commutative ring. -/
theorem two_smul_bubble : (2 : R) • bubble (R := R) = 0 := by
  rw [two_smul]
  nth_rewrite 1 [bubble_eq_neg]
  exact neg_add_cancel _

/-- **Example 1.5(iii)**: if `2` is invertible in the ground ring (e.g. over a field of
characteristic different from `2`), the bubble vanishes. -/
theorem bubble_eq_zero (h2 : IsUnit (2 : R)) : bubble (R := R) = 0 := by
  have := two_smul_bubble (R := R)
  rwa [h2.smul_eq_zero] at this

end StringDiagrams.OddBrauer

end
