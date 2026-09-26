import StringDiagrams.Biadjunction.PivotalExtension

/-!
# Example: the walking biadjunction with a cyclic dot

Two regions `a`, `b`, strands `E : a → b` and `F : b → a` with `E* = F`, and one generator, a dot
`E ⟶ E`. The pivotal extension adds the four cups and caps (the cup and the cap of `E` and of
`F`) and the four zigzag relations; we add one more relation, `rotR = rotL`, saying that the two
rotations of the dot to the strand `F` (by the cup and cap of `E ⊣ F`, and by those of `F ⊣ E`)
agree.

* `biadjEF`: the biadjunction `E ⊣⊢ F`, whose units and counits are the cups and caps
  (`biadjEF_left_unit`, ...); words such as `E F E` are biadjoint to their dual words.
* `dot_isCyclic`: the dot is cyclic, from the relation; `isCyclic`: hence, by rotation
  invariance, every 2-morphism is cyclic, and `pivotal` is a pivotal structure.
* `dotF_eq_rotR`, `dotF_eq_rotL`: the mate of the dot is the class of either rotated diagram.
* `dot_slide_cup`, `dot_slide_cup'`: the dot slides along both cups to the same dot on `F`.
* `dottedBubble`: a dotted bubble, an endomorphism of the empty word `𝟙 a`;
  `bubble_eq_trace_snakes`: the plain `E`-bubble equals the trace of the endomorphism
  `snakeDown ≫ snakeUp` of `E F E`, a consequence of rotation invariance (the trace of `α ≫ β`
  equals the trace of `β ≫ α`) and the zigzag relation.

The example is generic: there are no weights and no relations beyond zigzags and cyclicity.
-/

noncomputable section

namespace StringDiagrams.WalkingBiadjunction

open CategoryTheory Bicategory Biadjunction Presentation

/-- The two regions. -/
inductive Reg
  | a
  | b
  deriving DecidableEq

/-- The two strands: `E` from `a` to `b` and `F` from `b` to `a`. -/
inductive Col
  | E
  | F
  deriving DecidableEq

/-- The single generator: a dot on the strand `E`. -/
inductive Gen
  | dot
  deriving DecidableEq

/-- The signature: two regions, the strands `E : a → b`, `F : b → a`, and a dot `E ⟶ E`. -/
def sig : Signature where
  Region := Reg
  Colour := Col
  colourSrc
    | .E => .a
    | .F => .b
  colourTgt
    | .E => .b
    | .F => .a
  Gen := Gen
  dom _ := [.E]
  cod _ := [.E]
  left _ := .a
  right _ := .b

instance : sig.IsEven := ⟨fun _ => rfl⟩

/-- `E* = F` and `F* = E`. -/
def inv : sig.ColourInvolution where
  dual
    | .E => .F
    | .F => .E
  src_dual c := by cases c <;> rfl
  tgt_dual c := by cases c <;> rfl
  dual_dual c := by cases c <;> rfl

/-- The pivotal extension. -/
abbrev psig : Signature := sig.pivotal inv.toColourDuality

instance : DecidableEq psig.Region := inferInstanceAs (DecidableEq Reg)
instance : DecidableEq psig.Colour := inferInstanceAs (DecidableEq Col)

/-- The dot on `F`, rotated using the cup and the cap of `E ⊣ F`. -/
def rotR : (⟨.b, [.F]⟩ : Obj psig) ⟶ ⟨.b, [.F]⟩ :=
  Diagram.mk [⟨.b, [.F], .cup .E, []⟩, ⟨.b, [.F], .gen .dot, [.F]⟩, ⟨.b, [], .cap .E, [.F]⟩]
    (by decide)

/-- The dot on `F`, rotated using the cup and the cap of `F ⊣ E`. -/
def rotL : (⟨.b, [.F]⟩ : Obj psig) ⟶ ⟨.b, [.F]⟩ :=
  Diagram.mk [⟨.b, [], .cup .F, [.F]⟩, ⟨.b, [.F], .gen .dot, [.F]⟩, ⟨.b, [.F], .cap .F, []⟩]
    (by decide)

/-- No relations among the original generators. -/
def pres₀ (R : Type) [CommRing R] : Presentation.{0, 0} sig R := ⟨Empty, Empty.elim, Empty.elim,
  fun i => i.elim⟩

variable (R : Type) [CommRing R]

/-- The walking biadjunction with a cyclic dot: the pivotal extension of `pres₀` (four cups and
caps and the four zigzag relations), with the relation `rotR = rotL`: the two rotations of the
dot agree. -/
def pres : Presentation.{0, 0} psig R :=
  ((pres₀ R).pivotal inv.toColourDuality).addRels Unit (fun _ => ⟨.b, [.F]⟩) (fun _ => ⟨.b, [.F]⟩)
    (fun _ => LinDiagram.of rotR - LinDiagram.of rotL)

theorem zigzags : (pres R).PivotalZigzags inv.toColourDuality :=
  Presentation.pivotal_addRels_zigzags inv.toColourDuality (pres₀ R) Unit _ _ _

/-- The biadjunctions of the strands. -/
abbrev B : ColourBiadjunctions (pres R) inv.toColourDuality.pivotal :=
  Presentation.pivotalBiadj inv (pres R) (zigzags R)

/-- The dot is cyclic, by the relation `rotR = rotL`. -/
theorem dot_isCyclic (hg : psig.GenValid (.gen .dot)) :
    Biadjunction.IsCyclic (biadj (B R) ((pres R).genDom (.gen .dot) hg))
      (biadj (B R) ((pres R).genCod (.gen .dot) hg)) ((pres R).gen2 (.gen .dot) hg) := by
  rw [isCyclic_biadj_iff_single (B R) (c := .E) (c' := .E) rfl rfl]
  refine isCyclic_diag_of_rel (B R ((pres R).genDom (.gen .dot) hg) .E rfl)
    (B R ((pres R).genCod (.gen .dot) hg) .E rfl) _ rfl _ rfl _ rfl _ rfl
    (genDiag _ hg) (.inr ()) (r₁ := rotR) (r₂ := rotL) ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- Every 2-morphism of the walking biadjunction with a cyclic dot is cyclic: rotating any
diagram by the cups and caps on the left or on the right gives the same result. -/
theorem isCyclic {l m : (pres R).Bicat} {x x' : l ⟶ m} (θ : x ⟶ x') :
    Biadjunction.IsCyclic (biadj (B R) x) (biadj (B R) x') θ :=
  pivotal_isCyclic inv (pres R) (zigzags R) (fun g hg => by cases g; exact dot_isCyclic R hg) θ

/-- The pivotal structure. -/
abbrev pivotal : StringDiagrams.Pivotal (pres R).Bicat :=
  pivotalStructure inv (pres R) (zigzags R) (fun g hg => by cases g; exact dot_isCyclic R hg)

/-! ## The strands, their adjunctions, and the dot -/

/-- The region `a`. -/
abbrev A : (pres R).Bicat := ⟨.a⟩

/-- The region `b`. -/
abbrev Bo : (pres R).Bicat := ⟨.b⟩

/-- The strand `E : a ⟶ b`. -/
abbrev strandE : A R ⟶ Bo R := (pres R).colourHom .E

/-- The strand `F : b ⟶ a`, the dual of `E`. -/
abbrev strandF : Bo R ⟶ A R := (pres R).dualHom inv.toColourDuality.pivotal (strandE R)

/-- `E ⊣⊢ F`, with units and counits the four cups and caps. -/
abbrev biadjEF : strandE R ⊣⊢ strandF R := B R (strandE R) .E rfl

/-- The adjunction `E ⊣ F`: its unit is the cup of `E`, its counit the cap of `E`. -/
theorem biadjEF_left_unit :
    (biadjEF R).left.unit = (pres R).diag (Pivotal.cupD inv.toColourDuality .E) := rfl

theorem biadjEF_left_counit :
    (biadjEF R).left.counit = (pres R).diag (Pivotal.capD inv.toColourDuality .E) := rfl

/-- The adjunction `F ⊣ E`: its unit is the cup of `F`, its counit the cap of `F`. -/
theorem biadjEF_right_unit :
    (biadjEF R).right.unit = (pres R).diag (Pivotal.cupD inv.toColourDuality .F) := rfl

theorem biadjEF_right_counit :
    (biadjEF R).right.counit = (pres R).diag (Pivotal.capD inv.toColourDuality .F) := rfl

/-- The word `E F E` has the biadjoint `F E F` (the reversed word of duals). -/
example : ((pres R).dualHom inv.toColourDuality.pivotal
    (strandE R ≫ strandF R ≫ strandE R)).obj.word = [.F, .E, .F] := rfl

/-- The word `E F E` is biadjoint to its dual, by nested cups and caps. -/
example : strandE R ≫ strandF R ≫ strandE R ⊣⊢
    (pres R).dualHom inv.toColourDuality.pivotal (strandE R ≫ strandF R ≫ strandE R) :=
  biadj (B R) _

/-- The dot, as a 2-morphism `E ⟶ E`. -/
def dot : strandE R ⟶ strandE R :=
  (pres R).gen2 (.gen .dot) ⟨⟨rfl, trivial⟩, rfl, ⟨rfl, trivial⟩, rfl⟩

/-- The dot, rotated to the strand `F` (its mate). -/
def dotF : strandF R ⟶ strandF R := rightMate (biadjEF R) (biadjEF R) (dot R)

/-- The dot is cyclic for the biadjunction `E ⊣⊢ F`. -/
theorem dot_isCyclic_EF : Biadjunction.IsCyclic (biadjEF R) (biadjEF R) (dot R) :=
  (isCyclic_biadj_iff_single (B R) rfl rfl (dot R)).1 (isCyclic R (dot R))

/-- The dot on `F` is the class of either rotated diagram. -/
theorem dotF_eq_rotR : dotF R = (pres R).diag rotR :=
  (rightMate_diag _ _ _ rfl _ rfl _).trans ((pres R).diag_eq_of_layers_eq rfl)

theorem dotF_eq_rotL : dotF R = (pres R).diag rotL := by
  rw [dotF, (dot_isCyclic_EF R).eq]
  exact (leftMate_diag _ _ _ rfl _ rfl _).trans ((pres R).diag_eq_of_layers_eq rfl)

/-! ## Sliding the dot along cups and caps -/

/-- Sliding the dot along the cup of `E ⊣ F`: it moves to the strand `F`. -/
theorem dot_slide_cup :
    (biadjEF R).left.unit ≫ dot R ▷ strandF R = (biadjEF R).left.unit ≫ strandE R ◁ dotF R :=
  (biadjEF R).left_unit_comp_whiskerRight (biadjEF R) (dot R)

/-- Sliding the dot along the cup of `F ⊣ E`: by cyclicity it becomes the same dot on `F`. -/
theorem dot_slide_cup' :
    (biadjEF R).right.unit ≫ strandF R ◁ dot R = (biadjEF R).right.unit ≫ dotF R ▷ strandE R :=
  (dot_isCyclic_EF R).right_unit_comp_whiskerLeft

/-! ## Bubbles -/

attribute [local instance] pivotal

/-- The clockwise bubble in the region `a` with a dot on it: the right trace of the dot, an
endomorphism of the empty word `𝟙 a`. -/
abbrev dottedBubble : 𝟙 (A R) ⟶ 𝟙 (A R) := StringDiagrams.Pivotal.rightTrace (dot R)

/-- A dot can be moved around a bubble: the trace of a composite does not depend on the order
of the factors (for any `α : E ⟶ f` and `β : f ⟶ E`). -/
theorem bubble_comp_comm {f : A R ⟶ Bo R} (α : strandE R ⟶ f) (β : f ⟶ strandE R) :
    StringDiagrams.Pivotal.rightTrace (α ≫ β) = StringDiagrams.Pivotal.rightTrace (β ≫ α) :=
  StringDiagrams.Pivotal.rightTrace_comp_comm α β

/-- The snake `E ⟶ E F E` (a cup to the left of `E`). -/
def snakeUp : strandE R ⟶ strandE R ≫ strandF R ≫ strandE R :=
  (λ_ _).inv ≫ (biadjEF R).left.unit ▷ strandE R ≫ (α_ _ _ _).hom

/-- The snake `E F E ⟶ E` (a cap to the right of `E`). -/
def snakeDown : strandE R ≫ strandF R ≫ strandE R ⟶ strandE R :=
  strandE R ◁ (biadjEF R).left.counit ≫ (ρ_ _).hom

theorem snakeUp_comp_snakeDown : snakeUp R ≫ snakeDown R = 𝟙 _ := by
  have h := (biadjEF R).left.left_triangle
  rw [leftZigzag_eq] at h
  have e : snakeUp R ≫ snakeDown R = (λ_ _).inv ≫ ((biadjEF R).left.unit ▷ strandE R ≫
      (α_ _ _ _).hom ≫ strandE R ◁ (biadjEF R).left.counit) ≫ (ρ_ _).hom := by
    simp only [snakeUp, snakeDown, Category.assoc]
  rw [e, h]
  simp

/-- **A consequence of rotation invariance.** The plain `E`-bubble equals the closed diagram
obtained by closing up the endomorphism `snakeDown ≫ snakeUp` of `E F E` (a cap followed by a
cup, with a through-strand), traced with the nested cups and caps of `E F E`. -/
theorem bubble_eq_trace_snakes :
    StringDiagrams.Pivotal.rightTrace (𝟙 (strandE R)) =
      StringDiagrams.Pivotal.rightTrace (snakeDown R ≫ snakeUp R) := by
  rw [← snakeUp_comp_snakeDown R]
  exact bubble_comp_comm R _ _

end StringDiagrams.WalkingBiadjunction
