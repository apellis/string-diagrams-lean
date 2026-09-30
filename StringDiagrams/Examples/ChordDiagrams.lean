import StringDiagrams.Chord.PresentedRegions
import StringDiagrams.Biadjunction.Zigzag

/-!
# Example: chord diagrams with weights

A signature with several regions to which `StringDiagrams.Chord.PresentedRegions` applies. The
regions are the integers (weights); there are two letters, `E` (`true`) and `F` (`false`), and the
strand of the letter `a` with the weight `ρ` on its right is the colour `(a, ρ)`, from the weight
`ρ + sh a` to `ρ` (`sh E = 2`, `sh F = -2`), as for the 1-morphisms `E 1_ρ`, `F 1_ρ` of a
categorified `sl(2)`. In every weight there are a cup `1 ⟶ a (d a)` (with `d E = F`, `d F = E`)
and a crossing `a b ⟶ b a` of any two letters.

In the presentation `pres` the braid relation on three strands and the pitchfork relation on one
strand are imposed in every weight. Then the images of chord diagrams are determined up to the
reductions of the normal form: the image of every chord diagram on the empty boundary word is
that of a diagram containing a double crossing, of a diagram containing a curl, or of the
canonical diagram of its pairing (`near_canon_or_reducible`), exactly (the filtration is trivial).
-/

noncomputable section

namespace StringDiagrams.Examples.ChordDiagrams

open CategoryTheory StringDiagrams.Chord

/-- The weight shift of a letter: `E` (`true`) raises weights by `2`, `F` lowers them by `2`. -/
def sh : Bool → ℤ
  | true => 2
  | false => -2

@[simp] theorem sh_not_add (a : Bool) : sh (!a) + sh a = 0 := by cases a <;> rfl

/-- The generators: a cup `1 ⟶ a (d a)` and a crossing `a b ⟶ b a` for every weight `ρ` on the
right. -/
inductive Gen
  | cup (a : Bool) (ρ : ℤ)
  | cross (a b : Bool) (ρ : ℤ)

/-- The signature: regions the weights, colours `(a, ρ)` from `ρ + sh a` to `ρ`. -/
abbrev sig : Signature where
  Region := ℤ
  Colour := Bool × ℤ
  colourSrc c := c.2 + sh c.1
  colourTgt c := c.2
  Gen := Gen
  dom
    | .cup _ _ => []
    | .cross a b ρ => [(a, ρ + sh b), (b, ρ)]
  cod
    | .cup a ρ => [(a, ρ + sh (!a)), (!a, ρ)]
    | .cross a b ρ => [(b, ρ + sh a), (a, ρ)]
  left
    | .cup _ ρ => ρ
    | .cross a b ρ => ρ + sh b + sh a
  right
    | .cup _ ρ => ρ
    | .cross _ _ ρ => ρ

/-- The letters: the letter `a` with the weight `ρ` on its right is the colour `(a, ρ)`. -/
def letters : Letters sig Bool where
  col a ρ := ((a, ρ) : Bool × ℤ)
  col_tgt _ _ := rfl

theorem valid_cup (a : Bool) (ρ : ℤ) : Layer.Valid (⟨ρ, [], .cup a ρ, []⟩ : Layer sig) := by
  refine ⟨trivial, rfl, trivial, rfl, ?_, rfl, trivial⟩
  refine ⟨?_, rfl, trivial⟩
  show ρ + sh (!a) + sh a = ρ
  rw [add_assoc, sh_not_add, add_zero]

theorem valid_cross (a b : Bool) (ρ : ℤ) :
    Layer.Valid (⟨ρ + sh b + sh a, [], .cross a b ρ, []⟩ : Layer sig) := by
  refine ⟨trivial, rfl, ⟨rfl, rfl, trivial⟩, rfl, ⟨?_, rfl, trivial⟩, rfl, trivial⟩
  show ρ + sh a + sh b = ρ + sh b + sh a
  ring

/-- Cups and crossings, one generator each, in every weight. -/
def gens : RegionChordGens letters (!·) where
  cup ρ a := [⟨ρ, [], .cup a ρ, []⟩]
  cross ρ a b := [⟨ρ + sh b + sh a, [], .cross a b ρ, []⟩]
  chain_cup ρ a := by
    refine ⟨valid_cup a ρ, rfl, Obj.ext ?_ rfl⟩
    show ρ = ρ + sh (!a) + sh a
    rw [add_assoc, sh_not_add, add_zero]
  chain_cross ρ a b := by
    refine ⟨valid_cross a b ρ, rfl, Obj.ext ?_ rfl⟩
    show ρ + sh b + sh a = ρ + sh a + sh b
    ring
  cup_even _ _ _ _ := rfl
  cross_even _ _ _ _ _ := rfl

/-- The two sides of the braid relation. -/
abbrev braidL : List (Move Bool) := [.cross 0, .cross 1, .cross 0]
/-- The two sides of the braid relation. -/
abbrev braidR : List (Move Bool) := [.cross 1, .cross 0, .cross 1]
/-- The two sides of the pitchfork relation. -/
abbrev pitchL (a : Bool) : List (Move Bool) := [.cup 0 a, .cross 1]
/-- The two sides of the pitchfork relation. -/
abbrev pitchR (a : Bool) : List (Move Bool) := [.cup 1 a, .cross 0]

theorem foldl_braid (a b c : Bool) :
    braidR.foldl (lstep (!·)) [a, b, c] = braidL.foldl (lstep (!·)) [a, b, c] := by
  simp [lstep, swapAt]

theorem foldl_pitch (a c : Bool) :
    (pitchR a).foldl (lstep (!·)) [c] = (pitchL a).foldl (lstep (!·)) [c] := by
  simp [lstep, swapAt, insAt]

/-- The relations: the braid relation and the pitchfork relation in every weight. -/
inductive Rel
  | braid (ρ : ℤ) (a b c : Bool)
  | pitch (ρ : ℤ) (a c : Bool)

/-- The diagram of a chord diagram `D` on the word `l`, in the weight `ρ`. -/
def chordDiag (ρ : ℤ) (l : List Bool) (D : List (Move Bool)) :
    letters.obj ρ l ⟶ letters.obj ρ (D.foldl (lstep (!·)) l) :=
  ⟨gens.layersOf ρ l D, gens.chain_layersOf ρ l D⟩

/-- The presentation imposing the braid and pitchfork relations in every weight. -/
def pres (R : Type) [CommRing R] : Presentation.{0, 0} sig R where
  Rel := Rel
  dom
    | .braid ρ a b c => letters.obj ρ [a, b, c]
    | .pitch ρ _ c => letters.obj ρ [c]
  cod
    | .braid ρ a b c => letters.obj ρ (braidL.foldl (lstep (!·)) [a, b, c])
    | .pitch ρ a c => letters.obj ρ ((pitchL a).foldl (lstep (!·)) [c])
  rel
    | .braid ρ a b c => LinDiagram.of (chordDiag ρ [a, b, c] braidL) -
        LinDiagram.of (Diagram.cast (chordDiag ρ [a, b, c] braidR) rfl
          (congrArg (letters.obj ρ) (foldl_braid a b c)))
    | .pitch ρ a c => LinDiagram.of (chordDiag ρ [c] (pitchL a)) -
        LinDiagram.of (Diagram.cast (chordDiag ρ [c] (pitchR a)) rfl
          (congrArg (letters.obj ρ) (foldl_pitch a c)))

/-- Cups have weight `0` and crossings weight `1`. -/
def wt : sig.Gen → ℕ
  | .cup _ _ => 0
  | .cross _ _ _ => 1

variable (R : Type) [CommRing R]

/-- The chord moves hold exactly in `pres R`, for the trivial filtration. -/
abbrev filt (ρ : ℤ) : ((gens.interp (pres R) ρ)).Filtration :=
  gens.toFiltration ρ (LayerFiltration.bot (pres R) wt) (fun _ _ => rfl) (fun _ _ _ => rfl)

theorem braid (ρ : ℤ) (a b c : Bool) : (filt R ρ).Near 3 [a, b, c] braidL braidR := by
  apply gens.near_of_diag_eq (pres R) ρ
  intro f₁ f₂ h₁ h₂
  exact (pres R).diag_eq_of_diag_eq_of_layers f₁ f₂ (chordDiag ρ [a, b, c] braidL)
    (Diagram.cast (chordDiag ρ [a, b, c] braidR) rfl (congrArg (letters.obj ρ) (foldl_braid a b c)))
    rfl (congrArg (letters.obj ρ) (foldl_braid a b c)).symm h₁ (by rw [h₂]; rfl)
    ((pres R).diag_eq_of_rel (.braid ρ a b c) rfl)

theorem pitch (ρ : ℤ) (a c : Bool) : (filt R ρ).Near 1 [c] (pitchL a) (pitchR a) := by
  apply gens.near_of_diag_eq (pres R) ρ
  intro f₁ f₂ h₁ h₂
  exact (pres R).diag_eq_of_diag_eq_of_layers f₁ f₂ (chordDiag ρ [c] (pitchL a))
    (Diagram.cast (chordDiag ρ [c] (pitchR a)) rfl (congrArg (letters.obj ρ) (foldl_pitch a c)))
    rfl (congrArg (letters.obj ρ) (foldl_pitch a c)).symm h₁ (by rw [h₂]; rfl)
    ((pres R).diag_eq_of_rel (.pitch ρ a c) rfl)

/-- **The normal form.** In `pres R`, the image of every chord diagram on the empty boundary word
in the weight `ρ` equals (after retyping) that of a diagram with a double crossing, that of a
diagram with a curl, or that of the canonical diagram of its pairing. -/
theorem near_canon_or_reducible (ρ : ℤ) {D : List (Move Bool)} (hf : Fits 0 D) :
    (∃ A B : List (Move Bool), ∃ p : ℕ, (filt R ρ).Near (ncross D) [] D
        (A ++ [.cross p, .cross p] ++ B)) ∨
      (∃ A B : List (Move Bool), ∃ p : ℕ, ∃ a : Bool,
        (filt R ρ).Near (ncross D) [] D (A ++ [.cup p a, .cross p] ++ B)) ∨
      (filt R ρ).Near (ncross D) [] D (canon (run (!·) D)) :=
  gens.near_canon_or_reducible (LayerFiltration.bot (pres R) wt) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun ρ a b c => braid R ρ a b c) (fun ρ a c => pitch R ρ a c) ρ hf

end StringDiagrams.Examples.ChordDiagrams
