import StringDiagrams.Biadjunction.PivotalInclusion

/-!
# Example: a cyclic generator with a two-letter boundary

Two regions `a`, `b`, strands `E : a → b` and `F : b → a` with `E* = F`, and one generator
`s : E F ⟶ E F` in the region `a`. Its boundary words have two letters, so its rotations use the
nested cups and caps of the word `E F` (whose dual word `F* E* = E F` is again `E F`).

The presentation `pres` is the cyclic pivotal extension of the presentation without relations
(`Presentation.pivotalCyclic`): the four cups and caps, the zigzag relations, and the relation
identifying the right and left rotations of `s`. Its presented bicategory is pivotal (`pivotal`,
one line) and every 2-morphism is cyclic (`isCyclic`).

Consequences, all derived and stated as identities of classes of explicit diagrams:

* `layers_cupEF`, `layers_capEF`, `layers_rotS`: the nested cups and caps of `E F` and the rotated
  generator, as explicit lists of layers.
* `zigzagEF_eq_id`: the zigzag identity for the nested cups and caps of `E F` (a diagram with four
  layers), derived from the one-letter zigzag relations.
* `s_slide_cup`, `s_slide_cup'`: `s` slides along the nested cups of `E F` from either copy of
  `E F` to the other, becoming its rotation `rotS`; the second uses the cyclicity of `s`.
* `toPivotal_s`: the inclusion of the presentation without cups and caps sends `s` to `s`.

The example is generic: there are no weights and no relations beyond zigzags and cyclicity.
-/

noncomputable section

namespace StringDiagrams.TwoStrandGenerator

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

/-- The single generator `s : E F ⟶ E F`. -/
inductive Gen
  | s
  deriving DecidableEq

/-- The signature: two regions, the strands `E : a → b`, `F : b → a`, and `s : E F ⟶ E F`. -/
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
  dom _ := [.E, .F]
  cod _ := [.E, .F]
  left _ := .a
  right _ := .a

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

/-- No relations among the original generators. -/
def pres₀ (R : Type) [CommRing R] : Presentation.{0, 0} sig R :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩

variable (R : Type) [CommRing R]

/-- The cyclic pivotal extension of `pres₀`: cups and caps, the zigzag relations, and the
relation identifying the two rotations of `s`. -/
abbrev pres : Presentation.{0, 0} psig R := (pres₀ R).pivotalCyclic inv

/-- **The presented bicategory is pivotal.** -/
abbrev pivotal : StringDiagrams.Pivotal (pres R).Bicat := (pres₀ R).pivotalCyclicStructure inv

/-- The biadjunctions of the strands. -/
abbrev B : ColourBiadjunctions (pres R) inv.toColourDuality.pivotal :=
  pivotalBiadj inv (pres R) ((pres₀ R).pivotalCyclic_zigzags inv)

/-- Every 2-morphism is cyclic. -/
theorem isCyclic {l m : (pres R).Bicat} {x x' : l ⟶ m} (θ : x ⟶ x') :
    Biadjunction.IsCyclic (biadj (B R) x) (biadj (B R) x') θ :=
  (pres₀ R).pivotalCyclic_isCyclic inv θ

/-- The cups and caps of the strands, with their zigzag identities. -/
abbrev Q : ColourCupsCaps (pres R) inv.toColourDuality.pivotal :=
  (pres R).pivotalCupsCaps inv ((pres₀ R).pivotalCyclic_zigzags inv)

/-- The cup and cap diagrams. -/
abbrev K : ColourCupCapDiagrams psig inv.toColourDuality.pivotal := Pivotal.cupCapDiagrams inv

/-! ## Nested cups and caps of `E F` -/

theorem ok_EF : psig.ok .a [.E, .F] := ⟨rfl, rfl, trivial⟩

/-- The word `E F`, read from the region `a`. -/
abbrev wEF : Obj psig := ⟨.a, [.E, .F]⟩

/-- The nested cups `1 ⟶ E F E F` of `E F`. -/
abbrev cupEF : Obj.nil (S := psig) .a ⟶ ⟨.a, [.E, .F, .E, .F]⟩ := K.cupW .a [.E, .F] ok_EF

/-- The nested caps `E F E F ⟶ 1` of `E F`. -/
abbrev capEF : (⟨.a, [.E, .F, .E, .F]⟩ : Obj psig) ⟶ Obj.nil .a := K.capW .a [.E, .F] ok_EF

/-- The cup of `E` below the cup of `F`, inserted between `E` and `E* = F`. -/
theorem layers_cupEF :
    Diagram.layers cupEF = [⟨.a, [], .cup .E, []⟩, ⟨.a, [.E], .cup .F, [.F]⟩] := rfl

/-- The cap of `E`, between `(E F)* = E F` and `E F`, below the cap of `F`. -/
theorem layers_capEF :
    Diagram.layers capEF = [⟨.a, [.E], .cap .E, [.F]⟩, ⟨.a, [], .cap .F, []⟩] := rfl

/-- The word `E F` as a 1-morphism `a ⟶ a`. -/
abbrev EF : (⟨.a⟩ : (pres R).Bicat) ⟶ ⟨.a⟩ := (pres R).wordHom .a [.E, .F] ok_EF

/-- The zigzag of the nested cups and caps of `E F`. -/
def zigzagEF : (⟨.a, [.E, .F]⟩ : Obj psig) ⟶ ⟨.a, [.E, .F]⟩ :=
  Diagram.mk [⟨.a, [], .cup .E, [.E, .F]⟩, ⟨.a, [.E], .cup .F, [.F, .E, .F]⟩,
    ⟨.a, [.E, .F, .E], .cap .E, [.F]⟩, ⟨.a, [.E, .F], .cap .F, []⟩] (by decide)

/-- **The zigzag identity for the nested cups and caps of `E F`**, derived from the zigzag
relations of the single strands. -/
theorem zigzagEF_eq_id : (pres R).diag zigzagEF = 𝟙 _ :=
  ((pres R).diag_eq_of_layers_eq rfl).trans (diag_leftZigzag_wordCup_wordCap (Q R) (EF R))

/-! ## The generator and its rotations -/

theorem hs : psig.GenValid (.gen .s) :=
  ⟨⟨rfl, rfl, trivial⟩, rfl, ⟨rfl, rfl, trivial⟩, rfl⟩

/-- The generator `s` as a diagram. -/
abbrev sD : (⟨.a, [.E, .F]⟩ : Obj psig) ⟶ ⟨.a, [.E, .F]⟩ :=
  genDiag (S := psig) (.gen .s) hs

/-- The right rotation of `s` by the nested cups and caps of `E F`. -/
abbrev rotS : (⟨.a, [.E, .F]⟩ : Obj psig) ⟶ ⟨.a, [.E, .F]⟩ := K.genRotR (.gen .s) hs

theorem layers_rotS :
    Diagram.layers rotS =
      [⟨.a, [.E, .F], .cup .E, []⟩, ⟨.a, [.E, .F, .E], .cup .F, [.F]⟩,
        ⟨.a, [.E, .F], .gen .s, [.E, .F]⟩,
        ⟨.a, [.E], .cap .E, [.F, .E, .F]⟩, ⟨.a, [], .cap .F, [.E, .F]⟩] := rfl

/-- The two rotations of `s` agree (the imposed relation). -/
theorem rotS_eq : (pres R).diag rotS = (pres R).diag (K.genRotL (.gen .s) hs) :=
  (pres₀ R).pivotalCyclic_genRot inv .s hs

/-- **Sliding `s` along the nested cups of `E F`**, from the left copy of `E F` to the right one,
turns it into its rotation `rotS`. -/
theorem s_slide_cup :
    (pres R).diag (cupEF ≫ Diagram.rwhisker sD wEF ⟨ok_EF, rfl, ok_EF⟩) =
      (pres R).diag (cupEF ≫ Diagram.lwhisker wEF rotS ⟨ok_EF, rfl, ok_EF⟩) :=
  ((pres R).diag_eq_of_layers_eq rfl).trans
    ((diag_wordCup_comp_rwhisker (Q R) (x := EF R) (x' := EF R) sD).trans
      ((pres R).diag_eq_of_layers_eq rfl))

/-- **Sliding `s` along the nested cups of `E F`**, from the right copy of `E F` to the left one,
also turns it into `rotS`: this uses the cyclicity of `s`. -/
theorem s_slide_cup' :
    (pres R).diag (cupEF ≫ Diagram.lwhisker wEF sD ⟨ok_EF, rfl, ok_EF⟩) =
      (pres R).diag (cupEF ≫ Diagram.rwhisker rotS wEF ⟨ok_EF, rfl, ok_EF⟩) := by
  have h := diag_wordCup'_comp_lwhisker (Q R) (x := EF R) (x' := EF R) sD
  rw [(pres R).diag_comp, (pres R).diag_comp] at h ⊢
  rw [← (pres R).wRAt_diag _ _ _ rfl rfl]
  rw [← (pres R).wRAt_diag _ _ _ rfl rfl] at h
  have e : (pres R).diag rotS = (pres R).diag (ColourCupCapDiagrams.rotateL (P := pres R)
      (K) (x := EF R) (x' := EF R) sD) :=
    (rotS_eq R).trans ((pres R).diag_eq_of_layers_eq rfl)
  rw [e]
  exact ((congrArg (· ≫ _) ((pres R).diag_eq_of_layers_eq rfl)).trans h).trans
    (congrArg (· ≫ _) ((pres R).diag_eq_of_layers_eq rfl))

/-! ## The inclusion of the presentation without cups and caps -/

/-- The inclusion functor sends the generator `s` to the generator `s` of the pivotal
extension. -/
theorem toPivotal_s (hg : sig.GenValid Gen.s) :
    ((pres₀ R).toPivotalLift inv.toColourDuality (pres R)
        ((pres₀ R).pivotalCyclic_containsRels inv)).map
        ((pres₀ R).diag (genDiag (S := sig) .s hg)) =
      (pres R).diag sD :=
  toPivotalLift_genDiag (P := pres₀ R) (Q := pres R) (D := inv.toColourDuality)
    ((pres₀ R).pivotalCyclic_containsRels inv) Gen.s hg hs

end StringDiagrams.TwoStrandGenerator
