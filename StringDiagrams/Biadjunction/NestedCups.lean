import StringDiagrams.Biadjunction.PivotalExtension

/-!
# Nested cups and caps of words, and rotation of diagrams with arbitrary boundaries

Let `D` be a duality on the colours of a signature and `K : ColourCupCapDiagrams S D` a choice of
cup and cap diagrams for every colour `c` in canonical position: `cup c : 1 ⟶ c c*`,
`cap c : c* c ⟶ 1` (for `c ⊣ c*`) and `cup' c : 1 ⟶ c* c`, `cap' c : c c* ⟶ 1` (for `c* ⊣ c`).
For a presentation with chosen cups and caps `Q : ColourCupsCaps P D` these are
`Q.toDiagrams`; for the pivotal extension they are the cup and cap generators
(`Pivotal.cupCapDiagrams`).

## Nested cups and caps

For every well-formed word `w = c₁ ⋯ c_k` read from a region `r`, with dual `w* = c_k* ⋯ c₁*`,
the layered diagrams

* `K.cupW r w : 1 ⟶ w w*` (the cup of `c₁` is the outermost one, drawn lowest),
* `K.capW r w : w* w ⟶ 1` (the cap of `c₁` is the innermost one, drawn lowest),
* `K.cup'W r w : 1 ⟶ w* w` (the cup of `c₁` is the innermost one, drawn highest),
* `K.cap'W r w : w w* ⟶ 1` (the cap of `c₁` is the outermost one, drawn highest)

are defined by recursion on `w`. Their layers are given by the simp lemmas `layers_cupW_cons`, …
(each layer of the inner diagram is whiskered by the outer letter and its dual), and for
concatenations `u w` by `layers_cupW_append`, …, which apply to words of symbolic length. The
versions `K.wordCup x`, `K.wordCap x`, `K.wordCup' x`, `K.wordCap' x` for a 1-morphism
`x : l ⟶ m` of `P.Bicat` are the same diagrams, typed as 2-morphisms `𝟙 l ⟶ x ≫ x*`, … .

The units and counits of the biadjunction `biadj Q.biadjunctions x : x ⊣⊢ x*` of words
(`StringDiagrams.Biadjunction.Words`) are exactly the classes of these diagrams
(`Presentation.biadj_left_unit_eq_wordCup`, `biadj_left_counit_eq_wordCap`,
`biadj_right_unit_eq_wordCup'`, `biadj_right_counit_eq_wordCap'`); no coherence isomorphisms
appear, since the presented bicategory is strict and the diagrams are typed accordingly.
Consequently the four zigzag identities of nested cups and caps hold as identities of classes of
diagrams (`diag_leftZigzag_wordCup_wordCap`, …): they are derived from the zigzag identities of
the single colours, not imposed.

## Rotation of diagrams

For a diagram `d : u ⟶ u'` between words from `r` to `s`, `K.rotR d : u'* ⟶ u*` is the nested
cups of `u` below, `d` in the middle (with `u'*` on its left and `u*` on its right) and the
nested caps of `u'` above; `K.rotL d` is the mirror image using `cup'W` and `cap'W`. For
1-morphisms of `P.Bicat` these are `K.rotateR`, `K.rotateL`, and

* `rightMate_biadj_diag`, `leftMate_biadj_diag`: the right and left mates of `P.diag d` for the
  biadjunctions of words are `P.diag (rotateR d)` and `P.diag (rotateL d)`;
* `isCyclic_biadj_diag_iff`: `P.diag d` is cyclic iff its two rotations have the same class;
* `diag_wordCup_comp_rwhisker`, …: sliding a diagram along nested cups and caps (pitchfork
  identities for arbitrary words), as identities of classes of diagrams.

## Cyclicity relations for generators

`K.genRotR g`, `K.genRotL g : (cod g)* ⟶ (dom g)*` are the two rotations of a generator `g`,
defined from the signature alone, so that `rotR g = rotL g` can be imposed as a relation of a
presentation. `Presentation.isCyclic_gen_of_rel` turns such a relation into cyclicity of `g`
(the hypothesis of `Presentation.isCyclic_of_generators`), and `Presentation.pivotalOfGenRot`
gives the pivotal structure once all generators are handled.

For the pivotal extension of a presentation `P` along an involution `E`,
`Presentation.pivotalCyclic P E` adds to `P.pivotal` the relations `rotR g = rotL g` for all
original generators; its presented bicategory is pivotal (`pivotalCyclicStructure`) and every
2-morphism is cyclic (`pivotalCyclic_isCyclic`), with no further hypotheses. For an arbitrary
presentation of the pivotal extension in which the zigzag identities hold,
`pivotalStructureOfGenRot` needs only the equalities of the two rotations of the original
generators.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Biadjunction

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

/-- Cup and cap diagrams for every colour `c` and its dual `c*`, in canonical position: the
unit `cup c` and counit `cap c` of `c ⊣ c*`, and the unit `cup' c` and counit `cap' c` of
`c* ⊣ c`. No relations are required. -/
structure ColourCupCapDiagrams (S : Signature.{u₀, u₁, u₂}) (D : S.ColourDuality) where
  /-- The cup `1 ⟶ c c*`. -/
  cup : ∀ c : S.Colour, Obj.nil (S.colourSrc c) ⟶ ⟨S.colourSrc c, [c, D.dual c]⟩
  /-- The cap `c* c ⟶ 1`. -/
  cap : ∀ c : S.Colour, (⟨S.colourTgt c, [D.dual c, c]⟩ : Obj S) ⟶ Obj.nil (S.colourTgt c)
  /-- The cup `1 ⟶ c* c`. -/
  cup' : ∀ c : S.Colour, Obj.nil (S.colourTgt c) ⟶ ⟨S.colourTgt c, [D.dual c, c]⟩
  /-- The cap `c c* ⟶ 1`. -/
  cap' : ∀ c : S.Colour, (⟨S.colourSrc c, [c, D.dual c]⟩ : Obj S) ⟶ Obj.nil (S.colourSrc c)

namespace ColourCupCapDiagrams

variable {D : S.ColourDuality} (K : ColourCupCapDiagrams S D)

/-- Nested cups `1 ⟶ w w*` for a word `w` read from the region `r`: the cup of the first letter
is the outermost (lowest) one. -/
def cupW : (r : S.Region) → (w : List S.Colour) → S.ok r w →
    (Obj.nil r ⟶ ⟨r, w ++ D.dualWord w⟩)
  | _, [], _ => 𝟙 _
  | r, c :: w, h =>
    (Diagram.cast (K.cup c) (by rw [h.1]) (Obj.ext h.1 rfl) :
      Obj.nil r ⟶ (Obj.nil (S.colourTgt c)).whisker ⟨r, [c]⟩ [D.dual c]) ≫
      (Diagram.cast (Diagram.whisker (cupW (S.colourTgt c) w h.2) ⟨r, [c]⟩ [D.dual c]
        ⟨⟨h.1, trivial⟩, rfl, ⟨D.src_dual c, trivial⟩⟩) rfl (Obj.ext rfl (by simp)) :
        (Obj.nil (S.colourTgt c)).whisker ⟨r, [c]⟩ [D.dual c] ⟶
          ⟨r, (c :: w) ++ D.dualWord (c :: w)⟩)

/-- Nested caps `w* w ⟶ 1` for a word `w` read from the region `r` (so `w* w` is read from the
final region of `w`): the cap of the first letter is the innermost (lowest) one. -/
def capW : (r : S.Region) → (w : List S.Colour) → (h : S.ok r w) →
    ((⟨S.endR r w, D.dualWord w ++ w⟩ : Obj S) ⟶ Obj.nil (S.endR r w))
  | _, [], _ => 𝟙 _
  | _, c :: w, h =>
    (Diagram.cast (Diagram.whisker (K.cap c) ⟨S.endR (S.colourTgt c) w, D.dualWord w⟩ w
        ⟨(D.ok_dualWord _ w h.2).1, (D.ok_dualWord _ w h.2).2, h.2⟩)
      (Obj.ext rfl (by simp)) (Obj.ext rfl (by simp)) :
      (⟨S.endR (S.colourTgt c) w, D.dualWord (c :: w) ++ c :: w⟩ : Obj S) ⟶
        ⟨S.endR (S.colourTgt c) w, D.dualWord w ++ w⟩) ≫
      capW (S.colourTgt c) w h.2

/-- Nested cups `1 ⟶ w* w` for a word `w` read from the region `r`: the cup of the first letter
is the innermost (highest) one. -/
def cup'W : (r : S.Region) → (w : List S.Colour) → (h : S.ok r w) →
    (Obj.nil (S.endR r w) ⟶ ⟨S.endR r w, D.dualWord w ++ w⟩)
  | _, [], _ => 𝟙 _
  | _, c :: w, h =>
    cup'W (S.colourTgt c) w h.2 ≫
      (Diagram.cast (Diagram.whisker (K.cup' c) ⟨S.endR (S.colourTgt c) w, D.dualWord w⟩ w
        ⟨(D.ok_dualWord _ w h.2).1, (D.ok_dualWord _ w h.2).2, h.2⟩)
      (Obj.ext rfl (by simp)) (Obj.ext rfl (by simp)) :
      (⟨S.endR (S.colourTgt c) w, D.dualWord w ++ w⟩ : Obj S) ⟶
        ⟨S.endR (S.colourTgt c) w, D.dualWord (c :: w) ++ c :: w⟩)

/-- Nested caps `w w* ⟶ 1` for a word `w` read from the region `r`: the cap of the first letter
is the outermost (highest) one. -/
def cap'W : (r : S.Region) → (w : List S.Colour) → S.ok r w →
    ((⟨r, w ++ D.dualWord w⟩ : Obj S) ⟶ Obj.nil r)
  | _, [], _ => 𝟙 _
  | r, c :: w, h =>
    (Diagram.cast (Diagram.whisker (cap'W (S.colourTgt c) w h.2) ⟨r, [c]⟩ [D.dual c]
        ⟨⟨h.1, trivial⟩, rfl, by
          show S.ok (S.endR (S.colourTgt c) (w ++ D.dualWord w)) [D.dual c]
          rw [Signature.endR_append, (D.ok_dualWord _ w h.2).2]
          exact ⟨D.src_dual c, trivial⟩⟩)
      (Obj.ext rfl (by simp)) rfl :
      (⟨r, (c :: w) ++ D.dualWord (c :: w)⟩ : Obj S) ⟶
        (Obj.nil (S.colourTgt c)).whisker ⟨r, [c]⟩ [D.dual c]) ≫
    (Diagram.cast (K.cap' c) (Obj.ext h.1 rfl) (by rw [h.1]) :
      (Obj.nil (S.colourTgt c)).whisker ⟨r, [c]⟩ [D.dual c] ⟶ Obj.nil r)

variable {r : S.Region}

theorem layers_cupW_congr {w w' : List S.Colour} (e : w = w') (h : S.ok r w) :
    Diagram.layers (K.cupW r w h) = Diagram.layers (K.cupW r w' (e ▸ h)) := by
  subst e; rfl

theorem layers_capW_congr {w w' : List S.Colour} (e : w = w') (h : S.ok r w) :
    Diagram.layers (K.capW r w h) = Diagram.layers (K.capW r w' (e ▸ h)) := by
  subst e; rfl

theorem layers_cup'W_congr {w w' : List S.Colour} (e : w = w') (h : S.ok r w) :
    Diagram.layers (K.cup'W r w h) = Diagram.layers (K.cup'W r w' (e ▸ h)) := by
  subst e; rfl

theorem layers_cap'W_congr {w w' : List S.Colour} (e : w = w') (h : S.ok r w) :
    Diagram.layers (K.cap'W r w h) = Diagram.layers (K.cap'W r w' (e ▸ h)) := by
  subst e; rfl

@[simp] theorem layers_cupW_nil (h : S.ok r []) : Diagram.layers (K.cupW r [] h) = [] := rfl

@[simp] theorem layers_cupW_cons (c : S.Colour) (w : List S.Colour) (h : S.ok r (c :: w)) :
    Diagram.layers (K.cupW r (c :: w) h) =
      Diagram.layers (K.cup c) ++
        (Diagram.layers (K.cupW (S.colourTgt c) w h.2)).map (·.whisker ⟨r, [c]⟩ [D.dual c]) :=
  rfl

@[simp] theorem layers_capW_nil (h : S.ok r []) : Diagram.layers (K.capW r [] h) = [] := rfl

@[simp] theorem layers_capW_cons (c : S.Colour) (w : List S.Colour) (h : S.ok r (c :: w)) :
    Diagram.layers (K.capW r (c :: w) h) =
      (Diagram.layers (K.cap c)).map
          (·.whisker ⟨S.endR (S.colourTgt c) w, D.dualWord w⟩ w) ++
        Diagram.layers (K.capW (S.colourTgt c) w h.2) :=
  rfl

@[simp] theorem layers_cup'W_nil (h : S.ok r []) : Diagram.layers (K.cup'W r [] h) = [] := rfl

@[simp] theorem layers_cup'W_cons (c : S.Colour) (w : List S.Colour) (h : S.ok r (c :: w)) :
    Diagram.layers (K.cup'W r (c :: w) h) =
      Diagram.layers (K.cup'W (S.colourTgt c) w h.2) ++
        (Diagram.layers (K.cup' c)).map
          (·.whisker ⟨S.endR (S.colourTgt c) w, D.dualWord w⟩ w) :=
  rfl

@[simp] theorem layers_cap'W_nil (h : S.ok r []) : Diagram.layers (K.cap'W r [] h) = [] := rfl

@[simp] theorem layers_cap'W_cons (c : S.Colour) (w : List S.Colour) (h : S.ok r (c :: w)) :
    Diagram.layers (K.cap'W r (c :: w) h) =
      (Diagram.layers (K.cap'W (S.colourTgt c) w h.2)).map (·.whisker ⟨r, [c]⟩ [D.dual c]) ++
        Diagram.layers (K.cap' c) :=
  rfl

theorem layers_whisker_nil_of_start {a b : Obj S} (f : a ⟶ b) :
    (Diagram.layers f).map (·.whisker ⟨a.start, []⟩ []) = Diagram.layers f := by
  conv_rhs => rw [← List.map_id (Diagram.layers f)]
  exact List.map_congr_left fun L hL =>
    Layer.ext ((Diagram.chain f).start_of_mem hL).symm (List.nil_append _) rfl (List.append_nil _)

/-- Nested cups of a concatenation `u w`: the nested cups of `u`, then those of `w` inserted
between `u` and `u*`. -/
theorem layers_cupW_append (u w : List S.Colour) (h : S.ok r (u ++ w)) :
    Diagram.layers (K.cupW r (u ++ w) h) =
      Diagram.layers (K.cupW r u ((Signature.ok_append r u w).1 h).1) ++
        (Diagram.layers (K.cupW (S.endR r u) w ((Signature.ok_append r u w).1 h).2)).map
          (·.whisker ⟨r, u⟩ (D.dualWord u)) := by
  induction u generalizing r with
  | nil => exact (layers_whisker_nil_of_start (K.cupW r w h)).symm
  | cons c u ih =>
    simp only [List.cons_append, layers_cupW_cons, ih, List.map_append, List.map_map,
      List.append_assoc]
    congr 2
    exact List.map_congr_left fun L _ => by
      simp [Layer.whisker_whisker, Obj.tensor]

/-- Nested caps of a concatenation `u w`: the nested caps of `u` (between `w*` and `w`), then
those of `w`. -/
theorem layers_capW_append (u w : List S.Colour) (h : S.ok r (u ++ w)) :
    Diagram.layers (K.capW r (u ++ w) h) =
      (Diagram.layers (K.capW r u ((Signature.ok_append r u w).1 h).1)).map
          (·.whisker ⟨S.endR r (u ++ w), D.dualWord w⟩ w) ++
        Diagram.layers (K.capW (S.endR r u) w ((Signature.ok_append r u w).1 h).2) := by
  induction u generalizing r with
  | nil => rfl
  | cons c u ih =>
    simp only [List.cons_append, layers_capW_cons, ih, List.map_append, List.map_map,
      List.append_assoc]
    congr 1
    exact List.map_congr_left fun L _ => by
      simp [Layer.whisker_whisker, Obj.tensor]

/-- Nested cups `1 ⟶ (u w)* (u w)` of a concatenation: those of `w`, then those of `u` inserted
between `w*` and `w`. -/
theorem layers_cup'W_append (u w : List S.Colour) (h : S.ok r (u ++ w)) :
    Diagram.layers (K.cup'W r (u ++ w) h) =
      Diagram.layers (K.cup'W (S.endR r u) w ((Signature.ok_append r u w).1 h).2) ++
        (Diagram.layers (K.cup'W r u ((Signature.ok_append r u w).1 h).1)).map
          (·.whisker ⟨S.endR r (u ++ w), D.dualWord w⟩ w) := by
  induction u generalizing r with
  | nil => simp
  | cons c u ih =>
    simp only [List.cons_append, layers_cup'W_cons, ih, List.map_append, List.map_map,
      List.append_assoc]
    congr 2
    exact List.map_congr_left fun L _ => by
      simp [Layer.whisker_whisker, Obj.tensor]

/-- Nested caps `(u w) (u w)* ⟶ 1` of a concatenation: those of `w` (between `u` and `u*`), then
those of `u`. -/
theorem layers_cap'W_append (u w : List S.Colour) (h : S.ok r (u ++ w)) :
    Diagram.layers (K.cap'W r (u ++ w) h) =
      (Diagram.layers (K.cap'W (S.endR r u) w ((Signature.ok_append r u w).1 h).2)).map
          (·.whisker ⟨r, u⟩ (D.dualWord u)) ++
        Diagram.layers (K.cap'W r u ((Signature.ok_append r u w).1 h).1) := by
  induction u generalizing r with
  | nil => simpa using (layers_whisker_nil_of_start (K.cap'W r w h)).symm
  | cons c u ih =>
    simp only [List.cons_append, layers_cap'W_cons, ih, List.map_append, List.map_map,
      List.append_assoc]
    congr 1
    exact List.map_congr_left fun L _ => by
      simp [Layer.whisker_whisker, Obj.tensor]

/-! ### Rotation of diagrams by nested cups and caps -/

section Rotation

variable {r s : S.Region} {u u' : List S.Colour}

theorem _root_.StringDiagrams.Signature.ColourDuality.ok_dualWord' (hu : S.ok r u)
    (hs : S.endR r u = s) : S.ok s (D.dualWord u) ∧ S.endR s (D.dualWord u) = r := by
  subst hs; exact D.ok_dualWord r u hu

/-- The right rotation `u'* ⟶ u*` of a diagram `d : u ⟶ u'` between words from the region `r` to
the region `s`: the nested cups `K.cupW` of `u` below, `d` in the middle (with `u'*` on its left and
`u*` on its right), and the nested caps `K.capW` of `u'` above. -/
def rotR (d : (⟨r, u⟩ : Obj S) ⟶ ⟨r, u'⟩) (hu : S.ok r u) (hs : S.endR r u = s) :
    (⟨s, D.dualWord u'⟩ : Obj S) ⟶ ⟨s, D.dualWord u⟩ :=
  have hu' : S.ok r u' := (Diagram.chain d).wf hu
  have hs' : S.endR r u' = s := (Diagram.chain d).endR_eq.trans hs
  have hy := D.ok_dualWord' hu hs
  have hy' := D.ok_dualWord' hu' hs'
  have c₁ : (⟨s, D.dualWord u'⟩ : Obj S).Composable ⟨r, u⟩ := ⟨hy'.1, hy'.2, hu⟩
  have c₂ : (⟨r, u⟩ : Obj S).Composable ⟨s, D.dualWord u⟩ := ⟨hu, hs, hy.1⟩
  have c₃ : (⟨s, D.dualWord u'⟩ : Obj S).Composable ⟨r, u'⟩ := ⟨hy'.1, hy'.2, hu'⟩
  have c₄ : (⟨r, u'⟩ : Obj S).Composable ⟨s, D.dualWord u⟩ := ⟨hu', hs', hy.1⟩
  Diagram.cast
    (Diagram.lwhisker ⟨s, D.dualWord u'⟩ (K.cupW r u hu) ⟨hy'.1, hy'.2, trivial⟩ ≫
      Diagram.lwhisker ⟨s, D.dualWord u'⟩ (Diagram.rwhisker d ⟨s, D.dualWord u⟩ c₂)
        (c₁.tensor_right c₂) ≫
      eqToHom (Obj.tensor_assoc ⟨s, D.dualWord u'⟩ ⟨r, u'⟩ ⟨s, D.dualWord u⟩).symm ≫
      Diagram.rwhisker
        (Diagram.cast (K.capW r u' hu') (Obj.ext hs' rfl) (by rw [hs']) :
          (⟨s, D.dualWord u' ++ u'⟩ : Obj S) ⟶ Obj.nil s)
        ⟨s, D.dualWord u⟩ (c₃.tensor_left c₄))
    (Obj.tensor_nil _ r) (Obj.nil_tensor rfl)

/-- The left rotation `u'* ⟶ u*` of a diagram `d : u ⟶ u'` between words from the region `r` to
the region `s`: the nested cups `K.cup'W` of `u` below, `d` in the middle (with `u*` on its left and
`u'*` on its right), and the nested caps `K.cap'W` of `u'` above. -/
def rotL (d : (⟨r, u⟩ : Obj S) ⟶ ⟨r, u'⟩) (hu : S.ok r u) (hs : S.endR r u = s) :
    (⟨s, D.dualWord u'⟩ : Obj S) ⟶ ⟨s, D.dualWord u⟩ :=
  have hu' : S.ok r u' := (Diagram.chain d).wf hu
  have hs' : S.endR r u' = s := (Diagram.chain d).endR_eq.trans hs
  have hy := D.ok_dualWord' hu hs
  have hy' := D.ok_dualWord' hu' hs'
  have c₁ : (⟨s, D.dualWord u⟩ : Obj S).Composable ⟨r, u⟩ := ⟨hy.1, hy.2, hu⟩
  have c₂ : (⟨r, u⟩ : Obj S).Composable ⟨s, D.dualWord u'⟩ := ⟨hu, hs, hy'.1⟩
  have c₃ : (⟨s, D.dualWord u⟩ : Obj S).Composable ⟨r, u'⟩ := ⟨hy.1, hy.2, hu'⟩
  have c₄ : (⟨r, u'⟩ : Obj S).Composable ⟨s, D.dualWord u'⟩ := ⟨hu', hs', hy'.1⟩
  Diagram.cast
    (Diagram.rwhisker
        (Diagram.cast (K.cup'W r u hu) (by rw [hs]) (Obj.ext hs rfl) :
          Obj.nil s ⟶ ⟨s, D.dualWord u ++ u⟩)
        ⟨s, D.dualWord u'⟩ (Obj.Composable.nil_left (b := ⟨s, D.dualWord u'⟩) hy'.1 rfl) ≫
      eqToHom (Obj.tensor_assoc ⟨s, D.dualWord u⟩ ⟨r, u⟩ ⟨s, D.dualWord u'⟩) ≫
      Diagram.lwhisker ⟨s, D.dualWord u⟩ (Diagram.rwhisker d ⟨s, D.dualWord u'⟩ c₂)
        (c₁.tensor_right c₂) ≫
      Diagram.lwhisker ⟨s, D.dualWord u⟩ (K.cap'W r u' hu') (c₃.tensor_right c₄))
    (Obj.nil_tensor rfl) (Obj.tensor_nil _ r)

@[simp] theorem layers_rotR (d : (⟨r, u⟩ : Obj S) ⟶ ⟨r, u'⟩) (hu : S.ok r u)
    (hs : S.endR r u = s) :
    Diagram.layers (K.rotR d hu hs) =
      (Diagram.layers (K.cupW r u hu)).map (·.wl ⟨s, D.dualWord u'⟩) ++
        ((Diagram.layers d).map (·.wr (D.dualWord u))).map (·.wl ⟨s, D.dualWord u'⟩) ++
          (Diagram.layers (K.capW r u' ((Diagram.chain d).wf hu))).map
            (·.wr (D.dualWord u)) := by
  simp [rotR]

@[simp] theorem layers_rotL (d : (⟨r, u⟩ : Obj S) ⟶ ⟨r, u'⟩) (hu : S.ok r u)
    (hs : S.endR r u = s) :
    Diagram.layers (K.rotL d hu hs) =
      (Diagram.layers (K.cup'W r u hu)).map (·.wr (D.dualWord u')) ++
        ((Diagram.layers d).map (·.wr (D.dualWord u'))).map (·.wl ⟨s, D.dualWord u⟩) ++
          (Diagram.layers (K.cap'W r u' ((Diagram.chain d).wf hu))).map
            (·.wl ⟨s, D.dualWord u⟩) := by
  simp [rotL]

end Rotation

end ColourCupCapDiagrams

namespace Presentation

variable {R : Type w} [CommRing R] {P : Presentation.{w, v} S R} {D : S.ColourDuality}
  (K : ColourCupCapDiagrams S D) {l m : P.Bicat}

theorem Bicat.Hom.ok_region (x : l ⟶ m) : S.ok l.region x.obj.word := by
  have := x.wf; rw [Obj.WF, x.start_eq] at this; exact this

theorem Bicat.Hom.endR_region (x : l ⟶ m) : S.endR l.region x.obj.word = m.region := by
  have := x.endR_eq; rw [Obj.endR, x.start_eq] at this; exact this

theorem Bicat.Hom.colourSrc_eq_of_word_eq_cons (x : l ⟶ m) {c : S.Colour} {w : List S.Colour}
    (hx : x.obj.word = c :: w) : S.colourSrc c = l.region := by
  have := Bicat.Hom.ok_region x; rw [hx] at this; exact this.1

/-- The nested cups `1 ⟶ x x*` of a 1-morphism `x` of `P.Bicat` (the diagram `K.cupW` of its
word). -/
def _root_.StringDiagrams.ColourCupCapDiagrams.wordCup (x : l ⟶ m) :
    (𝟙 l : l ⟶ l).obj ⟶ (x ≫ P.dualHom D x).obj :=
  Diagram.cast (K.cupW l.region x.obj.word (Bicat.Hom.ok_region x)) rfl
    (Obj.ext x.start_eq.symm rfl)

/-- The nested caps `x* x ⟶ 1` of a 1-morphism `x` of `P.Bicat` (the diagram `K.capW` of its
word). -/
def _root_.StringDiagrams.ColourCupCapDiagrams.wordCap (x : l ⟶ m) :
    (P.dualHom D x ≫ x).obj ⟶ (𝟙 m : m ⟶ m).obj :=
  Diagram.cast (K.capW l.region x.obj.word (Bicat.Hom.ok_region x))
    (Obj.ext (Bicat.Hom.endR_region x) rfl) (by rw [Bicat.Hom.endR_region x]; rfl)

/-- The nested cups `1 ⟶ x* x` of a 1-morphism `x` of `P.Bicat` (the diagram `K.cup'W` of its
word). -/
def _root_.StringDiagrams.ColourCupCapDiagrams.wordCup' (x : l ⟶ m) :
    (𝟙 m : m ⟶ m).obj ⟶ (P.dualHom D x ≫ x).obj :=
  Diagram.cast (K.cup'W l.region x.obj.word (Bicat.Hom.ok_region x))
    (by rw [Bicat.Hom.endR_region x]; rfl) (Obj.ext (Bicat.Hom.endR_region x) rfl)

/-- The nested caps `x x* ⟶ 1` of a 1-morphism `x` of `P.Bicat` (the diagram `K.cap'W` of its
word). -/
def _root_.StringDiagrams.ColourCupCapDiagrams.wordCap' (x : l ⟶ m) :
    (x ≫ P.dualHom D x).obj ⟶ (𝟙 l : l ⟶ l).obj :=
  Diagram.cast (K.cap'W l.region x.obj.word (Bicat.Hom.ok_region x))
    (Obj.ext x.start_eq.symm rfl) rfl

@[simp] theorem layers_wordCup (x : l ⟶ m) :
    Diagram.layers (K.wordCup x) =
      Diagram.layers (K.cupW l.region x.obj.word (Bicat.Hom.ok_region x)) := rfl

@[simp] theorem layers_wordCap (x : l ⟶ m) :
    Diagram.layers (K.wordCap x) =
      Diagram.layers (K.capW l.region x.obj.word (Bicat.Hom.ok_region x)) := rfl

@[simp] theorem layers_wordCup' (x : l ⟶ m) :
    Diagram.layers (K.wordCup' x) =
      Diagram.layers (K.cup'W l.region x.obj.word (Bicat.Hom.ok_region x)) :=
  rfl

@[simp] theorem layers_wordCap' (x : l ⟶ m) :
    Diagram.layers (K.wordCap' x) =
      Diagram.layers (K.cap'W l.region x.obj.word (Bicat.Hom.ok_region x)) :=
  rfl

variable [S.IsEven]

/-- The cup and cap diagrams of chosen cups and caps. -/
def ColourCupsCaps.toDiagrams (Q : ColourCupsCaps P D) : ColourCupCapDiagrams S D :=
  ⟨Q.cup, Q.cap, Q.cup', Q.cap'⟩

/-! ### Classes of diagrams as 2-morphisms -/

section DiagLemmas

variable (P) {n : P.Bicat}

/-- Composition of classes of diagrams, as 2-morphisms of `P.Bicat`. -/
theorem Bicat.diag_comp_diag {x y z : l ⟶ m} (d : x.obj ⟶ y.obj) (e : y.obj ⟶ z.obj) :
    Bicat.homOf (x := x) (x' := y) (P.diag d) ≫ Bicat.homOf (x' := z) (P.diag e) =
      Bicat.homOf (P.diag (d ≫ e)) :=
  (P.diag_comp d e).symm

theorem Bicat.id_eq_diag (x : l ⟶ m) : 𝟙 x = (P.diag (𝟙 x.obj) : x ⟶ x) :=
  (P.diag_id x.obj).symm

theorem Bicat.eqToHom_eq_diag {x y : l ⟶ m} (h : x = y) :
    eqToHom h = (P.diag (eqToHom (congrArg Bicat.Hom.obj h)) : x ⟶ y) := by
  subst h; exact Bicat.id_eq_diag P x

/-- Left whiskering of the class of a diagram, as a 2-morphism of `P.Bicat`. -/
theorem Bicat.whiskerLeft_diag (x : l ⟶ m) {y y' : m ⟶ n} (d : y.obj ⟶ y'.obj) :
    x ◁ (P.diag d : y ⟶ y') =
      (P.diag (Diagram.lwhisker x.obj d (Bicat.Hom.composable x y) :
        (x ≫ y).obj ⟶ (x ≫ y').obj) : x ≫ y ⟶ x ≫ y') :=
  P.wL_diag_of_composable _ d _

/-- Right whiskering of the class of a diagram, as a 2-morphism of `P.Bicat`. -/
theorem Bicat.diag_whiskerRight {x x' : l ⟶ m} (d : x.obj ⟶ x'.obj) (y : m ⟶ n) :
    (P.diag d : x ⟶ x') ▷ y =
      (P.diag (Diagram.rwhisker d y.obj (Bicat.Hom.composable x y) :
        (x ≫ y).obj ⟶ (x' ≫ y).obj) : x ≫ y ⟶ x' ≫ y) :=
  P.wRAt_diag d _ _ _ _

end DiagLemmas

/-- The unit of the chosen biadjunction of a one-letter word is the class of the chosen cup. -/
theorem ColourCupsCaps.biadjunctions_left_unit (Q : ColourCupsCaps P D) (x : l ⟶ m) (c : S.Colour)
    (hx : x.obj.word = [c]) (h₁ : Obj.nil (S.colourSrc c) = (𝟙 l : l ⟶ l).obj)
    (h₂ : (⟨S.colourSrc c, [c, D.dual c]⟩ : Obj S) = (x ≫ P.dualHom D x).obj) :
    (Q.biadjunctions x c hx).left.unit = P.diag (Diagram.cast (Q.cup c) h₁ h₂) := rfl

theorem ColourCupsCaps.biadjunctions_left_counit (Q : ColourCupsCaps P D) (x : l ⟶ m)
    (c : S.Colour) (hx : x.obj.word = [c])
    (h₁ : (⟨S.colourTgt c, [D.dual c, c]⟩ : Obj S) = (P.dualHom D x ≫ x).obj)
    (h₂ : Obj.nil (S.colourTgt c) = (𝟙 m : m ⟶ m).obj) :
    (Q.biadjunctions x c hx).left.counit = P.diag (Diagram.cast (Q.cap c) h₁ h₂) := rfl

theorem ColourCupsCaps.biadjunctions_right_unit (Q : ColourCupsCaps P D) (x : l ⟶ m)
    (c : S.Colour) (hx : x.obj.word = [c]) (h₁ : Obj.nil (S.colourTgt c) = (𝟙 m : m ⟶ m).obj)
    (h₂ : (⟨S.colourTgt c, [D.dual c, c]⟩ : Obj S) = (P.dualHom D x ≫ x).obj) :
    (Q.biadjunctions x c hx).right.unit = P.diag (Diagram.cast (Q.cup' c) h₁ h₂) := rfl

theorem ColourCupsCaps.biadjunctions_right_counit (Q : ColourCupsCaps P D) (x : l ⟶ m)
    (c : S.Colour) (hx : x.obj.word = [c])
    (h₁ : (⟨S.colourSrc c, [c, D.dual c]⟩ : Obj S) = (x ≫ P.dualHom D x).obj)
    (h₂ : Obj.nil (S.colourSrc c) = (𝟙 l : l ⟶ l).obj) :
    (Q.biadjunctions x c hx).right.counit = P.diag (Diagram.cast (Q.cap' c) h₁ h₂) := rfl

theorem _root_.StringDiagrams.Biadjunction.congr_right_unit {B : Type*} [Bicategory B]
    {a b : B} {f f' : a ⟶ b} {g g' : b ⟶ a} (Q : f ⊣⊢ g) (hf : f = f') (hg : g = g') :
    (Q.congr hf hg).right.unit = Q.right.unit ≫ eqToHom (by rw [hf, hg]) := by
  subst hf hg; simp

theorem _root_.StringDiagrams.Biadjunction.congr_right_counit {B : Type*} [Bicategory B]
    {a b : B} {f f' : a ⟶ b} {g g' : b ⟶ a} (Q : f ⊣⊢ g) (hf : f = f') (hg : g = g') :
    (Q.congr hf hg).right.counit = eqToHom (by rw [hf, hg]) ≫ Q.right.counit := by
  subst hf hg; simp

/-- The unit of `x ⊣ x*` for a word `w` is the class of the nested cups (induction on `w`). -/
theorem biadjW_left_unit_eq_wordCup (Q : ColourCupsCaps P D) (w : List S.Colour) :
    ∀ {l m : P.Bicat} (x : l ⟶ m) (hx : x.obj.word = w),
      (biadjW Q.biadjunctions w x hx).left.unit = P.diag (Q.toDiagrams.wordCup x) := by
  induction w with
  | nil =>
    intro l m x hx
    refine P.diag_eq_of_layers_eq ?_
    simp [ColourCupCapDiagrams.layers_cupW_congr _ hx]
  | cons c w ih =>
    intro l m x hx
    rw [biadjW_cons_left_unit]
    have ih' : (biadj Q.biadjunctions (P.tailHom x c w hx)).left.unit = _ :=
      ih (P.tailHom x c w hx) rfl
    rw [ih']
    simp [bicategoricalComp, Strict.associator_eqToIso, Strict.leftUnitor_eqToIso,
      Strict.rightUnitor_eqToIso]
    rw [ColourCupsCaps.biadjunctions_left_unit Q (P.headHom x c w hx) c rfl
      (congrArg Obj.nil (Bicat.Hom.colourSrc_eq_of_word_eq_cons x hx))
      (Obj.ext (Bicat.Hom.colourSrc_eq_of_word_eq_cons x hx) rfl)]
    simp only [Bicat.whiskerLeft_diag, Bicat.diag_whiskerRight, Bicat.eqToHom_eq_diag,
      Bicat.id_eq_diag]
    simp only [Bicat.diag_comp_diag]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_lwhisker,
      Diagram.layers_rwhisker, Diagram.layers_eqToHom, Diagram.layers_id, List.map_nil,
      List.nil_append, List.append_nil, layers_wordCup,
      ColourCupCapDiagrams.layers_cupW_congr _ hx, ColourCupCapDiagrams.layers_cupW_cons,
      List.map_map]
    erw [Diagram.layers_id]
    simp only [List.map_nil, List.nil_append, List.append_nil]
    rfl

/-- The counit of `x ⊣ x*` for a word `w` is the class of the nested caps. -/
theorem biadjW_left_counit_eq_wordCap (Q : ColourCupsCaps P D) (w : List S.Colour) :
    ∀ {l m : P.Bicat} (x : l ⟶ m) (hx : x.obj.word = w),
      (biadjW Q.biadjunctions w x hx).left.counit = P.diag (Q.toDiagrams.wordCap x) := by
  induction w with
  | nil =>
    intro l m x hx
    refine P.diag_eq_of_layers_eq ?_
    simp [ColourCupCapDiagrams.layers_capW_congr _ hx]
  | cons c w ih =>
    intro l m x hx
    rw [biadjW_cons_left_counit]
    have ih' : (biadj Q.biadjunctions (P.tailHom x c w hx)).left.counit = _ :=
      ih (P.tailHom x c w hx) rfl
    rw [ih']
    simp [bicategoricalComp, Strict.associator_eqToIso, Strict.leftUnitor_eqToIso,
      Strict.rightUnitor_eqToIso]
    rw [ColourCupsCaps.biadjunctions_left_counit Q (P.headHom x c w hx) c rfl rfl rfl]
    simp only [Bicat.whiskerLeft_diag, Bicat.diag_whiskerRight, Bicat.eqToHom_eq_diag,
      Bicat.id_eq_diag]
    simp only [Bicat.diag_comp_diag]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_lwhisker,
      Diagram.layers_rwhisker, Diagram.layers_eqToHom, Diagram.layers_id, List.map_nil,
      List.nil_append, List.append_nil, layers_wordCap,
      ColourCupCapDiagrams.layers_capW_congr _ hx, ColourCupCapDiagrams.layers_capW_cons,
      List.map_map]
    erw [Diagram.layers_id]
    simp only [List.map_nil, List.nil_append]
    congr 1
    exact List.map_congr_left fun L _ =>
      Layer.ext (Bicat.Hom.endR_region (P.tailHom x c w hx)).symm rfl rfl rfl

/-- The unit of `x* ⊣ x` for a word `w` is the class of the nested cups `cup'W`. -/
theorem biadjW_right_unit_eq_wordCup' (Q : ColourCupsCaps P D) (w : List S.Colour) :
    ∀ {l m : P.Bicat} (x : l ⟶ m) (hx : x.obj.word = w),
      (biadjW Q.biadjunctions w x hx).right.unit = P.diag (Q.toDiagrams.wordCup' x) := by
  induction w with
  | nil =>
    intro l m x hx
    refine P.diag_eq_of_layers_eq ?_
    simp [ColourCupCapDiagrams.layers_cup'W_congr _ hx]
  | cons c w ih =>
    intro l m x hx
    have ih' : (biadj Q.biadjunctions (P.tailHom x c w hx)).right.unit = _ :=
      ih (P.tailHom x c w hx) rfl
    simp only [biadjW, Biadjunction.congr_right_unit, Biadjunction.comp_right,
      Bicategory.Adjunction.comp_unit, Bicategory.Adjunction.compUnit]
    erw [ih']
    simp [bicategoricalComp, Strict.associator_eqToIso, Strict.leftUnitor_eqToIso,
      Strict.rightUnitor_eqToIso]
    rw [ColourCupsCaps.biadjunctions_right_unit Q (P.headHom x c w hx) c rfl rfl rfl]
    simp only [Bicat.whiskerLeft_diag, Bicat.diag_whiskerRight, Bicat.eqToHom_eq_diag,
      Bicat.id_eq_diag]
    simp only [Bicat.diag_comp_diag]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_lwhisker,
      Diagram.layers_rwhisker, Diagram.layers_eqToHom, Diagram.layers_id, List.map_nil,
      List.nil_append, List.append_nil, layers_wordCup',
      ColourCupCapDiagrams.layers_cup'W_congr _ hx, ColourCupCapDiagrams.layers_cup'W_cons,
      List.map_map]
    erw [Diagram.layers_id]
    simp only [List.map_nil, List.nil_append]
    congr 1
    exact List.map_congr_left fun L _ =>
      Layer.ext (Bicat.Hom.endR_region (P.tailHom x c w hx)).symm rfl rfl rfl

/-- The counit of `x* ⊣ x` for a word `w` is the class of the nested caps `cap'W`. -/
theorem biadjW_right_counit_eq_wordCap' (Q : ColourCupsCaps P D) (w : List S.Colour) :
    ∀ {l m : P.Bicat} (x : l ⟶ m) (hx : x.obj.word = w),
      (biadjW Q.biadjunctions w x hx).right.counit = P.diag (Q.toDiagrams.wordCap' x) := by
  induction w with
  | nil =>
    intro l m x hx
    refine P.diag_eq_of_layers_eq ?_
    simp [ColourCupCapDiagrams.layers_cap'W_congr _ hx]
  | cons c w ih =>
    intro l m x hx
    have ih' : (biadj Q.biadjunctions (P.tailHom x c w hx)).right.counit = _ :=
      ih (P.tailHom x c w hx) rfl
    simp only [biadjW, Biadjunction.congr_right_counit, Biadjunction.comp_right,
      Bicategory.Adjunction.comp_counit, Bicategory.Adjunction.compCounit]
    erw [ih']
    simp [bicategoricalComp, Strict.associator_eqToIso, Strict.leftUnitor_eqToIso,
      Strict.rightUnitor_eqToIso]
    rw [ColourCupsCaps.biadjunctions_right_counit Q (P.headHom x c w hx) c rfl
      (Obj.ext (Bicat.Hom.colourSrc_eq_of_word_eq_cons x hx) rfl)
      (congrArg Obj.nil (Bicat.Hom.colourSrc_eq_of_word_eq_cons x hx))]
    simp only [Bicat.whiskerLeft_diag, Bicat.diag_whiskerRight, Bicat.eqToHom_eq_diag,
      Bicat.id_eq_diag]
    simp only [Bicat.diag_comp_diag]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_cast, Diagram.layers_lwhisker,
      Diagram.layers_rwhisker, Diagram.layers_eqToHom, Diagram.layers_id, List.map_nil,
      List.nil_append, List.append_nil, layers_wordCap',
      ColourCupCapDiagrams.layers_cap'W_congr _ hx, ColourCupCapDiagrams.layers_cap'W_cons,
      List.map_map]
    rfl

/-! ### The units and counits of the biadjunctions of words -/

section Units

variable (Q : ColourCupsCaps P D) (x : l ⟶ m)

/-- The unit of `x ⊣ x*` is the class of the nested cups of `x`. -/
theorem biadj_left_unit_eq_wordCup :
    (biadj Q.biadjunctions x).left.unit = P.diag (Q.toDiagrams.wordCup x) :=
  biadjW_left_unit_eq_wordCup Q _ x rfl

/-- The counit of `x ⊣ x*` is the class of the nested caps of `x`. -/
theorem biadj_left_counit_eq_wordCap :
    (biadj Q.biadjunctions x).left.counit = P.diag (Q.toDiagrams.wordCap x) :=
  biadjW_left_counit_eq_wordCap Q _ x rfl

/-- The unit of `x* ⊣ x` is the class of the nested cups `K.cup'W` of `x`. -/
theorem biadj_right_unit_eq_wordCup' :
    (biadj Q.biadjunctions x).right.unit = P.diag (Q.toDiagrams.wordCup' x) :=
  biadjW_right_unit_eq_wordCup' Q _ x rfl

/-- The counit of `x* ⊣ x` is the class of the nested caps `K.cap'W` of `x`. -/
theorem biadj_right_counit_eq_wordCap' :
    (biadj Q.biadjunctions x).right.counit = P.diag (Q.toDiagrams.wordCap' x) :=
  biadjW_right_counit_eq_wordCap' Q _ x rfl

/-! ### Zigzag identities for nested cups and caps -/

/-- The left zigzag identity for the nested cups and caps of `x ⊣ x*`, as an identity of diagram
classes. -/
theorem diag_leftZigzag_wordCup_wordCap :
    P.diag (P.leftZigzagD x (P.dualHom D x) (Q.toDiagrams.wordCup x) (Q.toDiagrams.wordCap x)) =
      𝟙 _ := by
  have h := (biadj Q.biadjunctions x).left.left_triangle
  rw [biadj_left_unit_eq_wordCup, biadj_left_counit_eq_wordCap, leftZigzag_diag] at h
  simp only [Category.assoc, Iso.cancel_iso_hom_left] at h
  have h' := (Iso.cancel_iso_inv_right _ _ _).1 (h.trans (Category.id_comp _).symm)
  exact h'

/-- The right zigzag identity for the nested cups and caps of `x ⊣ x*`. -/
theorem diag_rightZigzag_wordCup_wordCap :
    P.diag (P.rightZigzagD x (P.dualHom D x) (Q.toDiagrams.wordCup x) (Q.toDiagrams.wordCap x)) =
      𝟙 _ := by
  have h := (biadj Q.biadjunctions x).left.right_triangle
  rw [biadj_left_unit_eq_wordCup, biadj_left_counit_eq_wordCap, rightZigzag_diag] at h
  simp only [Category.assoc, Iso.cancel_iso_hom_left] at h
  have h' := (Iso.cancel_iso_inv_right _ _ _).1 (h.trans (Category.id_comp _).symm)
  exact h'

/-- The left zigzag identity for the nested cups and caps of `x* ⊣ x`. -/
theorem diag_leftZigzag_wordCup'_wordCap' :
    P.diag (P.leftZigzagD (P.dualHom D x) x (Q.toDiagrams.wordCup' x)
      (Q.toDiagrams.wordCap' x)) = 𝟙 _ := by
  have h := (biadj Q.biadjunctions x).right.left_triangle
  rw [biadj_right_unit_eq_wordCup', biadj_right_counit_eq_wordCap', leftZigzag_diag] at h
  simp only [Category.assoc, Iso.cancel_iso_hom_left] at h
  have h' := (Iso.cancel_iso_inv_right _ _ _).1 (h.trans (Category.id_comp _).symm)
  exact h'

/-- The right zigzag identity for the nested cups and caps of `x* ⊣ x`. -/
theorem diag_rightZigzag_wordCup'_wordCap' :
    P.diag (P.rightZigzagD (P.dualHom D x) x (Q.toDiagrams.wordCup' x)
      (Q.toDiagrams.wordCap' x)) = 𝟙 _ := by
  have h := (biadj Q.biadjunctions x).right.right_triangle
  rw [biadj_right_unit_eq_wordCup', biadj_right_counit_eq_wordCap', rightZigzag_diag] at h
  simp only [Category.assoc, Iso.cancel_iso_hom_left] at h
  have h' := (Iso.cancel_iso_inv_right _ _ _).1 (h.trans (Category.id_comp _).symm)
  exact h'

end Units

/-! ### Mates as rotated diagrams -/

section Mates

/-- The right rotation `x'* ⟶ x*` of a diagram `d : x ⟶ x'` between 1-morphisms of `P.Bicat`
(`ColourCupCapDiagrams.rotR`). -/
def _root_.StringDiagrams.ColourCupCapDiagrams.rotateR {x x' : l ⟶ m} (d : x.obj ⟶ x'.obj) :
    (P.dualHom D x').obj ⟶ (P.dualHom D x).obj :=
  K.rotR (Diagram.cast d (Obj.ext x.start_eq rfl) (Obj.ext x'.start_eq rfl))
    (Bicat.Hom.ok_region x) (Bicat.Hom.endR_region x)

/-- The left rotation `x'* ⟶ x*` of a diagram `d : x ⟶ x'` between 1-morphisms of `P.Bicat`
(`ColourCupCapDiagrams.rotL`). -/
def _root_.StringDiagrams.ColourCupCapDiagrams.rotateL {x x' : l ⟶ m} (d : x.obj ⟶ x'.obj) :
    (P.dualHom D x').obj ⟶ (P.dualHom D x).obj :=
  K.rotL (Diagram.cast d (Obj.ext x.start_eq rfl) (Obj.ext x'.start_eq rfl))
    (Bicat.Hom.ok_region x) (Bicat.Hom.endR_region x)

variable (Q : ColourCupsCaps P D) {x x' : l ⟶ m}

/-- **Rotation of diagrams with arbitrary boundaries.** The right mate of the class of a diagram
`d : x ⟶ x'`, for the biadjunctions of words, is the class of its right rotation by the nested
cups and caps. -/
theorem rightMate_biadj_diag (d : x.obj ⟶ x'.obj) :
    rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x') (P.diag d : x ⟶ x') =
      P.diag (Q.toDiagrams.rotateR d) := by
  rw [rightMate_diag _ _ _ (biadj_left_unit_eq_wordCup Q x) _
    (biadj_left_counit_eq_wordCap Q x') d]
  exact P.diag_eq_of_layers_eq (by simp [ColourCupCapDiagrams.rotateR])

/-- The left mate of the class of a diagram `d : x ⟶ x'`, for the biadjunctions of words, is the
class of its left rotation by the nested cups and caps. -/
theorem leftMate_biadj_diag (d : x.obj ⟶ x'.obj) :
    leftMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x') (P.diag d : x ⟶ x') =
      P.diag (Q.toDiagrams.rotateL d) := by
  rw [leftMate_diag _ _ _ (biadj_right_unit_eq_wordCup' Q x) _
    (biadj_right_counit_eq_wordCap' Q x') d]
  exact P.diag_eq_of_layers_eq (by simp [ColourCupCapDiagrams.rotateL])

/-- The class of a diagram is cyclic for the biadjunctions of words if and only if its right and
left rotations by the nested cups and caps have the same class. -/
theorem isCyclic_biadj_diag_iff (d : x.obj ⟶ x'.obj) :
    Biadjunction.IsCyclic (biadj Q.biadjunctions x) (biadj Q.biadjunctions x')
        (P.diag d : x ⟶ x') ↔
      P.diag (Q.toDiagrams.rotateR d) = P.diag (Q.toDiagrams.rotateL d) := by
  rw [Biadjunction.IsCyclic, rightMate_biadj_diag, leftMate_biadj_diag]

/-! ### Sliding diagrams along nested cups and caps -/

/-- Sliding a diagram `d : x ⟶ x'` along the nested cups of `x ⊣ x*` turns it into its right
rotation on the other strands. -/
theorem diag_wordCup_comp_rwhisker (d : x.obj ⟶ x'.obj) :
    P.diag (Q.toDiagrams.wordCup x ≫
        Diagram.rwhisker d (P.dualHom D x).obj (Bicat.Hom.composable x (P.dualHom D x))) =
      P.diag (Q.toDiagrams.wordCup x' ≫ Diagram.lwhisker x'.obj (Q.toDiagrams.rotateR d)
        (Bicat.Hom.composable x' (P.dualHom D x'))) := by
  have h := Biadjunction.left_unit_comp_whiskerRight (biadj Q.biadjunctions x)
    (biadj Q.biadjunctions x') (P.diag d : x ⟶ x')
  rw [biadj_left_unit_eq_wordCup, biadj_left_unit_eq_wordCup, rightMate_biadj_diag] at h
  simp only [Bicat.whiskerLeft_diag, Bicat.diag_whiskerRight, Bicat.diag_comp_diag] at h
  exact h

/-- Sliding a diagram `d : x ⟶ x'` along the nested caps of `x' ⊣ x'*` turns it into its right
rotation on the other strands. -/
theorem diag_lwhisker_comp_wordCap (d : x.obj ⟶ x'.obj) :
    P.diag (Diagram.lwhisker (P.dualHom D x').obj d (Bicat.Hom.composable (P.dualHom D x') x) ≫
        Q.toDiagrams.wordCap x') =
      P.diag (Diagram.rwhisker (Q.toDiagrams.rotateR d) x.obj
        (Bicat.Hom.composable (P.dualHom D x') x) ≫ Q.toDiagrams.wordCap x) := by
  have h := Biadjunction.whiskerLeft_comp_left_counit (biadj Q.biadjunctions x)
    (biadj Q.biadjunctions x') (P.diag d : x ⟶ x')
  rw [biadj_left_counit_eq_wordCap, biadj_left_counit_eq_wordCap, rightMate_biadj_diag] at h
  simp only [Bicat.whiskerLeft_diag, Bicat.diag_whiskerRight, Bicat.diag_comp_diag] at h
  exact h

/-- Sliding a diagram `d : x ⟶ x'` along the nested cups of `x* ⊣ x` turns it into its left
rotation on the other strands. -/
theorem diag_wordCup'_comp_lwhisker (d : x.obj ⟶ x'.obj) :
    P.diag (Q.toDiagrams.wordCup' x ≫
        Diagram.lwhisker (P.dualHom D x).obj d (Bicat.Hom.composable (P.dualHom D x) x)) =
      P.diag (Q.toDiagrams.wordCup' x' ≫ Diagram.rwhisker (Q.toDiagrams.rotateL d) x'.obj
        (Bicat.Hom.composable (P.dualHom D x') x')) := by
  have h := Biadjunction.right_unit_comp_whiskerLeft (biadj Q.biadjunctions x)
    (biadj Q.biadjunctions x') (P.diag d : x ⟶ x')
  rw [biadj_right_unit_eq_wordCup', biadj_right_unit_eq_wordCup', leftMate_biadj_diag] at h
  simp only [Bicat.whiskerLeft_diag, Bicat.diag_whiskerRight, Bicat.diag_comp_diag] at h
  exact h

/-- Sliding a diagram `d : x ⟶ x'` along the nested caps of `x'* ⊣ x'` turns it into its left
rotation on the other strands. -/
theorem diag_rwhisker_comp_wordCap' (d : x.obj ⟶ x'.obj) :
    P.diag (Diagram.rwhisker d (P.dualHom D x').obj (Bicat.Hom.composable x (P.dualHom D x')) ≫
        Q.toDiagrams.wordCap' x') =
      P.diag (Diagram.lwhisker x.obj (Q.toDiagrams.rotateL d)
        (Bicat.Hom.composable x (P.dualHom D x')) ≫ Q.toDiagrams.wordCap' x) := by
  have h := Biadjunction.whiskerRight_comp_right_counit (biadj Q.biadjunctions x)
    (biadj Q.biadjunctions x') (P.diag d : x ⟶ x')
  rw [biadj_right_counit_eq_wordCap', biadj_right_counit_eq_wordCap', leftMate_biadj_diag] at h
  simp only [Bicat.whiskerLeft_diag, Bicat.diag_whiskerRight, Bicat.diag_comp_diag] at h
  exact h

end Mates

/-! ### Cyclicity of generators as diagram relations -/

section Generators

/-- The right rotation `(cod g)* ⟶ (dom g)*` of a generator `g`, by the nested cups and caps of
its boundary words. -/
def _root_.StringDiagrams.ColourCupCapDiagrams.genRotR (g : S.Gen) (hg : S.GenValid g) :
    (⟨S.right g, D.dualWord (S.cod g)⟩ : Obj S) ⟶ ⟨S.right g, D.dualWord (S.dom g)⟩ :=
  K.rotR (genDiag g hg) hg.dom_ok hg.dom_end

/-- The left rotation `(cod g)* ⟶ (dom g)*` of a generator `g`, by the nested cups and caps of
its boundary words. -/
def _root_.StringDiagrams.ColourCupCapDiagrams.genRotL (g : S.Gen) (hg : S.GenValid g) :
    (⟨S.right g, D.dualWord (S.cod g)⟩ : Obj S) ⟶ ⟨S.right g, D.dualWord (S.dom g)⟩ :=
  K.rotL (genDiag g hg) hg.dom_ok hg.dom_end

omit [S.IsEven] in
theorem _root_.StringDiagrams.ColourCupCapDiagrams.layers_genRotR [S.IsEven] (g : S.Gen)
    (hg : S.GenValid g) :
    Diagram.layers (K.genRotR g hg) =
      (Diagram.layers (K.cupW (S.left g) (S.dom g) hg.dom_ok)).map
          (·.wl ⟨S.right g, D.dualWord (S.cod g)⟩) ++
        [⟨S.right g, D.dualWord (S.cod g), g, D.dualWord (S.dom g)⟩] ++
          (Diagram.layers (K.capW (S.left g) (S.cod g) hg.cod_ok)).map
            (·.wr (D.dualWord (S.dom g))) := by
  simp [ColourCupCapDiagrams.genRotR, genDiag, Layer.wl, Layer.wr]

omit [S.IsEven] in
theorem _root_.StringDiagrams.ColourCupCapDiagrams.layers_genRotL [S.IsEven] (g : S.Gen)
    (hg : S.GenValid g) :
    Diagram.layers (K.genRotL g hg) =
      (Diagram.layers (K.cup'W (S.left g) (S.dom g) hg.dom_ok)).map
          (·.wr (D.dualWord (S.cod g))) ++
        [⟨S.right g, D.dualWord (S.dom g), g, D.dualWord (S.cod g)⟩] ++
          (Diagram.layers (K.cap'W (S.left g) (S.cod g) hg.cod_ok)).map
            (·.wl ⟨S.right g, D.dualWord (S.dom g)⟩) := by
  simp [ColourCupCapDiagrams.genRotL, genDiag, Layer.wl, Layer.wr]

variable (Q : ColourCupsCaps P D)

/-- A generator is cyclic for the biadjunctions of its boundary words if and only if its right
and left rotations by the nested cups and caps have the same class. -/
theorem isCyclic_gen_iff (g : S.Gen) (hg : S.GenValid g) :
    Biadjunction.IsCyclic (biadj Q.biadjunctions (P.genDom g hg))
        (biadj Q.biadjunctions (P.genCod g hg)) (P.gen2 g hg) ↔
      P.diag (Q.toDiagrams.genRotR g hg) = P.diag (Q.toDiagrams.genRotL g hg) := by
  have e₁ : P.diag (Q.toDiagrams.rotateR (x := P.genDom g hg) (x' := P.genCod g hg)
      (genDiag g hg)) = P.diag (Q.toDiagrams.genRotR g hg) :=
    P.diag_eq_of_layers_eq (by
      simp only [ColourCupCapDiagrams.rotateR, ColourCupCapDiagrams.genRotR,
        ColourCupCapDiagrams.layers_rotR, Diagram.layers_cast]
      rfl)
  have e₂ : P.diag (Q.toDiagrams.rotateL (x := P.genDom g hg) (x' := P.genCod g hg)
      (genDiag g hg)) = P.diag (Q.toDiagrams.genRotL g hg) :=
    P.diag_eq_of_layers_eq (by
      simp only [ColourCupCapDiagrams.rotateL, ColourCupCapDiagrams.genRotL,
        ColourCupCapDiagrams.layers_rotL, Diagram.layers_cast]
      rfl)
  rw [← e₁, ← e₂]
  exact isCyclic_biadj_diag_iff Q (x := P.genDom g hg) (x' := P.genCod g hg) (genDiag g hg)

omit [S.IsEven] in
/-- A relation `r₁ - r₂` of `P` whose terms have the layers of the two diagrams `d₁` and `d₂`
identifies their classes. -/
theorem diag_eq_diag_of_rel {a b : Obj S} (d₁ d₂ : a ⟶ b) (i : P.Rel)
    {r₁ r₂ : P.dom i ⟶ P.cod i} (hi : P.rel i = LinDiagram.of r₁ - LinDiagram.of r₂)
    (hdom : P.dom i = a) (hcod : P.cod i = b) (h₁ : Diagram.layers r₁ = Diagram.layers d₁)
    (h₂ : Diagram.layers r₂ = Diagram.layers d₂) : P.diag d₁ = P.diag d₂ := by
  rw [P.diag_eq_of_layers_eq' _ r₁ hdom.symm hcod.symm h₁.symm,
    P.diag_eq_of_layers_eq' _ r₂ hdom.symm hcod.symm h₂.symm, P.diag_eq_of_rel i hi]

/-- **Cyclicity of a generator from a relation.** A relation `r₁ - r₂` of `P` whose terms are the
right and left rotations of the generator `g` makes `g` cyclic. -/
theorem isCyclic_gen_of_rel (g : S.Gen) (hg : S.GenValid g) (i : P.Rel)
    {r₁ r₂ : P.dom i ⟶ P.cod i} (hi : P.rel i = LinDiagram.of r₁ - LinDiagram.of r₂)
    (hdom : P.dom i = ⟨S.right g, D.dualWord (S.cod g)⟩)
    (hcod : P.cod i = ⟨S.right g, D.dualWord (S.dom g)⟩)
    (h₁ : Diagram.layers r₁ = Diagram.layers (Q.toDiagrams.genRotR g hg))
    (h₂ : Diagram.layers r₂ = Diagram.layers (Q.toDiagrams.genRotL g hg)) :
    Biadjunction.IsCyclic (biadj Q.biadjunctions (P.genDom g hg))
      (biadj Q.biadjunctions (P.genCod g hg)) (P.gen2 g hg) :=
  (isCyclic_gen_iff Q g hg).2 (diag_eq_diag_of_rel _ _ i hi hdom hcod h₁ h₂)

/-- **Rotation invariance from rotated generators.** If the two rotations of every generator have
the same class (for example, because their difference is a relation of `P`), then every
2-morphism of `P.Bicat` is cyclic. -/
theorem isCyclic_of_genRot
    (hrot : ∀ (g : S.Gen) (hg : S.GenValid g),
      P.diag (Q.toDiagrams.genRotR g hg) = P.diag (Q.toDiagrams.genRotL g hg))
    {x x' : l ⟶ m} (θ : x ⟶ x') :
    Biadjunction.IsCyclic (biadj Q.biadjunctions x) (biadj Q.biadjunctions x') θ :=
  isCyclic_of_generators _ (fun g hg => (isCyclic_gen_iff Q g hg).2 (hrot g hg)) θ

/-- The pivotal structure on `P.Bicat` given by the nested cups and caps, when the two rotations
of every generator have the same class. -/
def pivotalOfGenRot
    (hrot : ∀ (g : S.Gen) (hg : S.GenValid g),
      P.diag (Q.toDiagrams.genRotR g hg) = P.diag (Q.toDiagrams.genRotL g hg)) :
    StringDiagrams.Pivotal P.Bicat :=
  pivotalOfGenerators Q.biadjunctions (fun g hg => (isCyclic_gen_iff Q g hg).2 (hrot g hg))

end Generators

end Presentation

/-! ## The pivotal extension -/

namespace Pivotal

variable (E : S.ColourInvolution)

/-- The cups and caps of the pivotal extension, as diagrams: the cup and the cap of `c` for
`c ⊣ c*`, and the cup and the cap of `c*` (retyped along `c** = c`) for `c* ⊣ c`. -/
def cupCapDiagrams :
    ColourCupCapDiagrams (S.pivotal E.toColourDuality) E.toColourDuality.pivotal where
  cup c := cupD E.toColourDuality c
  cap c := capD E.toColourDuality c
  cup' c := Diagram.cast (cupD E.toColourDuality (E.dual c))
    (by rw [E.src_dual]; rfl) (Obj.ext (E.src_dual c) (by simp [E.dual_dual]))
  cap' c := Diagram.cast (capD E.toColourDuality (E.dual c))
    (Obj.ext (E.tgt_dual c) (by simp [E.dual_dual])) (by rw [E.tgt_dual]; rfl)

@[simp] theorem layers_cupCapDiagrams_cup (c : S.Colour) :
    Diagram.layers ((cupCapDiagrams E).cup c) = [⟨S.colourSrc c, [], .cup c, []⟩] := rfl

@[simp] theorem layers_cupCapDiagrams_cap (c : S.Colour) :
    Diagram.layers ((cupCapDiagrams E).cap c) = [⟨S.colourTgt c, [], .cap c, []⟩] := rfl

@[simp] theorem layers_cupCapDiagrams_cup' (c : S.Colour) :
    Diagram.layers ((cupCapDiagrams E).cup' c) =
      [⟨S.colourSrc (E.dual c), [], .cup (E.dual c), []⟩] := rfl

@[simp] theorem layers_cupCapDiagrams_cap' (c : S.Colour) :
    Diagram.layers ((cupCapDiagrams E).cap' c) =
      [⟨S.colourTgt (E.dual c), [], .cap (E.dual c), []⟩] := rfl

end Pivotal

@[simp] theorem Signature.ColourDuality.pivotal_dualWord (D : S.ColourDuality)
    (w : List S.Colour) : D.pivotal.dualWord w = D.dualWord w := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [ih]

namespace Presentation

variable {R : Type w} [CommRing R] [S.IsEven] (E : S.ColourInvolution)

omit [S.IsEven] in
theorem pivotalCupsCaps_toDiagrams [S.IsEven]
    (Q : Presentation.{w, v} (S.pivotal E.toColourDuality) R)
    (hz : Q.PivotalZigzags E.toColourDuality) :
    (Q.pivotalCupsCaps E hz).toDiagrams = Pivotal.cupCapDiagrams E := rfl

/-- **Rotation invariance in a presentation of the pivotal extension, from rotated generators.**
If the zigzag identities hold and the two rotations of every original generator (by the nested
cups and caps of `Pivotal.cupCapDiagrams`) have the same class, then every 2-morphism is
cyclic. -/
theorem pivotal_isCyclic_of_genRot (Q : Presentation.{w, v} (S.pivotal E.toColourDuality) R)
    (hz : Q.PivotalZigzags E.toColourDuality)
    (hrot : ∀ (g : S.Gen) (hg : (S.pivotal E.toColourDuality).GenValid (.gen g)),
      Q.diag ((Pivotal.cupCapDiagrams E).genRotR (.gen g) hg) =
        Q.diag ((Pivotal.cupCapDiagrams E).genRotL (.gen g) hg))
    {l m : Q.Bicat} {x x' : l ⟶ m} (θ : x ⟶ x') :
    Biadjunction.IsCyclic (biadj (pivotalBiadj E Q hz) x) (biadj (pivotalBiadj E Q hz) x') θ :=
  pivotal_isCyclic E Q hz (fun g hg => (isCyclic_gen_iff (Q.pivotalCupsCaps E hz) (.gen g) hg).2
    (hrot g hg)) θ

/-- The pivotal structure on the bicategory presented by a presentation of the pivotal extension
in which the zigzag identities hold and the two rotations of every original generator have the
same class. -/
def pivotalStructureOfGenRot (Q : Presentation.{w, v} (S.pivotal E.toColourDuality) R)
    (hz : Q.PivotalZigzags E.toColourDuality)
    (hrot : ∀ (g : S.Gen) (hg : (S.pivotal E.toColourDuality).GenValid (.gen g)),
      Q.diag ((Pivotal.cupCapDiagrams E).genRotR (.gen g) hg) =
        Q.diag ((Pivotal.cupCapDiagrams E).genRotL (.gen g) hg)) :
    StringDiagrams.Pivotal Q.Bicat :=
  pivotalStructure E Q hz (fun g hg => (isCyclic_gen_iff (Q.pivotalCupsCaps E hz) (.gen g) hg).2
    (hrot g hg))

/-- The cyclic pivotal extension of a presentation: the pivotal extension `P.pivotal` (the
relations of `P`, cups and caps with the zigzag relations), together with, for every original
generator `g`, the relation `rotR g = rotL g` identifying its two rotations by the nested cups
and caps of its boundary words (`ColourCupCapDiagrams.genRotR`, `genRotL`). -/
def pivotalCyclic (P : Presentation.{w, v} S R) :
    Presentation.{w, max u₁ u₂ v} (S.pivotal E.toColourDuality) R where
  Rel := (P.pivotal E.toColourDuality).Rel ⊕
    {g : S.Gen // (S.pivotal E.toColourDuality).GenValid (.gen g)}
  dom
    | .inl i => (P.pivotal E.toColourDuality).dom i
    | .inr g => ⟨(S.pivotal E.toColourDuality).right (.gen g.1),
        E.toColourDuality.pivotal.dualWord ((S.pivotal E.toColourDuality).cod (.gen g.1))⟩
  cod
    | .inl i => (P.pivotal E.toColourDuality).cod i
    | .inr g => ⟨(S.pivotal E.toColourDuality).right (.gen g.1),
        E.toColourDuality.pivotal.dualWord ((S.pivotal E.toColourDuality).dom (.gen g.1))⟩
  rel
    | .inl i => (P.pivotal E.toColourDuality).rel i
    | .inr g => LinDiagram.of (R := R) ((Pivotal.cupCapDiagrams E).genRotR (.gen g.1) g.2) -
        LinDiagram.of (R := R) ((Pivotal.cupCapDiagrams E).genRotL (.gen g.1) g.2)

variable (P : Presentation.{w, v} S R)

omit [S.IsEven] in
theorem pivotalCyclic_zigzags [S.IsEven] : (P.pivotalCyclic E).PivotalZigzags E.toColourDuality :=
  fun c =>
    ⟨((P.pivotalCyclic E).diag_eq_of_rel (i := Sum.inl (Sum.inr (Sum.inl c))) rfl).trans
      (diag_id _ _),
    ((P.pivotalCyclic E).diag_eq_of_rel (i := Sum.inl (Sum.inr (Sum.inr c))) rfl).trans
      (diag_id _ _)⟩

omit [S.IsEven] in
theorem pivotalCyclic_genRot [S.IsEven] (g : S.Gen)
    (hg : (S.pivotal E.toColourDuality).GenValid (.gen g)) :
    (P.pivotalCyclic E).diag ((Pivotal.cupCapDiagrams E).genRotR (.gen g) hg) =
      (P.pivotalCyclic E).diag ((Pivotal.cupCapDiagrams E).genRotL (.gen g) hg) :=
  (P.pivotalCyclic E).diag_eq_of_rel (i := Sum.inr ⟨g, hg⟩) rfl

/-- **Rotation invariance for the cyclic pivotal extension**: every 2-morphism of the presented
bicategory is cyclic for the biadjunctions of words given by the cups and caps. -/
theorem pivotalCyclic_isCyclic {l m : (P.pivotalCyclic E).Bicat} {x x' : l ⟶ m} (θ : x ⟶ x') :
    Biadjunction.IsCyclic (biadj (pivotalBiadj E (P.pivotalCyclic E) (P.pivotalCyclic_zigzags E)) x)
      (biadj (pivotalBiadj E (P.pivotalCyclic E) (P.pivotalCyclic_zigzags E)) x') θ :=
  pivotal_isCyclic_of_genRot E _ _ (P.pivotalCyclic_genRot E) θ

/-- The pivotal structure on the bicategory presented by the cyclic pivotal extension. -/
def pivotalCyclicStructure : StringDiagrams.Pivotal (P.pivotalCyclic E).Bicat :=
  pivotalStructureOfGenRot E _ (P.pivotalCyclic_zigzags E) (P.pivotalCyclic_genRot E)

end Presentation

