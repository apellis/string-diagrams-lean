import StringDiagrams.Bicategory
import StringDiagrams.Interpretation

/-!
# Test example: bubbles whose value depends on the region

A small test of the region-aware (2-categorical) part of the library. It is loosely modelled
on the `sl₂` case of the 2-category of Khovanov–Lauda (arXiv:0807.3250), whose regions are
labelled by weights, but it is a toy example and **not** a formalization of that 2-category:
there is only one orientation of cups and caps, no dots, no crossings, and the value of a
bubble is an arbitrary function of its region.

## Conventions

Regions are integers (weights). Strands carry the weight of the region on their right in the
usual right-to-left reading of 1-morphisms, and our words are read from left to right:

* `E μ` has the region `μ + 2` on its left and `μ` on its right (`E 1_μ = 1_{μ+2} E 1_μ`);
* `F μ` has the region `μ` on its left and `μ + 2` on its right (`F 1_{μ+2} = 1_μ F 1_{μ+2}`).

Both are indexed by the smaller of their two weights, so that all region equalities below
hold by definition. The generators are the cup `cup μ : 1_{μ+2} ⟶ E F` and the cap
`cap μ : E F ⟶ 1_{μ+2}` (the word `E μ, F μ`, in the region `μ + 2`). The closed diagram
`bubble μ = cup μ ≫ cap μ` is a bubble in the region `μ + 2` enclosing the region `μ`.

Given `c : ℤ → R`, the presentation `pres c` imposes the single family of relations
`bubble μ = c (μ + 2) • 1`: a bubble in the region `λ` evaluates to `c λ`.

## Results

* `diag_whisker_bubble`: a bubble at any (whiskered) position evaluates to the value of its
  region.
* `interleaved`: on the strand `E (μ + 2)` (regions `μ + 4 | μ + 2`), the diagram with a
  bubble on each side of the strand, drawn with interleaved heights (left cup, right cup,
  left cap, right cap), equals `c (μ + 4) c (μ + 2) • 1`. The proof moves the right cup above
  the left cap with the interchange law for general regions
  (`Presentation.diag_swap_layers_of_composable`), then evaluates each bubble in its own
  region.
* `leftBubble_eq`, `rightBubble_eq`: in the presented bicategory `(pres c).Bicat`, the bubble
  to the left of `E (μ + 2)` (`bubble ▷ E`) is `c (μ + 4)` and the bubble to the right
  (`E ◁ bubble`) is `c (μ + 2)`.
* `rep`: an `R`-linear functor to `ModuleCat R` sending every layer to its scalar, obtained by
  soundness; `smul_id_injective`: scalars are faithfully represented on every object.
* `leftBubble_ne_rightBubble`: the two bubbles, which have the same shape but lie in
  different regions, are different morphisms whenever `c (μ + 4) ≠ c (μ + 2)`; for example
  for `R = ℤ` and `c = id` (`leftBubble_ne_rightBubble_int`).
-/

noncomputable section

namespace StringDiagrams.WeightedBubbles

open CategoryTheory Bicategory

universe u

/-- Strand colours, indexed by the smaller of their two regions. -/
inductive Colour
  /-- `E μ`: region `μ + 2` on the left, `μ` on the right. -/
  | E (μ : ℤ)
  /-- `F μ`: region `μ` on the left, `μ + 2` on the right. -/
  | F (μ : ℤ)

/-- Generators: cups and caps of the word `E μ, F μ` in the region `μ + 2`. -/
inductive Gen
  /-- `cup μ : [] ⟶ [E μ, F μ]`. -/
  | cup (μ : ℤ)
  /-- `cap μ : [E μ, F μ] ⟶ []`. -/
  | cap (μ : ℤ)

/-- The signature: regions are weights. -/
def sig : Signature where
  Region := ℤ
  Colour := Colour
  colourSrc
    | .E μ => μ + 2
    | .F μ => μ
  colourTgt
    | .E μ => μ
    | .F μ => μ + 2
  Gen := Gen
  dom
    | .cup _ => []
    | .cap μ => [.E μ, .F μ]
  cod
    | .cup μ => [.E μ, .F μ]
    | .cap _ => []
  left
    | .cup μ => μ + 2
    | .cap μ => μ + 2
  right
    | .cup μ => μ + 2
    | .cap μ => μ + 2

instance : sig.IsEven := ⟨fun _ => rfl⟩

/-- The empty word in the region `l`. -/
abbrev vac (l : ℤ) : Obj sig := Obj.nil (S := sig) l

/-- The single strand `E (μ + 2)`, from the region `μ + 4` to the region `μ + 2`. -/
def strandE (μ : ℤ) : Obj sig := ⟨(μ + 2 + 2 : ℤ), [Colour.E (μ + 2)]⟩

/-- A generator with the given strands on its left and right, starting in region `r`. -/
abbrev lay (r : ℤ) (l : List Colour) (g : Gen) (rt : List Colour) : Layer sig := ⟨r, l, g, rt⟩

/-- Validity of the layers used below: all region conditions hold by definition. -/
macro "valid_layer" : tactic =>
  `(tactic| (constructor <;> simp [sig, Signature.ok, Signature.endR]))

/-- The bubble `cup μ ≫ cap μ` in the region `μ + 2`. -/
def bubble (μ : ℤ) : vac (μ + 2) ⟶ vac (μ + 2) :=
  Diagram.mk [lay (μ + 2) [] (.cup μ) [], lay (μ + 2) [] (.cap μ) []]
    ⟨by valid_layer, rfl, by valid_layer, rfl, rfl⟩

variable {R : Type u} [CommRing R] (c : ℤ → R)

/-- The relations `bubble μ = c (μ + 2) • 1`. -/
def pres : Presentation sig R where
  Rel := ℤ
  dom μ := vac (μ + 2)
  cod μ := vac (μ + 2)
  rel μ := LinDiagram.of (bubble μ) - c (μ + 2) • LinDiagram.of (𝟙 _)

/-! ## Evaluating bubbles -/

/-- A bubble at any whiskered position evaluates to the value of its region. -/
theorem diag_whisker_bubble (μ : ℤ) (u : Obj sig) (v : List sig.Colour)
    (hw : (vac (μ + 2)).WhiskerOK u v) :
    (pres c).diag (Diagram.whisker (bubble μ) u v hw) = c (μ + 2) • 𝟙 _ := by
  have key := (pres c).lin_rel μ u v hw
  have hrel : (pres c).rel μ = LinDiagram.of (bubble μ) - c (μ + 2) • LinDiagram.of (𝟙 _) := rfl
  rw [hrel] at key
  simp only [LinDiagram.whisker_sub, LinDiagram.whisker_smul, LinDiagram.whisker_of,
    Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, sub_eq_zero] at key
  rw [key]
  exact congrArg (fun f => c (μ + 2) • f) ((pres c).diag_id _)

theorem diag_bubble (μ : ℤ) : (pres c).diag (bubble μ) = c (μ + 2) • 𝟙 _ :=
  diag_whisker_bubble c μ (vac (μ + 2)) [] ⟨trivial, rfl, trivial⟩

/-- The layers of the interleaved diagram on the strand `E (μ + 2)`. -/
abbrev leftCup (μ : ℤ) : Layer sig := lay (μ + 2 + 2) [] (.cup (μ + 2)) [.E (μ + 2)]
/-- The right cup, with the strands of the left bubble to its left. -/
abbrev rightCup (μ : ℤ) : Layer sig := lay (μ + 2 + 2) [.E (μ + 2), .F (μ + 2), .E (μ + 2)] (.cup μ) []
/-- The left cap, with the strands of the right bubble to its right. -/
abbrev leftCap (μ : ℤ) : Layer sig := lay (μ + 2 + 2) [] (.cap (μ + 2)) [.E (μ + 2), .E μ, .F μ]
/-- The right cap. -/
abbrev rightCap (μ : ℤ) : Layer sig := lay (μ + 2 + 2) [.E (μ + 2)] (.cap μ) []
/-- The left cap on its own boundary. -/
abbrev capL (μ : ℤ) : Layer sig := lay (μ + 2 + 2) [] (.cap (μ + 2)) []
/-- The right cup on its own boundary. -/
abbrev cupR (μ : ℤ) : Layer sig := lay (μ + 2 + 2) [.E (μ + 2)] (.cup μ) []

theorem leftCup_valid (μ : ℤ) : (leftCup μ).Valid := by valid_layer
theorem rightCup_valid (μ : ℤ) : (rightCup μ).Valid := by valid_layer
theorem leftCap_valid (μ : ℤ) : (leftCap μ).Valid := by valid_layer
theorem rightCap_valid (μ : ℤ) : (rightCap μ).Valid := by valid_layer
theorem capL_valid (μ : ℤ) : (capL μ).Valid := by valid_layer
theorem cupR_valid (μ : ℤ) : (cupR μ).Valid := by valid_layer

/-- The interleaved diagram on the strand `E (μ + 2)`: left cup, right cup, left cap, right
cap (from bottom to top). -/
def interleavedDiagram (μ : ℤ) : strandE μ ⟶ strandE μ :=
  Diagram.mk [leftCup μ, rightCup μ, leftCap μ, rightCap μ]
    ⟨leftCup_valid μ, rfl, rightCup_valid μ, rfl, leftCap_valid μ, rfl, rightCap_valid μ, rfl, rfl⟩

/-- Two bubbles on either side of a strand, drawn at interleaved heights, evaluate to the
product of the values of their two (different) regions. The proof uses the interchange law
for general regions. -/
theorem interleaved (μ : ℤ) :
    (pres c).diag (interleavedDiagram μ) = (c (μ + 2 + 2) * c (μ + 2)) • 𝟙 _ := by
  have hL := capL_valid μ
  have hM := cupR_valid μ
  have hc : (capL μ).dom.Composable (cupR μ).dom := ⟨hL.wf_dom, rfl, hM.wf_dom⟩
  have h₁ : (capL μ).cod.Composable (cupR μ).dom := hc.map_left (Diagram.ofLayer _ hL)
  have h₂ : (capL μ).dom.Composable (cupR μ).cod := hc.map_right (Diagram.ofLayer _ hM)
  have swap := (pres c).diag_swap_layers_of_composable _ _ hL hM hc h₁ h₂
  have h0 : ∀ N : Layer sig, Diagram.oddCountList [N] = 0 := fun N => by
    simp [Diagram.oddCountList, Signature.IsEven.odd_eq_false]
  rw [h0, h0, mul_zero, pow_zero, one_smul] at swap
  have hw₁ : (vac (μ + 2 + 2)).WhiskerOK (vac (μ + 2 + 2)) [.E (μ + 2)] :=
    ⟨trivial, rfl, ⟨rfl, trivial⟩⟩
  have hw₂ : (vac (μ + 2)).WhiskerOK (strandE μ) [] := ⟨⟨rfl, trivial⟩, rfl, trivial⟩
  have e₁ : (pres c).diag (interleavedDiagram μ) =
      (pres c).diag (Diagram.ofLayer _ (leftCup_valid μ)) ≫
        (pres c).diag (Diagram.lwhisker (capL μ).dom (Diagram.ofLayer _ hM) hc ≫
          Diagram.rwhisker (Diagram.ofLayer _ hL) (cupR μ).cod h₂) ≫
        (pres c).diag (Diagram.ofLayer _ (rightCap_valid μ)) := by
    rw [← Presentation.diag_comp, ← Presentation.diag_comp]; rfl
  have e₂ : (pres c).diag (Diagram.ofLayer _ (leftCup_valid μ)) ≫
        (pres c).diag (Diagram.rwhisker (Diagram.ofLayer _ hL) (cupR μ).dom hc ≫
          Diagram.lwhisker (capL μ).cod (Diagram.ofLayer _ hM) h₁) ≫
        (pres c).diag (Diagram.ofLayer _ (rightCap_valid μ)) =
      (pres c).diag (Diagram.whisker (bubble (μ + 2)) (vac (μ + 2 + 2)) [.E (μ + 2)] hw₁) ≫
        (pres c).diag (Diagram.whisker (bubble μ) (strandE μ) [] hw₂) := by
    rw [← Presentation.diag_comp, ← Presentation.diag_comp, ← Presentation.diag_comp]; rfl
  rw [e₁, ← swap, e₂, diag_whisker_bubble, diag_whisker_bubble, Linear.smul_comp,
    Linear.comp_smul, Category.id_comp, smul_smul]
  rfl

/-! ## Bubbles on either side of a strand, in the presented bicategory -/

/-- The region `l` as an object of the presented bicategory. -/
abbrev reg (l : ℤ) : (pres c).Bicat := ⟨l⟩

/-- The strand `E (μ + 2)` as a 1-morphism from `μ + 4` to `μ + 2`. -/
def E (μ : ℤ) : reg c (μ + 2 + 2) ⟶ reg c (μ + 2) :=
  ⟨strandE μ, rfl, ⟨rfl, trivial⟩, rfl⟩

/-- The bubble as an endomorphism of the identity 1-morphism of `μ + 2`. -/
def bubble₂ (μ : ℤ) : 𝟙 (reg c (μ + 2)) ⟶ 𝟙 (reg c (μ + 2)) := (pres c).diag (bubble μ)

/-- The bubble to the left of the strand `E (μ + 2)`, in the region `μ + 4`. -/
def leftBubble (μ : ℤ) : (pres c).obj (strandE μ) ⟶ (pres c).obj (strandE μ) :=
  bubble₂ c (μ + 2) ▷ E c μ

/-- The bubble to the right of the strand `E (μ + 2)`, in the region `μ + 2`. -/
def rightBubble (μ : ℤ) : (pres c).obj (strandE μ) ⟶ (pres c).obj (strandE μ) :=
  E c μ ◁ bubble₂ c μ

theorem leftBubble_eq (μ : ℤ) : leftBubble c μ = c (μ + 2 + 2) • 𝟙 _ := by
  have h := (pres c).wRAt_id (a := vac (μ + 2 + 2)) (r := μ + 2 + 2) rfl (strandE μ)
    ⟨rfl, trivial⟩
  rw [leftBubble, Presentation.Bicat.whiskerRight_eq, bubble₂, diag_bubble,
    Presentation.wRAt_smul]
  exact congrArg (fun f => c (μ + 2 + 2) • f) h

theorem rightBubble_eq (μ : ℤ) : rightBubble c μ = c (μ + 2) • 𝟙 _ := by
  have h := (pres c).wL_id_of_composable (a := strandE μ) (b := vac (μ + 2))
    ⟨⟨rfl, trivial⟩, rfl, trivial⟩
  rw [rightBubble, Presentation.Bicat.whiskerLeft_eq, bubble₂, diag_bubble,
    Presentation.wL_smul]
  exact congrArg (fun f => c (μ + 2) • f) h

/-! ## A scalar interpretation -/

/-- The scalar of a generator: `1` for a cup, the value of its region for a cap. -/
def scal : Gen → R
  | .cup _ => 1
  | .cap μ => c (μ + 2)

/-- Every object goes to `R`, every layer to multiplication by the scalar of its generator. -/
def interp : Interpretation sig (ModuleCat.{u} R) where
  obj _ := ModuleCat.of R R
  layer L _ := scal c L.gen • 𝟙 (ModuleCat.of R R)

theorem interp_mapChain {a b : Obj sig} (ls : List (Layer sig)) (h : Chain a ls b) :
    (interp c).mapChain a ls b h = (ls.map fun L => scal c L.gen).prod • 𝟙 (ModuleCat.of R R) := by
  induction ls generalizing a with
  | nil =>
    simp only [Interpretation.mapChain, List.map_nil, List.prod_nil, one_smul]
    exact eqToHom_refl _ _
  | cons L ls ih =>
    simp only [Interpretation.mapChain, ih, List.map_cons, List.prod_cons]
    rw [eqToHom_refl _ _, Category.id_comp]
    simp only [interp, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
      mul_comm]

theorem interp_map {a b : Obj sig} (d : a ⟶ b) :
    (interp c).functor.map d =
      ((Diagram.layers d).map fun L => scal c L.gen).prod • 𝟙 (ModuleCat.of R R) :=
  interp_mapChain c _ _

theorem interp_respects : (pres c).Respects (interp c).functor where
  rel μ u v hw := by
    simp only [pres, LinDiagram.whisker_sub, LinDiagram.whisker_smul, LinDiagram.whisker_of,
      Functor.map_sub, Functor.map_smul, freeLift_map_of, interp_map, Diagram.layers_whisker,
      Diagram.whisker_id, Diagram.layers_id, bubble, Diagram.layers_mk, List.map_map,
      Function.comp_def, Layer.whisker, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, scal, mul_one, one_mul, smul_smul, sub_self]
  interchange x hx u v hw := by
    have hs : ((x.sign : ℤ) : R) = 1 := by
      simp [InterchangeData.sign, Signature.IsEven.odd_eq_false]
    simp only [InterchangeData.rel, hs, one_smul, LinDiagram.whisker_sub, LinDiagram.whisker_of,
      Functor.map_sub, freeLift_map_of, interp_map, Diagram.layers_whisker,
      InterchangeData.ghDiagram, InterchangeData.hgDiagram, Diagram.layers_mk, List.map_map,
      Function.comp_def, Layer.whisker, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, InterchangeData.gh₁, InterchangeData.gh₂, InterchangeData.hg₁,
      InterchangeData.hg₂, mul_one]
    rw [mul_comm, sub_self]

/-- The scalar representation of the presented category. -/
def rep : (pres c).Presented ⥤ ModuleCat.{u} R := (pres c).lift (interp_respects c)

instance : (rep c).Linear R := (pres c).lift_linear (interp_respects c)

/-- Scalar multiples of identities are faithfully represented. -/
theorem smul_id_injective (a : Obj sig) {x y : R}
    (h : x • 𝟙 ((pres c).obj a) = y • 𝟙 ((pres c).obj a)) : x = y := by
  have h' := congrArg (fun f => ((rep c).map f).hom (1 : R)) h
  simpa [Functor.map_smul, rep] using h'

/-- The bubbles on the two sides of the strand `E (μ + 2)` have the same shape but lie in
different regions; they differ whenever the values of the two regions differ. -/
theorem leftBubble_ne_rightBubble (μ : ℤ) (hc : c (μ + 2 + 2) ≠ c (μ + 2)) :
    leftBubble c μ ≠ rightBubble c μ := by
  intro h
  rw [leftBubble_eq, rightBubble_eq] at h
  exact hc (smul_id_injective c _ h)

/-- For `R = ℤ` and bubbles evaluating to the weight of their region, the two bubbles
differ. -/
theorem leftBubble_ne_rightBubble_int (μ : ℤ) :
    leftBubble (R := ℤ) id μ ≠ rightBubble id μ :=
  leftBubble_ne_rightBubble id μ (by simp)

end StringDiagrams.WeightedBubbles

end
