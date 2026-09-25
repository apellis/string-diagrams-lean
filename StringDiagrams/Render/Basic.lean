import StringDiagrams.DSL.Basic

/-!
# Layout of layered diagrams for drawing

This file computes a planar picture of a layered diagram: a list of drawing primitives in
integer coordinates, independent of the output format. The SVG and TikZ back ends
(`StringDiagrams.Render.SVG`, `StringDiagrams.Render.TikZ`) only translate primitives.

Drawing is presentation only. Nothing in this file (or in the back ends) is used as
evidence for any statement about diagrams; equalities of diagrams are established by
proofs about `StringDiagrams.Diagram` and presentations.

## Layout

Coordinates are integers in hundredths of a unit, with `y` pointing up; one unit is the
distance between neighbouring strands and the height of a slab.

* Layer `j` occupies the horizontal slab `j ≤ y ≤ j + 1`, so layer `0` is at the bottom.
* On each boundary, the strands sit at `x = 1, 2, …, n`.
* Within the slab of a layer `id_u ⊗ g ⊗ id_v`, the strands of `u` are vertical, the
  generator `g` occupies the columns `|u| + 1, …, |u| + m` (where `m` is the width of its
  glyph) and a band of heights (`Glyph.extent`), and the strands of `v` are moved by cubic
  Bézier curves (with vertical tangents) from their positions on the bottom boundary to the
  columns right of the glyph below that band, and from there to their positions on the top
  boundary above it.
* The label of the leftmost region of each slab is drawn at `x = 0.4`, when non-empty.
* Strand labels (if any) are drawn below the bottom and above the top boundary.

A diagram without layers is drawn as one slab of vertical strands.
-/

namespace StringDiagrams

universe u₀ u₁ u₂

namespace Render

/-- A colour given by its red, green and blue components (`0`–`255`). -/
structure RGB where
  /-- Red component. -/
  r : Nat
  /-- Green component. -/
  g : Nat
  /-- Blue component. -/
  b : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Black. -/
def RGB.black : RGB := ⟨0, 0, 0⟩

/-- How a generator is drawn. A glyph that does not fit the boundary of the generator is
replaced by a labelled box (`Glyph.fit`). -/
inductive Glyph
  /-- A filled dot on one strand (bottom and top boundary of length one). -/
  | dot
  /-- Two strands crossing (bottom and top boundary of length two). -/
  | crossing
  /-- A cup: empty bottom boundary, top boundary of length two. -/
  | cup
  /-- A cap: bottom boundary of length two, empty top boundary. -/
  | cap
  /-- A rectangle with a text label, for any boundary. -/
  | box (label : String)
  deriving Repr, Inhabited, DecidableEq

/-- The two-digit decimal representation of a number below `100`. -/
def twoDigits (n : Nat) : String := if n < 10 then "0" ++ toString n else toString n

/-- Print `n / 100` as a decimal number with at most two decimals (no trailing zeros). -/
def fmtHundredths (n : Int) : String :=
  let sign := if n < 0 then "-" else ""
  let a := n.natAbs
  let q := a / 100
  let r := a % 100
  if r = 0 then sign ++ toString q
  else
    let frac := twoDigits r
    let frac := if frac.endsWith "0" then frac.dropRight 1 else frac
    sign ++ toString q ++ "." ++ frac

/-- Escape the characters that are special in LaTeX text. -/
def texEscape (s : String) : String :=
  String.join <| s.toList.map fun c =>
    match c with
    | '\\' => "\\textbackslash{}"
    | '{' => "\\{"
    | '}' => "\\}"
    | '$' => "\\$"
    | '&' => "\\&"
    | '#' => "\\#"
    | '%' => "\\%"
    | '_' => "\\_"
    | '^' => "\\textasciicircum{}"
    | '~' => "\\textasciitilde{}"
    | c => c.toString

end Render

open Render

/-- How to draw the generators, strands and regions of a signature.

* `glyph g`: the glyph of a generator (falling back to a box labelled with the generator's
  name when the glyph does not fit its boundary);
* `strandColour c`: the stroke colour of strands of colour `c`;
* `regionLabel r`: the text drawn in region `r` (empty for no label);
* `strandLabel c`: the text drawn at the ends of boundary strands of colour `c` (empty for
  no label);
* `texText`: how plain label text is turned into TeX for TikZ output (by default, special
  characters are escaped; a style may instead map labels to math, e.g. `λ ↦ $\lambda$`). -/
class DrawStyle (S : Signature.{u₀, u₁, u₂}) where
  /-- The glyph of a generator. -/
  glyph : S.Gen → Glyph
  /-- The stroke colour of a strand. -/
  strandColour : S.Colour → RGB := fun _ => RGB.black
  /-- The label of a region (empty for none). -/
  regionLabel : S.Region → String := fun _ => ""
  /-- The label drawn at the ends of boundary strands (empty for none). -/
  strandLabel : S.Colour → String := fun _ => ""
  /-- Conversion of label text to TeX. -/
  texText : String → String := texEscape

namespace Render

/-! ## Geometry -/

/-- A point, in hundredths of a unit, `y` pointing up. -/
structure Pt where
  /-- Abscissa. -/
  x : Int
  /-- Ordinate (upwards). -/
  y : Int
  deriving Repr, Inhabited, DecidableEq

/-- A segment of a path. -/
inductive Seg
  /-- A straight segment to a point. -/
  | line (p : Pt)
  /-- A cubic Bézier segment with control points `c₁`, `c₂` to the point `p`. -/
  | curve (c₁ c₂ p : Pt)
  deriving Repr, Inhabited

/-- Drawing primitives. -/
inductive Prim
  /-- A stroked path. -/
  | path (colour : RGB) (start : Pt) (segs : List Seg)
  /-- A filled disc of radius `r`. -/
  | disc (colour : RGB) (centre : Pt) (r : Int)
  /-- A rectangle with lower left corner `p` and upper right corner `q`, white fill. -/
  | rect (p q : Pt)
  /-- A text label centred at a point. -/
  | text (p : Pt) (s : String)
  deriving Repr, Inhabited

/-- A picture: primitives, drawn in order, and a bounding box. -/
structure Picture where
  /-- Lower left corner of the bounding box. -/
  lo : Pt
  /-- Upper right corner of the bounding box. -/
  hi : Pt
  /-- Primitives, drawn in order (later ones on top). -/
  prims : List Prim
  deriving Repr, Inhabited

/-- Unit length (strand spacing and slab height), in hundredths. -/
def unit : Int := 100

/-- The abscissa of the strand in column `p` (counting from `0`). -/
def colX (p : Nat) : Int := (p + 1 : Int) * unit

/-- `(κ * v)` for the circle constant `κ ≈ 0.5523` of cubic quarter-ellipses. -/
def kappa (v : Int) : Int := v * 5523 / 10000

/-- A vertical segment. -/
def vline (col : RGB) (x y₀ y₁ : Int) : Prim := .path col ⟨x, y₀⟩ [.line ⟨x, y₁⟩]

/-- A curve from `(x₀, y₀)` to `(x₁, y₁)` with vertical tangents at both ends (a straight
segment when `x₀ = x₁`). -/
def sCurve (x₀ y₀ x₁ y₁ : Int) : Seg :=
  if x₀ = x₁ then .line ⟨x₁, y₁⟩
  else .curve ⟨x₀, (y₀ + y₁) / 2⟩ ⟨x₁, (y₀ + y₁) / 2⟩ ⟨x₁, y₁⟩

/-- Whether a glyph fits a generator with bottom boundary of length `d` and top boundary of
length `c`. -/
def Glyph.fits : Glyph → Nat → Nat → Bool
  | .dot, d, c => d == 1 && c == 1
  | .crossing, d, c => d == 2 && c == 2
  | .cup, d, c => d == 0 && c == 2
  | .cap, d, c => d == 2 && c == 0
  | .box _, _, _ => true

/-- The glyph actually drawn: the requested one if it fits, otherwise a box labelled
`fallback`. -/
def Glyph.fit (gl : Glyph) (fallback : String) (d c : Nat) : Glyph :=
  if gl.fits d c then gl else .box fallback

/-- The number of columns occupied by a glyph. -/
def Glyph.width : Glyph → Nat → Nat → Nat
  | .dot, _, _ => 1
  | .crossing, _, _ => 2
  | .cup, _, _ => 2
  | .cap, _, _ => 2
  | .box _, d, c => max (max d c) 1

/-- The vertical extent of a glyph within its slab, in hundredths of the slab height. The
strands to the right of the generator are moved below and above this extent. -/
def Glyph.extent : Glyph → Int × Int
  | .dot => (0, 100)
  | .crossing => (0, 100)
  | .cup => (40, 100)
  | .cap => (0, 60)
  | .box _ => (30, 70)

/-- A cup with legs at `x₀ < x₁` from height `y₁` down to its lowest point at height `yb`,
as two quarter-ellipses with colours `c₀` and `c₁`. -/
def cupPrims (c₀ c₁ : RGB) (x₀ x₁ yb y₁ : Int) : List Prim :=
  let xm := (x₀ + x₁) / 2
  [.path c₀ ⟨x₀, y₁⟩ [.curve ⟨x₀, y₁ - kappa (y₁ - yb)⟩ ⟨xm - kappa (xm - x₀), yb⟩ ⟨xm, yb⟩],
   .path c₁ ⟨xm, yb⟩ [.curve ⟨xm + kappa (x₁ - xm), yb⟩ ⟨x₁, y₁ - kappa (y₁ - yb)⟩ ⟨x₁, y₁⟩]]

/-- Primitives of a glyph in column `k` of the slab `y₀ ≤ y ≤ y₁`, with bottom colours `dom`
and top colours `cod`. -/
def glyphPrims (gl : Glyph) (k : Nat) (y₀ y₁ : Int) (dom cod : List RGB) : List Prim :=
  let ym := (y₀ + y₁) / 2
  let x₀ := colX k
  let x₁ := colX (k + 1)
  let colAt (l : List RGB) (i : Nat) := l.getD i RGB.black
  let yb := y₀ + gl.extent.1 * (y₁ - y₀) / 100
  let yt := y₀ + gl.extent.2 * (y₁ - y₀) / 100
  match gl with
  | .dot => [vline (colAt dom 0) x₀ y₀ y₁, .disc (colAt dom 0) ⟨x₀, ym⟩ 9]
  | .crossing =>
    [.path (colAt dom 0) ⟨x₀, y₀⟩ [sCurve x₀ y₀ x₁ y₁],
     .path (colAt dom 1) ⟨x₁, y₀⟩ [sCurve x₁ y₀ x₀ y₁]]
  | .cup => cupPrims (colAt cod 0) (colAt cod 1) x₀ x₁ yb y₁
  | .cap => cupPrims (colAt dom 0) (colAt dom 1) x₀ x₁ yt y₀
  | .box label =>
    let m := Glyph.width (.box label) dom.length cod.length
    let xl := colX k
    let xr := colX (k + m - 1)
    (dom.zipIdx.map fun (col, i) => vline col (colX (k + i)) y₀ yb) ++
    (cod.zipIdx.map fun (col, i) => vline col (colX (k + i)) yt y₁) ++
    [.rect ⟨xl - 35, yb⟩ ⟨xr + 35, yt⟩, .text ⟨(xl + xr) / 2, (yb + yt) / 2⟩ label]

variable {S : Signature.{u₀, u₁, u₂}} [DSLNames S] [DrawStyle S]

open DSLNames DrawStyle

/-- The glyph used for a generator. -/
def glyphOf (g : S.Gen) : Glyph :=
  (glyph g).fit (genName g) (S.dom g).length (S.cod g).length

/-- Primitives of the slab of layer `L` between heights `y₀` and `y₁`: strands (first),
then glyph. Returns strand paths and the remaining primitives separately, so that strands
are drawn below boxes, dots and labels. -/
def slabPrims (L : Layer S) (y₀ y₁ : Int) : List Prim × List Prim :=
  let k := L.left.length
  let d := (S.dom L.gen).length
  let c := (S.cod L.gen).length
  let gl := glyphOf L.gen
  let m := gl.width d c
  let yb := y₀ + gl.extent.1 * (y₁ - y₀) / 100
  let yt := y₀ + gl.extent.2 * (y₁ - y₀) / 100
  let lefts := L.left.zipIdx.map fun (col, p) => vline (strandColour col) (colX p) y₀ y₁
  let rights := L.right.zipIdx.map fun (col, q) =>
    let xb := colX (k + d + q)
    let xm := colX (k + m + q)
    let xt := colX (k + c + q)
    .path (strandColour col) ⟨xb, y₀⟩ [sCurve xb y₀ xm yb, .line ⟨xm, yt⟩, sCurve xm yt xt y₁]
  let gp := glyphPrims gl k y₀ y₁ ((S.dom L.gen).map strandColour)
    ((S.cod L.gen).map strandColour)
  let isStrand : Prim → Bool := fun | .path .. => true | _ => false
  (lefts ++ rights ++ gp.filter isStrand, gp.filter (!isStrand ·))

/-- The number of columns needed by the slab of a layer. -/
def slabWidth (L : Layer S) : Nat :=
  let d := (S.dom L.gen).length
  let c := (S.cod L.gen).length
  L.left.length + max (max d c) ((glyphOf L.gen).width d c) + L.right.length

/-- A region label at the left of a slab, if non-empty. -/
def regionLabelPrims (r : S.Region) (y₀ y₁ : Int) : List Prim :=
  let s := regionLabel r
  if s = "" then [] else [.text ⟨40, (y₀ + y₁) / 2⟩ s]

/-- Labels of the strands of a boundary word at height `y`. -/
def strandLabelPrims (w : List S.Colour) (y : Int) : List Prim :=
  w.zipIdx.filterMap fun (col, p) =>
    let s := strandLabel col
    if s = "" then none else some (.text ⟨colX p, y⟩ s)

/-- The picture of a diagram given by its source object and its layers (bottom to top). -/
def layout (a : Obj S) (ls : List (Layer S)) : Picture :=
  let n := ls.length
  let top : Obj S := Chain.target a ls
  let slabs := ls.zipIdx.map fun (L, j) => slabPrims L (j * unit) ((j + 1) * unit)
  let (strands, marks) : List Prim × List Prim :=
    match ls with
    | [] => (a.word.zipIdx.map fun (col, p) => vline (strandColour col) (colX p) 0 unit, [])
    | _ :: _ => (slabs.flatMap (·.1), slabs.flatMap (·.2))
  let h : Int := max n 1 * unit
  let regions :=
    match ls with
    | [] => regionLabelPrims a.start 0 unit
    | _ :: _ => ls.zipIdx.flatMap fun (L, j) => regionLabelPrims L.start (j * unit) ((j + 1) * unit)
  let labels := strandLabelPrims a.word (-18) ++ strandLabelPrims top.word (h + 18)
  let cols := (ls.map slabWidth ++ [a.word.length, top.word.length]).foldl max 1
  { lo := ⟨0, -35⟩, hi := ⟨colX cols, h + 35⟩, prims := strands ++ marks ++ regions ++ labels }

end Render

end StringDiagrams
