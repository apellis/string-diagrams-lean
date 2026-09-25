import StringDiagrams.Render.Basic

/-!
# SVG output

`Render.renderSVG a ls` draws the diagram with source `a` and layers `ls` (see
`StringDiagrams.Render.Basic` for the layout) as a standalone SVG document. The exact
one-line notation of the diagram (`DSL.print a ls`) is embedded, XML-escaped, in the
element `<metadata id="string-diagrams-dsl">`, and `Render.extractDSL` recovers it from the
SVG text; the diagram itself is then recovered with `DSL.parse`.

The SVG is presentation only and is never used as evidence.
-/

namespace StringDiagrams

universe u₀ u₁ u₂

namespace Render

/-! ## Text utilities -/

/-- The XML escape of a character. -/
def xmlEscapeChar : Char → List Char
  | '&' => ['&', 'a', 'm', 'p', ';']
  | '<' => ['&', 'l', 't', ';']
  | '>' => ['&', 'g', 't', ';']
  | '"' => ['&', 'q', 'u', 'o', 't', ';']
  | '\'' => ['&', 'a', 'p', 'o', 's', ';']
  | c => [c]

/-- Escape the characters `& < > " '` for XML text and attribute values. -/
def xmlEscape (s : String) : String := String.mk (s.toList.flatMap xmlEscapeChar)

/-- The character of one of the five predefined XML entities, and the remaining input. -/
def xmlEntity? : List Char → Option (Char × List Char)
  | 'a' :: 'm' :: 'p' :: ';' :: rest => some ('&', rest)
  | 'l' :: 't' :: ';' :: rest => some ('<', rest)
  | 'g' :: 't' :: ';' :: rest => some ('>', rest)
  | 'q' :: 'u' :: 'o' :: 't' :: ';' :: rest => some ('"', rest)
  | 'a' :: 'p' :: 'o' :: 's' :: ';' :: rest => some ('\'', rest)
  | _ => none

theorem xmlEntity?_length {cs rest : List Char} {d : Char} (h : xmlEntity? cs = some (d, rest)) :
    rest.length < cs.length := by
  unfold xmlEntity? at h
  split at h <;> first | (cases h; simp only [List.length_cons]; omega) | cases h

/-- Replace the predefined XML entities by their characters. -/
def xmlUnescapeAux : List Char → List Char
  | [] => []
  | c :: cs =>
    if c = '&' then
      match h : xmlEntity? cs with
      | some (d, rest) =>
        have := xmlEntity?_length h
        d :: xmlUnescapeAux rest
      | none => '&' :: xmlUnescapeAux cs
    else c :: xmlUnescapeAux cs
termination_by l => l.length

/-- Undo `xmlEscape`. -/
def xmlUnescape (s : String) : String := String.mk (xmlUnescapeAux s.toList)

theorem xmlUnescapeAux_cons {c : Char} (h : c ≠ '&') (cs : List Char) :
    xmlUnescapeAux (c :: cs) = c :: xmlUnescapeAux cs := by
  rw [xmlUnescapeAux]; simp [h]

theorem xmlUnescapeAux_escapeChar_append (c : Char) (rest : List Char) :
    xmlUnescapeAux (xmlEscapeChar c ++ rest) = c :: xmlUnescapeAux rest := by
  unfold xmlEscapeChar
  split
  all_goals first
    | (rw [List.singleton_append, xmlUnescapeAux_cons]; assumption)
    | (simp only [List.cons_append, List.nil_append]; rw [xmlUnescapeAux]; simp [xmlEntity?])

/-- Unescaping inverts escaping. -/
@[simp] theorem xmlUnescape_xmlEscape (s : String) : xmlUnescape (xmlEscape s) = s := by
  suffices h : ∀ l : List Char, xmlUnescapeAux (l.flatMap xmlEscapeChar) = l from
    congrArg String.mk (h s.toList)
  intro l
  induction l with
  | nil => simp [xmlUnescapeAux]
  | cons c l ih => rw [List.flatMap_cons, xmlUnescapeAux_escapeChar_append, ih]

/-! ## SVG -/

/-- The SVG colour of an `RGB` value. -/
def RGB.toSVG (c : RGB) : String := s!"rgb({c.r},{c.g},{c.b})"

/-- Pixels per unit in SVG output. -/
def svgScale : Int := 40

/-- An SVG length from hundredths of a unit. -/
def svgLen (v : Int) : String := fmtHundredths (v * svgScale)

/-- SVG coordinates of a point in a picture with top edge `ytop` (SVG's `y` points down). -/
def svgPt (ytop : Int) (lo : Pt) (p : Pt) : String :=
  svgLen (p.x - lo.x) ++ " " ++ svgLen (ytop - p.y)

/-- An SVG path segment. -/
def svgSeg (ytop : Int) (lo : Pt) : Seg → String
  | .line p => "L " ++ svgPt ytop lo p
  | .curve c₁ c₂ p =>
    "C " ++ svgPt ytop lo c₁ ++ ", " ++ svgPt ytop lo c₂ ++ ", " ++ svgPt ytop lo p

/-- An SVG element for a primitive. -/
def svgPrim (ytop : Int) (lo : Pt) : Prim → String
  | .path col p segs =>
    s!"<path d=\"M {svgPt ytop lo p} {" ".intercalate (segs.map (svgSeg ytop lo))}\" " ++
      s!"stroke=\"{col.toSVG}\"/>"
  | .disc col c r =>
    s!"<circle cx=\"{svgLen (c.x - lo.x)}\" cy=\"{svgLen (ytop - c.y)}\" r=\"{svgLen r}\" " ++
      s!"fill=\"{col.toSVG}\" stroke=\"none\"/>"
  | .rect p q =>
    s!"<rect x=\"{svgLen (p.x - lo.x)}\" y=\"{svgLen (ytop - q.y)}\" " ++
      s!"width=\"{svgLen (q.x - p.x)}\" height=\"{svgLen (q.y - p.y)}\" " ++
      "fill=\"white\" stroke=\"black\" stroke-width=\"1.5\"/>"
  | .text p s =>
    s!"<text x=\"{svgLen (p.x - lo.x)}\" y=\"{svgLen (ytop - p.y)}\" " ++
      "text-anchor=\"middle\" dominant-baseline=\"central\" font-family=\"serif\" " ++
      s!"font-size=\"14\" fill=\"black\" stroke=\"none\">{xmlEscape s}</text>"

/-- The opening tag of the metadata element carrying the notation of the diagram. -/
def dslMetadataOpen : String := "<metadata id=\"string-diagrams-dsl\">"

/-- The closing tag of the metadata element. -/
def dslMetadataClose : String := "</metadata>"

/-- A standalone SVG document of a picture, with `dsl` embedded as metadata. -/
def Picture.toSVG (pic : Picture) (dsl : String) : String :=
  let w := svgLen (pic.hi.x - pic.lo.x)
  let h := svgLen (pic.hi.y - pic.lo.y)
  let isPath : Prim → Bool := fun | .path .. => true | _ => false
  let paths := (pic.prims.filter isPath).map (svgPrim pic.hi.y pic.lo)
  let others := (pic.prims.filter (!isPath ·)).map (svgPrim pic.hi.y pic.lo)
  "\n".intercalate <|
    ["<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
     s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{w}\" height=\"{h}\" " ++
       s!"viewBox=\"0 0 {w} {h}\">",
     dslMetadataOpen ++ xmlEscape dsl ++ dslMetadataClose,
     "<rect width=\"100%\" height=\"100%\" fill=\"white\"/>",
     "<g fill=\"none\" stroke-width=\"2.5\" stroke-linecap=\"round\">"] ++
    paths ++ ["</g>"] ++ others ++ ["</svg>", ""]

variable {S : Signature.{u₀, u₁, u₂}} [DSLNames S] [DrawStyle S]

/-- A standalone SVG drawing of the diagram with source `a` and layers `ls` (bottom to
top), embedding the notation `DSL.print a ls` as metadata. -/
def renderSVG (a : Obj S) (ls : List (Layer S)) : String :=
  (layout a ls).toSVG (DSL.print a ls)

/-- A standalone SVG drawing of a typed diagram. -/
def renderHomSVG {a b : Obj S} (f : a ⟶ b) : String := renderSVG a (Diagram.layers f)

/-- Recover the notation embedded in an SVG document produced by `renderSVG`. -/
def extractDSL (svg : String) : Option String :=
  match svg.splitOn dslMetadataOpen with
  | [_, rest] =>
    match rest.splitOn dslMetadataClose with
    | body :: _ :: _ => some (xmlUnescape body)
    | _ => none
  | _ => none

/-- Recover a diagram (source object and layers) from an SVG document produced by
`renderSVG`. -/
def parseSVG [DecidableEq S.Colour] (svg : String) : Except String (Obj S × List (Layer S)) :=
  match extractDSL svg with
  | some s => DSL.parse s
  | none => .error "no diagram notation found in the SVG metadata"

end Render

end StringDiagrams
