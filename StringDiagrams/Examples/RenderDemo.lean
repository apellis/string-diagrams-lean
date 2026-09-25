import StringDiagrams.Render.SVG
import StringDiagrams.Render.TikZ

/-!
# Examples for the diagram notation and the renderer

Three small signatures exercise the notation of `StringDiagrams.DSL` and the renderers:

* `nilHecke`: one colour, a dot and a crossing (monoidal; width shorthand `3 | …`);
* `klr`: two colours `i`, `j` with a dot `x` on either colour and crossings `psi` of any
  two colours, with generator names resolved from the strands they act on;
* `cupCap`: two regions `λ`, `μ`, strands `E : λ → μ` and `F : μ → λ`, cups and caps
  (generators with empty bottom or top boundary), a dot on `E`, and a generic generator
  `phi : E F E ⇒ E` drawn as a labelled box.

The checks below are `#guard`s evaluated at compile time; nothing is written to disk. The
script `scripts/render_examples.lean` writes the drawings of `gallery` to `out/`.
-/

namespace StringDiagrams.Examples.RenderDemo

open CategoryTheory StringDiagrams DSL Render

/-! ## The nilHecke signature -/

/-- Generators of the nilHecke signature. -/
inductive NHGen
  | dot
  | crossing
  deriving DecidableEq, Repr

/-- The nilHecke signature: one colour, a dot and a crossing. -/
def nilHecke : Signature.{0, 0, 0} where
  Region := PUnit
  Colour := PUnit
  colourSrc _ := ⟨⟩
  colourTgt _ := ⟨⟩
  Gen := NHGen
  dom | .dot => [⟨⟩] | .crossing => [⟨⟩, ⟨⟩]
  cod | .dot => [⟨⟩] | .crossing => [⟨⟩, ⟨⟩]
  left _ := ⟨⟩
  right _ := ⟨⟩

instance : DecidableEq nilHecke.Region := inferInstanceAs (DecidableEq PUnit)
instance : DecidableEq nilHecke.Colour := inferInstanceAs (DecidableEq PUnit)
instance : DecidableEq nilHecke.Gen := inferInstanceAs (DecidableEq NHGen)

instance : DSLNames nilHecke where
  regionName _ := ""
  regionOfName? n := if n = "" then some ⟨⟩ else none
  colourName _ := "s"
  colourOfName? n := if n = "s" then some ⟨⟩ else none
  genName | .dot => "x" | .crossing => "psi"
  genOfName? n _ _ :=
    if n = "x" then some NHGen.dot else if n = "psi" then some NHGen.crossing else none
  soleColour? := some ⟨⟩

instance : LawfulDSLNames nilHecke where
  regionOfName_regionName _ := rfl
  regionName_valid _ := Or.inl rfl
  colourOfName_colourName _ := rfl
  colourName_valid _ := rfl
  genOfName_genName g _ := by cases g <;> rfl
  genName_valid g := by cases g <;> rfl
  soleColour_eq _ _ := rfl

instance : DrawStyle nilHecke where
  glyph | .dot => .dot | .crossing => .crossing

/-! ## A two-colour KLR-type signature -/

/-- Two strand colours. -/
inductive KC
  | i
  | j
  deriving DecidableEq, Repr

/-- Generators: a dot on a strand of colour `c`, and a crossing of strands `c` and `d`. -/
inductive KGen
  | x (c : KC)
  | psi (c d : KC)
  deriving DecidableEq, Repr

/-- A monoidal signature with two colours, dots and crossings. -/
def klr : Signature.{0, 0, 0} where
  Region := PUnit
  Colour := KC
  colourSrc _ := ⟨⟩
  colourTgt _ := ⟨⟩
  Gen := KGen
  dom | .x c => [c] | .psi c d => [c, d]
  cod | .x c => [c] | .psi c d => [d, c]
  left _ := ⟨⟩
  right _ := ⟨⟩

instance : DecidableEq klr.Region := inferInstanceAs (DecidableEq PUnit)
instance : DecidableEq klr.Colour := inferInstanceAs (DecidableEq KC)
instance : DecidableEq klr.Gen := inferInstanceAs (DecidableEq KGen)

instance : DSLNames klr where
  regionName _ := ""
  regionOfName? n := if n = "" then some ⟨⟩ else none
  colourName | .i => "i" | .j => "j"
  colourOfName? n := if n = "i" then some KC.i else if n = "j" then some KC.j else none
  genName | .x _ => "x" | .psi _ _ => "psi"
  genOfName? n _ rest :=
    match rest with
    | c :: d :: _ =>
      if n = "x" then some (KGen.x c) else if n = "psi" then some (KGen.psi c d) else none
    | [c] => if n = "x" then some (KGen.x c) else none
    | [] => none

instance : LawfulDSLNames klr where
  regionOfName_regionName _ := rfl
  regionName_valid _ := Or.inl rfl
  colourOfName_colourName c := by cases c <;> rfl
  colourName_valid c := by cases c <;> decide
  genOfName_genName g rest := by cases g <;> cases rest <;> rfl
  genName_valid g := by cases g <;> rfl
  soleColour_eq h := nomatch h

instance : DrawStyle klr where
  glyph | .x _ => .dot | .psi _ _ => .crossing
  strandColour | .i => ⟨31, 119, 180⟩ | .j => ⟨214, 39, 40⟩
  strandLabel | .i => "i" | .j => "j"

/-! ## A signature with regions, cups and caps -/

/-- Two regions. -/
inductive CRegion
  | lam
  | mu
  deriving DecidableEq, Repr

/-- Two strands: `E` from `λ` (left) to `μ` (right), and `F` from `μ` to `λ`. -/
inductive CColour
  | E
  | F
  deriving DecidableEq, Repr

/-- Cups, caps, a dot on `E`, and a generic generator `phi : E F E ⇒ E`. -/
inductive CGen
  | cupEF
  | cupFE
  | capEF
  | capFE
  | dotE
  | phi
  deriving DecidableEq, Repr

/-- A 2-categorical signature with nontrivial regions, cups and caps. -/
def cupCap : Signature.{0, 0, 0} where
  Region := CRegion
  Colour := CColour
  colourSrc | .E => .lam | .F => .mu
  colourTgt | .E => .mu | .F => .lam
  Gen := CGen
  dom
    | .cupEF | .cupFE => []
    | .capEF => [.E, .F]
    | .capFE => [.F, .E]
    | .dotE => [.E]
    | .phi => [.E, .F, .E]
  cod
    | .cupEF => [.E, .F]
    | .cupFE => [.F, .E]
    | .capEF | .capFE => []
    | .dotE => [.E]
    | .phi => [.E]
  left
    | .cupEF | .capEF | .dotE | .phi => .lam
    | .cupFE | .capFE => .mu
  right
    | .cupEF | .capEF => .lam
    | .cupFE | .capFE => .mu
    | .dotE | .phi => .mu

instance : DecidableEq cupCap.Region := inferInstanceAs (DecidableEq CRegion)
instance : DecidableEq cupCap.Colour := inferInstanceAs (DecidableEq CColour)
instance : DecidableEq cupCap.Gen := inferInstanceAs (DecidableEq CGen)

instance : DSLNames cupCap where
  regionName | .lam => "λ" | .mu => "μ"
  regionOfName? n := if n = "λ" then some CRegion.lam else if n = "μ" then some CRegion.mu
    else none
  colourName | .E => "E" | .F => "F"
  colourOfName? n := if n = "E" then some CColour.E else if n = "F" then some CColour.F
    else none
  genName
    | .cupEF | .cupFE => "cup"
    | .capEF | .capFE => "cap"
    | .dotE => "x"
    | .phi => "phi"
  genOfName? n r _ :=
    if n = "cup" then some (match r with | .lam => CGen.cupEF | .mu => CGen.cupFE)
    else if n = "cap" then some (match r with | .lam => CGen.capEF | .mu => CGen.capFE)
    else if n = "x" then some CGen.dotE
    else if n = "phi" then some CGen.phi
    else none

instance : LawfulDSLNames cupCap where
  regionOfName_regionName r := by cases r <;> rfl
  regionName_valid r := by cases r <;> decide
  colourOfName_colourName c := by cases c <;> rfl
  colourName_valid c := by cases c <;> decide
  genOfName_genName g _ := by cases g <;> rfl
  genName_valid g := by cases g <;> rfl
  soleColour_eq h := nomatch h

instance : DrawStyle cupCap where
  glyph
    | .cupEF | .cupFE => .cup
    | .capEF | .capFE => .cap
    | .dotE => .dot
    | .phi => .box "φ"
  strandColour | .E => ⟨31, 119, 180⟩ | .F => ⟨44, 160, 44⟩
  regionLabel | .lam => "λ" | .mu => "μ"
  strandLabel | .E => "E" | .F => "F"
  texText s :=
    if s = "λ" then "$\\lambda$" else if s = "μ" then "$\\mu$"
    else if s = "φ" then "$\\varphi$" else texEscape s

/-! ## Notation checks -/

/-- Parse and print again (the identity on canonical strings). -/
def reprint (S : Signature.{0, 0, 0}) [DSLNames S] [DecidableEq S.Colour] (s : String) :
    String :=
  match parse (S := S) s with
  | .ok (a, ls) => print a ls
  | .error e => "error: " ++ e

/-- Whether a string parses to a well-typed diagram. -/
def wellTyped (S : Signature.{0, 0, 0}) [DSLNames S] [DecidableEq S.Region]
    [DecidableEq S.Colour] (s : String) : Bool :=
  match parseDiagram (S := S) s with
  | .ok _ => true
  | .error _ => false

/-- Whether a string fails to parse. -/
def parseFails (S : Signature.{0, 0, 0}) [DSLNames S] [DecidableEq S.Colour] (s : String) :
    Bool :=
  match parse (S := S) s with
  | .ok _ => false
  | .error _ => true

/-- Parse, then check the round trip `parse ∘ print` on the result. -/
def roundTripsStr (S : Signature.{0, 0, 0}) [DSLNames S] [DecidableEq S.Region]
    [DecidableEq S.Colour] [DecidableEq S.Gen] (s : String) : Bool :=
  match parse (S := S) s with
  | .ok (a, ls) => roundTrips a ls
  | .error _ => false

-- nilHecke: width shorthand, canonical spacing, and the bracketed form.
#guard reprint nilHecke "3 | x@0 ; psi@1 ; psi@0" == "3 | x@0 ; psi@1 ; psi@0"
#guard reprint nilHecke "3|x@0;psi@1;psi@0" == "3 | x@0 ; psi@1 ; psi@0"
#guard reprint nilHecke "  [s s s]  |  x @ 0 ;psi@ 1  " == "3 | x@0 ; psi@1"
#guard reprint nilHecke "2" == "2"
#guard reprint nilHecke "0" == "0"
#guard reprint nilHecke "{} 2 | psi@0" == "2 | psi@0"
#guard reprint nilHecke "12 | psi@10 ; x@11" == "12 | psi@10 ; x@11"
#guard roundTripsStr nilHecke "4 | x@0 ; psi@1 ; psi@2 ; x@3 ; psi@0"
#guard wellTyped nilHecke "4 | x@0 ; psi@1 ; psi@2 ; x@3 ; psi@0"
#guard parseFails nilHecke "2 | psi@1"      -- the crossing does not fit
#guard parseFails nilHecke "2 | chi@0"      -- unknown generator
#guard parseFails nilHecke "2 | x@0 ;"      -- trailing separator
#guard parseFails nilHecke "2 | x0"         -- missing '@'
#guard parseFails nilHecke "2 x@0"          -- missing '|'
#guard parseFails nilHecke "[s t]"          -- unknown colour

-- KLR: colour names and generator names resolved from the strands they act on.
#guard reprint klr "[i i j] | x@0 ; psi@1 ; psi@0" == "[i i j] | x@0 ; psi@1 ; psi@0"
#guard reprint klr "[] " == "[]"
#guard reprint klr "[j i] | psi@0 ; x@1 ; psi@0" == "[j i] | psi@0 ; x@1 ; psi@0"
#guard roundTripsStr klr "[i i j] | x@0 ; psi@1 ; psi@0"
#guard roundTripsStr klr "[j i j i] | psi@2 ; psi@1 ; x@3 ; psi@0 ; psi@2"
#guard wellTyped klr "[i i j] | x@0 ; psi@1 ; psi@0"
#guard parseFails klr "3 | x@0"             -- no width shorthand with two colours
#guard parseFails klr "[i j] | psi@1"       -- position out of range
#guard parseFails klr "[i k]"               -- unknown colour
-- the layers carry the resolved generators and the reconstructed side strands
#guard (match parse (S := klr) "[i i j] | x@0 ; psi@1 ; psi@0" with
    | .ok (a, ls) => decide (a = ⟨⟨⟩, [.i, .i, .j]⟩ ∧ ls =
        [⟨⟨⟩, [], KGen.x .i, [.i, .j]⟩, ⟨⟨⟩, [.i], KGen.psi .i .j, []⟩,
          ⟨⟨⟩, [], KGen.psi .i .j, [.i]⟩])
    | .error _ => false)

-- cups and caps: region labels, empty boundaries, and region-dependent names.
#guard reprint cupCap "{λ} [] | cup@0 ; cap@0" == "{λ} [] | cup@0 ; cap@0"
#guard reprint cupCap "{μ}[]|cup@0;cup@1;cap@0" == "{μ} [] | cup@0 ; cup@1 ; cap@0"
#guard reprint cupCap "{λ} [E] | cup@1 ; cap@0" == "{λ} [E] | cup@1 ; cap@0"
#guard reprint cupCap "{λ} [E F E] | phi@0 ; x@0" == "{λ} [E F E] | phi@0 ; x@0"
#guard roundTripsStr cupCap "{λ} [] | cup@0 ; cap@0"
#guard roundTripsStr cupCap "{λ} [E] | cup@1 ; cap@0"
#guard roundTripsStr cupCap "{μ} [F] | cup@1 ; x@1 ; cap@0"
#guard roundTripsStr cupCap "{λ} [E F E] | phi@0 ; cup@1 ; x@0 ; cap@1"
#guard wellTyped cupCap "{λ} [E] | cup@1 ; cap@0"
#guard wellTyped cupCap "{μ} [F] | cup@1 ; x@1 ; cap@0"
#guard wellTyped cupCap "{λ} [E] | cup@0"
#guard !wellTyped cupCap "{μ} [E F E] | phi@0"  -- `phi` needs region `λ` on its left
#guard parseFails cupCap "[E]"                -- a region label is required
#guard parseFails cupCap "{ν} [E]"            -- unknown region
#guard parseFails cupCap "{λ} [E E] | cap@0"  -- `E E` is not the bottom of a cap

/-! ## Rendering checks -/

/-- The SVG drawing of a diagram given in the notation (or the parse error). -/
def svgOf (S : Signature.{0, 0, 0}) [DSLNames S] [DrawStyle S] [DecidableEq S.Colour]
    (s : String) : Except String String :=
  (parse (S := S) s).map fun (a, ls) => renderSVG a ls

/-- The TikZ drawing of a diagram given in the notation (or the parse error). -/
def tikzOf (S : Signature.{0, 0, 0}) [DSLNames S] [DrawStyle S] [DecidableEq S.Colour]
    (s : String) : Except String String :=
  (parse (S := S) s).map fun (a, ls) => renderTikZ a ls

/-- Whether the notation embedded in the SVG drawing of a diagram is its printed form, and
parsing it back returns the diagram. -/
def svgRoundTrips (S : Signature.{0, 0, 0}) [DSLNames S] [DrawStyle S] [DecidableEq S.Region]
    [DecidableEq S.Colour] [DecidableEq S.Gen] (s : String) : Bool :=
  match parse (S := S) s with
  | .ok (a, ls) =>
    extractDSL (renderSVG a ls) == some (print a ls) &&
      match parseSVG (S := S) (renderSVG a ls) with
      | .ok (a', ls') => decide (a' = a ∧ ls' = ls)
      | .error _ => false
  | .error _ => false

/-- The first line of the TikZ drawing of a diagram. -/
def tikzHead (S : Signature.{0, 0, 0}) [DSLNames S] [DrawStyle S] [DecidableEq S.Colour]
    (s : String) : String :=
  match tikzOf S s with
  | .ok t => (t.splitOn "\n").headD ""
  | .error e => e

#guard svgRoundTrips nilHecke "3 | x@0 ; psi@1 ; psi@0"
#guard svgRoundTrips nilHecke "0"
#guard svgRoundTrips klr "[i i j] | x@0 ; psi@1 ; psi@0"
#guard svgRoundTrips klr "[j i j i] | psi@2 ; psi@1 ; x@3 ; psi@0 ; psi@2"
#guard svgRoundTrips cupCap "{λ} [] | cup@0 ; cap@0"
#guard svgRoundTrips cupCap "{λ} [E] | cup@1 ; cap@0"
#guard svgRoundTrips cupCap "{μ} [F] | cup@1 ; x@1 ; cap@0"
#guard svgRoundTrips cupCap "{λ} [E F E] | phi@0 ; cup@1 ; x@0 ; cap@1"
#guard tikzHead klr "[i i j] | x@0 ; psi@1 ; psi@0" == "% [i i j] | x@0 ; psi@1 ; psi@0"
#guard tikzHead cupCap "{λ} [E] | cup@1 ; cap@0" == "% {λ} [E] | cup@1 ; cap@0"
-- region labels and the metadata are XML-escaped in the SVG text
#guard xmlEscape "a<b & \"c\"" == "a&lt;b &amp; &quot;c&quot;"
#guard xmlUnescape "&amp;lt;&foo;&" == "&lt;&foo;&"
#guard fmtHundredths 1250 == "12.5" && fmtHundredths (-5) == "-0.05" && fmtHundredths 300 == "3"
-- the bounding box: three columns plus margins, three slabs plus margins
#guard (match parse (S := nilHecke) "3 | x@0 ; psi@1 ; psi@0" with
    | .ok (a, ls) => let p := layout a ls; decide (p.lo = ⟨0, -35⟩ ∧ p.hi = ⟨400, 335⟩)
    | .error _ => false)
-- a cup widens the picture of the slab: the strand to its right moves over
#guard (match parse (S := cupCap) "{λ} [E] | cup@0" with
    | .ok (a, ls) => decide ((layout a ls).hi.x = 400)
    | .error _ => false)

/-- Diagrams drawn by `scripts/render_examples.lean`: file name and drawings. -/
def gallery : List (String × Except String String × Except String String) :=
  [("nilhecke", svgOf nilHecke "3 | x@0 ; psi@1 ; psi@0 ; x@2",
      tikzOf nilHecke "3 | x@0 ; psi@1 ; psi@0 ; x@2"),
   ("klr", svgOf klr "[i i j] | x@0 ; psi@1 ; psi@0",
      tikzOf klr "[i i j] | x@0 ; psi@1 ; psi@0"),
   ("zigzag", svgOf cupCap "{λ} [E] | cup@1 ; cap@0",
      tikzOf cupCap "{λ} [E] | cup@1 ; cap@0"),
   ("bubble", svgOf cupCap "{μ} [F] | cup@1 ; x@1 ; cap@0 ; cup@0 ; cap@0",
      tikzOf cupCap "{μ} [F] | cup@1 ; x@1 ; cap@0 ; cup@0 ; cap@0"),
   ("box", svgOf cupCap "{λ} [E F E] | phi@0 ; cup@1 ; x@0 ; cap@1",
      tikzOf cupCap "{λ} [E F E] | phi@0 ; cup@1 ; x@0 ; cap@1")]

#guard gallery.all fun (_, s, t) => s.isOk && t.isOk

-- The general round trip applies to all three signatures.
example {a b : Obj nilHecke} (f : a ⟶ b) : parseHom a b (printHom f) = .ok f :=
  parseHom_printHom f
example {a b : Obj klr} (f : a ⟶ b) : parseHom a b (printHom f) = .ok f := parseHom_printHom f
example {a b : Obj cupCap} (f : a ⟶ b) : parseHom a b (printHom f) = .ok f :=
  parseHom_printHom f

end StringDiagrams.Examples.RenderDemo
