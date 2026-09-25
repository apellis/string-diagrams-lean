import StringDiagrams.Render.Basic

/-!
# TikZ output

`Render.renderTikZ a ls` draws the diagram with source `a` and layers `ls` (see
`StringDiagrams.Render.Basic` for the layout) as a `tikzpicture` environment, to be used
with `\usepackage{tikz}`. The one-line notation of the diagram is included as a TeX comment
on the first line. Colours use the extended `xcolor` syntax `{rgb,255:red,…;green,…;blue,…}`,
and label text passes through `DrawStyle.texText`.

The TikZ picture is presentation only and is never used as evidence.
-/

namespace StringDiagrams

universe u₀ u₁ u₂

namespace Render

/-- The `xcolor` specification of an `RGB` value. -/
def RGB.toTikZ (c : RGB) : String := s!"\{rgb,255:red,{c.r};green,{c.g};blue,{c.b}}"

/-- TikZ coordinates of a point (one TikZ unit per unit). -/
def tikzPt (p : Pt) : String :=
  "(" ++ fmtHundredths p.x ++ "," ++ fmtHundredths p.y ++ ")"

/-- A TikZ path segment. -/
def tikzSeg : Seg → String
  | .line p => "-- " ++ tikzPt p
  | .curve c₁ c₂ p => ".. controls " ++ tikzPt c₁ ++ " and " ++ tikzPt c₂ ++ " .. " ++ tikzPt p

/-- A TikZ command for a primitive; `tex` converts label text. -/
def tikzPrim (tex : String → String) : Prim → String
  | .path col p segs =>
    s!"  \\draw[line width=0.9pt, color={col.toTikZ}] {tikzPt p} " ++
      " ".intercalate (segs.map tikzSeg) ++ ";"
  | .disc col c r =>
    s!"  \\fill[color={col.toTikZ}] {tikzPt c} circle[radius={fmtHundredths r}];"
  | .rect p q => s!"  \\draw[fill=white] {tikzPt p} rectangle {tikzPt q};"
  | .text p s => s!"  \\node[font=\\small] at {tikzPt p} \{{tex s}};"

variable {S : Signature.{u₀, u₁, u₂}} [DSLNames S] [DrawStyle S]

/-- A `tikzpicture` of the diagram with source `a` and layers `ls` (bottom to top). The
first line is a TeX comment containing `DSL.print a ls`. -/
def renderTikZ (a : Obj S) (ls : List (Layer S)) : String :=
  let pic := layout a ls
  let isPath : Prim → Bool := fun | .path .. => true | _ => false
  let tex := DrawStyle.texText (S := S)
  "\n".intercalate <|
    ["% " ++ DSL.print a ls,
     "\\begin{tikzpicture}[x=1cm, y=1cm, line cap=round]",
     s!"  \\useasboundingbox {tikzPt pic.lo} rectangle {tikzPt pic.hi};"] ++
    ((pic.prims.filter isPath).map (tikzPrim tex)) ++
    ((pic.prims.filter (!isPath ·)).map (tikzPrim tex)) ++
    ["\\end{tikzpicture}", ""]

/-- A `tikzpicture` of a typed diagram. -/
def renderHomTikZ {a b : Obj S} (f : a ⟶ b) : String := renderTikZ a (Diagram.layers f)

end Render

end StringDiagrams
