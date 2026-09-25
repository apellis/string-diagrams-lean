import StringDiagrams.Syntax
import Mathlib.Data.Nat.Digits

/-!
# A one-line textual notation for layered diagrams

This file defines a human-writable, one-line notation for raw layered diagrams over a
signature `S`, a printer and a parser for it, and the passage from parsed layer lists to
typed diagrams of the free 2-category.

## Notation

A diagram is written as its source object followed by its layers, read from bottom to top:

```
{λ} [i i j] | x@0 ; psi@1 ; psi@0
```

* `{λ}` is the optional label of the leftmost region. It is omitted exactly when the
  region's printed name is the empty string (as for the unique region of a monoidal
  signature, `Region = PUnit`).
* `[i i j]` is the word of strand colours, from left to right. For a signature with a
  single colour (declared by `DSLNames.soleColour?`), the word may be abbreviated by its
  width: `3 | x@0 ; psi@1`.
* each layer `gen@k` is the generator `gen` with `k` identity strands to its left; the
  strands to its right are then determined by the current boundary.

Grammar (whitespace separates tokens and is otherwise ignored):

```
diagram ::= region? word ( '|' layer ( ';' layer )* )?
region  ::= '{' name? '}'
word    ::= '[' name* ']' | numeral
layer   ::= name '@' numeral
```

A *name* is a nonempty string of characters that are neither whitespace nor one of the
reserved characters `[ ] { } | ; @`. The printer produces `{r} ` only for nonempty region
names, `[]`-words unless `soleColour?` is set, and no `|` for a diagram without layers.

## Generator names in context

A generator is recovered from its name *and its position*: `DSLNames.genOfName?` receives
the region to the left of the generator and the boundary strands from the generator's
position rightwards. This allows one name for a family of generators distinguished by the
strands they act on (for example a dot `x` on a strand of any colour, or a crossing `psi`
of any two colours), as is customary for KLR algebras.

## Main definitions and results

* `DSLNames S`: printable names for regions, colours and generators, with parsing back;
  `LawfulDSLNames S`: the conditions under which printing and parsing are inverse.
* `DSL.print : Obj S → List (Layer S) → String` and
  `DSL.parse : String → Except String (Obj S × List (Layer S))`.
* `DSL.parse_print`: for a well-typed layer list (`Chain a ls b`) and lawful names,
  `parse (print a ls) = .ok (a, ls)`.
* `DSL.parseDiagram`, `DSL.parseHom`: parsing directly to typed diagrams, using the
  decidability of `Chain` (`StringDiagrams.decChain`) under decidable equality of regions
  and colours; `DSL.printHom` and `DSL.parseHom_printHom`.
-/

namespace StringDiagrams

universe u₀ u₁ u₂

/-! ## Decidability of well-typedness -/

section Decidable

variable {S : Signature.{u₀, u₁, u₂}}

instance Signature.decOk [DecidableEq S.Region] :
    (r : S.Region) → (w : List S.Colour) → Decidable (S.ok r w)
  | _, [] => isTrue trivial
  | r, c :: w =>
    have := Signature.decOk (S.colourTgt c) w
    decidable_of_iff _ (Signature.ok_cons r c w).symm

instance Obj.decEq [DecidableEq S.Region] [DecidableEq S.Colour] : DecidableEq (Obj S) :=
  fun a b => decidable_of_iff (a.start = b.start ∧ a.word = b.word) Obj.ext_iff.symm

instance Layer.decValid [DecidableEq S.Region] (L : Layer S) : Decidable L.Valid :=
  decidable_of_iff
    (S.ok L.start L.left ∧ S.endR L.start L.left = S.left L.gen ∧
      S.ok (S.left L.gen) (S.dom L.gen) ∧ S.endR (S.left L.gen) (S.dom L.gen) = S.right L.gen ∧
      S.ok (S.left L.gen) (S.cod L.gen) ∧ S.endR (S.left L.gen) (S.cod L.gen) = S.right L.gen ∧
      S.ok (S.right L.gen) L.right)
    ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩,
      fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩⟩

instance decChain [DecidableEq S.Region] [DecidableEq S.Colour] :
    (a : Obj S) → (ls : List (Layer S)) → (b : Obj S) → Decidable (Chain a ls b)
  | a, [], b => decidable_of_iff (a = b) (chain_nil a b).symm
  | a, L :: ls, b =>
    have := decChain L.cod ls b
    decidable_of_iff _ (chain_cons a b L ls).symm

instance Layer.decEq [DecidableEq S.Region] [DecidableEq S.Colour] [DecidableEq S.Gen] :
    DecidableEq (Layer S) :=
  fun L L' => decidable_of_iff
    (L.start = L'.start ∧ L.left = L'.left ∧ L.gen = L'.gen ∧ L.right = L'.right)
    Layer.ext_iff.symm

/-- The top boundary of a layer list read from the bottom boundary `a`: the codomain of its
last layer, or `a` if there are no layers. -/
def Chain.target (a : Obj S) : List (Layer S) → Obj S
  | [] => a
  | L :: ls => Chain.target L.cod ls

theorem Chain.target_eq {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    Chain.target a ls = b := by
  induction ls generalizing a with
  | nil => exact h
  | cons L ls ih => exact ih h.2.2

end Decidable

/-! ## Names -/

/-- Printable names for the regions, colours and generators of a signature, together with
the inverse lookups used by the parser.

* `regionName r` may be empty; the region prefix `{…}` is then omitted when printing, and
  a missing prefix is parsed as `regionOfName? ""`.
* `genOfName? n r rest` resolves the generator named `n` whose left region is `r` and
  whose bottom boundary is a prefix of `rest` (the boundary strands from the generator's
  position rightwards). Signatures whose generator names are unambiguous may ignore the
  last two arguments.
* `soleColour? = some c` declares that `c` is the only colour; words are then printed by
  their width. -/
class DSLNames (S : Signature.{u₀, u₁, u₂}) where
  /-- The printed name of a region (possibly empty). -/
  regionName : S.Region → String
  /-- The region with a given name. -/
  regionOfName? : String → Option S.Region
  /-- The printed name of a colour. -/
  colourName : S.Colour → String
  /-- The colour with a given name. -/
  colourOfName? : String → Option S.Colour
  /-- The printed name of a generator. -/
  genName : S.Gen → String
  /-- The generator with a given name, left region and boundary to its right. -/
  genOfName? : String → S.Region → List S.Colour → Option S.Gen
  /-- The unique colour of a single-colour signature, enabling the width shorthand. -/
  soleColour? : Option S.Colour := none

namespace DSL

/-! ## Characters and tokens -/

/-- Tokens of the notation. -/
inductive Tok
  | lbrack
  | rbrack
  | lbrace
  | rbrace
  | bar
  | semi
  | atSign
  | ident (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- The token of a reserved character. -/
def specialTok? : Char → Option Tok
  | '[' => some .lbrack
  | ']' => some .rbrack
  | '{' => some .lbrace
  | '}' => some .rbrace
  | '|' => some .bar
  | ';' => some .semi
  | '@' => some .atSign
  | _ => none

/-- Characters allowed in names: neither whitespace nor reserved. -/
def isNameChar (c : Char) : Bool := (specialTok? c).isNone && !c.isWhitespace

/-- A valid name: nonempty, consisting of name characters. -/
def validName (s : String) : Bool := !s.toList.isEmpty && s.toList.all isNameChar

/-- The characters of a token. -/
def Tok.chars : Tok → List Char
  | .lbrack => ['[']
  | .rbrack => [']']
  | .lbrace => ['{']
  | .rbrace => ['}']
  | .bar => ['|']
  | .semi => [';']
  | .atSign => ['@']
  | .ident s => s.toList

/-- Emit a pending name (if any) before the tokens `ts`. -/
def flush (acc : List Char) (ts : List Tok) : List Tok :=
  match acc with
  | [] => ts
  | _ :: _ => .ident (String.mk acc) :: ts

/-- The lexer, with an accumulator for the name being read. -/
def lexAux : List Char → List Char → List Tok
  | [], acc => flush acc []
  | c :: cs, acc =>
    match specialTok? c with
    | some t => flush acc (t :: lexAux cs [])
    | none => if c.isWhitespace then flush acc (lexAux cs []) else lexAux cs (acc ++ [c])

/-- Split a string into tokens. Whitespace separates names and is otherwise ignored. -/
def lex (s : String) : List Tok := lexAux s.toList []

/-- Whether the printer puts a space between two consecutive tokens. Two names are always
separated; no space is put inside brackets and braces or around `@`. -/
def space : Tok → Tok → Bool
  | .ident _, .ident _ => true
  | .lbrack, _ => false
  | .lbrace, _ => false
  | .atSign, _ => false
  | _, .rbrack => false
  | _, .rbrace => false
  | _, .atSign => false
  | _, _ => true

/-- The characters of a token list, with the spacing of `space`. -/
def render : List Tok → List Char
  | [] => []
  | [t] => t.chars
  | t :: t' :: ts => t.chars ++ ((if space t t' then [' '] else []) ++ render (t' :: ts))

/-- A token is well formed if it is not a name, or a valid name. -/
def Tok.wf : Tok → Bool
  | .ident s => validName s
  | _ => true

/-! ## Numerals -/

/-- The character of a decimal digit. -/
def digitChar : ℕ → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

/-- The value of a decimal digit character. -/
def charDigit? : Char → Option ℕ
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3 | '4' => some 4
  | '5' => some 5 | '6' => some 6 | '7' => some 7 | '8' => some 8 | '9' => some 9
  | _ => none

/-- The decimal numeral of a natural number. -/
def natChars (n : ℕ) : List Char :=
  if n = 0 then ['0'] else ((Nat.digits 10 n).reverse.map digitChar)

/-- Read the digits `l` onto the accumulator `acc`. -/
def readDigits : ℕ → List Char → Option ℕ
  | acc, [] => some acc
  | acc, c :: cs =>
    match charDigit? c with
    | some d => readDigits (10 * acc + d) cs
    | none => none

/-- Parse a nonempty decimal numeral. -/
def parseNat? (l : List Char) : Option ℕ :=
  match l with
  | [] => none
  | _ :: _ => readDigits 0 l

/-! ## Printing -/

section Print

variable {S : Signature.{u₀, u₁, u₂}} [DSLNames S]

open DSLNames

/-- Tokens of the region prefix. -/
def regionToks (r : S.Region) : List Tok :=
  if regionName r = "" then [] else [.lbrace, .ident (regionName r), .rbrace]

/-- Tokens of a word of colours. -/
def wordToks (w : List S.Colour) : List Tok :=
  match soleColour? (S := S) with
  | some _ => [.ident (String.mk (natChars w.length))]
  | none => .lbrack :: (w.map fun c => .ident (colourName c)) ++ [.rbrack]

/-- Tokens of an object. -/
def objToks (a : Obj S) : List Tok := regionToks a.start ++ wordToks a.word

/-- Tokens of a layer `gen@k`. -/
def layerToks (L : Layer S) : List Tok :=
  [.ident (genName L.gen), .atSign, .ident (String.mk (natChars L.left.length))]

/-- Tokens of a nonempty list of layers, separated by `;`. -/
def layersToks : List (Layer S) → List Tok
  | [] => []
  | [L] => layerToks L
  | L :: L' :: ls => layerToks L ++ .semi :: layersToks (L' :: ls)

/-- Tokens of a diagram given by its source object and its layers. -/
def printToks (a : Obj S) (ls : List (Layer S)) : List Tok :=
  match ls with
  | [] => objToks a
  | _ :: _ => objToks a ++ .bar :: layersToks ls

/-- Print a diagram given by its source object and its layers (bottom to top). Only the
lengths of the `left` fields and the generators of the layers are printed; the remaining
data is recovered by the parser from the running boundary. -/
def print (a : Obj S) (ls : List (Layer S)) : String := String.mk (render (printToks a ls))

/-- Print an object. -/
def printObj (a : Obj S) : String := String.mk (render (objToks a))

end Print

/-! ## Parsing -/

section Parse

variable {S : Signature.{u₀, u₁, u₂}} [DSLNames S] [DecidableEq S.Colour]

open DSLNames

/-- Look up a region by name. -/
def lookupRegion (n : String) (ts : List Tok) : Except String (S.Region × List Tok) :=
  match regionOfName? (S := S) n with
  | some r => .ok (r, ts)
  | none =>
    if n = "" then .error "a region label '{…}' is required"
    else .error s!"unknown region '{n}'"

/-- Parse the optional region prefix. -/
def parseRegion : List Tok → Except String (S.Region × List Tok)
  | .lbrace :: .ident n :: .rbrace :: ts => lookupRegion n ts
  | .lbrace :: .rbrace :: ts => lookupRegion "" ts
  | .lbrace :: _ => .error "expected a region name followed by '}'"
  | ts => lookupRegion "" ts

/-- Parse colour names up to the closing `]`. -/
def parseColours : List Tok → Except String (List S.Colour × List Tok)
  | .rbrack :: ts => .ok ([], ts)
  | .ident n :: ts =>
    match colourOfName? (S := S) n with
    | some c =>
      match parseColours ts with
      | .ok (w, ts') => .ok (c :: w, ts')
      | .error e => .error e
    | none => .error s!"unknown colour '{n}'"
  | _ => .error "expected a colour name or ']'"

/-- Parse a word: `[c₁ … cₙ]`, or a width for a single-colour signature. -/
def parseWord : List Tok → Except String (List S.Colour × List Tok)
  | .lbrack :: ts => parseColours ts
  | .ident n :: ts =>
    match soleColour? (S := S) with
    | some c =>
      match parseNat? n.toList with
      | some k => .ok (List.replicate k c, ts)
      | none => .error s!"expected a width, got '{n}'"
    | none => .error "a width is only allowed for a single-colour signature; expected '['"
  | _ => .error "expected '[' or a width"

/-- Parse one layer `g@k` on the boundary word `w`, with leftmost region `r₀`. -/
def parseLayer (r₀ : S.Region) (w : List S.Colour) (g k : String) :
    Except String (Layer S) :=
  match parseNat? k.toList with
  | none => .error s!"expected a position after '{g}@', got '{k}'"
  | some n =>
    if n ≤ w.length then
      match genOfName? g (S.endR r₀ (w.take n)) (w.drop n) with
      | none => .error s!"no generator '{g}' at position {n}"
      | some gen =>
        if (S.dom gen).isPrefixOf (w.drop n) then
          .ok ⟨r₀, w.take n, gen, (w.drop n).drop (S.dom gen).length⟩
        else .error s!"the bottom boundary of '{g}' does not match the strands at position {n}"
    else .error s!"position {n} of '{g}' exceeds the width {w.length}"

/-- Parse a nonempty list of layers separated by `;`, starting from the boundary word `w`. -/
def parseLayers (r₀ : S.Region) : List S.Colour → List Tok → Except String (List (Layer S))
  | w, .ident g :: .atSign :: .ident k :: ts =>
    match parseLayer r₀ w g k with
    | .error e => .error e
    | .ok L =>
      match ts with
      | [] => .ok [L]
      | .semi :: ts' =>
        match parseLayers r₀ L.cod.word ts' with
        | .ok ls => .ok (L :: ls)
        | .error e => .error e
      | _ => .error "expected ';' or the end of the diagram"
  | _, _ => .error "expected a layer 'generator@position'"

/-- Parse a token list into a source object and a list of layers. -/
def parseToks (ts : List Tok) : Except String (Obj S × List (Layer S)) :=
  match parseRegion (S := S) ts with
  | .error e => .error e
  | .ok (r, ts) =>
    match parseWord (S := S) ts with
    | .error e => .error e
    | .ok (w, ts) =>
      match ts with
      | [] => .ok (⟨r, w⟩, [])
      | .bar :: ts =>
        match parseLayers r w ts with
        | .ok ls => .ok (⟨r, w⟩, ls)
        | .error e => .error e
      | _ => .error "expected '|' or the end of the diagram"

/-- Parse a diagram into its source object and its layers (bottom to top). The layers
produced are consistent with the running boundary; region compatibility is not checked
here (see `parseDiagram`). -/
def parse (s : String) : Except String (Obj S × List (Layer S)) := parseToks (lex s)

end Parse

/-! ## Lawful names and the round trip -/

end DSL

open DSL in
/-- Conditions under which `DSL.parse` inverts `DSL.print` on well-typed diagrams: lookups
invert the printed names, printed names are valid names (region names may also be empty),
a generator is recovered from its name, its left region and any boundary beginning with its
bottom boundary, and `soleColour?` is only set for a signature with one colour. -/
class LawfulDSLNames (S : Signature.{u₀, u₁, u₂}) [DSLNames S] : Prop where
  regionOfName_regionName (r : S.Region) :
    DSLNames.regionOfName? (DSLNames.regionName r) = some r
  regionName_valid (r : S.Region) :
    DSLNames.regionName r = "" ∨ validName (DSLNames.regionName r) = true
  colourOfName_colourName (c : S.Colour) :
    DSLNames.colourOfName? (DSLNames.colourName c) = some c
  colourName_valid (c : S.Colour) : validName (DSLNames.colourName c) = true
  genOfName_genName (g : S.Gen) (rest : List S.Colour) :
    DSLNames.genOfName? (DSLNames.genName g) (S.left g) (S.dom g ++ rest) = some g
  genName_valid (g : S.Gen) : validName (DSLNames.genName g) = true
  soleColour_eq {c₀ : S.Colour} (h : DSLNames.soleColour? (S := S) = some c₀) (c : S.Colour) :
    c = c₀

namespace DSL

section Lex

theorem isNameChar_iff {c : Char} :
    isNameChar c = true ↔ specialTok? c = none ∧ c.isWhitespace = false := by
  simp [isNameChar, Option.isNone_iff_eq_none]

theorem validName_iff {s : String} :
    validName s = true ↔ s.toList ≠ [] ∧ s.toList.all isNameChar = true := by
  simp [validName, List.isEmpty_iff]

theorem flush_of_ne_nil {l : List Char} (h : l ≠ []) (ts : List Tok) :
    flush l ts = .ident (String.mk l) :: ts := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

@[simp] theorem flush_nil (ts : List Tok) : flush [] ts = ts := rfl

theorem lexAux_special {c : Char} {t : Tok} (h : specialTok? c = some t) (cs acc : List Char) :
    lexAux (c :: cs) acc = flush acc (t :: lexAux cs []) := by
  simp [lexAux, h]

theorem lexAux_space (cs acc : List Char) : lexAux (' ' :: cs) acc = flush acc (lexAux cs []) := by
  simp [lexAux, specialTok?]

theorem lexAux_append_name : ∀ (n : List Char), n.all isNameChar = true →
    ∀ (rest acc : List Char), lexAux (n ++ rest) acc = lexAux rest (acc ++ n)
  | [], _, rest, acc => by simp
  | c :: n, h, rest, acc => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h₁, h₂⟩ := isNameChar_iff.1 h.1
    simp only [List.cons_append, lexAux, h₁, h₂, Bool.false_eq_true, ↓reduceIte]
    rw [lexAux_append_name n h.2, List.append_assoc, List.singleton_append]

/-- Whether a token is a name. -/
def Tok.isIdent : Tok → Bool
  | .ident _ => true
  | _ => false

theorem Tok.chars_of_not_ident {t : Tok} (ht : t.isIdent = false) :
    ∃ c, t.chars = [c] ∧ specialTok? c = some t := by
  cases t <;> first | exact ⟨_, rfl, rfl⟩ | simp [Tok.isIdent] at ht

/-- The characters following the first token in `render (t :: ts)`. -/
def renderTail (t : Tok) : List Tok → List Char
  | [] => []
  | t' :: ts => (if space t t' then [' '] else []) ++ render (t' :: ts)

theorem render_cons (t : Tok) (ts : List Tok) : render (t :: ts) = t.chars ++ renderTail t ts := by
  cases ts <;> simp [render, renderTail]

theorem lexAux_render_of_not_ident {t : Tok} (ht : t.isIdent = false) (ts : List Tok)
    (acc : List Char) :
    lexAux (render (t :: ts)) acc = flush acc (lexAux (render (t :: ts)) []) := by
  obtain ⟨c, hc, hct⟩ := Tok.chars_of_not_ident ht
  rw [render_cons, hc, List.singleton_append, lexAux_special hct, lexAux_special hct, flush_nil]

theorem lexAux_renderTail_nil (t : Tok) (ts : List Tok) (ih : lexAux (render ts) [] = ts) :
    lexAux (renderTail t ts) [] = ts := by
  cases ts with
  | nil => rfl
  | cons t' ts =>
    simp only [renderTail]
    split
    · rw [List.singleton_append, lexAux_space, flush_nil, ih]
    · rw [List.nil_append, ih]

/-- Lexing inverts rendering on well-formed token lists. -/
theorem lexAux_render : ∀ ts : List Tok, ts.all Tok.wf = true → lexAux (render ts) [] = ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := lexAux_render ts h.2
    rw [render_cons]
    cases t with
    | ident s =>
      obtain ⟨hne, hs⟩ := validName_iff.1 h.1
      rw [Tok.chars, lexAux_append_name _ hs, List.nil_append]
      have : lexAux (renderTail (.ident s) ts) s.toList = flush s.toList ts := by
        cases ts with
        | nil => rfl
        | cons t' ts =>
          simp only [renderTail]
          split
          · rw [List.singleton_append, lexAux_space, ih]
          · rename_i hsp
            have ht' : t'.isIdent = false := by
              cases t' <;> simp_all [space, Tok.isIdent]
            rw [List.nil_append, lexAux_render_of_not_ident ht', ih]
      rw [this, flush_of_ne_nil hne]
      rfl
    | _ =>
      rw [Tok.chars, List.singleton_append, lexAux_special rfl, flush_nil,
        lexAux_renderTail_nil _ _ ih]

theorem lex_mk_render {ts : List Tok} (h : ts.all Tok.wf = true) :
    lex (String.mk (render ts)) = ts :=
  lexAux_render ts h

end Lex

section Numerals

theorem isNameChar_digitChar (d : ℕ) : isNameChar (digitChar d) = true := by
  unfold digitChar; split <;> decide

theorem charDigit_digitChar {d : ℕ} (h : d < 10) : charDigit? (digitChar d) = some d := by
  interval_cases d <;> rfl

theorem readDigits_map_digitChar :
    ∀ (L : List ℕ), (∀ d ∈ L, d < 10) → ∀ acc,
      readDigits acc (L.map digitChar) = some (L.foldl (fun a d => 10 * a + d) acc)
  | [], _, _ => rfl
  | d :: L, h, acc => by
    simp only [List.map_cons, readDigits, charDigit_digitChar (h d (by simp)), List.foldl_cons]
    exact readDigits_map_digitChar L (fun d hd => h d (by simp [hd])) _

theorem foldl_reverse_eq_ofDigits :
    ∀ (L : List ℕ) (acc : ℕ),
      L.reverse.foldl (fun a d => 10 * a + d) acc = acc * 10 ^ L.length + Nat.ofDigits 10 L
  | [], acc => by simp
  | d :: L, acc => by
    rw [List.reverse_cons, List.foldl_append, foldl_reverse_eq_ofDigits L acc]
    simp only [List.foldl_cons, List.foldl_nil, List.length_cons, Nat.ofDigits_cons, pow_succ]
    ring

theorem natChars_ne_nil (n : ℕ) : natChars n ≠ [] := by
  unfold natChars
  split
  · simp
  · simpa [Nat.digits_ne_nil_iff_ne_zero]

theorem parseNat_natChars (n : ℕ) : parseNat? (natChars n) = some n := by
  have hne := natChars_ne_nil n
  have : parseNat? (natChars n) = readDigits 0 (natChars n) := by
    cases h : natChars n with
    | nil => exact absurd h hne
    | cons _ _ => rfl
  rw [this]
  unfold natChars
  split
  · subst_vars; rfl
  · rw [readDigits_map_digitChar _ (fun d hd => Nat.digits_lt_base (by norm_num)
      (List.mem_reverse.1 hd)), foldl_reverse_eq_ofDigits, Nat.ofDigits_digits]
    simp

theorem validName_natChars (n : ℕ) : validName (String.mk (natChars n)) = true :=
  validName_iff.2 ⟨natChars_ne_nil n, by
    unfold natChars; split
    · decide
    · simp [List.all_map, Function.comp_def, isNameChar_digitChar]⟩

end Numerals

section RoundTrip

variable {S : Signature.{u₀, u₁, u₂}} [DSLNames S] [LawfulDSLNames S]

open DSLNames LawfulDSLNames

theorem printToks_wf (a : Obj S) (ls : List (Layer S)) : (printToks a ls).all Tok.wf = true := by
  have hobj : (objToks a).all Tok.wf = true := by
    simp only [objToks, List.all_append, Bool.and_eq_true]
    constructor
    · unfold regionToks; split
      · rfl
      · rename_i h
        simp [Tok.wf, (regionName_valid a.start).resolve_left h]
    · unfold wordToks; split
      · simp [Tok.wf, validName_natChars]
      · simp [Tok.wf, colourName_valid]
  have hls : ∀ ls : List (Layer S), (layersToks ls).all Tok.wf = true := by
    intro ls
    induction ls with
    | nil => rfl
    | cons L ls ih =>
      cases ls with
      | nil => simp [layersToks, layerToks, Tok.wf, genName_valid, validName_natChars]
      | cons L' ls =>
        simp only [layersToks] at ih ⊢
        simp [layerToks, Tok.wf, genName_valid, validName_natChars, ih]
  unfold printToks; split
  · exact hobj
  · simp [hobj, hls, Tok.wf]

omit [LawfulDSLNames S] in
theorem lookupRegion_of_eq {n : String} {r : S.Region} (h : regionOfName? n = some r)
    (ts : List Tok) : lookupRegion n ts = .ok (r, ts) := by
  simp [lookupRegion, h]

theorem parseRegion_objToks (a : Obj S) (rest : List Tok) :
    parseRegion (S := S) (objToks a ++ rest) = .ok (a.start, wordToks a.word ++ rest) := by
  have hl := regionOfName_regionName a.start
  unfold objToks regionToks
  split
  · rename_i h
    rw [h] at hl
    simp only [List.nil_append]
    unfold wordToks
    split <;> exact lookupRegion_of_eq hl _
  · exact lookupRegion_of_eq hl _

theorem parseColours_map (w : List S.Colour) (rest : List Tok) :
    parseColours (S := S) ((w.map fun c => .ident (colourName c)) ++ .rbrack :: rest) =
      .ok (w, rest) := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [parseColours, colourOfName_colourName, ih]

theorem parseWord_wordToks (w : List S.Colour) (rest : List Tok) :
    parseWord (S := S) (wordToks w ++ rest) = .ok (w, rest) := by
  unfold wordToks
  split
  · rename_i c₀ hc
    simp only [List.cons_append, List.nil_append, parseWord, hc]
    rw [String.toList, parseNat_natChars]
    have : List.replicate w.length c₀ = w :=
      (List.eq_replicate_iff.2 ⟨rfl, fun c _ => soleColour_eq hc c⟩).symm
    dsimp only
    rw [this]
  · simp only [List.cons_append, List.append_assoc, List.singleton_append, parseWord]
    exact parseColours_map w rest

variable [DecidableEq S.Colour]

theorem parseLayer_eq {r₀ : S.Region} {L : Layer S} (hv : L.Valid) (hs : L.start = r₀) :
    parseLayer r₀ L.dom.word (genName L.gen) (String.mk (natChars L.left.length)) = .ok L := by
  have hw : L.dom.word = L.left ++ (S.dom L.gen ++ L.right) := by simp
  have hg := genOfName_genName L.gen L.right
  have hend : S.endR r₀ L.left = S.left L.gen := hs ▸ hv.left_end
  simp only [parseLayer, String.toList, parseNat_natChars, hw, List.take_left, List.drop_left,
    hend, hg, List.isPrefixOf_iff_prefix, List.prefix_append, ↓reduceIte, List.length_append]
  simp only [Nat.le_add_right, ↓reduceIte, Except.ok.injEq]
  cases L; subst hs; rfl

theorem parseLayers_layersToks :
    ∀ (ls : List (Layer S)) (a b : Obj S), Chain a ls b → ls ≠ [] →
      parseLayers a.start a.word (layersToks ls) = .ok ls
  | [], _, _, _, h => absurd rfl h
  | L :: ls, a, b, ⟨hv, hdom, hc⟩, _ => by
    have hL : parseLayer a.start a.word (genName L.gen)
        (String.mk (natChars L.left.length)) = .ok L := by
      rw [← hdom]; exact parseLayer_eq hv rfl
    cases ls with
    | nil => simp [layersToks, layerToks, parseLayers, hL]
    | cons L' ls =>
      have ih := parseLayers_layersToks (L' :: ls) L.cod b hc (List.cons_ne_nil _ _)
      have hst : L.cod.start = a.start := by rw [← hdom]; rfl
      rw [hst] at ih
      simp only [Layer.cod_word, List.append_assoc] at ih
      simp [layersToks, layerToks, parseLayers, hL, ih]

theorem parseToks_printToks {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    parseToks (printToks a ls) = .ok (a, ls) := by
  unfold printToks
  split
  · have := parseRegion_objToks a []
    rw [List.append_nil] at this
    have hw := parseWord_wordToks a.word []
    rw [List.append_nil] at hw
    simp only [parseToks, this, List.append_nil, hw]
  · rename_i L ls
    simp only [parseToks, parseRegion_objToks, parseWord_wordToks,
      parseLayers_layersToks _ a b h (List.cons_ne_nil _ _)]

/-- **Round trip.** For lawful names, parsing the printed form of a well-typed layer list
returns the source object and the layers. -/
theorem parse_print {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    parse (print a ls) = .ok (a, ls) := by
  rw [parse, print, lex_mk_render (printToks_wf a ls), parseToks_printToks h]

end RoundTrip

/-! ## Typed diagrams -/

section Typed

variable {S : Signature.{u₀, u₁, u₂}} [DSLNames S]

/-- Print a typed diagram. -/
def printHom {a b : Obj S} (f : a ⟶ b) : String := print a (Diagram.layers f)

variable [DecidableEq S.Region] [DecidableEq S.Colour]

/-- The typed diagram with the given source and layers, if the layers form a chain. -/
def toDiagram? (a : Obj S) (ls : List (Layer S)) : Option (a ⟶ Chain.target a ls) :=
  if h : Chain a ls (Chain.target a ls) then some (Diagram.mk ls h) else none

/-- Parse a typed diagram together with its source and target. -/
def parseDiagram (s : String) : Except String ((a : Obj S) × (b : Obj S) × (a ⟶ b)) :=
  match parse (S := S) s with
  | .error e => .error e
  | .ok (a, ls) =>
    if h : Chain a ls (Chain.target a ls) then .ok ⟨a, _, Diagram.mk ls h⟩
    else .error "the layers are not well typed (region mismatch)"

/-- Parse a typed diagram `a ⟶ b` with prescribed source and target. -/
def parseHom (a b : Obj S) (s : String) : Except String (a ⟶ b) :=
  match parse (S := S) s with
  | .error e => .error e
  | .ok (a', ls) =>
    if a' = a then
      if h : Chain a ls b then .ok (Diagram.mk ls h)
      else .error "the layers do not form a well-typed diagram with the given target"
    else .error "the source object does not match"

/-- **Round trip for typed diagrams.** For lawful names, `parseHom a b` inverts `printHom`
on diagrams `a ⟶ b`. -/
theorem parseHom_printHom [LawfulDSLNames S] {a b : Obj S} (f : a ⟶ b) :
    parseHom a b (printHom f) = .ok f := by
  simp only [parseHom, printHom, parse_print (Diagram.chain f), ↓reduceIte,
    dif_pos (Diagram.chain f)]
  rfl

/-- Whether `parse (print a ls)` returns exactly `(a, ls)` (a decidable check, for tests). -/
def roundTrips [DecidableEq S.Gen] (a : Obj S) (ls : List (Layer S)) : Bool :=
  match parse (S := S) (print a ls) with
  | .ok (a', ls') => decide (a' = a ∧ ls' = ls)
  | .error _ => false

end Typed

end DSL

end StringDiagrams
