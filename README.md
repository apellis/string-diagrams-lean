# string-diagrams-lean

A Lean 4 library for diagrammatic reasoning: typed diagram syntax, presentations by generators and relations, interpretations, and Lean-checked diagram rewriting.

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain
`leanprover/lean4:v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` are
pinned.

```sh
lake exe cache get
lake build
```

## Notation and drawings

`StringDiagrams.DSL` provides a one-line notation for layered diagrams, e.g.
`[i i j] | x@0 ; psi@1 ; psi@0` (source object, then layers `generator@position` from
bottom to top), with a printer, a parser and the round-trip theorem `DSL.parse_print`.
`StringDiagrams.Render` draws diagrams as SVG (embedding the notation as metadata) and
TikZ. Drawings are presentation only; they are not evidence for any statement. Example
drawings are written to `out/` by

```sh
lake env lean --run scripts/render_examples.lean
```

## License

Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
