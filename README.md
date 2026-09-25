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

## License

Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
