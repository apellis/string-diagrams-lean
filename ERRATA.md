# Errata and corrected statements

## Brundan–Ellis, *Super Kac–Moody 2-categories*, §11: parity and freeness

**Source.** J. Brundan and A. P. Ellis, arXiv:1701.04133v2, first preliminary
fact of §11, used in Theorem 11.3.

**Printed assertion.** For a Laurentian graded superalgebra, the category of
finitely generated graded projective supermodules has the Krull–Schmidt
property, and its split Grothendieck group is free over
`ℒ = ℤ[π]/(π²−1)[q,q⁻¹]`, with an integral basis consisting of the
indecomposable isomorphism classes.

**Correction.** Integral Krull–Schmidt freeness does not imply covering-ring
freeness. A parity-self-isomorphic nonzero indecomposable (type Q) contributes
an orbit summand on which `π` acts as `1`, not a free parity-ring summand.
Without integer grading, the precise replacement is:

> In a Hom-finite, idempotent-complete linear Π-category with binary
> biproducts, the split Grothendieck group is free over `Zπ` if and only if
> no nonzero indecomposable is isomorphic to its parity shift. When this
> holds, one representative from each parity pair gives a `Zπ`-basis.

This statement is valid for infinitely many indecomposables. The obstruction
is the quotient of parity-fixed vectors by norms `x + πx`: a fixed integral
basis vector has odd coordinate at itself and hence is not a norm, whereas
every fixed vector in a free `Zπ`-module is a norm. The mere existence of a
fixed vector is not an obstruction: free modules also have fixed vectors.

**Declarations.** `KrullSchmidt.k0_free_zpi_iff`,
`KrullSchmidt.parityBasis`, `KrullSchmidt.indec_not_norm`,
`ParityBasis.TateZero`, `ParityBasis.fixed_tate_ne_zero`, and
`ParityBasis.free_iff_norm_surjective`. The hypotheses and integral basis
are derived for finite-dimensional superalgebras and graded-superalgebras
in `SKarAlg.k0_free_zpi_iff` and `GSKarAlg.k0_free_zpi_iff`.

**Concrete checks.** The even rational field has a free parity module
(`KrullSchmidtParityExamples.typeM_free`, `typeMPairedBasis`). The
finite-dimensional superalgebra `ℚ[c]/(c²−1)`, with `c` odd, has an
indecomposable regular projective isomorphic to its parity shift
(`typeQ_indec`, `typeQParityIso`). Its split Grothendieck group is not
`Zπ`-free, and the regular projective gives a nonzero Tate class
(`typeQ_not_free`, `typeQ_tate_ne_zero`).

**Laurentian envelope theorem.** For a graded supercategory with degreewise
finite-dimensional, bounded-below Homs, `GSKar.k0_free_laurentInt` proves
`R = ℤ[q,q⁻¹]`-freeness on the existing K₀. `KrullSchmidt.laurentBasis` is the
basis indexed by integer-shift orbits of indecomposables.
`GradedSupercategory.qPow_iso_degree_zero` isolates the rigidity argument:
a nonzero object with bounded-below graded endomorphisms cannot admit a
degree-zero isomorphism to a nontrivial integer shift. The rational graded
field supplies a nonzero rank-one example with every hypothesis proved.

**Mixed Laurent decomposition.** `KrullSchmidt.laurentDecomposition` now gives
`K₀ ≅ (⨁_M ℒ) ⊕ (⨁_Q ℒ/(π−1))`, where M and Q are paired and fixed parity
orbits on the integer-shift orbit set. `laurentParity_fixed_iff` identifies the
fixed orbits with parity-self-associate indecomposables: parity squared and
integer-shift rigidity eliminate any nonzero grading twist.
`GSKar.laurentDecomposition` and `GSKarAlg.laurentDecomposition` derive the
statement from degreewise Hom-finiteness and lower bounds. The rational
projective has nonzero coordinates, and the type-Q quotient has nonzero unit.

**Formalization boundary.** The identification of the graded envelope with
graded left projectives remains separate. Neither Theorem 11.3 nor Theorem 11.7
itself is claimed here.

**Author-ready explanation.** The first preliminary fact in §11 needs to
separate the integral Krull–Schmidt basis from the covering-ring module
structure. Parity acts by an involution on the integral basis. Two-element
orbits yield free `ℤ[π]/(π²−1)` summands, while one-element orbits yield
summands with `π=1`. Thus a covering-ring freeness statement needs an
exclusion of type-Q indecomposables, with the grading-shift analysis supplied
separately. The fixed-point-modulo-norm quotient detects this obstruction
without a finite-rank assumption.
