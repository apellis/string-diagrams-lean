# Contributor guide

This repository is developed largely by AI agents under human direction. Everything here is
public: keep it mathematical and technical.

## Ground rules

- The toolchain (`lean-toolchain`) and Mathlib and sibling-library pins (`lake-manifest.json`)
  are fixed. Do not run `lake update` except as a deliberate, coordinated bump. Build with
  `lake exe cache get` and then `lake --wfail build`. Warnings are errors.
- Before presenting a result as done, run `lake env lean -DwarningAsError=true scripts/AxiomAudit.lean`
  (CI runs it as well). Committed files contain no `sorry`, `admit`, `native_decide` or new
  `axiom`. The axiom closure is contained in `propext`, `Classical.choice` and `Quot.sound`.
  Compilation alone is not the acceptance criterion; source fidelity is.
- Dependencies: Mathlib only. This library is generic. It must not import `OddMath` or `Categorification`, and odd-specific generators, signs and interpretations belong downstream.
- Record the source of every main result in its docstring: paper and version, section, and
  theorem or equation number. Check each locator in the cited version. Distinguish the literal
  printed statement, a repaired statement, a proof gap and a counterexample. Never weaken a
  hypothesis or change a sign silently to make something compile.
- New modules go in a topical directory under `StringDiagrams/`, with a module docstring that names the
  source results they formalize.
- Commit messages describe the mathematics, not the process.

## Staying on course

These rules apply to every contributor and take precedence over local habits or private
instructions that conflict with them.

**Targets and scope**

- Every PR advances a specific numbered result of a cited source (theorem, proposition,
  corollary, lemma, definition or equation) or a roadmap item that one of them needs. The PR
  title or body names it. Supporting lemmas land with, or shortly before, the result that uses
  them.
- Formalize what the source states. Do not label results "original", and do not develop new
  theory when a source step is missing. When a cited proof relies on a reference that is not
  available, on a step that has a gap, or on a result outside the library, stop and record this
  in the tracking issue as a question for the maintainer. The options are: (a) obtain the
  reference; (b) take the missing input as an explicit, documented hypothesis of the dependent
  results; (c) build a replacement route. Do not start (c) without the maintainer's approval.
- Scope decisions are the maintainer's. These include declaring a numbered result out of scope,
  choosing between several valid conventions, and substituting a different object for the one
  the source uses (for example a crystal basis for a canonical basis). List them as open
  questions; do not decide them silently.
- Effort budget: suppose a sub-route has taken about five PRs, or about 3000 lines, without a
  numbered result landing. Stop and post in the tracking issue: what is done, what remains, and
  an honest estimate of the distance to the numbered result. Then wait for the maintainer before
  continuing that sub-route.
- Prove one form of a result. Restate it in another form (maps → bimodule maps → natural
  isomorphisms → mates, and so on) only when a named downstream result needs that form.

**Statements**

- A headline statement carries exactly the source's hypotheses, after any recorded erratum
  correction.
- An extra hypothesis that the current proof route needs is allowed only on an intermediate
  statement. Its docstring must say so, the README status must say so, and a roadmap item must
  track its removal.
- Names, docstrings and status tables never overstate. Do not use `_unconditional` on a
  conditional theorem, and do not use "full" or "complete" for a statement that assumes part of
  its conclusion.
- An erratum entry gives the printed statement, the corrected statement with the extra
  hypothesis or correction, the declarations, and a short paragraph that can be sent to the
  authors as is.

**Lean engineering**

- Elaboration trouble is not a mathematical obstruction. Examples: `whnf` or `isDefEq` timeouts
  on dependent transports, heartbeat limits, motive errors, slow instance search.
- After two failed attempts at the same proof, redesign the encoding. Possible changes: reindex
  so that the types agree definitionally, prove one generic lemma instead of many instances, or
  avoid nested casts. Do not raise `maxHeartbeats` or retry with a larger budget.
- Names of declarations, modules and PRs describe the mathematics. Avoid process adjectives
  ("actual", "genuine", "original", "native", "fixed", "frontier"), stage labels (`LegA`,
  `AdapterB7`, `PbwL3`) and "WIP". A PR whose title says WIP is not merged.

**Workflow and evidence**

- All proof work happens on topic branches of this repository and lands through PRs with green
  CI. Work that does not build yet may be pushed as a draft PR. Proof developments are not kept
  in private copies, scratch archives or other repositories.
- The evidence that a result is done is CI: full build with warnings as errors, plus the axiom
  audit. Agreement between reviewers, private sign-offs, hash manifests and log archives are not
  evidence. Do not commit logs, manifests, archives or review packets.
- The same PR updates the README/ROADMAP status row and the tracking issue. Close an issue when
  its goal is met.
