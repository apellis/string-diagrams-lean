import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Tactic.Abel

/-!
# Rewriting words in a noncommutative ring

In an endomorphism ring of a diagrammatic category, a diagram built from generators by
vertical composition is a *word* in the generators, and a diagrammatic argument is a sequence
of local rewrites of subwords together with far commutativity (sliding a generator past a
distant one). This file provides tactics which perform these steps directly on expressions in
an arbitrary (semi)ring, so that a rewrite can be applied to any contiguous subword without
first reassociating by hand.

## Normal form

All tactics first put expressions into the *word normal form*: products are right-associated,
multiplication is distributed over `+` and `-`, negations and scalar multiplications are pulled
out of products, and the unit and zero laws are applied. Concretely this is `simp only` with
`mul_assoc`, `mul_add`, `add_mul`, `mul_sub`, `sub_mul`, `neg_mul`, `mul_neg`,
`smul_mul_assoc`, `mul_smul_comm`, `mul_one`, `one_mul`, `mul_zero`, `zero_mul`, `add_zero`,
`zero_add`, `sub_zero`, `zero_sub`, `neg_zero`, `neg_neg`, `smul_zero` (applied to every
subterm, with no other simp lemmas or simprocs). A *word* is a maximal right-associated product
`a₁ * (a₂ * (⋯ * a_k))`; its *letters* `aᵢ` are the maximal subterms which are not products.

## Tactics

* `word_norm` / `word_norm at h`: put the goal (or `h`) into word normal form.
* `word_rw [e₁, ← e₂, …]` / `word_rw [e] at h`: rewrite with each equation `eᵢ` in turn,
  modulo associativity. Let `e : ∀ xs, hyps → lhs = rhs` with `lhs` a product of letters
  `a₁, …, a_k` (in any association). The goal is normalized, and the variables `xs` are
  instantiated by matching `a₁, …, a_k` (up to reducible defeq with instances) against a
  contiguous run of letters of a word of the goal; words are visited in pre-order and positions
  from left to right, and the first match whose propositional hypotheses are all proved by the
  discharger is used (if there is none, the first match is used and its hypotheses become new
  goals). The instantiated equation is then used, in word normal form, either as it stands
  (for an occurrence at the end of a word) or in the form `lhs * t = rhs * t` (for an occurrence
  followed by a tail `t`), by `rw`; thus all occurrences of that instance with that tail are
  rewritten. If no match is found, the quantified forms of these two equations are tried
  directly with `rw`. Afterwards the goal is renormalized and `with_reducible rfl` is tried.
  Side conditions are attempted with the discharger (default `first | assumption | omega`;
  override with `word_rw (disch := tac) [...]`); those not discharged remain as new goals after
  the main goal.
* `word_comm [c₁, …]`: prove an equation between linear combinations of words which agree
  after reordering letters by commutations. Each `cᵢ : ∀ xs, hyps → a * b = b * a` is a
  (possibly conditional) commutation lemma, used in either direction; side conditions are
  discharged by the discharger (default `first | assumption | omega`). Two letters that are
  syntactically equal always commute. Every word on both sides is brought to a canonical
  representative of its commutation class (see below); the goal is then closed by
  `with_reducible rfl` or, failing that, by `abel1` (so the summands may appear in different
  orders and with different groupings).
* `word_comm_nf [c₁, …]` / `word_comm_nf [c₁, …] at h`: the same normalization, without
  trying to close the goal.

A typical use of commutation before a rewrite is
`word_rw [(show w = w' by word_comm [c]), e]`, where `w'` brings together the letters of the
left-hand side of `e`.

## The commutation normal form

For each word the tactic computes the lexicographically least word (for the total order
`Lean.Expr.lt` on letters) reachable by commuting adjacent letters, using the greedy algorithm
of the theory of trace monoids: among the letters that commute with every letter to their left,
move the least one (the leftmost among equal ones) to the front, and recurse on the rest.
If commutation of letters is decided exactly (that is, whenever the provided lemmas and the
discharger establish `a * b = b * a` for every pair of letters that commute in the intended
partially commutative monoid, and the relation is symmetric), then two words are related by
commutations if and only if their normal forms coincide.

## Limitations

* The left-hand side of a `word_rw` rule should be a word; a rule whose left-hand side is a sum
  is only found if that sum occurs literally (up to reducible defeq) in the normalized goal.
* Letters are matched up to reducible defeq with instances (as in `rw`); in particular a letter
  whose index is written differently (`x (i + 1)` vs `x (1 + i)`) does not match.
* Like `rw`, `word_rw` rewrites every occurrence of the chosen instance (not only the matched
  one), and cannot rewrite under binders. Only letters of words are matched: a letter of the
  rule matches exactly one letter of the goal, so a rule letter that is a variable standing for
  a product only matches a single letter.
* Normalization rewrites every subterm, including the arguments of letters (for example
  `f (a * b * c)` becomes `f (a * (b * c))`); the rules are normalized in the same way.
* `word_comm` does not use any relation other than the given commutations (and `abel1` on
  the resulting linear combination); in particular it does not cancel or combine scalars
  beyond what `abel1` does, and it only commutes letters whose commutation lemma instantiates
  by unification with the letters themselves.
* Commutation is decided by the lemmas and the discharger: if a side condition is true but
  not provable by the discharger, the two letters are treated as non-commuting (soundness is
  unaffected; `word_comm` may then fail).
-/

namespace StringDiagrams.WordRw

/-- Commuting two letters in front of a tail. -/
theorem swap_cons {α : Type*} [Semigroup α] {a b : α} (h : a * b = b * a) (t : α) :
    a * (b * t) = b * (a * t) := by
  rw [← mul_assoc, h, mul_assoc]

open Lean Meta Elab Tactic

/-- The lemmas defining the word normal form. -/
def normLemmaNames : List Name :=
  [``mul_assoc, ``mul_add, ``add_mul, ``mul_sub, ``sub_mul, ``neg_mul, ``mul_neg,
    ``smul_mul_assoc, ``mul_smul_comm, ``mul_one, ``one_mul, ``mul_zero, ``zero_mul,
    ``add_zero, ``zero_add, ``sub_zero, ``zero_sub, ``neg_zero, ``neg_neg, ``smul_zero]

/-- The simp context for the word normal form. -/
def normCtx : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for n in normLemmaNames do
    thms ← thms.addConst n
  Simp.mkContext {} #[thms] (← getSimpCongrTheorems)

/-- Word normal form of an expression. -/
def normExpr (e : Expr) : MetaM Simp.Result := do
  let (r, _) ← simp e (← normCtx)
  return r

/-- Normalize the target of `g`; returns `none` if the goal was closed. -/
def normTarget (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let r ← normExpr tgt
  if r.expr.consumeMData.isConstOf ``True then
    g.assign (← mkOfEqTrue (← r.getProof))
    return none
  applySimpResultToTarget g tgt r

/-- Normalize the hypothesis `fvarId` of `g`; returns `none` if the goal was closed. -/
def normLocal (g : MVarId) (fvarId : FVarId) : MetaM (Option (FVarId × MVarId)) :=
  g.withContext do
    let ty ← instantiateMVars (← fvarId.getType)
    let r ← normExpr ty
    applySimpResultToLocalDecl g fvarId r (mayCloseGoal := false)

/-- From `e : ∀ xs, lhs = rhs` (or its reverse if `symm`), the normalized forms of
`∀ xs t, lhs * t = rhs * t` (when `lhs` normalizes to a product) and of `∀ xs, lhs = rhs`,
in this order. -/
def mkVariants (e : Expr) (symm : Bool) : MetaM (Array Expr) := do
  let ty ← instantiateMVars (← inferType e)
  forallTelescopeReducing ty fun xs body => do
    let body ← whnfR body
    let some (_, l, r) := body.eq?
      | throwError "word_rw: expected an equation, got{indentExpr body}"
    let pf0 := mkAppN e xs
    let (pf, lhs, rhs) ← if symm then pure (← mkEqSymm pf0, r, l) else pure (pf0, l, r)
    let rl ← normExpr lhs
    let rr ← normExpr rhs
    let pfN ← mkEqTrans (← mkEqSymm (← rl.getProof)) (← mkEqTrans pf (← rr.getProof))
    let pfN ← mkExpectedTypeHint pfN (← mkEq rl.expr rr.expr)
    let plain ← mkLambdaFVars xs pfN
    let lhs' := rl.expr.consumeMData
    if lhs'.isAppOfArity ``HMul.hMul 6 then
      let mulFn := lhs'.appFn!.appFn!
      let α ← inferType lhs'
      let ext ← withLocalDeclD `t α fun t => do
        let pfT ← mkCongrFun (← mkCongrArg mulFn pfN) t
        let el ← normExpr (mkApp2 mulFn rl.expr t)
        let er ← normExpr (mkApp2 mulFn rr.expr t)
        let pfE ← mkEqTrans (← mkEqSymm (← el.getProof)) (← mkEqTrans pfT (← er.getProof))
        let pfE ← mkExpectedTypeHint pfE (← mkEq el.expr er.expr)
        mkLambdaFVars (xs.push t) pfE
      return #[ext, plain]
    else
      return #[plain]

/-- Rewrite `ty` with the first variant that applies. -/
def rewriteWithVariants (g : MVarId) (ty : Expr) (vs : Array Expr) : MetaM RewriteResult := do
  for v in vs do
    let s ← saveState
    try
      return ← g.rewrite ty v
    catch _ =>
      s.restore
  let desc ← match vs.back? with
    | some v => do
        let t ← inferType v
        forallTelescopeReducing t fun _ b => pure m!"{b}"
    | none => pure m!"?"
  throwError "word_rw: did not find an instance (modulo associativity) of the left-hand side \
    of{indentD desc}\nin{indentExpr ty}"

/-- The letters of a product, for any association. -/
partial def flattenMul (e : Expr) : List Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``HMul.hMul 6 then flattenMul e.appFn!.appArg! ++ flattenMul e.appArg!
  else [e]

/-- The letters of every right-associated product occurring in `e` (outside binders), in
pre-order. -/
partial def collectWords (e : Expr) : Array (Array Expr) :=
  go e #[]
where
  go (e : Expr) (acc : Array (Array Expr)) : Array (Array Expr) :=
    let e := e.consumeMData
    if e.hasLooseBVars then acc else
    let acc := if e.isAppOfArity ``HMul.hMul 6 then acc.push (spine e).toArray else acc
    match e with
    | .app f a => go a (go f acc)
    | _ => acc
  spine (e : Expr) : List Expr :=
    if e.isAppOfArity ``HMul.hMul 6 then e.appFn!.appArg! :: spine e.appArg! else [e]

/-- The default discharger for side conditions. -/
def defaultDisch : TacticM (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  `(tacticSeq| first | assumption | omega)

/-- Try the discharger on each propositional goal; return the goals that remain. -/
def tryDischarge (disch : Syntax) (gs : List MVarId) : TacticM (List MVarId) := do
  let mut rest : Array MVarId := #[]
  for g in gs do
    if ← g.isAssigned then continue
    if !(← isProp (← g.getType)) then
      rest := rest.push g
      continue
    let s ← saveState
    try
      let r ← Tactic.run g (evalTactic disch)
      if r.isEmpty then continue
      s.restore
      rest := rest.push g
    catch _ =>
      s.restore
      rest := rest.push g
  return rest.toList

/-- Instantiate the universally quantified variables of `e : ∀ xs, lhs = rhs` (or its reverse
if `symm`) by matching the letters of `lhs` against a contiguous subword of a word of `ty`
(words in pre-order, positions from left to right). The first match whose propositional
hypotheses are all proved by the discharger is used; if there is none, the first match is used
and its hypotheses are left open. Returns the instantiated proof and whether the match is a
suffix of its word. -/
def instantiateByMatch (disch : Syntax) (ty e : Expr) (symm : Bool) :
    TacticM (Option (Expr × Bool)) := do
  let s ← saveState
  let (mvs, bis, body) ← forallMetaTelescopeReducing (← instantiateMVars (← inferType e))
  let body ← whnfR (← instantiateMVars body)
  let some (_, l, r) := body.eq? | do s.restore; return none
  let pat := (flattenMul (if symm then r else l)).toArray
  let k := pat.size
  let mut first : Option (Tactic.SavedState × Expr × Bool) := none
  for w in collectWords ty do
    if w.size < k then continue
    for j in [0:w.size - k + 1] do
      let s' ← saveState
      let mut ok := true
      for q in [0:k] do
        unless ← withTransparency .instances (isDefEq pat[q]! w[j + q]!) do
          ok := false
          break
      if ok then
        for (mv, bi) in mvs.zip bis do
          if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
            if let some inst ← synthInstance? (← instantiateMVars (← inferType mv)) then
              discard <| isDefEq mv inst
        let res := (← instantiateMVars (mkAppN e mvs), j + k == w.size)
        if first.isNone then first := some (← saveState, res)
        let hyps ← mvs.filterM fun mv => do
          pure (!(← mv.mvarId!.isAssigned) && (← isProp (← inferType mv)))
        let open_ ← tryDischarge disch (hyps.toList.map (·.mvarId!))
        if open_.isEmpty then
          return some (← instantiateMVars res.1, res.2)
      s'.restore
  match first with
  | some (st, res) =>
    st.restore
    return some res
  | none =>
    s.restore
    return none

/-- Rewrite `ty` with `e` modulo associativity (see `word_rw`). The variables of `e` are first
instantiated by matching its left-hand side against the words of `ty`; if this fails, the
quantified variants of `e` are used directly. -/
def wordRewrite (disch : Syntax) (g : MVarId) (ty e : Expr) (symm : Bool) :
    TacticM RewriteResult := do
  let s ← saveState
  if let some (pf, suffix) ← instantiateByMatch disch ty e symm then
    let vs ← mkVariants pf symm
    let vs := if suffix then vs.reverse else vs
    try
      return ← rewriteWithVariants g ty vs
    catch _ =>
      s.restore
  rewriteWithVariants g ty (← mkVariants e symm)

/-- Try to close `g` by `with_reducible rfl`. -/
def tryRfl (g : MVarId) : MetaM (Option MVarId) := do
  let s ← saveState
  try
    withReducible g.refl
    return none
  catch _ =>
    s.restore
    return some g

/-- Normalize the main goal. -/
def normMainTarget : TacticM Unit := do
  let g ← getMainGoal
  match ← normTarget g with
  | some g' => replaceMainGoal [g']
  | none => replaceMainGoal []

/-- Normalize a hypothesis of the main goal. -/
def normMainLocal (fvarId : FVarId) : TacticM Unit := do
  let g ← getMainGoal
  match ← normLocal g fvarId with
  | some (_, g') => replaceMainGoal [g']
  | none => replaceMainGoal []

/-- One `word_rw` step at the target. -/
def wordRwTarget (stx : Syntax) (symm : Bool) (disch : Syntax) : TacticM Unit := do
  withMainContext normMainTarget
  let (r, g) ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    if e.hasSyntheticSorry then throwAbortTactic
    let g ← getMainGoal
    let r ← wordRewrite disch g (← instantiateMVars (← g.getType)) e symm
    pure (r, g)
  let g' ← g.replaceTargetEq r.eNew r.eqProof
  let main ← match ← normTarget g' with
    | some m => tryRfl m
    | none => pure none
  let side ← tryDischarge disch r.mvarIds
  replaceMainGoal (main.toList ++ side)

/-- One `word_rw` step at a hypothesis. -/
def wordRwLocal (stx : Syntax) (symm : Bool) (disch : Syntax) (fvarId : FVarId) :
    TacticM Unit := do
  let n ← withMainContext do pure (← fvarId.getDecl).userName
  withMainContext (normMainLocal fvarId)
  -- normalization may have replaced the hypothesis; find it again by its user name
  let fvarId ← withMainContext do pure (← getLocalDeclFromUserName n).fvarId
  let r ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    if e.hasSyntheticSorry then throwAbortTactic
    wordRewrite disch (← getMainGoal) (← instantiateMVars (← fvarId.getType)) e symm
  let res ← (← getMainGoal).replaceLocalDecl fvarId r.eNew r.eqProof
  let main ← normLocal res.mvarId res.fvarId
  let side ← tryDischarge disch r.mvarIds
  replaceMainGoal ((main.map (·.2)).toList ++ side)

/--
`word_rw [e₁, ← e₂, …]` rewrites with the equations `eᵢ` modulo associativity of
multiplication: an equation whose left-hand side is a product `a₁ * ⋯ * a_k` rewrites any
contiguous occurrence of `a₁, …, a_k` in a product of the goal. Goals and rules are first put
into word normal form (right-associated products, multiplication distributed over `+`, `-`,
negation and scalar multiplication pulled out, unit and zero laws). Side conditions are
attempted with `first | assumption | omega`, or with `tac` in `word_rw (disch := tac) [...]`;
those not discharged remain as goals. Supports `at h`.
-/
syntax (name := wordRwSeq) "word_rw" (Lean.Parser.Tactic.discharger)? Lean.Parser.Tactic.rwRuleSeq
  (Lean.Parser.Tactic.location)? : tactic

/-- Extract the discharger tactic from an optional `(disch := tac)`. -/
def getDisch (stx : Syntax) : TacticM Syntax := do
  if stx.isNone then return (← defaultDisch).raw
  return stx[0][3]

@[tactic wordRwSeq] def evalWordRw : Tactic := fun stx => do
  let disch ← getDisch stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (wordRwLocal term symm disch ·)
      (wordRwTarget term symm disch)
      (throwTacticEx `word_rw · "did not find instance of the pattern in the current goal")

/-- `word_norm` puts the goal (or `at h`, a hypothesis) into word normal form: products
right-associated and distributed over sums and differences, negation and scalar multiplication
pulled out of products, unit and zero laws applied. -/
syntax (name := wordNorm) "word_norm" (Lean.Parser.Tactic.location)? : tactic

@[tactic wordNorm] def evalWordNorm : Tactic := fun stx => do
  let loc := expandOptLocation stx[1]
  withLocation loc (fun f => withMainContext (normMainLocal f)) (withMainContext normMainTarget)
    (throwTacticEx `word_norm · "failed")

/-! ### Commutation normal form -/

/-- The data used while computing commutation normal forms. -/
structure CommCtx where
  /-- The commutation lemmas, with their elaboration metavariables abstracted. -/
  lemmas : Array AbstractMVarsResult
  /-- The discharger for side conditions. -/
  disch : Syntax
  /-- Cache of commutation proofs `a * b = b * a` (or `none` if none was found). -/
  cache : IO.Ref (Std.HashMap (Expr × Expr) (Option Expr))

/-- Try to discharge all unassigned metavariables in `mvs` (propositions via the discharger,
instances by synthesis). -/
def dischargeAll (disch : Syntax) (mvs : Array Expr) : TacticM Bool := do
  for mv in mvs do
    let mv := mv.mvarId!
    if ← mv.isAssigned then continue
    let ty ← instantiateMVars (← mv.getType)
    if ← isProp ty then
      if ty.hasExprMVar then return false
      let r ← try Tactic.run mv (evalTactic disch) catch _ => return false
      unless r.isEmpty do return false
    else if (← isClass? ty).isSome then
      let some inst ← synthInstance? ty | return false
      unless ← isDefEq (.mvar mv) inst do return false
    else
      return false
  return true

/-- Try to prove `a * b = b * a` from one lemma, in one orientation. -/
def tryCommLemma (ctx : CommCtx) (res : AbstractMVarsResult) (ab ba : Expr) (rev : Bool) :
    TacticM (Option Expr) := do
  let s ← saveState
  try
    let (_, _, L) ← openAbstractMVarsResult res
    let (mvs, _, ty) ← forallMetaTelescopeReducing (← inferType L)
    let ty ← whnfR ty
    let some (_, l, r) := ty.eq? | do s.restore; return none
    let (tl, tr) := if rev then (ba, ab) else (ab, ba)
    unless ← withTransparency .instances (isDefEq l tl <&&> isDefEq r tr) do
      s.restore; return none
    unless ← dischargeAll ctx.disch mvs do
      s.restore; return none
    let pf ← instantiateMVars (mkAppN L mvs)
    let pf ← if rev then mkEqSymm pf else pure pf
    return some (← mkExpectedTypeHint pf (← mkEq ab ba))
  catch _ =>
    s.restore
    return none

/-- A proof of `a * b = b * a`, if one is found. -/
def commProof? (ctx : CommCtx) (mulFn a b : Expr) : TacticM (Option Expr) := do
  if let some r := (← ctx.cache.get)[(a, b)]? then return r
  let ab := mkApp2 mulFn a b
  let ba := mkApp2 mulFn b a
  let result ← do
    if a == b then pure (some (← mkEqRefl ab)) else
    let mut found : Option Expr := none
    for L in ctx.lemmas do
      if let some p ← tryCommLemma ctx L ab ba false then
        found := some p; break
      if let some p ← tryCommLemma ctx L ab ba true then
        found := some p; break
    pure found
  ctx.cache.modify (·.insert (a, b) result)
  return result

/-- The right-associated product of a nonempty list of letters. -/
def prodList (mulFn : Expr) : List Expr → Expr
  | [] => mkConst ``Unit.unit -- unreachable: words are nonempty
  | [a] => a
  | a :: w => mkApp2 mulFn a (prodList mulFn w)

/-- The letters of a right-associated product. -/
partial def letters (mulFn : Expr) (e : Expr) : List Expr :=
  if e.isAppOfArity ``HMul.hMul 6 && e.appFn!.appFn! == mulFn then
    e.appFn!.appArg! :: letters mulFn e.appArg!
  else [e]

/-- `mkEqTrans` on optional proofs (`none` is reflexivity). -/
def transOpt : Option Expr → Option Expr → MetaM (Option Expr)
  | none, q => pure q
  | p, none => pure p
  | some p, some q => some <$> mkEqTrans p q

/-- A proof that `prodList w = w[p] * prodList (w.eraseIdx p)`, given that `w[p]` commutes
with every earlier letter. -/
partial def moveFront (ctx : CommCtx) (mulFn : Expr) : List Expr → Nat → TacticM (Option Expr)
  | _, 0 => pure none
  | [], _ => throwError "word_comm: internal error (moveFront)"
  | c :: w', p + 1 => do
    let b := w'[p]!
    let ih ← moveFront ctx mulFn w' p
    let rest := w'.eraseIdx p
    let some comm ← commProof? ctx mulFn c b
      | throwError "word_comm: internal error (missing commutation)"
    let step1 ← ih.mapM fun q => mkCongrArg (mkApp mulFn c) q
    let step2 ← if rest.isEmpty then pure comm else
      mkAppM ``swap_cons #[comm, prodList mulFn rest]
    transOpt step1 (some step2)

/-- The commutation normal form of a word, with a proof `prodList w = prodList w'`. -/
partial def nfWord (ctx : CommCtx) (mulFn : Expr) (w : List Expr) :
    TacticM (List Expr × Option Expr) := do
  match w with
  | [] | [_] => return (w, none)
  | _ =>
    let arr := w.toArray
    let mut best : Nat := 0
    for p in [1:arr.size] do
      let b := arr[p]!
      unless Expr.lt b arr[best]! do continue
      let mut ok := true
      for q in [0:p] do
        if (← commProof? ctx mulFn arr[q]! b).isNone then
          ok := false
          break
      if ok then best := p
    let b := arr[best]!
    let pMove ← moveFront ctx mulFn w best
    let (rest', pRest) ← nfWord ctx mulFn (w.eraseIdx best)
    let pRest' ← pRest.mapM fun q => mkCongrArg (mkApp mulFn b) q
    return (b :: rest', ← transOpt pMove pRest')

/-- Rebuild `f a₀ … a_m`, replacing the arguments at the given indices by their normal forms. -/
def congrArgsWith (f : Expr) (args : Array Expr) (idx : List Nat)
    (k : Expr → TacticM (Expr × Option Expr)) : TacticM (Expr × Option Expr) := do
  let mut fOld := f
  let mut fNew := f
  let mut pf : Option Expr := none
  for i in [0:args.size] do
    let a := args[i]!
    if idx.contains i then
      let (a', pa) ← k a
      pf ← match pf, pa with
        | none, none => pure none
        | none, some q => some <$> mkCongrArg fOld q
        | some p, none => some <$> mkCongrFun p a
        | some p, some q => some <$> mkCongr p q
      fOld := mkApp fOld a
      fNew := mkApp fNew a'
    else
      pf ← pf.mapM (mkCongrFun · a)
      fOld := mkApp fOld a
      fNew := mkApp fNew a
  return (fNew, pf)

/-- Commutation normal form of every word in `e` (through `=`, `+`, `-`, negation and scalar
multiplication), with a proof of `e = e'`. -/
partial def nfExpr (ctx : CommCtx) (e : Expr) : TacticM (Expr × Option Expr) := do
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  let recurse (idx : List Nat) := congrArgsWith fn args idx (nfExpr ctx)
  match fn.constName?, args.size with
  | some ``Eq, 3 => recurse [1, 2]
  | some ``HAdd.hAdd, 6 => recurse [4, 5]
  | some ``HSub.hSub, 6 => recurse [4, 5]
  | some ``Neg.neg, 3 => recurse [2]
  | some ``HSMul.hSMul, 6 => recurse [5]
  | some ``HMul.hMul, 6 =>
    let mulFn := e.appFn!.appFn!
    let w := letters mulFn e
    let (w', pf) ← nfWord ctx mulFn w
    match pf with
    | none => return (e, none)
    | some pf =>
      let e' := prodList mulFn w'
      return (e', some (← mkExpectedTypeHint pf (← mkEq e e')))
  | _, _ => return (e, none)

/-- Elaborate the commutation lemmas. -/
def mkCommCtx (terms : Array Syntax) (disch : Syntax) : TacticM CommCtx := withMainContext do
  let lemmas ← terms.mapM fun t => do
    let e ← Term.withSynthesize <| elabTerm t none true
    abstractMVars (← instantiateMVars e)
  return { lemmas, disch, cache := ← IO.mkRef {} }

/-- Commutation normal form of the main target. -/
def commNfTarget (ctx : CommCtx) : TacticM Unit := withMainContext do
  normMainTarget
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let (tgt', pf) ← nfExpr ctx tgt
  match pf with
  | none => pure ()
  | some pf => replaceMainGoal [← g.replaceTargetEq tgt' pf]

/-- Commutation normal form of a hypothesis. -/
def commNfLocal (ctx : CommCtx) (fvarId : FVarId) : TacticM Unit := withMainContext do
  let n := (← fvarId.getDecl).userName
  normMainLocal fvarId
  withMainContext do
  let fvarId := (← getLocalDeclFromUserName n).fvarId
  let g ← getMainGoal
  let ty ← instantiateMVars (← fvarId.getType)
  let (ty', pf) ← nfExpr ctx ty
  match pf with
  | none => pure ()
  | some pf => replaceMainGoal [(← g.replaceLocalDecl fvarId ty' pf).mvarId]

/-- `word_comm_nf [c₁, …]` brings every word in the goal (or `at h`) into a canonical form
modulo the commutations `cᵢ : a * b = b * a` (possibly conditional; side conditions are
discharged by `first | assumption | omega` or by `tac` in `word_comm_nf (disch := tac) [...]`).
See the module documentation for the normal form. -/
syntax (name := wordCommNf) "word_comm_nf" (Lean.Parser.Tactic.discharger)?
  " [" term,* "]" (Lean.Parser.Tactic.location)? : tactic

/-- `word_comm [c₁, …]` proves an equation between linear combinations of words that agree
after commuting letters with the (possibly conditional) commutation lemmas `cᵢ`, and after
rearranging summands (`abel1`). Side conditions are discharged by
`first | assumption | omega` or by `tac` in `word_comm (disch := tac) [...]`. -/
syntax (name := wordComm) "word_comm" (Lean.Parser.Tactic.discharger)? " [" term,* "]" : tactic

@[tactic wordCommNf] def evalWordCommNf : Tactic := fun stx => do
  let disch ← getDisch stx[1]
  let ctx ← mkCommCtx stx[3].getSepArgs disch
  let loc := expandOptLocation stx[5]
  withLocation loc (commNfLocal ctx) (commNfTarget ctx)
    (throwTacticEx `word_comm_nf · "failed")

@[tactic wordComm] def evalWordComm : Tactic := fun stx => do
  let disch ← getDisch stx[1]
  let ctx ← mkCommCtx stx[3].getSepArgs disch
  commNfTarget ctx
  let gs ← getGoals
  match gs with
  | [] => pure ()
  | g :: _ =>
    let g' ← g.withContext (tryRfl g)
    match g' with
    | none => replaceMainGoal []
    | some g' =>
      let r ← try some <$> Tactic.run g' (evalTactic (← `(tactic| abel1))) catch _ => pure none
      match r with
      | some [] => replaceMainGoal []
      | _ => throwError "word_comm: the commutation normal forms differ:{indentExpr (← g'.getType)}"

end StringDiagrams.WordRw
