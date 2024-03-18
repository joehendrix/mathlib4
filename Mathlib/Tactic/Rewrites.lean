/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.SolveByElim
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.TryThis
import Lean.Util.Heartbeats
import Std.Tactic.Relation.Rfl
import Std.Util.Pickle
import Mathlib.Lean.Expr.Traverse

/-!
# The `rewrites` tactic.

`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [← h]`.

-/

set_option autoImplicit true

namespace Lean.Meta

/-- Extract the lemma, with arguments, that was used to produce a `RewriteResult`. -/
-- This assumes that `r.eqProof` was constructed as:
-- `mkApp6 (.const ``congrArg _) α eType lhs rhs motive heq`
-- in `Lean.Meta.Tactic.Rewrite` and we want `heq`.
def RewriteResult.by? (r : RewriteResult) : Option Expr :=
  if r.eqProof.isAppOfArity ``congrArg 6 then
    r.eqProof.getArg! 5
  else
    none

end Lean.Meta

namespace Mathlib.Tactic.Rewrites

open Lean Meta Tactic.TryThis

initialize registerTraceClass `Tactic.rewrites
initialize registerTraceClass `Tactic.rewrites.lemmas

/-- Weight to multiply the "specificity" of a rewrite lemma by when rewriting forwards. -/
def forwardWeight := 2
/-- Weight to multiply the "specificity" of a rewrite lemma by when rewriting backwards. -/
def backwardWeight := 1

/-- Configuration for `DiscrTree`. -/
def discrTreeConfig : WhnfCoreConfig := {}

/-- Prepare the discrimination tree entries for a lemma. -/
def processLemma (name : Name) (constInfo : ConstantInfo) :
    MetaM (Array (Array DiscrTree.Key × (Name × Bool × Nat))) := do
  if constInfo.isUnsafe then return #[]
  if !allowCompletion (←getEnv) name then return #[]
  -- We now remove some injectivity lemmas which are not useful to rewrite by.
  if name matches .str _ "injEq" then return #[]
  if name matches .str _ "sizeOf_spec" then return #[]
  match name with
  | .str _ n => if n.endsWith "_inj" ∨ n.endsWith "_inj'" then return #[]
  | _ => pure ()
  withNewMCtxDepth do withReducible do
    let (_, _, type) ← forallMetaTelescopeReducing constInfo.type
    match type.getAppFnArgs with
    | (``Eq, #[_, lhs, rhs])
    | (``Iff, #[lhs, rhs]) => do
      let lhsKey ← DiscrTree.mkPath lhs discrTreeConfig
      let rhsKey ← DiscrTree.mkPath rhs discrTreeConfig
      return #[(lhsKey, (name, false, forwardWeight * lhsKey.size)),
               (rhsKey, (name, true, backwardWeight * rhsKey.size))]
    | _ => return #[]

/-- Select `=` and `↔` local hypotheses. -/
def localHypotheses (except : List FVarId := []) : MetaM (Array (Expr × Bool × Nat)) := do
  let r ← getLocalHyps
  let mut result := #[]
  for h in r do
    if except.contains h.fvarId! then continue
    let (_, _, type) ← forallMetaTelescopeReducing (← inferType h)
    let type ← whnfR type
    match type.getAppFnArgs with
    | (``Eq, #[_, lhs, rhs])
    | (``Iff, #[lhs, rhs]) => do
      let lhsKey : Array DiscrTree.Key ← DiscrTree.mkPath lhs discrTreeConfig
      let rhsKey : Array DiscrTree.Key ← DiscrTree.mkPath rhs discrTreeConfig
      result := result.push (h, false, forwardWeight * lhsKey.size)
        |>.push (h, true, backwardWeight * rhsKey.size)
    | _ => pure ()
  return result


def updateTree (name : Name) (constInfo : ConstantInfo) (tree : DiscrTree (Name × Bool × Nat)) := do
  let entries ← processLemma name constInfo
  pure <| entries.foldl (init := tree) (fun (t : DiscrTree (Name × Bool × Nat)) (k, v) => t.insertCore k v)

/--
Build a `DiscrTreeCache`,
from a function that returns a collection of keys and values for each declaration.
-/
def mkCache (profilingName : String)
    (init : MetaM (DiscrTree (Name × Bool × Nat)))
    (post? : Option (Array (Name × Bool × Nat) → Array (Name × Bool × Nat))) :
    MetaM (DiscrTree (Name × Bool × Nat)) := do
  try
    -- We allow arbitrary failures in the `pre` tactic,
    -- and fall back on folding over the entire environment.
    -- In practice the `pre` tactic may be unpickling an `.olean`,
    -- and may fail after leanprover/lean4#2766 because the embedded hash is incorrect.
    return ← init
  catch _ =>
    profileitM Exception profilingName (← getOptions) do
      let env ← getEnv
      let T₂ ←
            env.constants.map₁.foldM (init := {}) fun tree₂ name constInfo => do
              updateTree name constInfo tree₂
      let T₂ :=
        match post? with
        | some f => T₂.mapArrays f
        | none => T₂
      pure T₂

/-- Construct the discrimination tree of all lemmas. -/
def buildDiscrTree : MetaM (DiscrTree (Name × Bool × Nat)) :=
  mkCache "rw?: init cache"
    -- Sort so lemmas with longest names come first.
    -- This is counter-intuitive, but the way that `DiscrTree.getMatch` returns results
    -- means that the results come in "batches", with more specific matches *later*.
    -- Thus we're going to call reverse on the result of `DiscrTree.getMatch`,
    -- so if we want to try lemmas with shorter names first,
    -- we need to put them into the `DiscrTree` backwards.
    (init := failure)
    (post? := some fun A =>
      A.map (fun (n, m) => (n.toString.length, n, m)) |>.qsort (fun p q => p.1 > q.1) |>.map (·.2))

open System (FilePath)

def cachePath : IO FilePath :=
  try
    return (← findOLean `MathlibExtras.Rewrites).withExtension "extra"
  catch _ =>
    return ".lake" / "build" / "lib" / "MathlibExtras" / "Rewrites.extra"

/--
Retrieve the current cache of lemmas.
-/
unsafe def mkDiscrTree : MetaM (DiscrTree (Name × Bool × Nat)) := do
  let path ← cachePath
  if (← path.pathExists) then
    -- We can drop the `CompactedRegion` value from `unpickle`; we do not plan to free it
    let d := (·.1) <$> unpickle (DiscrTree (Name × Bool × Nat)) path
    mkCache "rw?: using cache" (init := d) (post? := none)
  else
    buildDiscrTree

/-- Data structure recording a potential rewrite to report from the `rw?` tactic. -/
structure RewriteResult where
  /-- The lemma we rewrote by.
  This is `Expr`, not just a `Name`, as it may be a local hypothesis. -/
  expr : Expr
  /-- `True` if we rewrote backwards (i.e. with `rw [← h]`). -/
  symm : Bool
  /-- The "weight" of the rewrite. This is calculated based on how specific the rewrite rule was. -/
  weight : Nat
  /-- The result from the `rw` tactic. -/
  result : Meta.RewriteResult
  /-- Pretty-printed result. -/
  -- This is an `Option` so that it can be computed lazily.
  ppResult? : Option String
  /-- The metavariable context after the rewrite.
  This needs to be stored as part of the result so we can backtrack the state. -/
  mctx : MetavarContext

/-- Update a `RewriteResult` by filling in the `rfl?` field if it is currently `none`,
to reflect whether the remaining goal can be closed by `with_reducible rfl`. -/
def RewriteResult.computeRfl (r : RewriteResult) : MetaM Bool := do
  try
    withoutModifyingState <| withMCtx r.mctx do
      -- We use `withReducible` here to follow the behaviour of `rw`.
      withReducible (← mkFreshExprMVar r.result.eNew).mvarId!.applyRfl
      -- We do not need to record the updated `MetavarContext` here.
      pure true
  catch _e =>
    pure false

/--
Pretty print the result of the rewrite.
If this will be done more than once you should use `prepare_ppResult`
-/
def RewriteResult.ppResult (r : RewriteResult) : MetaM String :=
  if let some pp := r.ppResult? then
    return pp
  else
    return (← ppExpr r.result.eNew).pretty

open Lean.Elab.Tactic.SolveByElim Lean.Meta.SolveByElim in
/-- Shortcut for calling `solveByElim`. -/
def solveByElim (goals : List MVarId) (depth : Nat := 6) : MetaM PUnit := do
  -- There is only a marginal decrease in performance for using the `symm` option for `solveByElim`.
  -- (measured via `lake build && time lake env lean test/librarySearch.lean`).
  let cfg : SolveByElimConfig :=
    { maxDepth := depth, exfalso := false, symm := true }
  let [] ← processSyntax cfg false false [] [] #[] goals
    | failure

/-- Should we try discharging side conditions? If so, using `assumption`, or `solve_by_elim`? -/
inductive SideConditions
| none
| assumption
| solveByElim


def rwLemma (ctx : MetavarContext) (goal : MVarId) (target : Expr) (side : SideConditions := .solveByElim) (lem : Expr ⊕ Name) (symm : Bool) (weight : Nat) : MetaM (Option RewriteResult) :=
  withMCtx ctx do
    let some expr ← (match lem with
    | .inl hyp => pure (some hyp)
    | .inr lem => some <$> mkConstWithFreshMVarLevels lem <|> pure none)
      | return none
    trace[Tactic.rewrites] m!"considering {if symm then "← " else ""}{expr}"
    let some result ← some <$> goal.rewrite target expr symm <|> pure none
      | return none
    if result.mvarIds.isEmpty then
      return some {
        expr,
        symm,
        weight,
        result,
        ppResult? := none,
        mctx := ← getMCtx
      }
    else
      -- There are side conditions, which we try to discharge using local hypotheses.
      match (← match side with
        | .none => pure false
        | .assumption => ((result.mvarIds.mapM fun m => m.assumption) >>= fun _ => pure true) <|> pure false
        | .solveByElim => (solveByElim result.mvarIds >>= fun _ => pure true) <|> pure false) with
      | false => return none
      | true =>
        -- If we succeed, we need to reconstruct the expression to report that we rewrote by.
        let some expr := result.by? | return none
        let expr ← instantiateMVars expr
        let (expr, symm) := if expr.isAppOfArity ``Eq.symm 4 then
            (expr.getArg! 3, true)
          else
            (expr, false)
        return some {
            expr, symm, weight, result,
            ppResult? := none,
            mctx := ← getMCtx
          }

/--
Find keys which match the expression, or some subexpression.

Note that repeated subexpressions will be visited each time they appear,
making this operation potentially very expensive.
It would be good to solve this problem!

Implementation: we reverse the results from `getMatch`,
so that we return lemmas matching larger subexpressions first,
and amongst those we return more specific lemmas first.
-/
partial def getSubexpressionMatches (d : DiscrTree α) (e : Expr) (config : WhnfCoreConfig) :
    MetaM (Array α) := do
  match e with
  | .bvar _ => return #[]
  | .forallE _ _ _ _ => forallTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
          pure <| acc ++ (← getSubexpressionMatches d (← inferType arg) config))
        (← getSubexpressionMatches d body config).reverse)
  | .lam _ _ _ _
  | .letE _ _ _ _ _ => lambdaLetTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
          pure <| acc ++ (← getSubexpressionMatches d (← inferType arg) config))
        (← getSubexpressionMatches d body config).reverse)
  | _ =>
    e.foldlM (fun a f => do
      pure <| a ++ (← getSubexpressionMatches d f config)) (← d.getMatch e config).reverse

/--
Find lemmas which can rewrite the goal.

This core function returns a monadic list, to allow the caller to decide how long to search.
See also `rewrites` for a more convenient interface.
-/
-- We need to supply the current `MetavarContext` (which will be reused for each lemma application)
-- because `MLList.squash` executes lazily,
-- so there is no opportunity for `← getMCtx` to record the context at the call site.
def rewriteCandidates (hyps : Array (Expr × Bool × Nat))
    (lemmas : DiscrTree (Name × Bool × Nat) × DiscrTree (Name × Bool × Nat))
    (target : Expr)
    (forbidden : NameSet := ∅) :
    MetaM (Array ((Expr ⊕ Name) × Bool × Nat)) := do
  -- Get all lemmas which could match some subexpression
  let candidates := (← getSubexpressionMatches lemmas.1 target discrTreeConfig)
    ++ (← getSubexpressionMatches lemmas.2 target discrTreeConfig)

  -- Sort them by our preferring weighting
  -- (length of discriminant key, doubled for the forward implication)
  let candidates := candidates.insertionSort fun r s => r.2.2 > s.2.2

  -- Now deduplicate. We can't use `Array.deduplicateSorted` as we haven't completely sorted,
  -- and in fact want to keep some of the residual ordering from the discrimination tree.
  let mut forward : NameSet := ∅
  let mut backward : NameSet := ∅
  let mut deduped := #[]
  for (l, s, w) in candidates do
    if forbidden.contains l then continue
    if s then
      if ¬ backward.contains l then
        deduped := deduped.push (l, s, w)
        backward := backward.insert l
    else
      if ¬ forward.contains l then
        deduped := deduped.push (l, s, w)
        forward := forward.insert l

  trace[Tactic.rewrites.lemmas] m!"Candidate rewrite lemmas:\n{deduped}"

  -- Lift to a monadic list, so the caller can decide how much of the computation to run.
  let hyps := hyps.map fun ⟨hyp, symm, weight⟩ => (Sum.inl hyp, symm, weight)
  let lemmas := deduped.map fun ⟨lem, symm, weight⟩ => (Sum.inr lem, symm, weight)
  pure <| hyps ++ lemmas

structure RewriteResultConfig where
  stopAtRfl : Bool
  max : Nat
  minHeartbeats : Nat
  goal : MVarId
  target : Expr
  side : SideConditions := .solveByElim
  mctx : MetavarContext

structure FinRwResult where
  /-- The lemma we rewrote by.
  This is `Expr`, not just a `Name`, as it may be a local hypothesis. -/
  expr : Expr
  /-- `True` if we rewrote backwards (i.e. with `rw [← h]`). -/
  symm : Bool
  /-- The result from the `rw` tactic. -/
  result : Meta.RewriteResult
  /-- The metavariable context after the rewrite.
  This needs to be stored as part of the result so we can backtrack the state. -/
  mctx : MetavarContext
  newGoal : Option Expr

def FinRwResult.mkFin (r : RewriteResult) (rfl? : Bool) : FinRwResult := {
    expr := r.expr,
    symm := r.symm,
    result := r.result,
    mctx := r.mctx,
    newGoal :=
      if rfl? = true then
        some (Expr.lit (.strVal "no goals"))
      else
        some r.result.eNew
  }

def FinRwResult.addSuggestion (ref : Syntax) (r : FinRwResult) : Elab.TermElabM Unit := do
  withMCtx r.mctx do
    addRewriteSuggestion ref [(r.expr, r.symm)] (type? := r.newGoal) (origSpan? := ← getRef)

def takeListAux (cfg : RewriteResultConfig) (seen : HashMap String Unit) (acc : Array FinRwResult)
    (xs : List ((Expr ⊕ Name) × Bool × Nat)) : MetaM (Array FinRwResult) := do
  let mut seen := seen
  let mut acc := acc
  for (lem, symm, weight) in xs do
    if (← getRemainingHeartbeats) < cfg.minHeartbeats then
      return acc
    if acc.size ≥ cfg.max then
      return acc
    let res ←
          withoutModifyingState <| withMCtx cfg.mctx do
            rwLemma cfg.mctx cfg.goal cfg.target cfg.side lem symm weight
    match res with
    | none => continue
    | some r =>
      let s ← withoutModifyingState <| withMCtx r.mctx r.ppResult
      if seen.contains s then
        continue
      let rfl? ← RewriteResult.computeRfl r
      if cfg.stopAtRfl then
        if rfl? then
          return #[FinRwResult.mkFin r true]
        else
          seen := seen.insert s ()
          acc := acc.push (FinRwResult.mkFin r false)
      else
        seen := seen.insert s ()
        acc := acc.push (FinRwResult.mkFin r  rfl?)
  return acc

/-- Find lemmas which can rewrite the goal. -/
def findRewrites (hyps : Array (Expr × Bool × Nat))
    (lemmas : DiscrTree (Name × Bool × Nat) × DiscrTree (Name × Bool × Nat))
    (goal : MVarId) (target : Expr)
    (forbidden : NameSet := ∅) (side : SideConditions := .solveByElim)
    (stopAtRfl : Bool) (max : Nat := 20)
    (leavePercentHeartbeats : Nat := 10) : MetaM (List FinRwResult) := do
  let mctx ← getMCtx
  let candidates ← rewriteCandidates hyps lemmas target forbidden
  let minHeartbeats : Nat :=
        if (← getMaxHeartbeats) = 0 then
          0
        else
          leavePercentHeartbeats * (← getRemainingHeartbeats) / 100
  let cfg : RewriteResultConfig := {
    stopAtRfl := stopAtRfl,
    minHeartbeats,
    max,
    mctx,
    goal,
    target,
    side
  }
  return (← takeListAux cfg {} (Array.mkEmpty max) candidates.toList).toList

open Lean.Parser.Tactic

/--
Syntax for excluding some names, e.g. `[-my_lemma, -my_theorem]`.
-/
-- TODO: allow excluding local hypotheses.
syntax forbidden := " [" (("-" ident),*,?) "]"

/--
`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [← h]`.

You can use `rw? [-my_lemma, -my_theorem]` to prevent `rw?` using the named lemmas.
-/
syntax (name := rewrites') "rw?" (ppSpace location)? (forbidden)? : tactic


private def ExtState := IO.Ref (Option (DiscrTree (Name × Bool × Nat)))

private initialize ExtState.default : IO.Ref (Option (DiscrTree (Name × Bool × Nat))) ← do
  IO.mkRef .none

private instance : Inhabited ExtState where
  default := ExtState.default

private initialize ext : EnvExtension ExtState ←
  registerEnvExtension (IO.mkRef .none)

def getDeclCache :
    MetaM (DiscrTree (Name × Bool × Nat) × DiscrTree (Name × Bool × Nat)) := do

  let treeRef := ext.getState (←getEnv)

  let importTree ←
    match ←treeRef.get with
    | some t => pure t
    | none => do
      let t ← profileitM Exception  "librarySearch launch" (←getOptions) (unsafe mkDiscrTree)
      treeRef.set (some t)
      pure t

  let T1 ← (← getEnv).constants.map₂.foldlM (init := {}) fun a name constInfo =>
    updateTree name constInfo a
  pure (T1, importTree)

open Elab.Tactic Elab Tactic in
elab_rules : tactic |
    `(tactic| rw?%$tk $[$loc]? $[[ $[-$forbidden],* ]]?) => do

  let lems ← getDeclCache
  let forbidden : NameSet :=
    ((forbidden.getD #[]).map Syntax.getId).foldl (init := ∅) fun s n => s.insert n
  reportOutOfHeartbeats `findRewrites tk
  let goal ← getMainGoal
  -- TODO fix doc of core to say that * fails only if all failed
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    fun f => do
      let some a ← f.findDecl? | return
      if a.isImplementationDetail then return
      let target ← instantiateMVars (← f.getType)
      let hyps ← localHypotheses (except := [f])
      let results ← findRewrites hyps lems goal target (stopAtRfl := false) forbidden
      reportOutOfHeartbeats `rewrites tk
      if results.isEmpty then
        throwError "Could not find any lemmas which can rewrite the hypothesis {← f.getUserName}"
      for r in results do withMCtx r.mctx do
        addRewriteSuggestion tk [(r.expr, r.symm)]
          r.result.eNew (loc? := .some (.fvar f)) (origSpan? := ← getRef)
      if let some r := results[0]? then
        setMCtx r.mctx
        let replaceResult ← goal.replaceLocalDecl f r.result.eNew r.result.eqProof
        replaceMainGoal (replaceResult.mvarId :: r.result.mvarIds)
    -- See https://github.com/leanprover/lean4/issues/2150
    do withMainContext do
      let target ← instantiateMVars (← goal.getType)
      let hyps ← localHypotheses
      let results ← findRewrites hyps lems goal target (stopAtRfl := true) forbidden
      reportOutOfHeartbeats `rewrites tk
      if results.isEmpty then
        throwError "Could not find any lemmas which can rewrite the goal"
      results.forM (·.addSuggestion tk)
      if let some r := results[0]? then
        setMCtx r.mctx
        replaceMainGoal
          ((← goal.replaceTargetEq r.result.eNew r.result.eqProof) :: r.result.mvarIds)
        evalTactic (← `(tactic| try rfl))
    (fun _ => throwError "Failed to find a rewrite for some location")
