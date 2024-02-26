--import Mathlib
import Std
/-
import Std.Base.Bool
import Std.Base.Logic
import Std.Util.CheckTactic
import Lean.Data.HashSet
import Lean.Elab.Command
import Std
-/

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command


-- This file runs many tests on simp and other operations on
-- Boolean/Prop values.
--
-- It is intended to systematically evaluate simp strategies on
-- different operators.

-- Note. These tests use the simp tactic not because simp is the best
-- strategy for these particular examples, but rather simp may wind up
-- needing to discharge conditions during rewriting, and we need tests
-- showing that is has generally effective and predictable behavior.

/-
General goals for simp are that the normal forms are sensible to a wide
rnge of users and that it performs well.

Specific goals with Bool are
1. Consistent behavior with equivalent Bool and Prop operators (e.g, &&
   and ∧).
2. Distributivity theorems exist between and, or and not but are not in
   default simp set.
3. Negation moves to outside of equality and inequality (xor), but will
   preserve operator.

The specific operations we want to test are:
* Coercions between `Bool` and `Prop` (decie)
* `not`, `and`, `or`, `beq` (for `Bool`), `bne` (for `Bool`), `cond`
* `Not`, `And`, `Or`, `->` (for `Prop`), `Eq` (for `Prop`), `HEq`, `Iff`, `dite`, `ite`.
* dec
* `∀(b:Bool)`,  `∀(p:Prop)`, `∃(b:Bool)`, and `∃(p:Prop)`.
-/
-- TODO:
-- * Add test for exclusive or
-- * Add test for decidable quantifiers
-- * Add test for ite/dite

inductive BoolType where
  | prop
  | bool
  deriving BEq, DecidableEq, Inhabited, Repr

inductive EqOp where
  | eqProp
  | eqBool
  | iffProp
  | beqBool
  deriving BEq, Repr

def EqOp.argType (op : EqOp) : BoolType :=
  match op with
  | .eqProp  | .iffProp => .prop
  | .beqBool | .eqBool => .bool

def EqOp.resultType (op : EqOp) : BoolType :=
  match op with
  | .eqProp | .eqBool | .iffProp => .prop
  | .beqBool => .bool

inductive NeOp where
  | neProp
  | neBool
  | bneBool
  deriving BEq, Repr

def NeOp.argType (op : NeOp) : BoolType :=
  match op with
  | .neProp  => .prop
  | .neBool | .bneBool => .bool

def NeOp.resultType (op : NeOp) : BoolType :=
  match op with
  | .neProp | .neBool  => .prop
  | .bneBool => .bool

inductive IteOp where
  | iteProp
  | iteBool
  | diteProp
  | diteBool
  | condBool
  deriving BEq, Repr

def IteOp.condType (op : IteOp) : BoolType :=
  match op with
  | .iteProp | .diteProp | .iteBool | .diteBool => .prop
  | .condBool => .bool

def IteOp.resultType (op : IteOp) : BoolType :=
  match op with
  | .iteProp | .diteProp => .prop
  | .iteBool | .diteBool | .condBool => .bool

/--
A first order term representing a `Bool` or `Prop` Lean expression
constructed from the operators described in the module header.

This groups operations that perform the same semantic function into the
same constructor while providing an operator type that identifies the
particular form of it.
-/
inductive BoolVal where
  | trueVal (tp : BoolType)
  | falseVal (tp : BoolType)
  | var (idx : Nat) (v : TSyntax `ident) (tp : BoolType)
    /-- `(t : Prop)` when `t` is a `Bool`.
    Equaivalent to `t = true`.
    -/
  | boolToProp (t : BoolVal)
    /-- `decide t` is the same as `p : Bool`
    -/
  | decide (t : BoolVal)
  | not (x   : BoolVal) (tp : BoolType)
  | and (x y : BoolVal) (tp : BoolType)
  | or  (x y : BoolVal) (tp : BoolType)
  | implies (x y : BoolVal)
  | eq (x y : BoolVal) (op : EqOp)
  | ne (x y : BoolVal) (op : NeOp)
  | ite (c t f : BoolVal) (op : IteOp)
  deriving BEq, Inhabited, Repr

namespace BoolVal

def typeOf (v : BoolVal) : BoolType :=
  match v with
  | .trueVal tp => tp
  | .falseVal tp => tp
  | .var _ _ tp => tp
  | .decide _ => .bool
  | .boolToProp _ => .prop
  | .not _ tp => tp
  | .and _ _ tp => tp
  | .or  _ _ tp => tp
  | .implies _ _ => .prop
  | .eq _ _ op => op.resultType
  | .ne _ _ op => op.resultType
  | .ite _ _ _ op => op.resultType

structure VarDecl where
  idx : Nat
  ident : TSyntax `ident
  type : BoolType

instance : BEq VarDecl where
  beq x y := x.idx == y.idx

instance : Hashable VarDecl where
  hash v := hash v.idx

def render [Monad M] [MonadQuotation M] (v : BoolVal) :
    StateT (HashSet VarDecl) M (TSyntax `term) :=
  match v with
  | .trueVal .bool  => `(true)
  | .trueVal .prop  => `(True)
  | .falseVal .bool => `(false)
  | .falseVal .prop => `(False)
  | .var idx t tp => do
    modify (·.insert ⟨idx, t, tp⟩)
    pure t
  | .boolToProp t => do `(term| ($(←t.render) : Prop))
  | .decide t => do `(term| ($(←t.render) : Bool))
  | .not x .bool => do `(term| !$(←x.render))
  | .not x .prop => do `(term| ¬$(←x.render))
  | .and x y .bool => do `(term| $(←x.render) && $(←y.render))
  | .and x y .prop => do `(term| $(←x.render) ∧  $(←y.render))
  | .or  x y .bool => do `(term| $(←x.render) || $(←y.render))
  | .or  x y .prop => do `(term| $(←x.render) ∨  $(←y.render))
  | .implies x y => do `(term| $(←x.render) → $(←y.render))
  | .eq x y .eqProp | .eq x y .eqBool => do `(term| $(←x.render) = $(←y.render))
  | .eq x y .iffProp => do `(term| $(←x.render) ↔ $(←y.render))
  | .eq x y .beqBool => do `(term| $(←x.render) == $(←y.render))
  | .ne x y .neProp | .ne x y .neBool => do `(term| $(←x.render) ≠ $(←y.render))
  | .ne x y .bneBool => do `(term| $(←x.render) != $(←y.render))
  | .ite c t f op =>
    match op with
    | .iteProp | .iteBool => do
    `(term| if $(←c.render) then $(←t.render) else $(←f.render))
    | .diteProp | .diteBool => do
    `(term| if h : $(←c.render) then $(←t.render) else $(←f.render))
    | .condBool => do
      `(term| bif $(←c.render) then $(←t.render) else $(←f.render))


def map (f : BoolVal -> BoolVal) (v : BoolVal) : BoolVal :=
  match v with
  | .trueVal _ | .falseVal _ | .var _ _ _ => v
  | .boolToProp t => .boolToProp (f t)
  | .decide t => .decide (f t)
  | .not x tp   => .not (f x) tp
  | .and x y tp   => .and (f x) (f y) tp
  | .or  x y tp   => .or  (f x) (f y) tp
  | .implies x y => .implies (f x) (f y)
  | .eq x y op => .eq (f x) (f y) op
  | .ne x y op => .ne (f x) (f y) op
  | .ite c x y op => .ite (f c) (f x) (f y) op

def coerceType (v : BoolVal) (type : BoolType) : BoolVal :=
  match v.typeOf, type with
  | .prop, .bool => .decide v
  | .bool, .prop => .boolToProp v
  | _, _ => v

def trueProp  : BoolVal := .trueVal .prop
def falseProp : BoolVal := .falseVal .prop
def trueBool  : BoolVal := .trueVal .bool
def falseBool : BoolVal := .falseVal .bool

local prefix:75 "~ " => fun t => BoolVal.not t (BoolVal.typeOf t)
local infix:40 "=v " => fun (x y : BoolVal) =>
  BoolVal.eq x y (match BoolVal.typeOf x with
            | .prop => EqOp.eqProp
            | .bool => EqOp.eqBool)
instance : AndOp BoolVal where
  and x y := BoolVal.and x y (BoolVal.typeOf x)
instance : OrOp BoolVal where
  or x y  := BoolVal.or x y (BoolVal.typeOf x)

section

--set_option quotPrecheck false
--local prefix:40 "↓ " => simp
--set_option quotPrecheck true

/--
Returns true if we have syntactic rules to
-/
def isComplement (x y : BoolVal) : Bool :=
  match x, y with
  | .not x _, y => x == y
  | x, .not y _ => x == y
  | .eq a b _, .ne c d _ => a.typeOf == c.typeOf && a == b && c == d
  | .ne a b _, .eq c d _ => a.typeOf == c.typeOf && a == b && c == d
  | _, _ => false

@[match_pattern]
def iff (x y : BoolVal) : BoolVal := .eq x y .iffProp

@[match_pattern]
def eq_true (x : BoolVal) : BoolVal := .eq x (.trueVal .bool) .eqBool

@[match_pattern]
def eq_false (x : BoolVal) : BoolVal := .eq x (.falseVal .bool) .eqBool

partial def simp (v : BoolVal) : BoolVal :=
  let v := map simp v
  match v with
  | .boolToProp b => simp <| eq_true b
  | .decide p =>
      match p with
      | .trueVal  _ => .trueVal  .bool
      | .falseVal _ => .falseVal .bool
      | .var _ _ .prop => v
      | .boolToProp _ => panic! "Expected boolToProp to simplify away"
      | .not x _   => simp <| ~(.decide x)
      | .and x y _ => simp <| (.decide x) &&& (.decide y)
      | .or x y _  => simp <| (.decide x) ||| (.decide y)
        -- Leave implication alone for now
      | .implies p q => simp <| ~(.decide p) ||| (.decide q)
      | .eq x y .eqBool =>
        match y with
        | .trueVal _ => x
        | .falseVal _ => simp (~ x)
        | _ => v
      | .eq x y .eqProp | iff x y =>
        simp <| .eq (.decide x) (.decide y) .beqBool
      | .ne _ _ op =>
        match op with
        | .neProp | .neBool => panic! "Expected ne to be reduced to not eq"
        | .bneBool => panic! "Unexpected bool"
      | .ite c t f op =>
        match op with
        | .iteProp =>
          .ite c (.decide t) (.decide f) .iteBool
        | .diteProp =>
          panic! "expected dite to simplify away."
        | _ =>
          panic! s!"Unexpected bool when prop expected."
      | .var _ _ .bool | .decide _ | .eq _ _ _ =>
        panic! s!"Unexpected prop {repr p} when bool expected."
  | .not t _ =>
    match t with
    | .trueVal tp => .falseVal tp
    | .falseVal tp => .trueVal tp
    | .not t _ => t
    | .and x y .prop => simp <| .implies x (.not y .prop)
    | .and x y .bool => simp <| .or (.not x .bool) (.not y .bool) .bool
    | .or x y  tp    => simp <| .and (.not x tp) (.not y tp) tp
    | .implies x y => simp <| .and x (.not y .prop) .prop
    | .eq b (.trueVal  .bool) .eqBool => .eq b (.falseVal .bool) .eqBool
    | .eq b (.falseVal .bool) .eqBool => .eq b (.trueVal  .bool) .eqBool
    | .eq b (.not c .bool) .eqBool => simp <| .eq b c .eqBool
    | .eq (.not b .bool) c .eqBool => simp <| .eq b c .eqBool
    | .ne b c .neBool  => .eq b c .eqBool
    | .ite c t f .iteProp =>
        match t, f with
        | eq_true  t, eq_true  f => .ite c (eq_false t) (eq_false f) .iteProp
        | eq_true  t, eq_false f => .ite c (eq_false t) (eq_true  f) .iteProp
        | eq_false t, eq_true  f => .ite c (eq_true t)  (eq_false f) .iteProp
        | eq_false t, eq_false f => .ite c (eq_true t)  (eq_true  f) .iteProp
        | _, _ => v
    | _ => v
  | .and x y tp => Id.run do
      if let .trueVal _ := x then
        return y
      if let .falseVal _ := x then
        return x
      if let .trueVal _ := y then
        return x
      if let .falseVal _ := y then
        return y
      if let .and _xl xr _ := x then
        if xr == y then return x
      if let .and yl _yr _ := y then
        if x == yl then return y
      if x == y then
        return x
      else if isComplement x y then
        return .falseVal tp
      else
        return v
  | .or x y tp => Id.run do
      if let .falseVal _ := x then
        return y
      if let .trueVal _ := x then
        return x
      if let .falseVal _ := y then
        return x
      if let .trueVal _ := y then
        return y
      if let .or _xl xr _ := x then
        if xr == y then return x
      if let .or yl _yr _ := y then
        if x == yl then return y
      if x == y then
        return x
      if isComplement x y then
        return .trueVal tp
      pure v
  | .implies x y =>
    match x, y with
    | .trueVal _, y => y
    | .falseVal _, _ => .trueVal .prop
    | _, .trueVal _ => y
    | _, .falseVal _ => simp <| .not x .prop
    | .and a b _, y => simp <| .implies a (.implies b y)
    | x, y => Id.run <| do
      if let .not y _ := y then
        if x == y then
          return .falseVal .prop
      return if x == y then .trueVal .prop else v
  | .eq (.trueVal _) y op =>
    match y with
    | .falseVal _ => .falseVal op.resultType
    | .trueVal _ => .trueVal op.resultType
    | _ =>
      match op with
      | .eqBool => simp <| .eq y (.trueVal .bool) .eqBool
      | .eqProp | .iffProp | .beqBool => y
  | .eq (.falseVal tp) y op =>
    match y with
    | .trueVal  _ => .falseVal op.resultType
    | .falseVal _ => .trueVal  op.resultType
    | _ =>
      match op with
      | .eqBool =>
        simp <| eq_false y
      | _ =>
        simp <| .not y tp
  | .eq x (.trueVal .bool) .eqBool =>
    (match x with
    | .trueVal _ | .falseVal _ | .implies _ _ | .boolToProp _ =>
      panic! "Unexpected term."
    | .var _ _ _ => v
    | .decide t => t
    | .not x _   => simp <| eq_false x
    | .and x y _  => simp <| eq_true x &&& eq_true y
    | .or x y _   => simp <| eq_true x ||| eq_true y
    | .eq x y .beqBool => simp <| .eq x y .eqBool
    | .ne x y .bneBool => simp <| .ne x y .neBool
    | .ite c t f op =>
      (match op with
      | .iteBool | .condBool =>
        simp <| .ite (coerceType c .prop) (eq_true t) (eq_true f) .iteProp
      | .diteBool => panic! "expected dite to simplify away."
      | _ => panic! "Unexpected prop when bool expected.")
    | .eq _ _ _ | .ne _ _ _ =>
        panic! "Unexpected prop when bool expected.")
  | .eq x (.trueVal _) _op => x
  | .eq x (.falseVal _) .eqBool  =>
    match x with
    | .trueVal _ | .falseVal _ | .implies _ _ | .boolToProp _ =>
      panic! "Unexpected term."
    | .var _ _ _ => v
    | .decide t =>
      simp <| .not t .prop
    | .not x _   =>
      simp <| .eq x (.trueVal .bool) .eqBool
    | .and x y _ => simp <| .implies (eq_true x) (eq_false y)
    | .or  x y _ => simp <| .and (eq_false x) (eq_false y) .prop
    | .eq x y .beqBool => simp <| .not (.eq x y .eqBool) .prop
    | .ne x y .bneBool => simp <| .not (.ne x y .neBool) .prop
    | .ite c t f _ =>
      simp <| .ite (coerceType c .prop) (eq_false t) (eq_false f) .iteProp
    | .eq _ _ _ | .ne _ _ _ =>
        panic! "Unexpected prop when bool expected."
   -- N.B. bool ops other than .eqBool do not change type.
  | .eq x y op => Id.run do
    if let .falseVal tp := y then
      return simp (.not x tp)
    if x == y then
      return (.trueVal op.resultType)
    if isComplement x y then
      return (.falseVal op.resultType)
    match op with
    | .eqProp | .iffProp =>
      match x, y with
      -- The cases below simplify the bool to prop normal forms (b = true, b = false) while
      -- avoiding distributing not over the normal form.
      | eq_true  x, eq_true  y => simp <| .eq x y .eqBool
      | eq_false x, eq_false y => simp <| .eq (~ x) (~ y) .eqBool
      | eq_true  x, eq_false y => simp <| .eq x (~ y) .eqBool
      | eq_false x, eq_true  y => simp <| .eq (~ x) y .eqBool
      | _, _ => iff x y
    | .eqBool =>
      match x, y with
      | .decide x, .decide y => iff x y
      | _, _ => v
    | .beqBool => v
  | .ne x y op => Id.run do
    if let .neBool := op then
      return simp (.not (.eq x y .eqBool) .prop)
    if let .neProp := op then
      return simp (.not (.eq x y .eqProp) .prop)
    if let .trueVal _ := x then
      return simp (~y)
    if let .falseVal _ := x then
      return y
    if let .trueVal _ := y then
      return simp (~x)
    if let .falseVal _ := y then
      return x
    if x == y then
      return .falseVal .bool
    if isComplement x y then
      return .trueVal .bool
    pure <|
      match x, y with
      | .ne a b .bneBool, c => .ne a (.ne b c .bneBool) .bneBool
      | .not x _, .not y _ =>  .ne x y .bneBool
      | _, _ => v
  | .ite c t f op => Id.run do
    if let .trueVal _ := c then
      return t
    if let .falseVal _ := c then
      return f
    if let .not c _ := c then
      return simp <| .ite c f t op
    if let .trueVal tp := t then
      return simp <| (coerceType c tp) ||| f
    if let .falseVal tp := t then
      return simp <| (~(coerceType c tp)) &&& f
    if let .trueVal tp := f then
      return simp <| (~(coerceType c tp)) ||| t
    if let .falseVal tp := f then
      return simp <| (coerceType c tp) &&& t
    if t == f then
      return t
    if c == t then
      return simp <| (coerceType c f.typeOf) ||| f
    if c == f then
      return simp <| (coerceType c f.typeOf) &&& t
    let op := match op with
              | .diteProp => .iteProp
              | .diteBool => .iteBool
              | _ => op
    .ite c t f op
  | .trueVal _ | .falseVal _ | .var _ _ _ => v
end
set_option profiler false

end BoolVal

structure BoolOp where
  apply : Array BoolVal → BoolVal
  args : Array BoolType
  result : BoolType

def boolOp
      (apply : Array BoolVal → BoolVal)
      (args : Array BoolType)
      (result : BoolType) : BoolOp :=
  { apply, args, result }

def trueOp  (tp : BoolType) : BoolOp := boolOp (fun _ => .trueVal  tp) #[] tp
def falseOp (tp : BoolType) : BoolOp := boolOp (fun _ => .falseVal tp) #[] tp
def varOp (n : Nat) (v : TSyntax `ident) (tp : BoolType) : BoolOp :=
  boolOp (fun _ => .var n v tp) #[] .prop
def boolToPropOp : BoolOp := boolOp (fun a => .boolToProp (a[0]!)) #[.bool] .prop
def propToBoolOp : BoolOp := boolOp (fun a => .decide (a[0]!)) #[.prop] .bool

def notOp (tp : BoolType) := boolOp (fun a => .not (a[0]!) tp) #[tp] tp
def andOp (tp : BoolType) := boolOp (fun a => .and (a[0]!) (a[1]!) tp) #[tp, tp] tp
def orOp  (tp : BoolType) := boolOp (fun a => .or  (a[0]!) (a[1]!) tp) #[tp, tp] tp
def impliesOp := boolOp (fun a => .implies  (a[0]!) (a[1]!)) #[.prop, .prop] .prop
def eqOp  (op : EqOp)  :=
  boolOp (fun a => .eq (a[0]!) (a[1]!) op) #[op.argType, op.argType] op.resultType
def neOp  (op : NeOp)  :=
  boolOp (fun a => .ne (a[0]!) (a[1]!) op) #[op.argType, op.argType] op.resultType
def iteOp (op : IteOp) :=
  let rtp := op.resultType
  boolOp (fun a => .ite (a[0]!) (a[1]!) (a[2]!) op) #[op.condType, rtp, rtp] rtp

structure GenConfig where
  maxTermSize : Nat
  boolOps : List BoolOp
  propOps : List BoolOp

structure GenState where
  termSize : Nat -- Size of term including empty slots that need to be populated.
  remainingVars : Nat
  propVars : Array (TSyntax `ident)
  boolVars : Array (TSyntax `ident)

@[reducible] def GenM (α : Type) := StateT GenState CommandElabM α

def appendOpApps (cfg : GenConfig) (op : BoolOp)
     (genTerm : BoolType -> GenState → CommandElabM (Array (BoolVal × GenState)))
     (r : Array (BoolVal × GenState))
     (gs : GenState) :
      CommandElabM (Array (BoolVal × GenState)) := do
  let newTermSize := gs.termSize + op.args.size
  if newTermSize > cfg.maxTermSize then
    pure #[]
  else
    -- invariant gs.termSize <= cfg.maxTermSize
    let gs := { gs with termSize := newTermSize }

    let pushArg (args : Array (Array BoolVal × GenState)) (type : BoolType) := do
          args.foldlM (init := #[]) fun r (a, gs) => do
            let terms ← genTerm type gs
            pure <| terms.foldl (init := r) (fun r (v, gs) => r.push (a.push v, gs))

    let args ← op.args.foldlM (init := #[(#[], gs)]) pushArg
    pure <| args.foldl (init := r) (fun r (a, gs) => (r.push (op.apply a, gs)))

def genTerm (cfg : GenConfig) (boolOps propOps : List BoolOp) (depth : Nat) (type : BoolType) (gs : GenState) :
    CommandElabM (Array (BoolVal × GenState)) :=
  match depth with
  | 0 =>
    pure #[]
  | depth + 1 => do
    -- Invariant gs.termSize <= cfg.maxTermSize
    let typedOps :=
          match type with
          | .bool => boolOps
          | .prop => propOps
    let mkTerm type := genTerm cfg boolOps propOps depth type
    let r ←
      if gs.remainingVars > 0 then
        -- Add vars
        let n := gs.remainingVars - 1
        let mut r : Array (BoolVal × GenState) := #[]
        match type with
        | .bool =>
          if gs.boolVars.size > 0 then
            let v := gs.boolVars.back
            let gs := { gs with remainingVars := n, boolVars := gs.boolVars.pop }
            r := r.push (BoolVal.var n v .bool, gs)
        | .prop =>
          if gs.propVars.size > 0 then
            let v := gs.propVars.back
            let gs := { gs with remainingVars := n, propVars := gs.propVars.pop }
            r := r.push (BoolVal.var n v .prop, gs)
        pure r
      else
        pure #[]

    typedOps.foldlM (init := r) fun r op =>
      appendOpApps cfg op mkTerm r gs

section Meta

open Lean
open Elab.Tactic
open Meta

/--
Type used to lift an arbitrary value into a type parameter so it can
appear in a proof goal.

It is used by the #check_tactic command.
-/
private inductive CheckGoalType {α : Sort u} : (val : α) → Prop where
| intro : (val : α) → CheckGoalType val

syntax (name := check_tactic_goal) "check_tactic_goal " term " to " term : tactic

/--
Implementation of `check_tactic_goal`
-/
@[tactic check_tactic_goal] private def evalCheckTacticGoal : Tactic := fun stx =>
  match stx with
  | `(tactic| check_tactic_goal $src to $exp) => do
    closeMainGoalUsing (checkUnassigned := true) fun goalType => do
      let u ← mkFreshLevelMVar
      let type ← mkFreshExprMVar (.some (.sort u))
      let src ← Tactic.elabTermEnsuringType src type
      let val  ← mkFreshExprMVar (.some type)
      let extType := mkAppN (.const ``CheckGoalType [u]) #[type, val]
      if !(← isDefEq goalType extType) then
        throwErrorAt stx "Goal{indentExpr goalType}\nis expected to match {indentExpr extType}"
      let expTerm ← Tactic.elabTermEnsuringType exp type
      if !(← Meta.withReducible <| isDefEq val expTerm) then
        --let src ← Tactic.elabTermEnsuringType src type
        throwErrorAt stx
          m!"{indentExpr src} reduces to{indentExpr val}\nbut is expected to reduce to {indentExpr expTerm}\n{toString src}"
      return mkAppN (.const ``CheckGoalType.intro [u]) #[type, val]
  | _ => throwErrorAt stx "check_goal syntax error"

end Meta

syntax:lead (name := simpTestElab) "#simpTest" : command

@[command_elab simpTestElab]
def elabSimpTest : Lean.Elab.Command.CommandElab := fun _stx => do
  let b : TSyntax `ident ←`(b)
  let c : TSyntax `ident ←`(c)
  let d : TSyntax `ident ←`(d)
  let b := (varOp 0 b .bool).apply #[]
  let c := (varOp 0 c .bool).apply #[]
  let d := (varOp 0 d .bool).apply #[]
  let u : TSyntax `ident ←`(u)
  let v : TSyntax `ident ←`(v)
  let u := (varOp 0 u .prop).apply #[]
  let v := (varOp 0 v .prop).apply #[]
  let e : BoolVal := .ite u (.decide v) (.decide (.trueVal .prop)) .iteBool
  let r := e.simp
  IO.println s!"Simp {repr r}"
  return ()

--#simpTest

syntax:lead (name := genTestElab) "#genTest" : command

open Lean.Elab.Command


private def addScope : CommandElabM Unit := do
  let newNamespace ← getCurrNamespace
  modify fun s => { s with
    env    := s.env.registerNamespace newNamespace,
    scopes := { s.scopes.head! with header := "", currNamespace := newNamespace, isNoncomputable := s.scopes.head!.isNoncomputable } :: s.scopes
  }
  pushScope

def endScope : CommandElabM Unit := do
  modify fun s => { s with scopes := s.scopes.drop 1 }
  popScope

def runTests (stx : Syntax) (cfg : GenConfig) (op : BoolOp) (depth : Nat) (maxVarCount : Nat) : CommandElabM Unit := do
  let b : TSyntax `ident ← `(b)
  let c : TSyntax `ident ← `(c)
  let d : TSyntax `ident ← `(d)
  let u : TSyntax `ident ← `(u)
  let v : TSyntax `ident ← `(v)
  let w : TSyntax `ident ← `(w)

  let genTermC type := genTerm cfg cfg.boolOps cfg.propOps depth type
  let gs : GenState := {
          termSize := 1,
          remainingVars := maxVarCount,
          boolVars := #[d, c, b],
          propVars := #[w, v, u]
        }
  let terms ← appendOpApps cfg op genTermC #[] gs
  for (tm, _) in terms do
    if ← IO.checkCanceled then
      -- should never be visible to users!
      throw <| Exception.error .missing "Testing interrupted"
    let res := tm.simp
    let (t, decls) ← (tm.render).run {}
    if tm.typeOf ≠ res.typeOf then
      logErrorAt stx m!"simp spec for {repr tm} did not preserve type."
    let (exp, _) ← (res.render).run {}
    elabCommand (←`(command|section))
    for ⟨_, nm, tp⟩ in decls do
      match tp with
      | .bool =>
        elabCommand (←`(command|variable ($nm : Bool)))
      | .prop =>
        elabCommand (←`(command|variable ($nm : Prop)))
        elabCommand (←`(command|variable [Decidable $nm]))
    elabCommand (←`(command|example : CheckGoalType $t := by (try simp); check_tactic_goal $t to $exp))
    elabCommand (←`(command|end))

def runCommandElabM (ctx : Command.Context) (ngen : NameGenerator) (env : Environment) (maxRecDepth : Nat)
      (act : CommandElabM Unit) :
    BaseIO (Except Exception MessageLog) := do
  let s : Command.State := {
    env,
    maxRecDepth,
    ngen    --nameGenerator
  }
  let r ← (act |>.run ctx |>.run s).toBaseIO
  match r with
  | .error e =>
    pure (.error e)
  | .ok ((), s) =>
    pure (.ok s.messages)

def runCommandElabM' (acts : List (CommandElabM Unit)) (concurrent := true ) : CommandElabM Unit := do
  if concurrent then
    let ctx : Command.Context ← read
    let s ← get
    let ngen := s.ngen
    let env := s.env
    let maxRecDepth := s.maxRecDepth
    let acts ← acts.mapM (runCommandElabM ctx ngen env maxRecDepth · |>.asTask)
    for act in acts do
      match act.get with
      | .error e =>
        throw e
      | .ok m =>
        modify fun s => { s with messages := s.messages ++ m }
    pure ()
  else
    acts.forM id

@[command_elab genTestElab]
def elabGenTest : CommandElab := fun stx => do
  let baseOps := [
      trueOp  .bool,  trueOp .prop,
      falseOp .bool, falseOp .prop,
      boolToPropOp, propToBoolOp,
      notOp .bool, notOp .prop,
      andOp .bool, andOp .prop,
      orOp .bool,  orOp .prop,
      impliesOp
  ]
  let eqOps := [ eqOp .eqProp, eqOp .eqBool, eqOp .iffProp, eqOp .beqBool ]
  let neOps := [ neOp .neProp, neOp .neBool, neOp .bneBool ]
  let iteOps := [
    iteOp .iteProp, iteOp .iteBool,
    --iteOp .diteProp,  iteOp .diteBool,
    iteOp .condBool
  ]
  let ops := baseOps ++ eqOps ++ neOps ++ iteOps
  let depth := 2
  let maxVarCount := 3
  let boolOps := ops.filter (·.result == .bool)
  let propOps := ops.filter (·.result == .prop)
  let cfg : GenConfig := { maxTermSize := 9, boolOps, propOps }

  let runOp op := runTests stx cfg op (depth := depth) (maxVarCount := maxVarCount)
  -- Note. Can replace ops with a smaller set for specific root
  -- operators.
  runCommandElabM' (ops.map runOp)


#genTest

-- # Direct simplification tests


-- ## Specific unit tests

section simp
variable (p q : Prop)
variable (b c d : Bool)
variable (u v w : Prop) [Decidable u] [Decidable v] [Decidable w]


-- FIXME.  Remove simp from Bool.or_eq_true_iff
set_option trace.Meta.Tactic.simp.rewrite true
set_option trace.Meta.Tactic.simp.rewrite false

-- Specific regressions
#check_simp true ≠ (b || c) ~> b = false ∧ c = false
#check_simp ¬((!b = false) ∧ (c = false)) ~> b = true → c = true
#check_simp (((!b) && c) ≠ false) ~> b = false ∧ c = true
#check_simp (cond b false c ≠ false) ~> b = false ∧ c
#check_simp (b && c) = false ~> b → c = false
#check_simp (b && c) ≠ false ~> b ∧ c
#check_simp decide (u → False) ~> !decide u
#check_simp decide (¬u) ~> !decide u
#check_simp (b = true) ≠ (c = false) ~> b = c
#check_simp (b != c) != (false != d) ~> b != (c != d)
#check_simp (b == false) ≠ (c != d) ~> b = (c != d)
#check_simp (b = true) ≠ (c = false) ~> b = c
#check_simp ¬b = !c ~> b = c
#check_simp (b == c) = false ~> ¬(b = c)
#check_simp (true ≠ if u then b else c) ~> (if u then b = false else c = false)
#check_simp (u ∧ v → False) ~> u → v → False
#check_simp (u = (v ≠ w)) ~> (u ↔ ¬(v ↔ w))
#check_simp ((b = false) = (c = false)) ~> (!b) = (!c)
#check_simp True ≠ (c = false) ~> c = true
#check_simp u ∧ u ∧ v ~> u ∧ v
#check_simp b || (b || c) ~> b || c
#check_simp ((b ≠ c) : Bool) ~> !(decide (b = c))
#check_simp ((u ≠ v) : Bool) ~> !((u : Bool) == (v : Bool))
#check_simp decide (u → False) ~> !(decide u)
#check_simp decide (¬u) ~> !u
-- Specific regressions done

-- Round trip isomorphisms
#check_simp (decide (b : Prop)) ~> b
#check_simp ((u : Bool) : Prop) ~> u

/- # not -/

variable [Decidable u]

-- Ground
#check_simp (¬True) ~> False
#check_simp (¬true) ~> False
#check_simp (!True) ~> false
#check_simp (!true) ~> false

#check_simp (¬False) ~> True
#check_simp (!False) ~> true
#check_simp (¬false) ~> True
#check_simp (!false) ~> true

-- Coercions and not
#check_simp (¬u : Prop) ~> ¬u
#check_simp (¬u : Bool) ~> !u
#check_simp (!u : Prop) ~> ¬u
#check_simp (!u : Bool) ~> !u
#check_simp (¬b : Prop) ~> b = false
#check_simp (¬b : Bool) ~> !b
#check_simp (!b : Prop) ~> b = false
#check_simp (!b : Bool) ~> !b

#check_simp (¬¬u) ~> u

/- # and -/

-- Validate coercions
#check_simp (u ∧  v : Prop) ~> u ∧  v
#check_simp (u ∧  v : Bool) ~> u && v
#check_simp (u && v : Prop) ~> u ∧  v
#check_simp (u && v : Bool) ~> u && v
#check_simp (b ∧  c : Prop) ~> b ∧  c
#check_simp (b ∧  c : Bool) ~> b && c
#check_simp (b && c : Prop) ~> b ∧  c
#check_simp (b && c : Bool) ~> b && c

-- Partial evaluation
#check_simp (True ∧  v : Prop) ~> v
#check_simp (True ∧  v : Bool) ~> (v : Bool)
#check_simp (True && v : Prop) ~> v
#check_simp (True && v : Bool) ~> (v : Bool)
#check_simp (true ∧  c : Prop) ~> (c : Prop)
#check_simp (true ∧  c : Bool) ~> c
#check_simp (true && c : Prop) ~> (c : Prop)
#check_simp (true && c : Bool) ~> c

#check_simp (u ∧  True : Prop) ~> u
#check_simp (u ∧  True : Bool) ~> (u : Bool)
#check_simp (u && True : Prop) ~> u
#check_simp (u && True : Bool) ~> (u : Bool)
#check_simp (b ∧  true : Prop) ~> (b : Prop)
#check_simp (b ∧  true : Bool) ~> b
#check_simp (b && true : Prop) ~> (b : Prop)
#check_simp (b && true : Bool) ~> b

#check_simp (False ∧  v : Prop) ~> False
#check_simp (False ∧  v : Bool) ~> false
#check_simp (False && v : Prop) ~> False
#check_simp (False && v : Bool) ~> false
#check_simp (false ∧  c : Prop) ~> False
#check_simp (false ∧  c : Bool) ~> false
#check_simp (false && c : Prop) ~> False
#check_simp (false && c : Bool) ~> false

#check_simp (u ∧  False : Prop) ~> False
#check_simp (u ∧  False : Bool) ~> false
#check_simp (u && False : Prop) ~> False
#check_simp (u && False : Bool) ~> false
#check_simp (b ∧  false : Prop) ~> False
#check_simp (b ∧  false : Bool) ~> false
#check_simp (b && false : Prop) ~> False
#check_simp (b && false : Bool) ~> false

-- Idempotence
#check_simp (u ∧  u) ~> u
#check_simp (u && u) ~> (u : Bool)
#check_simp (b ∧  b) ~> (b : Prop)
#check_simp (b && b) ~> b

-- Cancelation
#check_simp (u ∧ ¬u)  ~> False
#check_simp (¬u ∧ u)  ~> False
#check_simp (b && ¬b) ~> false
#check_simp (¬b && b) ~> false

#check_simp decide (u → ¬v)  ~> !u || !v

-- Check we swap operators, but do apply deMorgan etc
#check_simp ¬(u ∧ v)  ~> u → ¬v
#check_simp decide (¬(u ∧ v))  ~> !u || !v
#check_simp !(u ∧ v)  ~> !u || !v
#check_simp ¬(b ∧ c)  ~> b → c = false
#check_simp !(b ∧ c)  ~> !b || !c
#check_simp ¬(u && v) ~> u → ¬ v
#check_simp ¬(b && c) ~> b = true → c = false
#check_simp !(u && v) ~> !u || !v
#check_simp !(b && c) ~> !b || !c
#check_simp ¬u ∧  ¬v  ~> (¬u ∧  ¬v)
#check_simp ¬b ∧  ¬c  ~> ((b = false) ∧ (c = false))
#check_simp ¬u && ¬v  ~> (!u && !v)
#check_simp ¬b && ¬c  ~> (!b && !c)

-- Some ternary test cases
#check_simp (u ∧ (v ∧ w) : Prop) ~> (u ∧ v ∧ w)
#check_simp (u ∧ (v ∧ w) : Bool) ~> (u && (v && w))
#check_simp ((u ∧ v) ∧ w : Prop)  ~> ((u ∧ v) ∧ w)
#check_simp ((u ∧ v) ∧ w : Bool)  ~> ((u && v) && w)
#check_simp (b && (c && d) : Prop) ~> (b ∧ c ∧ d)
#check_simp (b && (c && d) : Bool) ~> (b && (c && d))
#check_simp ((b && c) && d : Prop)  ~> ((b ∧ c) ∧ d)
#check_simp ((b && c) && d : Bool)  ~> ((b && c) && d)

/- # or -/

-- Validate coercions
#check_simp (u ∨ v : Prop)  ~> u ∨  v
#check_simp (u ∨ v : Bool)  ~> u || v
#check_simp (u || v : Prop) ~> u ∨  v
#check_simp (u || v : Bool) ~> u || v
#check_simp (b ∨ c : Prop)  ~> b ∨  c
#check_simp (b ∨ c : Bool)  ~> b || c
#check_simp (b || c : Prop) ~> b ∨  c
#check_simp (b || c : Bool) ~> b || c

-- Partial evaluation
#check_simp (True ∨ v : Prop)  ~> True
#check_simp (True ∨ v : Bool)  ~> true
#check_simp (True || v : Prop) ~> True
#check_simp (True || v : Bool) ~> true
#check_simp (true ∨  c : Prop) ~> True
#check_simp (true ∨  c : Bool) ~> true
#check_simp (true || c : Prop) ~> True
#check_simp (true || c : Bool) ~> true

#check_simp (u ∨  True : Prop) ~> True
#check_simp (u ∨  True : Bool) ~> true
#check_simp (u || True : Prop) ~> True
#check_simp (u || True : Bool) ~> true
#check_simp (b ∨  true : Prop) ~> True
#check_simp (b ∨  true : Bool) ~> true
#check_simp (b || true : Prop) ~> True
#check_simp (b || true : Bool) ~> true

#check_simp (False ∨ v : Prop)  ~> v
#check_simp (False ∨ v : Bool)  ~> (v : Bool)
#check_simp (False || v : Prop) ~> v
#check_simp (False || v : Bool) ~> (v : Bool)
#check_simp (false ∨ c : Prop)  ~> (c : Prop)
#check_simp (false ∨ c : Bool)  ~> c
#check_simp (false || c : Prop) ~> (c : Prop)
#check_simp (false || c : Bool) ~> c

#check_simp (u ∨ False : Prop)  ~> u
#check_simp (u ∨ False : Bool)  ~> (u : Bool)
#check_simp (u || False : Prop) ~> u
#check_simp (u || False : Bool) ~> (u : Bool)
#check_simp (b ∨ false : Prop)  ~> (b : Prop)
#check_simp (b ∨ false : Bool)  ~> b
#check_simp (b || false : Prop) ~> (b : Prop)
#check_simp (b || false : Bool) ~> b

-- Idempotence
#check_simp (u ∨ u)  ~> u
#check_simp (u || u) ~> (u : Bool)
#check_simp (b ∨  b) ~> (b : Prop)
#check_simp (b || b) ~> b

-- Complement
--#check_simp ( u ∨  ¬u)  ~> True
--#check_simp (¬u ∨   u)  ~> True
#check_simp ( b || ¬b)  ~> true
#check_simp (¬b ||  b)  ~> true

-- Check we swap operators, but do apply deMorgan etc
#check_simp ¬(u ∨ v)  ~> ¬u ∧ ¬v
#check_simp !(u ∨ v)  ~> !u && !v
#check_simp ¬(b ∨ c)  ~> b = false ∧ c =false
#check_simp !(b ∨ c)  ~> !b && !c
#check_simp ¬(u || v) ~> ¬u ∧ ¬v
#check_simp ¬(b || c) ~> b = false ∧ c = false
#check_simp !(u || v) ~> !u && !v
#check_simp !(b || c) ~> !b && !c
#check_simp ¬u ∨  ¬v  ~> (¬u ∨  ¬v)
#check_simp (¬b) ∨ (¬c)  ~> b = false ∨ c = false
#check_simp ¬u || ¬v  ~> (!u || !v)
#check_simp ¬b || ¬c  ~> (!b || !c)

-- Some ternary test cases
#check_simp (u ∨ (v ∨ w) : Prop)   ~> (u ∨ v ∨ w)
#check_simp (u ∨ (v ∨ w) : Bool)   ~> (u || (v || w))
#check_simp ((u ∨ v) ∨ w : Prop)   ~> ((u ∨ v) ∨ w)
#check_simp ((u ∨ v) ∨ w : Bool)   ~> ((u || v) || w)
#check_simp (b || (c || d) : Prop) ~> (b ∨ c ∨ d)
#check_simp (b || (c || d) : Bool) ~> (b || (c || d))
#check_simp ((b || c) || d : Prop) ~> ((b ∨ c) ∨ d)
#check_simp ((b || c) || d : Bool) ~> ((b || c) || d)

/- # and/or -/

-- We don't currently do automatic simplification across and/or/not
-- This tests for non-unexpected reductions.

#check_simp u ∧ (v ∨ w) ~> u ∧ (v ∨ w)
#check_simp u ∨ (v ∧ w) ~> u ∨ (v ∧ w)
#check_simp (v ∨ w) ∧ u ~> (v ∨ w) ∧ u
#check_simp (v ∧ w) ∨ u ~> (v ∧ w) ∨ u
#check_simp b && (c || d) ~> b && (c || d)
#check_simp b || (c && d) ~> b || (c && d)
#check_simp (c || d) && b ~> (c || d) && b
#check_simp (c && d) || b ~> (c && d) || b

/- # iff -/

-- Without decidable test cases
#check_simp p = q ~> p ↔ q
#check_simp p ↔ q ~> p ↔ q

--set_option trace.Meta.Tactic.simp.rewrite true
-- Bool.not_eq_true
#check_simp ¬b ~> b = false

--#check_simp (false = b) ~> ¬b
--#check_simp (false = p : Prop) ~> not b


#check_simp (u = v : Prop) ~> u ↔ v
#check_simp (u = v : Bool) ~> u == v
#check_simp (u ↔ v : Prop) ~> u ↔ v
#check_simp (u ↔ v : Bool) ~> u == v
#check_simp (u == v : Prop) ~> u ↔ v
#check_simp (u == v : Bool) ~> u == v

#check_simp (b = c : Prop) ~> b = c
#check_simp (b = c : Bool) ~> decide (b = c)
#check_simp (b ↔ c : Prop) ~> b = c
#check_simp (b ↔ c : Bool) ~> decide (b = c)
#check_simp (b == c : Prop) ~> b = c
-- N.B. Mathlib would rewrite this to `decide(b = c)` via [`beq_eq_decide_eq`][1]:
-- [1]: <https://github.com/leanprover-community/mathlib4/blob/450459a3bc55a75e540d139dbeec9c0a92acabb8/Mathlib/Data/Bool/Basic.lean#L87)>
#check_simp (b == c : Bool) ~> b == c

-- Partial evaluation
#check_simp (True = v : Prop)  ~> v
#check_simp (True = v : Bool)  ~> (v : Bool)
#check_simp (True ↔ v : Prop)  ~> v
#check_simp (True ↔ v : Bool)  ~> (v : Bool)
#check_simp (True == v : Prop) ~> v
#check_simp (True == v : Bool) ~> (v : Bool)
 -- TODO: See if this can be further simplified
#check_simp (true =  c : Prop) ~> c = true
#check_simp (true =  c : Bool) ~> c
#check_simp (true ↔  c : Prop) ~> c = true
#check_simp (true ↔  c : Bool) ~> c
#check_simp (true == c : Prop) ~> (c : Prop)
#check_simp (true == c : Bool) ~> c

#check_simp (v = True : Prop)  ~> v
#check_simp (v = True : Bool)  ~> (v : Bool)
#check_simp (v ↔ True : Prop)  ~> v
#check_simp (v ↔ True : Bool)  ~> (v : Bool)
#check_simp (v == True : Prop) ~> v
#check_simp (v == True : Bool) ~> (v : Bool)
#check_simp (c = true : Prop) ~> c = true
#check_simp (c = true : Bool) ~> c
#check_simp (c ↔ true : Prop) ~> c = true
#check_simp (c ↔ true : Bool) ~> c
#check_simp (c == true : Prop) ~> c = true
#check_simp (c == true : Bool) ~> c

#check_simp (True = v : Prop)  ~> v
#check_simp (True = v : Bool)  ~> (v : Bool)
#check_simp (True ↔ v : Prop)  ~> v
#check_simp (True ↔ v : Bool)  ~> (v : Bool)
#check_simp (True == v : Prop) ~> v
#check_simp (True == v : Bool) ~> (v : Bool)
 -- TODO: See if this can be further simplified
#check_simp (true =  c : Prop) ~> c = true
#check_simp (true =  c : Bool) ~> c
#check_simp (true ↔  c : Prop) ~> c = true
#check_simp (true ↔  c : Bool) ~> c
#check_simp (true == c : Prop) ~> (c : Prop)
#check_simp (true == c : Bool) ~> c

#check_simp (v = False : Prop)  ~> ¬v
#check_simp (v = False : Bool)  ~> !v
#check_simp (v ↔ False : Prop)  ~> ¬v
#check_simp (v ↔ False : Bool)  ~> !v
#check_simp (v == False : Prop) ~> ¬v
#check_simp (v == False : Bool) ~> !v
#check_simp (c = false : Prop) ~> c = false
#check_simp (c = false : Bool) ~> !c
#check_simp (c ↔ false : Prop) ~> c = false
#check_simp (c ↔ false : Bool) ~> !c
#check_simp (c == false : Prop) ~> c = false
#check_simp (c == false : Bool) ~> !c

#check_simp (False = v : Prop)  ~> ¬v
#check_simp (False = v : Bool)  ~> !v
#check_simp (False ↔ v : Prop)  ~> ¬v
#check_simp (False ↔ v : Bool)  ~> !v
#check_simp (False == v : Prop) ~> ¬v
#check_simp (False == v : Bool) ~> !v
 -- TODO: See if this can be further simplified
#check_simp (false =  c : Prop) ~> c = false
#check_simp (false =  c : Bool) ~> !c
#check_simp (false ↔  c : Prop) ~> c = false
#check_simp (false ↔  c : Bool) ~> !c
#check_simp (false == c : Prop) ~> c = false
#check_simp (false == c : Bool) ~> !c

-- Ternary (expand these)

#check_simp (u == (v = w))  ~> u == (v == w)
#check_simp (u == (v == w)) ~> u == (v == w)

/- # xor -/

#check_simp (u == (v ∨ w)) ~>  u == (v || w)
#check_simp (u == (v || w)) ~> u == (v || w)

#check_simp ((u ∧ v) == w) ~> (u && v) == w

#check_simp p ≠ q ~> ¬(p ↔ q)
#check_simp (b != c : Bool) ~> b != c
#check_simp ¬(p = q) ~> ¬(p ↔ q)
#check_simp b ≠ c    ~> b ≠ c
#check_simp ¬(b = c) ~> b ≠ c
#check_simp ¬(b ↔ c) ~> ¬(b = c)
#check_simp (b != c : Prop) ~> b ≠ c
#check_simp u ≠ v    ~> ¬(u ↔ v)
#check_simp ¬(u = v) ~> ¬(u ↔ v)
#check_simp ¬(u ↔ v) ~> ¬(u ↔ v)
#check_simp ((u:Bool) != v : Bool) ~> (u:Bool) != v
#check_simp ((u:Bool) != v : Prop) ~> ¬(u ↔ v)

#check_simp ¬p ~> ¬p
#check_simp !b ~> !b
#check_simp ¬b ~> b = false
#check_simp ¬u ~> ¬u
#check_simp ((!u) : Prop) ~> ¬u


#check_simp b && (¬b) ~> false
#check_simp ¬b && b ~> false
#check_simp (u ∧ v)         ~> u ∧ v
#check_simp (u && v)        ~> u && v
#check_simp (u && v : Prop) ~> u ∧ v

#check_simp p ∨ q ~> p ∨ q
#check_simp q ∨ p ~> q ∨ p
#check_simp (b ∨ c)         ~> b ∨ c
#check_simp (b || c)        ~> b || c
#check_simp (b || c : Prop) ~> b ∨ c
#check_simp (u ∨ v)         ~> u ∨ v
#check_simp (u || v)        ~> u || v
#check_simp (u || v : Prop) ~> u ∨ v

#check_simp p ∧ (p ∨ q) ~> p ∧ (p ∨ q) -- ? See Cancelation discussion?
#check_simp (p ∨ q) ∧ p ~> (p ∨ q) ∧ p -- ?

#check_simp (b → c)         ~> b → c
#check_simp (u → v)         ~> u → v
#check_simp p → q ~> p → q

#check_simp if b then c else d ~> if b then c else d
#check_simp if b then p else q ~> if b then p else q
#check_simp if u then p else q ~> if u then p else q
#check_simp if u then b else c ~> if u then b else c
#check_simp if u then u else q ~> u ∨ q
#check_simp if u then q else u ~> u ∧ q
#check_simp if u then q else q  ~> q
#check_simp cond b c d ~> cond b c d

end simp
