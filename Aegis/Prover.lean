import Lean

/-!
# Aegis: Universal Prover/Disprover for Lean 4

A semi-decidable procedure that utilizes iterative deepening to find
the optimal (shortest) proof or refutation for a given proposition.

### Usage: Truly Running Forever
We have included a thread-based option to kill the running of this task
because Lean 4 does not allow a function execution to be remotely killed
in a proper manner. This makes it harness-aware, which is also what it is
expected to be used for(with) in most of the use cases.
To ensure the prover runs indefinitely until a result is found,
provide an `IO.Ref Bool` that is never modified:

```lean
let permanentlyFalse ← IO.mkRef false
let result ← Aegis.proveOrDisprove p permanentlyFalse
```

In this configuration, the cancellation check always fails, and
the iterative deepening recursion continues without interruption.
-/

open Lean Meta Elab Tactic

namespace Aegis

/--
Result structure for the prover/disprover.

`status = true` certifies `proof : p`; `status = false` certifies
`proof : p → False`. `Aegis.checkResponse` re-verifies that claim, so a
`ProofResponse` produced by an untrusted prover is never taken on faith.
-/
structure ProofResponse where
  status : Bool
  proof  : Expr
  deriving Inhabited

/--
The axioms a certificate is allowed to rest on: the three that Lean's own
`#print axioms` treats as the standard foundation.

Lean's environment also carries axioms that are trust escape hatches rather
than logical foundations -- `Lean.trustCompiler`, `Lean.ofReduceBool`,
`Lean.ofReduceNat` -- and `Lean.trustCompiler : True` in particular closes a
`True` goal in one step. A certificate resting on one of those is evidence
about the compiler, not about the proposition.
-/
def trustedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/--
The vocabulary a certificate may be built from, shared by the search and the
checker so that the two cannot disagree about what counts as a proof.

Three exclusions, each of which would otherwise let anything be "proved":
* unsafe constants -- the compiler's `lcProof : ∀ {α : Prop}, α` and
  `lcUnreachable : {α : Sort u} → α` close *any* goal in a single `apply`;
* `sorryAx`, the representation of an admitted proof;
* axioms outside `trustedAxioms`.

Type-checking cannot substitute for this. `lcProof` is a perfectly well-typed
constant, so a term built from it passes every checker Lean has; what makes it
inadmissible is *which* constant it is.
-/
def admissibleConstant (name : Name) (info : ConstantInfo) : Bool :=
  !info.isUnsafe && name != ``sorryAx &&
    (!(info matches .axiomInfo _) || trustedAxioms.contains name)

/--
Retrieves the names of all non-internal constants available in the environment.

Names rather than `Expr`s: a universe-polymorphic constant must be instantiated
with *fresh* universe metavariables at every use site, so sharing one `Expr`
across the whole search would let the first successful `apply` pin the universe
levels for every later one. The list is also built once per search rather than
once per node -- traversing the whole environment at every node dominated the
runtime of the search it was meant to serve.

Only admissible constants are offered to the search, so that Aegis's own
certificates pass `checkResponse` by construction rather than by luck.
-/
def getUniversalConstants : MetaM (Array Name) := do
  let env ← getEnv
  let mut constants := #[]
  for (name, info) in env.constants.toList do
    if !name.isInternal && admissibleConstant name info then
      constants := constants.push name
  return constants

/--
Generates the next layer of the search tree.

Every branch is returned together with the metavariable state that produced it.
Tactics work by *assigning* metavariables, so branches are not independent: once
one candidate has assigned `g`, the next candidate would be elaborating against
a goal that no longer exists. Saving a state per branch (and restoring the
entry state before each attempt) keeps the layer a genuine set of alternatives,
which is what completeness and depth-optimality both rest on.

The candidates are `intro`, `assumption`, application of every local hypothesis,
and application of every constant in the environment. Local hypotheses have to
be applied as well as matched: `assumption` closes `⊢ Q` from `h : Q`, but only
`apply h` closes it from `h : P → Q`.
-/
def universalStep (g : MVarId) (constants : Array Name) :
    MetaM (Array (Meta.SavedState × List MVarId)) := do
  let entry ← saveState
  let mut branches := #[]
  try
    entry.restore
    let (_, newGoal) ← g.intro1P
    branches := branches.push (← saveState, [newGoal])
  catch _ => pure ()
  try
    entry.restore
    g.assumption
    branches := branches.push (← saveState, [])
  catch _ => pure ()
  let locals ← g.withContext do
    let mut fvars := #[]
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        fvars := fvars.push decl.toExpr
    return fvars
  for h in locals do
    try
      entry.restore
      let newGoals ← g.apply h
      branches := branches.push (← saveState, newGoals)
    catch _ => pure ()
  for c in constants do
    try
      entry.restore
      let newGoals ← g.apply (← mkConstWithFreshMVarLevels c)
      branches := branches.push (← saveState, newGoals)
    catch _ => pure ()
  entry.restore
  return branches

/--
Bounded depth-first search component.

`fuel` bounds the number of proof steps, so the outer iterative deepening loop
walks the search space one layer at a time. Each branch is explored from the
state that branch produced, and the entry state is restored on failure so that
sibling branches -- and the next, deeper iteration -- start clean.

The stop signal is polled per node, not merely per depth: a single depth level
is itself unbounded (its branching factor is the size of the environment), so a
check that only ran between levels would leave a cancelled search grinding for
an arbitrarily long time.
-/
def universalSearch (goals : List MVarId) (fuel : Nat) (root : MVarId)
    (constants : Array Name) (stopSignal : IO.Ref Bool) : MetaM (Option Expr) := do
  if ← stopSignal.get then return none
  -- Drop goals that are already solved. Applying a constant unifies its
  -- conclusion with the goal, which can assign *sibling* goals as a side
  -- effect: closing `?h : ?w = 0` with `rfl` assigns the witness `?w := 0`.
  -- The witness then stays in this list as a goal that no candidate can touch
  -- -- every tactic raises `checkNotAssigned` on it -- so the node yields no
  -- branches and a finished proof is abandoned as a dead end. Lean's own
  -- tactic framework prunes for the same reason.
  let goals ← goals.filterM fun g => return !(← g.isAssigned)
  match goals with
  | [] => return some (← instantiateMVars (mkMVar root))
  | g :: rest =>
    match fuel with
    | 0 => return none
    | n + 1 =>
      let entry ← saveState
      for (state, branch) in ← universalStep g constants do
        state.restore
        if let some proof ← universalSearch (branch ++ rest) n root constants stopSignal then
          return some proof
        entry.restore
      return none

/--
Recursive implementation of the iterative deepening loop.

Fresh metavariables are allocated per iteration so that a failed search leaves
nothing behind to corrupt the next, deeper one.
-/
partial def deepen (p negation : Expr) (constants : Array Name)
    (stopSignal : IO.Ref Bool) (depth : Nat) : MetaM (Option ProofResponse) := do
  -- Poll the stopSignal; if permanently false, this branch is never taken.
  if ← stopSignal.get then return none

  -- Search for proof of P
  let mVarTrue ← mkFreshExprMVar p
  if let some proof ← universalSearch [mVarTrue.mvarId!] depth mVarTrue.mvarId!
      constants stopSignal then
    return some ⟨true, proof⟩

  -- Search for proof of P → False
  let mVarFalse ← mkFreshExprMVar negation
  if let some refutation ← universalSearch [mVarFalse.mvarId!] depth mVarFalse.mvarId!
      constants stopSignal then
    return some ⟨false, refutation⟩

  deepen p negation constants stopSignal (depth + 1)

/--
Entry point for the universal prover/disprover.
Accepts a stopSignal (IO.Ref Bool) for thread-safe cancellation.
If stopSignal is set to true externally, returns 'none' to halt recursion.

The search runs with `maxHeartbeats := 0`. That limit exists to stop a
misbehaving tactic from hanging an interactive session; here an unbounded
search is the specification, and leaving the limit in place would have the
prover abort with "maximum number of heartbeats reached" rather than run until
it finds a result.
-/
partial def proveOrDisprove (p : Expr) (stopSignal : IO.Ref Bool) :
    MetaM (Option ProofResponse) :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) do
    let negation ← mkArrow p (mkConst ``False)
    deepen p negation (← getUniversalConstants) stopSignal 1

/--
Walks the constants a certificate transitively depends on and rejects it unless
every one of them is `admissibleConstant`.

A prover we did not write hands us an arbitrary `Expr`, so the vocabulary it
used has to be checked rather than assumed. Internal names are allowed here,
unlike in the search: a legitimate proof term routinely mentions the internal
constants Lean generates for it.
-/
partial def auditCertificate (e : Expr) : MetaM Bool := do
  let env ← getEnv
  let rec go (pending : List Name) (seen : NameSet) : Bool :=
    match pending with
    | [] => true
    | c :: rest =>
      if seen.contains c then go rest seen
      else match env.find? c with
        | none => false
        | some info =>
          if !admissibleConstant c info then false
          else
            let next := info.type.getUsedConstants.toList
              ++ (info.value?.map (·.getUsedConstants.toList)).getD []
            go (next ++ rest) (seen.insert c)
  return go e.getUsedConstants.toList {}

/--
Re-checks a `ProofResponse` against the proposition it claims to settle:
the certificate must be closed (no holes, no `sorry`), must type-check, must
rest only on `trustedAxioms`, and its type must be defeq to `p` for a proof or
to `p → False` for a refutation.

This is what lets an unverified prover be trusted. Aegis's own certificates
pass by construction, but a response handed back by an AI is just an `Expr`
until the type checker and the axiom audit both agree with it.
-/
def checkResponse (p : Expr) (res : ProofResponse) : MetaM Bool :=
  -- Read-only: `isDefEq` assigns metavariables to make itself succeed, and `p`
  -- belongs to the caller. Without this, a competitor answering `True.intro`
  -- for a proposition that still carries a hole would *assign* that hole to
  -- `True` and thereby make its own claim come true.
  withoutModifyingState do
    try
      let proof ← instantiateMVars res.proof
      if proof.hasExprMVar || proof.hasSorry then return false
      -- `inferType` assumes its argument is already type-correct: it reads the
      -- pi type off the function and returns the instantiated body without ever
      -- looking at the argument, so `@id False True.intro` "has type" `False`.
      -- `check` is the one that actually type-checks.
      Meta.check proof
      unless ← auditCertificate proof do return false
      let expected ← if res.status then pure p else mkArrow p (mkConst ``False)
      isDefEq (← inferType proof) expected
    catch _ => return false

end Aegis
