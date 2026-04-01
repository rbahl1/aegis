import Lean

/-!
# Aegis: Universal Prover/Disprover for Lean 4

A semi-decidable procedure that utilizes iterative deepening to find 
the optimal (shortest) proof or refutation for a given proposition.

### Usage: Truly Running Forever
To ensure the prover runs indefinitely until a result is found, 
provide an `IO.Ref Bool` that is never modified:

```lean
let permanentlyFalse ← liftM (IO.mkRef false : IO (IO.Ref Bool))
let result ← Aegis.proveOrDisprove p permanentlyFalse
In this configuration, the cancellation check always fails, and
the iterative deepening recursion continues without interruption.
-/

open Lean Meta Elab Tactic

/-- Result structure for the prover/disprover. -/
structure ProofResponse where
  status : Bool
  proof  : Expr
  deriving Inhabited

namespace Aegis

/-- Retrieves all non-internal constants available in the environment. -/
def getUniversalConstants : MetaM (List Expr) := do
  let env ← getEnv
  let mut constants := []
  for (name, _) in env.constants.toList do
    if !name.isInternal then 
      constants := (mkConst name) :: constants
  return constants

/-- Generates the next layer of the search tree. -/
def universalStep (g : MVarId) : MetaM (List (List MVarId)) := do
  let mut nextStates := []
  try 
    let (_, newGoal) ← g.intro1P 
    nextStates := [newGoal] :: nextStates
  catch _ => pure ()
  try 
    g.assumption
    nextStates := [] :: nextStates 
  catch _ => pure ()
  for c in (← getUniversalConstants) do
    try nextStates := (← g.apply c) :: nextStates
    catch _ => continue
  return nextStates

/-- Bounded depth-first search component. -/
def universalSearch (goals : List MVarId) (fuel : Nat) (root : MVarId) : MetaM (Option Expr) := do
  if goals.isEmpty then 
    return ← instantiateMVars (mkMVar root)
  match fuel with
  | 0 => return none
  | n + 1 =>
    let g := goals.head!; let rest := goals.tail!
    for branch in (← universalStep g) do
      if let some proof ← universalSearch (branch ++ rest) n root then 
        return some proof
    return none

/-- 
Entry point for the universal prover/disprover. 
Recursive implementation of the iterative deepening loop.
Accepts a stopSignal (IO.Ref Bool) for thread-safe cancellation.
If stopSignal is set to true externally, returns 'none' to halt recursion.
-/
partial def proveOrDisprove (p : Expr) (stopSignal : IO.Ref Bool) : MetaM (Option ProofResponse) := do
  let negation ← mkArrow p (mkConst ``False)
  let mVarTrue ← mkFreshExprMVar p
  let mVarFalse ← mkFreshExprMVar negation
  
  -- 1. CRITICAL: The explicit return type MUST be here so Lean knows the monad
  let rec find (depth : Nat) : MetaM (Option ProofResponse) := do
    
    -- 2. CLEANER: Lean 4 auto-lifts IO to MetaM. No need for liftM or type ascriptions.
    if ← stopSignal.get then return none

    if let some proof ← universalSearch [mVarTrue.mvarId!] depth mVarTrue.mvarId! then
      return some ⟨true, proof⟩
    if let some refutation ← universalSearch [mVarFalse.mvarId!] depth mVarFalse.mvarId! then
      return some ⟨false, refutation⟩
      
    find (depth + 1)

  find 1

end Aegis
