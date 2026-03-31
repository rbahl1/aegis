import Lean

/-!
# Aegis: Universal Prover/Disprover for Lean 4

A semi-decidable procedure that utilizes iterative deepening to find 
the optimal (shortest) proof or refutation for a given proposition.
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
-/
partial def proveOrDisprove (p : Expr) : MetaM ProofResponse := do
  let negation ← mkArrow p (mkConst ``False)
  let mVarTrue ← mkFreshExprMVar p
  let mVarFalse ← mkFreshExprMVar negation
  
  let rec find (depth : Nat) : MetaM ProofResponse := do
    -- Search for proof of P
    if let some proof ← universalSearch [mVarTrue.mvarId!] depth mVarTrue.mvarId! then
      return ⟨true, proof⟩
    -- Search for proof of P → False
    if let some refutation ← universalSearch [mVarFalse.mvarId!] depth mVarFalse.mvarId! then
      return ⟨false, refutation⟩
    find (depth + 1)

  find 1

end Aegis
