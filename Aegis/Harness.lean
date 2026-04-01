import Aegis.Prover
import Lean

open Lean Meta

namespace Aegis

/-- Polling interval constant in milliseconds -/
def POLLING_MS : Nat := 20

/-- Validates the polling interval is at least 1ms -/
def getSleepTime : UInt32 := 
  if POLLING_MS > 0 then POLLING_MS.toUInt32 else 1

/-- 
  Harness races Aegis proveOrDisprove against a competitor and halts, returning the result of whichever one ended first. 
  Because proveOrDisprove is guaranteed to be best-possible modulo finite time see (Aegis.Prover), this is a useful way, 
  for peace-of-mind, to ensure that probabilistic provers with this harness are guaranteed to also be best-possible modulo
  finite time, and in all likelihood terminiating significantly faster than the very slow deterministic (among the other
  certainty guarantees) proveOrDisprove code. 
  Marked 'partial' to match the semi-decidability of 'proveOrDisprove'.
-/
partial def harness 
  (p : Expr) 
  (competitor : Expr → IO.Ref Bool → MetaM (Option ProofResponse)) 
  : MetaM (Option ProofResponse) := do
  
  let stopSignal ← IO.mkRef false
  
  -- Capture current environment and configuration
  let env ← getEnv
  let mctx ← getMCtx
  let opts ← getOptions

  -- The runner executes the MetaM stack inside the IO monad.
  let run (prover : Expr → IO.Ref Bool → MetaM (Option ProofResponse)) : IO (Option ProofResponse) := do
    let coreCtx : Core.Context := { fileName := "<harness>", fileMap := default, options := opts }
    let coreState : Core.State := { env := env }
    let metaCtx : Meta.Context := { lctx := {} }
    let metaState : Meta.State := { mctx := mctx }

    -- 1. Compose the Monad stack: MetaM -> CoreM -> EIO
    -- We pass the initial states directly into the runners.
    let task := (prover p stopSignal).run metaCtx metaState |>.run coreCtx coreState
    
    -- 2. Execute the EIO function and handle potential internal exceptions
    let result ← EIO.toIO (fun _ => IO.userError "Harness internal error") task
    
    -- 3. Pattern match to extract the Option ProofResponse from the nested state tuples:
    -- The structure is ((Option ProofResponse, Meta.State), Core.State)
    let ((res, _), _) := result
    return res

  -- Start the concurrent tasks
  let t1 ← IO.asTask (run Aegis.proveOrDisprove)
  let t2 ← IO.asTask (run competitor)

  -- The polling loop: Inherits the 'no weaker' guarantee of the provers.
  let rec poll : IO (Option ProofResponse) := do
    if ← IO.hasFinished t1 then
      let res ← IO.ofExcept (← IO.wait t1)
      if res.isSome then 
        stopSignal.set true
        return res
    
    if ← IO.hasFinished t2 then
      let res ← IO.ofExcept (← IO.wait t2)
      if res.isSome then 
        stopSignal.set true
        return res

    -- If both provers finish with 'none', return 'none'
    if (← IO.hasFinished t1) && (← IO.hasFinished t2) then
      return none

    IO.sleep getSleepTime
    poll

  -- Lift the IO poll loop back into MetaM for the final result
  liftM poll

end Aegis
