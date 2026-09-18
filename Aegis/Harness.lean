import Aegis.Prover
import Lean

open Lean Meta

namespace Aegis

/-- Polling interval in milliseconds. -/
def POLLING_MS : UInt32 := 20

/--
A racer's task. `IO.asTask` reports a crash as an `Except` value rather than
propagating it, which is exactly what the harness wants: a competitor that
throws must lose the race, not take the race down with it.
-/
abbrev Racer := Task (Except IO.Error (Option ProofResponse))

/--
The polling loop. Returns the first *verified* certificate produced by any
racer and sets the stop signal so the loser stops burning cores.

A racer is dropped from the pool once it has halted, whether it halted with
nothing, with a crash, or with a certificate that failed `checkResponse`. The
race is therefore only lost when every racer has halted without proving
anything -- an AI that returns garbage, or dies, cannot rob the caller of the
Aegis branch that is still running.

Marked `partial`: the loop inherits the semi-decidability of its racers, and
imposing a termination measure here would mean imposing an artificial timeout.
-/
partial def pollRace (p : Expr) (stopSignal : IO.Ref Bool) (racers : List Racer) :
    MetaM (Option ProofResponse) := do
  let mut running : List Racer := []
  for t in racers do
    if ← IO.hasFinished t then
      if let .ok (some res) ← IO.wait t then
        if ← checkResponse p res then
          stopSignal.set true
          return some res
    else
      running := t :: running
  if running.isEmpty then
    stopSignal.set true
    return none
  IO.sleep POLLING_MS
  pollRace p stopSignal running.reverse

/--
Harness races Aegis proveOrDisprove against a competitor and halts, returning the result of whichever one ended first.
Because proveOrDisprove is guaranteed to be best-possible modulo finite time see (Aegis.Prover), this is a useful way,
for peace-of-mind, to ensure that probabilistic provers with this harness are guaranteed to also be best-possible modulo
finite time, and in all likelihood terminating significantly faster than the very slow deterministic (among the other
certainty guarantees) proveOrDisprove code.

The guarantee is injected by `checkResponse`, not by the race: whatever the
competitor hands back is type-checked against `p` before it is allowed to win.
An unchecked answer from a non-deterministic prover would leave the harness no
stronger than that prover, which is the opposite of the point.
-/
def harness
    (p : Expr)
    (competitor : Expr → IO.Ref Bool → MetaM (Option ProofResponse))
    : MetaM (Option ProofResponse) := do

  let stopSignal ← IO.mkRef false

  -- Capture the caller's context in full. `p` is elaborated in the caller's
  -- local context and may mention its free variables, so a racer started with
  -- an empty context would be searching for a proof of a different statement.
  let coreCtx ← readThe Core.Context
  let coreState ← getThe Core.State
  let metaCtx ← readThe Meta.Context
  let metaState ← getThe Meta.State

  -- The runner executes the MetaM stack inside the IO monad.
  let run (prover : Expr → IO.Ref Bool → MetaM (Option ProofResponse)) :
      IO (Option ProofResponse) := do
    -- Compose the monad stack: MetaM -> CoreM -> EIO, then recover from any
    -- internal exception as a loss rather than an error.
    let task := (prover p stopSignal).run metaCtx metaState |>.run coreCtx coreState
    match ← EIO.toIO' task with
    | .ok ((res, _), _) => return res
    | .error _ => return none

  -- `Task.Priority.dedicated` gets each racer its own thread. Both may run
  -- unboundedly, so scheduling them on the shared task pool would let them
  -- starve it -- and each other -- instead of running in parallel.
  let t1 ← IO.asTask (run proveOrDisprove) Task.Priority.dedicated
  let t2 ← IO.asTask (run competitor) Task.Priority.dedicated

  pollRace p stopSignal [t1, t2]

end Aegis
