# Aegis

**Aegis** is a formal verification suite for Lean 4. It has deciders(provers) and wrapper(s) to inject absolute formal guarantees into non-guaranteed AI-based formal applications.

The engine implements a semi-decidable procedure using iterative deepening. By exhaustively searching the environment's space of proof terms, Aegis guarantees the discovery of the **globally optimal (shortest) proof term** for a given proposition or its negation, provided such a term exists.

### The Prover: Exhaustive Search & Optimality
- **Semi-Decidability**: Implements a semi-decidable procedure. If a proof exists within the search space, Aegis is guaranteed to find it, regardless of complexity. The search space is every term reachable by `intro`, `assumption`, and application of any local hypothesis or any non-internal constant in the environment -- universe-polymorphic constants included, each instantiated with fresh universe metavariables at every use site.
- **Path Optimality**: The iterative deepening architecture explores the search space layer by layer, one proof step at a time. The first certificate discovered is therefore guaranteed to be the shortest possible one. Branches are explored from their own metavariable state and the entry state is restored on failure, so a layer is a genuine set of alternatives rather than a single path.
- **Optimizations**: Constructs and verifies both the proposition $P$ and its negation $\neg P$, allowing for definitive refutation as well as proof.
- **No Artificial Ceiling**: The search runs with `maxHeartbeats := 0`. That limit exists to keep a runaway tactic from hanging an interactive session; here an unbounded search *is* the specification, so leaving it in place would have the prover abort rather than run until it finds a result.

### The Harness: Termination & Guarantee Injection
- **Wrapping**: Allows non-deterministic AI models (which typically lack termination proofs) to inherit the semi-decidable bounds of the Aegis engine.
- **Guarantee Injection**: The race alone would leave the harness no stronger than its weakest racer. What makes it stronger is `Aegis.checkResponse`: every certificate, whoever produced it, must be closed (no holes, no `sorry`) and must type-check against the proposition it claims to settle before it is allowed to win. An AI's answer is just an `Expr` until the type checker agrees with it.
- **Formal Anchoring**: Provides a "ground truth" fallback. If an AI prover loops forever, returns nothing, returns a bogus certificate, or crashes outright, it is simply dropped from the race and the Aegis branch keeps running -- the system still moves toward a best-possible deterministic guarantee, regardless of time.
- **Concurrency**: Each racer is started with `IO.asTask` at `Task.Priority.dedicated`, so two unbounded searches run on their own threads in parallel rather than starving the shared task pool.
- **Cancellation**: Lean 4 cannot kill a running task from the outside, so the loser is stopped cooperatively via a shared `IO.Ref Bool`. Aegis polls that signal at every node of the search, not merely between depths -- a single depth level is itself unbounded, so a per-depth check would leave a cancelled search grinding for an arbitrarily long time.
- **Best-possible prover (modulo finite-time) certification**: The race loop is a `partial` function, so the harness inherits the semi-decidability of its racers instead of imposing an artificial timeout.

---

## Features

### 1. The Prover (`Aegis.proveOrDisprove`)
The entry point for the universal search. A semi-decidable procedure that runs indefinitely until a proof or refutation is found, or an external stop signal is received. It trades computational speed for logical completeness.

### 2. The Harness (`Aegis.harness`)
The Harness is a **Wrapper with Guarantees**. It allows a non-deterministic AI prover (e.g., an LLM-based agent) to inherit the best-possible termination guarantees of a formal engine, and refuses to hand back anything the type checker has not confirmed.

### 3. The Checker (`Aegis.checkResponse`)
Re-verifies a `ProofResponse` against the proposition it claims to settle. This is the component that turns an unverified result into a formal guarantee; the harness applies it to every racer, itself included.

---

## Usage

Include `aegis` in your `lakefile.lean` and import the required modules.

### Simple Prover Usage
For direct, non-competitive proof search:

```lean
import Aegis.Prover

open Lean Meta

/-- Basic execution of the universal prover. -/
def runProver (targetProp : Expr) : MetaM Unit := do
  -- A stop signal that is never set to true, so the search runs indefinitely.
  let stopSignal ← IO.mkRef false

  match ← Aegis.proveOrDisprove targetProp stopSignal with
  | some res => IO.println s!"Result found! Status: {res.status}"
  | none     => IO.println "Search halted."
```

### Applying Guarantees to AI (Harness Example)
This example demonstrates how to wrap a "dummy" AI prover in the Aegis Harness to provide it with formal termination guarantees.

```lean
import Aegis.Harness

open Lean Meta

/--
  A dummy AI prover. In a real scenario, this would call
  an external LLM or a non-deterministic heuristic or something without the same
  level of guarantee. Whatever it hands back is type-checked by the harness
  before it is allowed to win the race.
-/
def dummyAIProver (_p : Expr) (stopSignal : IO.Ref Bool) :
    MetaM (Option Aegis.ProofResponse) := do
  -- Simulate a non-deterministic delay or search
  IO.sleep 100
  -- If the AI is "beaten" by Aegis, it should respect the stopSignal
  if ← stopSignal.get then return none

  -- Return a result if found (here we return none for the dummy)
  return none

/-- Example of calling the harness to race Aegis vs the AI -/
def runHarnessExample (targetProp : Expr) : MetaM Unit := do
  match ← Aegis.harness targetProp dummyAIProver with
  | some res =>
      if res.status then
        IO.println "Formal Proof Found!"
      else
        IO.println "Formal Refutation Found!"
  | none =>
      IO.println "Every prover halted without a verified certificate."
```

---

## A note on cost

The search is exhaustive over the whole environment, so its branching factor is
the number of constants in scope. That is the price of the completeness and
optimality guarantees above, and it is why the harness exists: in practice you
race Aegis against something fast and keep Aegis as the anchor that cannot be
wrong.
