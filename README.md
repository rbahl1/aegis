# Aegis

**Aegis** is an exhaustive, concurrent formal verification suite for Lean 4. It acts as a wrapper to inject absolute formal guarantees into non-guaranteed AI-based formal applications.

The engine implements a semi-decidable procedure using iterative BFS deepening. By exhaustively searching the environment's space of proof terms, Aegis guarantees the discovery of the **globally optimal (shortest-depth) proof term** for a given proposition or its negation, provided such a term exists.

### The Prover: Exhaustive Search & Optimality
- **Semi-Decidability**: Implements a semi-decidable procedure. If a proof term exists of finite length (for the finite input statement), Aegis is guaranteed to find it, regardless of complexity.
- **Path Optimality**: The iterative deepening architecture ensures that the search space is explored layer-by-layer. The first proof discovered is mathematically guaranteed to be the shortest possible term (least depth).
- **Optimizations**: Simultaneously constructs and verifies both the proposition $P$ and its negation $\neg P$, allowing for definitive refutation as well as proof.

### The Harness: Termination & Guarantee Injection
- **Wrapping**: Allows non-deterministic AI models (which typically lack termination proofs) to inherit the semi-decidable bounds of the Aegis engine.
- **Formal Anchoring**: Provides a "ground truth" fallback. If an AI prover enters an infinite loop or fails to converge, the Aegis branch of the harness ensures the system still moves toward a best-possible deterministic guarantee, regardless of time.
- **Execution**: The harness has the same logical (guarantee-)strength as the prover.

---

## Features

### 1. The Prover (`Aegis.proveOrDisprove`)
The entry point for the universal search. A semi-decidable procedure that runs indefinitely until a proof or refutation is found, or an external stop signal is received. It trades computational speed for logical completeness.

### 2. The Harness (`Aegis.harness`)
The Harness is a **Wrapper with Guarantees**. It allows a non-deterministic AI prover (e.g., an LLM-based agent) to inherit the best-possible termination guarantees of a formal engine.

* **Formal Anchoring**: By racing an AI against Aegis, the AI system effectively gains a semi-decidable upper bound. This provides a termination guarantee that the AI hitherto lacked.
* **Concurrency**: Can have `IO.asTask` execute the AI and Aegis in parallel across CPU cores.
* **Best-possible prover (modulo finite-time) certification**: The harness is a `partial` function, ensuring it maintains the same formal strength as the underlying provers without artificial timeouts.

---

## Usage

Include `aegis` in your `lakefile.lean` and import the required modules.

### Simple Prover Usage
For direct, non-competitive proof search:

```lean
import Aegis.Prover

/-- Basic execution of the universal prover -/

partial def runProver (targetProp : Expr) : MetaM Unit := do
  -- Create a stop signal that is never set to true to run indefinitely
  let stopSignal ← IO.mkRef false
  
  match ← Aegis.proveOrDisprove targetProp stopSignal with
  | some res => IO.println s!"Result found! Status: {res.status}"
  | none     => IO.println "Search halted."
```

### Applying Guarantees to AI (Harness Example)
This example demonstrates how to wrap a "dummy" AI prover in the Aegis Harness to provide it with formal termination guarantees.

```lean
import Aegis.Harness
import Lean

open Lean Meta

/-- 
  A dummy AI prover. In a real scenario, this would call 
  an external LLM or a non-deterministic heuristic or something without same level of guarantee. 
-/

partial def dummyAIProver (p : Expr) (stopSignal : IO.Ref Bool) : MetaM (Option Aegis.ProofResponse) := do
  -- Simulate a non-deterministic delay or search
  IO.sleep 100 
  -- If the AI is "beaten" by Aegis, it should respect the stopSignal
  if ← stopSignal.get then return none
  
  -- Return a result if found (here we return none for the dummy)
  return none

/-- Example of calling the harness to race Aegis vs the AI -/

partial def runHarnessExample (targetProp : Expr) : MetaM Unit := do
  let result ← Aegis.harness targetProp dummyAIProver
  match result with
  | some res => 
      if res.status then
        IO.println "Formal Proof Found!"
      else
        IO.println "Formal Refutation Found!"
  | none => 
      IO.println "Search cancelled."
```
