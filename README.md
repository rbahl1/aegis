# Aegis

**Aegis** is a formal verification suite for Lean 4. It has deciders(provers) and wrapper(s) to inject absolute formal guarantees into non-guaranteed AI-based formal applications.

The engine implements a semi-decidable procedure using iterative deepening. By exhaustively searching the environment's space of proof terms, Aegis guarantees the discovery of the **globally optimal (shortest) proof term** for a given proposition or its negation, provided such a term exists.

---

## Technical Specifications

### The Prover (`Aegis.proveOrDisprove`)
The entry point for the universal search. A semi-decidable procedure that runs indefinitely until a proof or refutation is found, or an external stop signal is received. It trades computational speed for logical completeness.

- **Semi-Decidability**: Implements a semi-decidable procedure. If a proof exists within the search space, Aegis is guaranteed to find it, regardless of complexity. The search space is every term reachable by `intro`, `assumption`, and application of any local hypothesis or any *admissible* non-internal constant in the environment -- universe-polymorphic constants included, each instantiated with fresh universe metavariables at every use site.
- **Admissible Vocabulary**: Lean's environment contains constants that close any goal in a single step: the compiler's unsafe `lcProof : ∀ {α : Prop}, α` and `lcUnreachable`, `sorryAx`, and trust axioms such as `Lean.trustCompiler : True`. They are excluded from the search, so the prover cannot derive `False` from them. `Aegis.admissibleConstant` defines the rule, and the checker applies the same one, so the two cannot disagree about what counts as a proof.
- **Solved-Goal Pruning**: Applying a constant unifies its conclusion with the goal, which can assign a *sibling* goal as a side effect -- closing `?h : ?w = 0` with `rfl` assigns the witness `?w := 0`. Such goals are pruned before recursing. Without that, the witness stays in the goal list where no tactic can touch it, and every witness-style proof is unreachable at any depth.
- **Path Optimality**: The iterative deepening architecture explores the search space layer by layer, one proof step at a time. The first certificate discovered is therefore guaranteed to be the shortest possible one. Branches are explored from their own metavariable state and the entry state is restored on failure, so a layer is a genuine set of alternatives rather than a single path.
- **Optimizations**: Constructs and verifies both the proposition $P$ and its negation $\neg P$, allowing for definitive refutation as well as proof.
- **No Artificial Ceiling**: The search runs with `maxHeartbeats := 0`. That limit exists to keep a runaway tactic from hanging an interactive session; here an unbounded search *is* the specification, so leaving it in place would have the prover abort rather than run until it finds a result.

### The Harness (`Aegis.harness`)
A **wrapper with guarantees**. It allows a non-deterministic AI prover (e.g., an LLM-based agent) to inherit the best-possible termination guarantees of a formal engine, and refuses to hand back anything the type checker has not confirmed. The race is the mechanism, not the point.

- **Wrapping**: Allows non-deterministic AI models (which typically lack termination proofs) to inherit the semi-decidable bounds of the Aegis engine.
- **Guarantee Injection**: The race alone would leave the harness no stronger than its weakest racer. What makes it stronger is `Aegis.checkResponse`: every certificate, whoever produced it, must be closed (no holes, no `sorry`) and must type-check against the proposition it claims to settle before it is allowed to win. An AI's answer is just an `Expr` until the type checker agrees with it.
- **Formal Anchoring**: Provides a "ground truth" fallback. If an AI prover loops forever, returns nothing, returns a bogus certificate, or crashes outright, it is simply dropped from the race and the Aegis branch keeps running -- the system still moves toward a best-possible deterministic guarantee, regardless of time.
- **Context Fidelity**: Racers are started from the caller's full `Core` and `Meta` state. The proposition is elaborated in the caller's local context and may mention its free variables, so a racer launched with an empty context would be searching for a proof of a different statement -- and could not close a goal from a hypothesis at all.
- **Concurrency**: Each racer is started with `IO.asTask` at `Task.Priority.dedicated`, so two unbounded searches run on their own threads in parallel rather than starving the shared task pool.
- **Cancellation**: Lean 4 cannot kill a running task from the outside, so the loser is stopped cooperatively via a shared `IO.Ref Bool`. Aegis polls that signal at every node of the search, not merely between depths -- a single depth level is itself unbounded, so a per-depth check would leave a cancelled search grinding for an arbitrarily long time.
- **Best-possible prover (modulo finite-time) certification**: The race loop is a `partial` function, so the harness inherits the semi-decidability of its racers instead of imposing an artificial timeout.

### The Checker (`Aegis.checkResponse`)
Re-verifies a `ProofResponse` against the proposition it claims to settle. This is the component that turns an unverified result into a formal guarantee; the harness applies it to every racer, itself included.

- **Closed Terms Only**: A certificate carrying holes or `sorry` is rejected, so an incomplete term cannot pass as a proof.
- **Actually Type-Checked**: Verification uses `Meta.check`, not `inferType`. `inferType` *assumes* its argument is type-correct -- it reads the pi type off the function and instantiates without ever looking at the argument -- so the ill-typed `@id False True.intro` "has type" `False` under it. That is precisely the certificate an adversarial prover would send.
- **Audited for Axioms**: `Aegis.auditCertificate` walks everything the term transitively depends on and rejects anything inadmissible. Type-checking alone cannot do this: `lcProof` is perfectly well-typed, and what disqualifies it is which constant it is. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
- **Matched Against the Goal**: The certificate's type must be defeq to $P$ for a proof or to $P \to \mathtt{False}$ for a refutation. Nothing else is accepted, whichever prover produced it.
- **Read-Only**: The check runs under `withoutModifyingState`. `isDefEq` assigns metavariables in order to succeed, and the proposition belongs to the caller, so without this a competitor answering `True.intro` for a proposition that still carries a hole would assign that hole to `True` and thereby make its own claim come true.

---

## Usage

Add Aegis to your `lakefile.lean`:

```lean
require aegis from git "https://github.com/rbahl1/aegis"
```

Then import what you need. `import Aegis` brings in the prover, the harness and
the checker; `import Aegis.Prover` alone is enough for the search.

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

These wrappers are ordinary `def`s. Lean's termination checking applies to a
definition's own recursion, not to what it calls, so a non-recursive caller of a
`partial` prover needs no `partial` of its own.

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

### Checking a Certificate From Anywhere (`Aegis.checkResponse`)
The checker stands alone. If you already have a term from some other prover, a
file, or a model response, you can hold it to the same standard without running
a search at all:

```lean
import Aegis.Prover

open Lean Meta

/-- Accept a term as settling `p`, or say why it cannot be accepted. -/
def vet (p : Expr) (candidate : Expr) : MetaM Unit := do
  if ← Aegis.checkResponse p ⟨true, candidate⟩ then
    IO.println "accepted: closed, type-checks, and rests only on trusted axioms"
  else
    IO.println "rejected"
```

Worked examples, all of which reject:

```lean
-- Ill-typed, but `inferType` would report its type as `False`.
#eval vet (mkConst ``False)
  (mkApp2 (mkConst ``id [levelZero]) (mkConst ``False) (mkConst ``True.intro))

-- Well-typed, but built from a compiler escape hatch.
#eval vet (mkConst ``False) (mkApp (mkConst ``lcUnreachable [levelZero]) (mkConst ``False))

-- Well-typed and axiom-free, but proves the wrong proposition.
#eval vet (mkConst ``False) (mkConst ``True.intro)
```

### Bounded Search Over a Chosen Vocabulary (`Aegis.universalSearch`)
`proveOrDisprove` runs forever over the whole environment. `universalSearch` is
the layer underneath: one bounded depth-first pass, over exactly the constants
you hand it. Use it when you want an answer within a step budget, or want to
know whether a proof of a given length exists:

```lean
import Aegis.Prover

open Lean Meta

/-- Is there a proof of `p` in at most `fuel` steps, using only `constants`? -/
def searchWithin (p : Expr) (fuel : Nat) (constants : Array Name) : MetaM Unit := do
  let stop ← IO.mkRef false
  let goal ← mkFreshExprMVar p
  match ← Aegis.universalSearch [goal.mvarId!] fuel goal.mvarId! constants stop with
  | some proof => IO.println s!"found in <= {fuel} steps: {← ppExpr proof}"
  | none       => IO.println s!"no proof within {fuel} steps"
```

Because the search is depth-optimal, a `none` at one budget and a hit at the
next is a statement about the shortest proof. For `∃ n : Nat, n = 0` with
`#[Exists.intro, rfl, OfNat.ofNat, instOfNatNat, Nat.zero]`, a budget of one
gives `none` and a budget of two gives `Exists.intro 0 rfl`, so that term is the
shortest proof over that vocabulary.

To search the full environment yourself, take the vocabulary from
`Aegis.getUniversalConstants`, which is the same admissible set `proveOrDisprove`
uses:

```lean
#eval show MetaM Unit from do
  searchWithin (mkConst ``True) 1 (← Aegis.getUniversalConstants)
```

### Auditing What a Term Rests On (`Aegis.auditCertificate`)
The audit is also usable on its own, against any term, whether or not it is a
proof of anything you care about:

```lean
import Aegis.Prover

open Lean Meta

#eval show MetaM Unit from do
  IO.println s!"trusted axioms: {Aegis.trustedAxioms}"
  -- false: rests on an unsafe compiler constant
  IO.println s!"{← Aegis.auditCertificate (mkApp (mkConst ``lcUnreachable [levelZero]) (mkConst ``False))}"
  -- false: `Lean.trustCompiler` is a trust escape hatch, not a foundation
  IO.println s!"{← Aegis.auditCertificate (mkConst ``Lean.trustCompiler)}"
  -- true: ordinary proof term
  IO.println s!"{← Aegis.auditCertificate (mkConst ``True.intro)}"
```

### Stopping a Search
Every entry point takes an `IO.Ref Bool`. Setting it to `true` from any thread
ends the search at the next node:

```lean
-- A signal that is already set: the search gives up at its first node.
#eval show MetaM Unit from do
  let result ← Aegis.proveOrDisprove (mkConst ``True) (← IO.mkRef true)
  IO.println s!"returned a certificate: {result.isSome}"
```

The same signal works across threads, which is how you impose a deadline on a
procedure that has none of its own:

```lean
/-- Run `p` for at most `ms` milliseconds. -/
def withDeadline (p : Expr) (ms : UInt32) : MetaM (Option Aegis.ProofResponse) := do
  let stop ← IO.mkRef false
  let timer ← IO.asTask (do IO.sleep ms; stop.set true) Task.Priority.dedicated
  let result ← Aegis.proveOrDisprove p stop
  let _ ← IO.wait timer
  return result
```

`Aegis.harness` owns its own signal and sets it for you when a racer wins, which
is the only way the loser ever stops: Lean cannot kill a running task from
outside.

---

## AI Integration Strategy

Aegis is meant to be the ground truth in a loop with an informal prover. That gives you three things:

- **Anchor**: Apply best-possible termination guarantees to a black-box AI model. The AI may loop forever or give up; the Aegis branch keeps going, so the pair is semi-decidable even when the AI alone is nothing of the kind.
- **Verify**: Every certificate is type-checked by `Aegis.checkResponse` against the proposition it claims to settle before the harness returns it. A model that hallucinates a proof loses the race rather than winning it with a term that does not check.
- **Optimize**: A certificate that Aegis itself produces is the shortest one in the search space, so it can replace a longer proof of the same proposition. Call the prover directly when that is what you want -- the harness returns whichever certificate arrives first, which is usually not the shortest.

---

## Project Structure

- `Aegis/Prover.lean`: iterative deepening, the search itself, and `checkResponse`.
- `Aegis/Harness.lean`: the race, its polling loop, and cooperative cancellation.
- `Aegis.lean`: library root, importing both.
- `Tests.lean`: the check suite. Kept out of the default target because the checks run real searches; run them with `lake build AegisTests`.

---

## A note on cost

The search is exhaustive over the whole environment, so its branching factor is
the number of constants in scope. That is the price of the completeness and
optimality guarantees above, and it is why the harness exists: in practice you
race Aegis against something fast and keep Aegis as the anchor that cannot be
wrong.
