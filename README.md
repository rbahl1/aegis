# Aegis

**Aegis** is a brute-force Universal Prover/Disprover for Lean 4.

The engine implements a semi-decidable procedure using iterative deepening. By exhaustively searching the environment's space of proof terms in a breadth-first manner, Aegis guarantees the discovery of the lengthwise shortest proof term for a given proposition or its negation, as long as the proposition is of finite-length and the proof-term is also finite.

## Technical Specifications
- **Universal Search**: Constructs applications of the minimal Lean-4-Complete tactics and verifies then via the Lean 4 kernel.
- **Optimal Discovery**: Iterative deepening ensures that the first proof found is the shortest possible path.
- **Dual-Track**: Simultaneously evaluates the proposition and its refutation.

## Usage
Include `aegis` in your `lakefile.lean` and import Aegis.Prover. Here is an example:

```lean
import Aegis.Prover

#eval (do
  let result ← Aegis.proveOrDisprove someExpression
  IO.println s!"Status: {result.status}"
)
