# Aegis

**Aegis** is a high-performance Universal Prover/Disprover for Lean 4.

The engine implements a semi-decidable procedure using iterative deepening. By exhaustively searching the environment's space of proof terms in a breadth-first manner, Aegis guarantees the discovery of the lengthwise shortest proof term for a given proposition or its negation.

## Technical Specifications
- **Universal Search**: Explores the global constant environment to construct valid proof terms.
- **Optimal Discovery**: Iterative deepening ensures that the first proof found is the shortest possible path.
- **Dual-Track**: Simultaneously evaluates the proposition and its refutation.

## Usage
Include `aegis` in your `lakefile.lean` and import:

```lean
import Aegis.Prover

#eval (do
  let result ← Aegis.proveOrDisprove someExpression
  IO.println s!"Status: {result.status}"
)
