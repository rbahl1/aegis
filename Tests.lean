import Aegis

/-!
# Aegis test suite

Kept out of the default build target: these exercise the search itself, which is
exhaustive over the environment and therefore not free. Run them with

```
lake build AegisTests
```

A failing check throws, so the build fails rather than merely printing.
-/

open Lean Meta Elab

namespace Aegis.Tests

private def check (name : String) (act : MetaM Bool) : MetaM Unit := do
  let ok ← try act catch _ => pure false
  IO.println s!"{if ok then "PASS" else "FAIL"}  {name}"
  unless ok do throwError "Aegis test failed: {name}"

/-- Claims a refutation of the goal while handing back a proof of `True`. -/
private def liar (_ : Expr) (_ : IO.Ref Bool) : MetaM (Option ProofResponse) :=
  return some ⟨false, mkConst ``True.intro⟩

/-- Dies instead of answering. -/
private def crasher (_ : Expr) (_ : IO.Ref Bool) : MetaM (Option ProofResponse) :=
  throwError "boom"

/-- Never finds anything; halts only when the stop signal is set. -/
private partial def spinner (_ : Expr) (stop : IO.Ref Bool) : MetaM (Option ProofResponse) := do
  if ← stop.get then return none
  IO.sleep 5
  spinner (mkConst ``True) stop

/-- Instantly returns a genuine proof of `True`. -/
private def honest (_ : Expr) (_ : IO.Ref Bool) : MetaM (Option ProofResponse) :=
  return some ⟨true, mkConst ``True.intro⟩

-- Search: backtracking, applying local hypotheses, and depth optimality.
-- `fun P Q a => a` takes four steps (intro, intro, intro, assumption); the
-- search must find it at fuel 4 and must find nothing at fuel 3. Getting there
-- requires trying `assumption` on a goal that `intro` has already consumed,
-- which is only possible if each branch is explored from its own state.
#eval show TermElabM Unit from do
  let p ← Term.elabTerm (← `(∀ (P Q : Prop), (P → Q) → P → Q)) (some (mkSort levelZero))
  let stop ← IO.mkRef false
  check "search finds the 4-step proof of (P → Q) → P → Q" do
    let mv ← mkFreshExprMVar p
    match ← universalSearch [mv.mvarId!] 4 mv.mvarId! #[] stop with
    | some pf => checkResponse p ⟨true, pf⟩
    | none => return false
  check "search finds nothing at fuel 3, so fuel 4 really is optimal" do
    let mv ← mkFreshExprMVar p
    return (← universalSearch [mv.mvarId!] 3 mv.mvarId! #[] stop).isNone

-- Universe-polymorphic constants must be usable: `rfl` is `@rfl.{u}`, so it is
-- only applicable once instantiated with fresh universe metavariables.
#eval show TermElabM Unit from do
  let p ← Term.elabTerm (← `(∀ (n : Nat), n = n)) (some (mkSort levelZero))
  let stop ← IO.mkRef false
  check "search applies the universe-polymorphic `rfl`" do
    let mv ← mkFreshExprMVar p
    match ← universalSearch [mv.mvarId!] 2 mv.mvarId! #[``rfl] stop with
    | some pf => checkResponse p ⟨true, pf⟩
    | none => return false

-- The checker is what turns an unverified answer into a guarantee.
#eval show MetaM Unit from do
  check "checkResponse accepts a real proof of True" do
    checkResponse (mkConst ``True) ⟨true, mkConst ``True.intro⟩
  check "checkResponse rejects True.intro as a proof of False" do
    return !(← checkResponse (mkConst ``False) ⟨true, mkConst ``True.intro⟩)
  check "checkResponse rejects True.intro as a refutation of True" do
    return !(← checkResponse (mkConst ``True) ⟨false, mkConst ``True.intro⟩)
  check "checkResponse rejects a certificate containing a hole" do
    return !(← checkResponse (mkConst ``True) ⟨true, ← mkFreshExprMVar (mkConst ``True)⟩)

-- Cancellation, and the end-to-end guarantee under a hostile competitor.
#eval show MetaM Unit from do
  let tru := mkConst ``True
  check "a pre-set stop signal halts proveOrDisprove" do
    return (← proveOrDisprove tru (← IO.mkRef true)).isNone
  check "proveOrDisprove settles True against the full environment" do
    match ← proveOrDisprove tru (← IO.mkRef false) with
    | some res => checkResponse tru res
    | none => return false
  check "harness: an honest competitor wins with a verified certificate" do
    match ← harness tru honest with
    | some res => checkResponse tru res
    | none => return false
  check "harness: a lying competitor is rejected and Aegis still delivers" do
    match ← harness tru liar with
    | some res => checkResponse tru res
    | none => return false
  check "harness: a crashing competitor does not take the race down" do
    match ← harness tru crasher with
    | some res => checkResponse tru res
    | none => return false
  check "harness: a spinning competitor is stopped once Aegis wins" do
    match ← harness tru spinner with
    | some res => checkResponse tru res
    | none => return false

end Aegis.Tests
