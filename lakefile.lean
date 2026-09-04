import Lake
open Lake DSL

package aegis where

@[default_target]
lean_lib Aegis where

/-- Not a default target: the tests run real searches, so they cost real time.
    Run them with `lake build AegisTests`. -/
lean_lib AegisTests where
  roots := #[`Tests]
