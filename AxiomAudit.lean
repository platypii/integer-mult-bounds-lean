import IntegerMultBounds
import Lean.Util.CollectAxioms

/-! Reject unproved statements and custom axioms anywhere in our namespace. -/
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`IntegerMultBounds).isPrefixOf name ||
        name.toString.startsWith "_private.IntegerMultBounds." then
      for ax in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "{name} depends on unapproved axiom {ax}"
      count := count + 1
  logInfo m!"Axiom audit passed for {count} declarations."
