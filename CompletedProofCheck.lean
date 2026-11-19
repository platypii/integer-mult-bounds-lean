module

import IntegerMultBounds.MathlibTM2.Theorem
import Lean.Util.CollectAxioms

/-! Verify the completed proof without importing the all-components root or
the optional native-model bridge and integration examples. -/

example : IntegerMultBounds.MathlibTM2.Statement := IntegerMultBounds.MathlibTM2.statement

example : IntegerMultBounds.MathlibTM2.MulInTime (4223103985 / 2 ^ 46 : ℝ) :=
  IntegerMultBounds.MathlibTM2.mulInTime

/-- info: 'IntegerMultBounds.MathlibTM2.mulInTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.mulInTime

/-- info: 'IntegerMultBounds.MathlibTM2.statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms IntegerMultBounds.MathlibTM2.statement

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
  logInfo m!"Completed-proof axiom audit passed for {count} declarations."
