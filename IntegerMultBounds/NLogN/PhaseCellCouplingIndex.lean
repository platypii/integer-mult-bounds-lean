module

public import IntegerMultBounds.NLogN.PhaseCellCouplingLift

/-! Physical source addresses for the original signed coupling offsets. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRationalArgs

def couplingIndex (negative : Bool) (s band i d : ℕ) : ℕ :=
  liftedTarget negative s band i d % s

theorem couplingIndex_lt (negative : Bool) {s band i d : ℕ} (hs : 0 < s) :
    couplingIndex negative s band i d < s := Nat.mod_lt _ hs

theorem couplingIndex_cast {s band i d : ℕ} [NeZero s] (negative : Bool) (hd : d ≤ band) :
    (couplingIndex negative s band i d : ZMod s) = (i : ZMod s)+(couplingOffset negative d : ZMod s) := by
  simpa [couplingIndex] using liftedTarget_zmod negative hd

end IntegerMultBounds.NLogN.PhaseCellRationalArgs
