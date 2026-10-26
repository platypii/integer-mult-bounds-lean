module

public import IntegerMultBounds.NLogN.PhaseCellCoefficientPeriod

/-! Lift an ambient row and each retained signed offset to nonnegative
coordinates. The selected coefficient and wrapped source coordinate are exact. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRationalArgs

def couplingOffset (negative : Bool) (d : ℕ) : ℤ := if negative then -(d : ℤ) else d

def liftedSource (s band i : ℕ) : ℕ := i+band*s

def liftedTarget (negative : Bool) (s band i d : ℕ) : ℕ :=
  if negative then liftedSource s band i-d else liftedSource s band i+d

theorem offset_le_liftedSource {s band i d : ℕ} (hs : 0 < s) (hd : d ≤ band) :
    d ≤ liftedSource s band i := by
  have hb : band ≤ band*s := by nlinarith only [hs]
  dsimp only [liftedSource]
  omega

theorem liftedSource_cast (s band i : ℕ) :
    (liftedSource s band i : ℤ) = (i : ℤ)+(band : ℤ)*s := by
  simp [liftedSource]

theorem liftedTarget_cast {s band i d : ℕ} (negative : Bool) (hs : 0 < s) (hd : d ≤ band) :
    (liftedTarget negative s band i d : ℤ) =
      (i : ℤ)+(band : ℤ)*s+couplingOffset negative d := by
  cases negative
  · simp [liftedTarget,couplingOffset,liftedSource]
  · simp only [liftedTarget,Bool.true_eq_false,ite_true,couplingOffset,
      Nat.cast_sub (offset_le_liftedSource hs hd),liftedSource_cast]
    ring

theorem liftedTarget_le {s band i d : ℕ} (negative : Bool) (hd : d ≤ band) :
    liftedTarget negative s band i d ≤ i+band*s+band := by
  cases negative <;> simp only [liftedTarget,liftedSource,Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem liftedSource_zmod {s : ℕ} [NeZero s] (band i : ℕ) :
    (liftedSource s band i : ZMod s) = (i : ZMod s) := by
  simp [liftedSource]

theorem liftedTarget_zmod {s band i d : ℕ} [NeZero s] (negative : Bool) (hd : d ≤ band) :
    (liftedTarget negative s band i d : ZMod s) = (i : ZMod s)+(couplingOffset negative d : ZMod s) := by
  have hh := congrArg (fun z : ℤ => (z : ZMod s)) (liftedTarget_cast (i := i) negative (NeZero.pos s) hd)
  simpa using hh

theorem lifted_entry {s band i d : ℕ} (negative : Bool) (P t u : ℕ)
    (hs : 0 < s) (hd : d ≤ band) :
    PhaseCellCrossCell.entry P s t u band (liftedSource s band i) (liftedTarget negative s band i d) =
      PhaseCellCrossCell.entry P s t u band i ((i : ℤ)+couplingOffset negative d) := by
  rw [liftedSource_cast,liftedTarget_cast negative hs hd]
  rw [show (i : ℤ)+(band : ℤ)*s+couplingOffset negative d =
    ((i : ℤ)+couplingOffset negative d)+(band : ℤ)*s by ring]
  exact PhaseCellCrossCell.entry_period P s t u band hs i _ band

end IntegerMultBounds.NLogN.PhaseCellRationalArgs
