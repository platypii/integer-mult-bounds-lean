import IntegerMultBounds.Machine.ActivePrefixEarlySequenceSemantics

/-! The physical four-load coordinate map is the packed early arithmetic on
every address, with its actual address-dependent source controls. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequencePacked
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open ActivePrefixEarlySequenceSemantics

private theorem ignored_controls (sh : Gather.Shape) (xs zs ws : List Bool) (n : ℕ) :
    Gather.gather (fun x _ => x) sh xs zs n=Gather.gather (fun x _ => x) sh xs ws n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Gather.gather,ih,Gather.digitWord]

variable (s : Shape) (p : Parameters s) (offset : ℕ) {rows : ℕ}

theorem parity_offset (x : Address s p rows) :
    ActivePrefixCompactConjugationLayout.offsetValue .parity .before s p offset x=
      BinaryPackedEarlyData.parity p.q p.b p.n p.hb p.hbq x.target := by
  exact congrArg Counter.value (ignored_controls _ _ _ _ _)

theorem negative_offset (x : Address s p rows) :
    ActivePrefixCompactConjugationLayout.offsetValue .negative .before s p offset x=
      BinaryPackedEarlyData.negative p.q p.b p.n (ActivePrefixLayoutTarget.controls s p x offset)
        p.hb p.hbq x.target := rfl

def state (x : Address s p rows) : BinaryPackedEarlyData.State p.q p.b p.n Unit :=
  (x.target,x.t,())

/-- The original source word is unchanged by all four current-address loads,
so each subsequent offset uses the same selected controls. -/
theorem packed_state (x : Address s p rows) :
    state s p (destination s p offset x)=
      BinaryPackedEarlyData.run p.q p.b p.n (ActivePrefixLayoutTarget.controls s p x offset)
        p.hb p.hbq (state s p x) := by
  simp only [state,destination,correctionDestination,selectedDestination,
    ActivePrefixCompactConjugationLayout.destination,negative_offset,parity_offset]
  rfl

theorem destination_as_run (x : Address s p rows) :
    destination s p offset x=
      let y := BinaryPackedEarlyData.run p.q p.b p.n
        (ActivePrefixLayoutTarget.controls s p x offset) p.hb p.hbq (state s p x)
      {x with target := y.1,t := y.2.1} := by
  simp only [state,destination,correctionDestination,selectedDestination,
    ActivePrefixCompactConjugationLayout.destination,negative_offset,parity_offset]
  rfl

/-- This identifies the implemented payload schedule with the mathematical
packed arithmetic even on exceptional addresses; repair can use its inverse. -/
theorem packed_value (x : Address s p rows) :
    (((destination s p offset x).target.val : ℤ),((destination s p offset x).t.val : ℤ))=
      Compact.packedEarly ((2 : ℤ)^p.q) ((2 : ℤ)^p.b)
        ((ActivePrefixLayoutTarget.controls s p x offset).map Compact.PowerTwo.ctrl)
        x.target.val x.t.val := by
  have hlen : (ActivePrefixLayoutTarget.controls s p x offset).length=p.n :=
    SelectedSourceBitsData.selected_length _ _ _ _
  have h := BinaryPackedEarlyData.agrees p.q p.b p.n (ActivePrefixLayoutTarget.controls s p x offset)
    p.hb p.hbq hlen (state s p x)
  rw [←packed_state s p offset x] at h
  exact h

end
end IntegerMultBounds.Machine.ActivePrefixEarlySequencePacked
