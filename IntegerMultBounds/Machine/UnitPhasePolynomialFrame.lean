import IntegerMultBounds.Machine.UnitPhasePolynomialLoop

/-! Polynomial iteration changes only the physical input/output streams.
All immutable phase descriptors, raw addresses, counters and caller metadata
are retained exactly until the paid once-per-address cleanup. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialFrame
noncomputable section
open UnitPhasePolynomialLoop (state flagsAt coreBlank)
open DelimitedRadixRecord (Context)

theorem frame (v : Tapes 60 2) (ctx : ℕ → Context 2) (p : Fin 4)
    (hflags : flagsAt v p) (hcore : coreBlank v) (i : Fin 60)
    (hi : i≠56 ∧ i≠58) (n : ℕ) :
    (state v ctx p n).head i=v.head i ∧ (state v ctx p n).tape i=v.tape i := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [state,UnitPhaseSharedCoefficient.output_eq _ _ _
      (UnitPhasePolynomialLoop.state_flags v ctx p hflags n)
      (UnitPhasePolynomialLoop.state_core v ctx p hcore n)]
    simpa only [UnitPhaseSharedCoefficient.streamOutput,SharedPlacementAlphabet.setTape,
      Function.update_apply,hi.1,hi.2,ite_false] using ih

end
end IntegerMultBounds.Machine.UnitPhasePolynomialFrame
