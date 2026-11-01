module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedInitializeCouplingMasks

/-! Retire shared coupling masks once after the replica traversal. Clearing
consumes only the cache streams and restores the empty-cache caller interface. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retireCouplingMasks (e : Fin 168 → Fin T) : Pr P T Q A U :=
  .seq (uclear (e 159)) (uclear (e 161))

def retiredCouplingMasksState (e : Fin 168 → Fin T) (S : Stacks T A) : Stacks T A :=
  {S with R := Function.update (Function.update S.R (e 159) []) (e 161) []}

theorem retireCouplingMasks_exec (e : Fin 168 → Fin T) (he : Function.Injective e)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (retireCouplingMasks e) (mk v S)
        ((2*(S.R (e 159)).length+2)+(2*(S.R (e 161)).length+2))
        (mk v' (retiredCouplingMasksState e S)) := by
  have hne : e 161 ≠ e 159 := he.ne (by decide)
  obtain ⟨v₁,hu₁,hex₁⟩ := uclear_exec body (e 159) v S
  obtain ⟨v₂,hu₂,hex₂⟩ := uclear_exec body (e 161) v₁ {S with R := Function.update S.R (e 159) []}
  refine ⟨v₂,hu₂.trans hu₁,?_⟩
  exact .seq hex₁ (by simpa only [retiredCouplingMasksState,Function.update_of_ne hne] using hex₂)

theorem retireCouplingMasks_native (e : Fin 168 → Fin T) :
    mnNativePushBound 0 (retireCouplingMasks (P := P) (Q := Q) (A := A) (U := U) e) := by
  simp [retireCouplingMasks,uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem retireCouplingMasks_exec_within (e : Fin 168 → Fin T) (he : Function.Injective e)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧ ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth) depth
        (retireCouplingMasks e) (mk v S)
        ((2*(S.R (e 159)).length+2)+(2*(S.R (e 161)).length+2))
        (mk v' (retiredCouplingMasksState e S)) := by
  obtain ⟨v',hu,hex⟩ := retireCouplingMasks_exec (body := body) e he v S
  refine ⟨v',hu,?_⟩
  intro depth
  simpa using mn_native_exec_within hex 0 (retireCouplingMasks_native e) depth _ (by omega)

theorem retiredCouplingMasksState_frame (e : Fin 168 → Fin T) (S : Stacks T A)
    (k : Fin T) (h159 : k ≠ e 159) (h161 : k ≠ e 161) :
    (retiredCouplingMasksState e S).R k = S.R k := by
  simp [retiredCouplingMasksState,h159,h161]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
