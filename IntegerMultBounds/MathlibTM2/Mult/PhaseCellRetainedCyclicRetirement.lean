module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicLayout
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Retire the generated selection controls and numerical byte ruler after a
batch. Erasure allocates no symbols and leaves every other role unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def controlWords : List (Fin tapes) := [geometry 91,geometry 109,geometry 116,caller.count]

theorem controlWords_nodup : controlWords.Nodup := by
  simp [controlWords,geometry,caller,selector,aux,port_injective.eq_iff,
    LocalRecoveryLayout.geometry_injective.eq_iff]

def retireControls : Pr P tapes Q A U := clearWords controlWords

def retiredControls (S : Stacks tapes A) : Stacks tapes A :=
  {S with R := fun r => if r ∈ controlWords then [] else S.R r}

def retireControlsCost (S : Stacks tapes A) : ℕ :=
  2*(controlWords.map (fun r => (S.R r).length)).sum+2*controlWords.length+1

theorem retiredControls_on (S : Stacks tapes A) {r : Fin tapes} (hr : r ∈ controlWords) :
    (retiredControls S).R r = [] := by simp only [retiredControls,hr,ite_true]

theorem retiredControls_off (S : Stacks tapes A) {r : Fin tapes} (hr : r ∉ controlWords) :
    (retiredControls S).R r = S.R r := by simp only [retiredControls,hr,ite_false]

theorem numeric_not_controlWords (i : Fin 909) : numeric i ∉ controlWords := by
  simp [controlWords,geometry,caller,selector,numeric,aux,port_injective.eq_iff]

theorem recovery_not_controlWords (i : RecoveryBank) :
    selector (LocalRecoveryLayout.recovery i) ∉ controlWords := by
  simp [controlWords,geometry,caller,selector,aux,port_injective.eq_iff,
    (LocalRecoveryLayout.geometry_ne_recovery _ _).symm]

theorem aux5_not_controlWords : aux 5 ∉ controlWords := by
  simp [controlWords,geometry,caller,selector,aux,port_injective.eq_iff]

theorem archive_not_controlWords : caller.archive ∉ controlWords := by
  simp [controlWords,geometry,caller,selector,aux,port_injective.eq_iff,
    LocalRecoveryLayout.source,LocalRecoveryLayout.geometry_injective.eq_iff]

theorem batch_not_controlWords (j : Fin 6) : selector (LocalRecoveryLayout.batch j) ∉ controlWords := by
  simp [controlWords,geometry,caller,selector,aux,port_injective.eq_iff,
    (LocalRecoveryLayout.geometry_ne_batch _ _).symm]

theorem retireControls_exec (v : HS tapes Q A U) (S : Stacks tapes A) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth) depth
        retireControls (mk v S) (retireControlsCost S) (mk v' (retiredControls S)) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) controlWords controlWords_nodup v S
  refine ⟨v',hu,?_⟩
  exact mn_native_exec_within he 0 (clearWords_native _) depth _ (by omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
