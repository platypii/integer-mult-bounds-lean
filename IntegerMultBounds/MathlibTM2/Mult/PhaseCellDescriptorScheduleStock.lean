module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSchedule
public import IntegerMultBounds.MathlibTM2.StackResources

/-! At restored descriptor boundaries only output words increase live stock.
Moving packets to the saved tape does not allocate another retained copy. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main

variable {N T Q A : ℕ} {U : Type}

private theorem updateR_stock (v : HS T Q A U) (S : Stacks T A) (i : Fin T)
    (xs : List (Fin (A+4))) :
    mnSize (mk v {S with R := Function.update S.R i xs})+(S.R i).length =
      mnSize (mk v S)+xs.length := by
  simpa only [mk,update_rt,get_rt] using mn_size_update (mk v S) v (.rt i) xs

/-- Parking a consumed packet preserves its volume; only the result is new. -/
theorem dispatchedDescriptorState_stock (work : Fin N → Fin T)
    (words : Fin N → List (Fin (A+4))) (src saved result : Fin T)
    (hreg : [src,saved,result].Nodup) (rest output : List (Fin (A+4)))
    (v v' : HS T Q A U) (S : Stacks T A)
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work words)++rest) :
    mnSize (mk v' (dispatchedDescriptorState work words src saved result rest output S)) =
      mnSize (mk v S)+output.length := by
  have hr := hreg
  regs_ne hr
  have h₁ := updateR_stock v S src rest
  let S₁ : Stacks T A := {S with R := Function.update S.R src rest}
  let packet := descriptorBankTape (placedDescriptorFields work words)
  have h₂ := updateR_stock v S₁ saved (packet.reverse++S.R saved)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R saved (packet.reverse++S.R saved)}
  have h₃ := updateR_stock v S₂ result (output++S.R result)
  simp only [S₁,S₂,Function.update_of_ne ‹src ≠ saved›.symm,
    Function.update_of_ne ‹src ≠ result›.symm,Function.update_of_ne ‹saved ≠ result›.symm,
    List.length_append,List.length_reverse] at h₂ h₃
  have hs : (S.R src).length = packet.length+rest.length := by simp [packet,hsource]
  change mnSize (mk v {S with R := Function.update (Function.update (Function.update S.R src rest)
    saved (packet.reverse++S.R saved)) result (output++S.R result)}) = _
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
