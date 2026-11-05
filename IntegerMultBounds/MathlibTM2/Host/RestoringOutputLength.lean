module

public import IntegerMultBounds.MathlibTM2.Host.RestoringSequence

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type}

/-- For an output-only frame, equality of live stock certifies equality of
output lengths. Prove this before instantiating a large concrete caller bank. -/
theorem mn_replace_right_length_of_size (v w : HS T Q A U) (S : Stacks T A)
    (output : Fin T) (ys : List (Fin (A+4)))
    (hsize : mnSize (mk w {S with R := Function.update S.R output ys}) = mnSize (mk v S)) :
    ys.length = (S.R output).length := by
  have hbalance : mnSize (mk w {S with R := Function.update S.R output ys})+(S.R output).length =
      mnSize (mk v S)+ys.length := by
    simpa only [mk,update_rt,get_rt] using mn_size_update (mk v S) w (.rt output) ys
  rw [hsize] at hbalance
  omega

end IntegerMultBounds.MathlibTM2.Host
