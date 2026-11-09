module

public import IntegerMultBounds.MathlibTM2.StackResources
public import IntegerMultBounds.MathlibTM2.Host.Core

/-! Consuming a cursor and retaining a packet grows stock only by the packet length. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type}

theorem mn_tail_prepend_size_le (cursor dst : Fin T) (hne : cursor ≠ dst)
    (v vf : HS T Q A U) (S : Stacks T A) (words : List (Fin (A+4))) :
    mnSize (mk vf {S with R := (Function.update
      (Function.update S.R cursor (S.R cursor).tail) dst (words++S.R dst))}) ≤
      mnSize (mk v S)+words.length := by
  let D : Stacks T A := {S with R := Function.update S.R cursor (S.R cursor).tail}
  have hd : mnSize (mk v D)+(S.R cursor).length = mnSize (mk v S)+(S.R cursor).tail.length := by
    simpa only [D,mk,update_rt,get_rt] using mn_size_update (mk v S) v (.rt cursor) (S.R cursor).tail
  have hw : mnSize (mk vf {D with R := Function.update D.R dst (words++S.R dst)})+(D.R dst).length =
      mnSize (mk v D)+(words++S.R dst).length := by
    simpa only [mk,update_rt,get_rt] using mn_size_update (mk v D) vf (.rt dst) (words++S.R dst)
  have hdst : D.R dst = S.R dst := by simp [D,hne.symm]
  rw [hdst,List.length_append] at hw
  have htail : (S.R cursor).tail.length ≤ (S.R cursor).length := by simp only [List.length_tail]; omega
  change mnSize (mk vf {D with R := Function.update D.R dst (words++S.R dst)}) ≤ _
  omega

end IntegerMultBounds.MathlibTM2.Host
