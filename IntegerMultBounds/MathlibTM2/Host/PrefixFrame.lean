module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! A prefix execution cannot write registers beyond its bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack

theorem embOvr_prefix_right {T T' A : ℕ} (h : T ≤ T')
    (B : Stacks T A) (S : Stacks T' A) (k : Fin T') (hk : T ≤ k.val) :
    (embOvr (Fin.castLE h) B.get S).R k = S.R k := by
  exact (embOvr_off B.get S (by
    intro i he
    have hv := congrArg (fun j : Fin T' => j.val) he
    have hi := i.isLt
    change i.val = k.val at hv
    omega)).2

end IntegerMultBounds.MathlibTM2.Host
