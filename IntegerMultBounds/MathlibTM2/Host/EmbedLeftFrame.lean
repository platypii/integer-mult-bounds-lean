module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! A local left-stack frame lifts through a host-register embedding. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack

theorem embOvr_left_eq {T T' A : ℕ} (e : Fin T → Fin T') (he : Function.Injective e)
    (B : Stacks T A) (S : Stacks T' A) (hleft : B.L = (embStk e S).L) :
    (embOvr e B.get S).L = S.L := by
  classical
  funext k
  by_cases hk : ∃ i, e i = k
  · obtain ⟨i,rfl⟩ := hk
    exact (congrArg (fun F : Stacks T A => F.L i) (embStk_ovr he B S)).trans (congrFun hleft i)
  · exact (embOvr_off B.get S (by simpa only [not_exists] using hk)).1

end IntegerMultBounds.MathlibTM2.Host
