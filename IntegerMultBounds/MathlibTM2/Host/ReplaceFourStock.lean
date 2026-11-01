module

public import IntegerMultBounds.MathlibTM2.Host.ReplaceThreeStock

/-! Extend the three-port storage balance by one independent replacement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type}

theorem mn_replace_four_size (a b c d : Fin T)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (v w : HS T Q A U) (S : Stacks T A) (xs ys zs us : List (Fin (A+4))) :
    mnSize (mk w {S with R := (Function.update (Function.update (Function.update
      (Function.update S.R a xs) b ys) c zs) d us)})+
      (S.R a).length+(S.R b).length+(S.R c).length+(S.R d).length =
      mnSize (mk v S)+xs.length+ys.length+zs.length+us.length := by
  let F : Stacks T A := {S with R := (Function.update (Function.update (Function.update S.R a xs) b ys) c zs)}
  have h₁ := mn_replace_three_size a b c hab hac hbc v v S xs ys zs
  have h₂ := mn_size_update (mk v F) w (.rt d) us
  have h₂' : mnSize (mk w {F with R := Function.update F.R d us})+(S.R d).length =
      mnSize (mk v F)+us.length := by
    simpa only [F,mk,update_rt,get_rt,Function.update_of_ne had.symm,
      Function.update_of_ne hbd.symm,Function.update_of_ne hcd.symm] using h₂
  change mnSize (mk v F)+(S.R a).length+(S.R b).length+(S.R c).length = _ at h₁
  change mnSize (mk w {F with R := Function.update F.R d us})+_+_+_+_ = _
  omega

end IntegerMultBounds.MathlibTM2.Host
