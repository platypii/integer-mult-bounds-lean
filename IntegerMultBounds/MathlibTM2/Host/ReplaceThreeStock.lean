module

public import IntegerMultBounds.MathlibTM2.Host.AppendRuns

/-! A three-port replacement has an exact storage balance, independent of data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type}

theorem mn_replace_three_size (a b c : Fin T) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v w : HS T Q A U) (S : Stacks T A) (xs ys zs : List (Fin (A+4))) :
    mnSize (mk w {S with R := (Function.update (Function.update (Function.update S.R a xs) b ys) c zs)})+
      (S.R a).length+(S.R b).length+(S.R c).length =
      mnSize (mk v S)+xs.length+ys.length+zs.length := by
  let F : Stacks T A := {S with R := Function.update S.R a xs}
  let G : Stacks T A := {F with R := Function.update F.R b ys}
  have h₁ : mnSize (mk v F)+(S.R a).length = mnSize (mk v S)+xs.length := by
    simpa only [F,mk,update_rt,get_rt] using mn_size_update (mk v S) v (.rt a) xs
  have h₂ : mnSize (mk v G)+(S.R b).length = mnSize (mk v F)+ys.length := by
    have h := mn_size_update (mk v F) v (.rt b) ys
    simpa only [G,F,mk,update_rt,get_rt,Function.update_of_ne hab.symm] using h
  have h₃ := mn_size_update (mk v G) w (.rt c) zs
  have h₃' :
      mnSize (mk w {S with R := (Function.update (Function.update (Function.update S.R a xs) b ys) c zs)})+
        (S.R c).length = mnSize (mk v G)+zs.length := by
    simpa only [G,F,mk,update_rt,get_rt,Function.update_of_ne hac.symm,
      Function.update_of_ne hbc.symm] using h₃
  omega

end IntegerMultBounds.MathlibTM2.Host
