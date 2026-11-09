module

public import IntegerMultBounds.MathlibTM2.StackResources
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPacking

/-! Replacing an ambient bank by equally many equal-width rows preserves total
storage, independently of coefficients, control state and borrowed suffixes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A N : ℕ} {U : Type}

theorem mnSize_replace_right_eq (v v' : HS T Q A U) (S : Stacks T A) (dst : Fin T)
    (word : List (Fin (A+4))) (hlen : word.length = (S.R dst).length) :
    mnSize (mk v' {S with R := Function.update S.R dst word}) = mnSize (mk v S) := by
  have h := mn_size_update (mk v S) v' (.rt dst) word
  have hsize : mnSize (mk v' {S with R := Function.update S.R dst word})+(S.R dst).length =
      mnSize (mk v S)+word.length := by
    simpa only [mk,update_rt,get_rt] using h
  omega

theorem row_bank_replacement_stock (v v' : HS T Q A U) (S : Stacks T A) (dst : Fin T)
    (L : ℕ) (ambient : Fin N → List (Fin (A+4))) (lines : List (List (Fin (A+4))))
    (tail : List (Fin (A+4))) (hambient : ∀ j, (ambient j).length = L)
    (hcount : lines.length = N) (hlines : ∀ line ∈ lines, line.length = L)
    (hsrc : S.R dst = (List.ofFn ambient).flatten++tail) :
    mnSize (mk v' {S with R := Function.update S.R dst (lines.flatten++tail)}) = mnSize (mk v S) := by
  apply mnSize_replace_right_eq
  rw [hsrc,List.length_append,List.length_append,
    length_flatten_const lines hlines,hcount,
    length_flatten_const _ (by
      intro line hline
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hline
      exact hambient j),List.length_ofFn]

end IntegerMultBounds.MathlibTM2.Host
