module

public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! A fresh private bank can contain only consumed input and growth of the
whole store. Spectator archives cancel rather than entering cleanup costs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main

theorem registerBankStock_le_of_consume_frame {N T Q A : ℕ} {U : Type}
    (bank : Fin N → Fin T) (hbank : Function.Injective bank) (source : Fin T)
    (hsource : ∀ i, bank i ≠ source) (v w : HS T Q A U) (S F : Stacks T A)
    (payload tail : List (Fin (A+4))) (budget : ℕ)
    (hblank : ∀ i, S.L (bank i) = [] ∧ S.R (bank i) = [])
    (hinput : F.inp = S.inp) (houtput : F.out = S.out)
    (hsourceL : F.L source = S.L source)
    (hsourceR : S.R source = payload++tail) (hfinal : F.R source = tail)
    (hframe : ∀ k, k ≠ source → (∀ i, bank i ≠ k) → F.L k = S.L k ∧ F.R k = S.R k)
    (hsize : mnSize (mk w F) ≤ mnSize (mk v S)+budget) :
    registerBankStock (embStk bank F) ≤ payload.length+budget := by
  classical
  let e : Option (Fin N) → Fin T := fun i => i.elim source bank
  have he : Function.Injective e := by
    intro x y hxy
    cases x with
    | none => cases y with
      | none => rfl
      | some j => exact False.elim (hsource j hxy.symm)
    | some i => cases y with
      | none => exact False.elim (hsource i hxy)
      | some j => exact congrArg some (hbank hxy)
  have hbalance := sum_replace_embedding e he
    (fun k => (F.L k).length+(F.R k).length)
    (fun k => (S.L k).length+(S.R k).length)
    (fun i => (F.L (e i)).length+(F.R (e i)).length) (fun _ => rfl) (by
      intro k hk
      have hnotSource : k ≠ source := by intro h; exact hk ⟨none,h.symm⟩
      have hnotBank : ∀ i, bank i ≠ k := by intro i h; exact hk ⟨some i,h⟩
      obtain ⟨hl,hr⟩ := hframe k hnotSource hnotBank
      rw [hl,hr])
  simp only [Fintype.sum_option,e,Option.elim_none,Option.elim_some,hsourceL,hsourceR,hfinal,
    List.length_append,(hblank _).1,(hblank _).2,List.length_nil,
    Finset.sum_const_zero,Nat.add_zero] at hbalance
  change registerBankStock F+((S.L source).length+(payload.length+tail.length)) =
    registerBankStock S+((S.L source).length+tail.length+registerBankStock (embStk bank F)) at hbalance
  rw [mnSize_mk_registerBankStock,mnSize_mk_registerBankStock,hinput,houtput] at hsize
  omega

end IntegerMultBounds.MathlibTM2.Host
