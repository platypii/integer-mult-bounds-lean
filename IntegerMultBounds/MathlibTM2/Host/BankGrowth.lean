module

public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock

/-! Replacing an injectively placed right bank accounts exactly for its word volume.
This avoids enumerating the concrete bank when extracting packet-size bounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {N T Q A : ℕ} {U : Type}

/-- Replacing an arbitrary owned bank changes stock by exactly its word-volume difference. -/
theorem mn_replace_bank_size (work : Fin N → Fin T) (hwork : Function.Injective work)
    (v w : HS T Q A U) (S F : Stacks T A) (words : Fin N → List (Fin (A+4)))
    (hwords : ∀ i, F.R (work i) = words i)
    (hframe : ∀ k, (∀ i, work i ≠ k) → F.R k = S.R k)
    (hin : F.inp = S.inp) (hout : F.out = S.out) (hleft : F.L = S.L) :
    mnSize (mk w F)+(∑ i, (S.R (work i)).length) = mnSize (mk v S)+(∑ i, (words i).length) := by
  have hsum := sum_replace_embedding work hwork (fun k => (F.R k).length) (fun k => (S.R k).length)
    (fun i => (words i).length) (by intro i; rw [hwords]) (by
      intro k hk
      rw [hframe k (by simpa only [not_exists] using hk)])
  rw [mnSize_mk_registerBankStock,mnSize_mk_registerBankStock,hin,hout]
  simp only [registerBankStock,Finset.sum_add_distrib,hleft]
  omega

theorem mn_fill_bank_size (work : Fin N → Fin T) (hwork : Function.Injective work)
    (v w : HS T Q A U) (S F : Stacks T A) (words : Fin N → List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hwords : ∀ i, F.R (work i) = words i)
    (hframe : ∀ k, (∀ i, work i ≠ k) → F.R k = S.R k)
    (hin : F.inp = S.inp) (hout : F.out = S.out) (hleft : F.L = S.L) :
    mnSize (mk w F) = mnSize (mk v S)+(∑ i, (words i).length) := by
  have h := mn_replace_bank_size work hwork v w S F words hwords hframe hin hout hleft
  simpa only [hblank,List.length_nil,Finset.sum_const_zero,Nat.add_zero] using h

end IntegerMultBounds.MathlibTM2.Host
