module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineRelease

/-! # Restore arbitrary spectators across setup release -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node

/-- Release restores the original state whenever only owned setup registers differ. -/
theorem releasedStack_eq_of_frame (S SF : Stacks 640 A)
    (hinp : SF.inp = S.inp) (hout : SF.out = S.out) (hL : SF.L = S.L)
    (hframe : ∀ k, k ∉ prepareWrites → (∀ b ∈ allBanks, ∀ r, k ≠ b.rg r) → SF.R k = S.R k)
    (hbank0 : ∀ b ∈ allBanks, ∀ r, S.R (b.rg r) = [])
    (hwrite0 : ∀ k ∈ prepareWrites, S.R k = [])
    (hbank : ∀ b ∈ allBanks, ∀ r, (releasedStack SF).R (b.rg r) = [])
    (hwrite : ∀ k ∈ prepareWrites, (releasedStack SF).R k = []) : releasedStack SF = S := by
  classical
  ext1
  · exact hinp
  · exact hout
  · exact hL
  funext k
  by_cases hw : k ∈ prepareWrites
  · exact (hwrite k hw).trans (hwrite0 k hw).symm
  by_cases hb : ∃ b ∈ allBanks, ∃ r, b.rg r = k
  · obtain ⟨b, hmem, r, rfl⟩ := hb
    exact (hbank b hmem r).trans (hbank0 b hmem r).symm
  have hoff : ∀ b ∈ allBanks, ∀ r, k ≠ b.rg r := by
    intro b hmem r h
    exact hb ⟨b, hmem, r, h.symm⟩
  change chirpBankFamilyClearR allBanks (clearPreparedR SF.R) k = _
  rw [chirpBankFamilyClearR_off allBanks _ k hoff]
  exact (ite_eq_right hw).trans (hframe k hw hoff)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
