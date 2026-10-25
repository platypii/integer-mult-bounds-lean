module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineRelease

/-! # Restore the original input state after the complete line and setup release -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node

/-- All non-output registers restore, including arbitrary spectators between allocated banks. -/
theorem released_lineResult_R (p q l Γ w t s α m M : ℕ) (S SB : Stacks 640 A)
    (u : ZMod s → GaussianInt)
    (hframe : ∀ k, (∀ r, k ≠ source r) → (∀ b ∈ consumers, ∀ r, k ≠ b.rg r) → SB.R k = S.R k)
    (hbank0 : ∀ b ∈ allBanks, ∀ r, S.R (b.rg r) = [])
    (hwrite0 : ∀ k ∈ prepareWrites, S.R k = [])
    (hbank : ∀ b ∈ allBanks, ∀ r, (releasedStack (lineResult p q l Γ w t s α m M SB u)).R (b.rg r) = [])
    (hwrite : ∀ k ∈ prepareWrites, (releasedStack (lineResult p q l Γ w t s α m M SB u)).R k = []) :
    (releasedStack (lineResult p q l Γ w t s α m M SB u)).R =
      Function.update S.R (output.nr .out)
        (cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u)) := by
  classical
  have hout : (releasedStack (lineResult p q l Γ w t s α m M SB u)).R (output.nr .out) =
      cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u) := by
    dsimp only [releasedStack]
    rw [clearBanks_output, clearPrepared_output]
    simp only [lineResult, Function.update_self]
  funext k
  by_cases ho : k = output.nr .out
  · subst k
    simpa only [Function.update_self] using hout
  by_cases hw : k ∈ prepareWrites
  · simpa only [Function.update_of_ne ho, hwrite0 k hw] using hwrite k hw
  by_cases hb : ∃ b ∈ allBanks, ∃ r, b.rg r = k
  · obtain ⟨b, hmem, r, rfl⟩ := hb
    simpa only [Function.update_of_ne ho, hbank0 b hmem r] using hbank b hmem r
  have hoff : ∀ b ∈ allBanks, ∀ r, k ≠ b.rg r := by
    intro b hmem r h
    exact hb ⟨b, hmem, r, h.symm⟩
  have hs : ∀ r, k ≠ source r := fun r => hoff ⟨16, source, id⟩ (by simp [allBanks]) r
  have hc : ∀ b ∈ consumers, ∀ r, k ≠ b.rg r :=
    fun b hmem => hoff b (List.mem_cons_of_mem _ hmem)
  change chirpBankFamilyClearR allBanks (clearPreparedR (lineResult p q l Γ w t s α m M SB u).R) k = _
  rw [chirpBankFamilyClearR_off allBanks _ k hoff]
  rw [show clearPreparedR (lineResult p q l Γ w t s α m M SB u).R k =
    (lineResult p q l Γ w t s α m M SB u).R k from ite_eq_right hw]
  change Function.update (preparedStack p q l Γ w t s α m M SB).R (output.nr .out) _ k = _
  rw [Function.update_of_ne ho, Function.update_of_ne ho, preparedStack_off p q l Γ w t s α m M SB k hw]
  exact hframe k hs hc

/-- The final native and left stacks restore along with every non-output right stack. -/
theorem released_lineResult_eq (p q l Γ w t s α m M : ℕ) (S SB : Stacks 640 A)
    (u : ZMod s → GaussianInt) (hinp : SB.inp = S.inp) (hout : SB.out = S.out) (hL : SB.L = S.L)
    (hframe : ∀ k, (∀ r, k ≠ source r) → (∀ b ∈ consumers, ∀ r, k ≠ b.rg r) → SB.R k = S.R k)
    (hbank0 : ∀ b ∈ allBanks, ∀ r, S.R (b.rg r) = [])
    (hwrite0 : ∀ k ∈ prepareWrites, S.R k = [])
    (hbank : ∀ b ∈ allBanks, ∀ r, (releasedStack (lineResult p q l Γ w t s α m M SB u)).R (b.rg r) = [])
    (hwrite : ∀ k ∈ prepareWrites, (releasedStack (lineResult p q l Γ w t s α m M SB u)).R k = []) :
    releasedStack (lineResult p q l Γ w t s α m M SB u) =
      { S with R := (Function.update S.R (output.nr .out)
        (cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u))) } := by
  ext1
  · exact hinp
  · exact hout
  · exact hL
  · exact released_lineResult_R p q l Γ w t s α m M S SB u hframe hbank0 hwrite0 hbank hwrite

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
