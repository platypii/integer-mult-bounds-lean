module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineClearBanks

/-! # One release program closes retained preparation and all generated table banks -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def release : Pr P 640 Q A U := .seq clearPrepared clearBanks

def releasedStack (S : Stacks 640 A) : Stacks 640 A :=
  { S with R := chirpBankFamilyClearR allBanks (clearPreparedR S.R) }

theorem clearPrepared_between (R : Regs 640 A) (k : Fin 640) (hk : 176 ≤ k.val ∧ k.val < 369) :
    clearPreparedR R k = R k := by
  apply ite_eq_right
  intro h
  have ho := prepareWrites_outside k h
  omega

/-- Preparation cleanup retains the source and consumer contents until their own release. -/
theorem release_exec (W w : ℕ) (z : TblSt 16 A) (hz : z.acc = [])
    (v : HS 640 Q A U) (S : Stacks 640 A)
    (hsrc : tblHolds source S (tblRho W (List.replicate W tick) (List.replicate w tick) z))
    (hbanks : ∀ b ∈ consumers, tblHolds b.rg S
      (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩)) :
    ∃ v', v'.user = v.user ∧
      Exec body release (mk v S) (clearPreparedCost S.R + (218 * W + 12 * w + 243)) (mk v' (releasedStack S)) ∧
      (∀ b ∈ allBanks, ∀ r, (releasedStack S).R (b.rg r) = []) ∧
      (∀ k ∈ prepareWrites, (releasedStack S).R k = []) := by
  obtain ⟨v₁, hu₁, he₁⟩ := clearPrepared_exec (body := body) v S
  let S₁ : Stacks 640 A := { S with R := clearPreparedR S.R }
  have hs₁ : tblHolds source S₁ (tblRho W (List.replicate W tick) (List.replicate w tick) z) := by
    intro r
    exact (clearPrepared_between S.R _ (bank_range (ForwardBankPlacement.source r))).trans (hsrc r)
  have hb₁ : ∀ b ∈ consumers, tblHolds b.rg S₁
      (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩) := by
    intro b hb r
    exact (clearPrepared_between S.R _ (consumer_range b hb r)).trans (hbanks b hb r)
  obtain ⟨v₂, hu₂, he₂, hz₂⟩ := clearBanks_exec (body := body) W w z hz v₁ S₁ hs₁ hb₁
  refine ⟨v₂, hu₂.trans hu₁, Exec.seq he₁ he₂, hz₂, ?_⟩
  intro k hk
  change chirpBankFamilyClearR allBanks (clearPreparedR S.R) k = []
  rw [chirpBankFamilyClearR_off allBanks _ k (by
    intro b hb r h
    have hr := allBanks_range b hb r
    have ho := prepareWrites_outside k hk
    have hv := congrArg Fin.val h
    omega)]
  exact ite_eq_left hk

/-- The initialized line retains every binary bank word until its release. -/
theorem lineResult_between (p q l Γ w t s α m M : ℕ) (SB : Stacks 640 A)
    (u : ZMod s → GaussianInt) (k : Fin 640) (hk : 176 ≤ k.val ∧ k.val < 369) :
    (lineResult p q l Γ w t s α m M SB u).R k = SB.R k := by
  have ho : k ≠ output.nr .out := by
    intro h
    have hv := congrArg Fin.val h
    have hn : (output.nr .out).val < 146 := (OutputPlacement.layout.nr .out).isLt
    omega
  have hw : k ∉ prepareWrites := by
    intro h
    have ho := prepareWrites_outside k h
    omega
  change Function.update (preparedStack p q l Γ w t s α m M SB).R (output.nr .out) _ k = SB.R k
  rw [Function.update_of_ne ho]
  exact preparedStack_off p q l Γ w t s α m M SB k hw

/-- The bank witness returned by initialized-line execution feeds the full release directly. -/
theorem release_lineResult_exec (W p q l Γ w t s α m M : ℕ) (z : TblSt 16 A) (hz : z.acc = [])
    (v : HS 640 Q A U) (SB : Stacks 640 A) (u : ZMod s → GaussianInt)
    (hsrc : tblHolds source SB (tblRho W (List.replicate W tick) (List.replicate w tick) z))
    (hbanks : ∀ b ∈ consumers, tblHolds b.rg SB
      (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩)) :
    let SL := lineResult p q l Γ w t s α m M SB u
    ∃ v', v'.user = v.user ∧
      Exec body release (mk v SL) (clearPreparedCost SL.R + (218 * W + 12 * w + 243))
        (mk v' (releasedStack SL)) ∧
      (∀ b ∈ allBanks, ∀ r, (releasedStack SL).R (b.rg r) = []) ∧
      (∀ k ∈ prepareWrites, (releasedStack SL).R k = []) := by
  apply release_exec (body := body) W w z hz v (lineResult p q l Γ w t s α m M SB u)
  · intro r
    exact (lineResult_between p q l Γ w t s α m M SB u _
      (bank_range (ForwardBankPlacement.source r))).trans (hsrc r)
  · intro b hb r
    exact (lineResult_between p q l Γ w t s α m M SB u _ (consumer_range b hb r)).trans (hbanks b hb r)

/-- Both phases preserve decoding of the actual returned tape. -/
theorem releasedStack_readOutput (p wo t : ℕ) (S : Stacks 640 A) :
    readOutput p wo t (releasedStack S) = readOutput p wo t S := by
  have hb := clearBanks_readOutput p wo t { S with R := clearPreparedR S.R }
  exact hb.trans (clearPrepared_readOutput p wo t S)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
