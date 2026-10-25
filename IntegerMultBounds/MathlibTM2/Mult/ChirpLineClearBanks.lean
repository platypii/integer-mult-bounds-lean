module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankFamilyClear
public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineClearPrepared

/-! # Release all six fixed-line source/consumer banks -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def allBanks : List (ChirpBankTarget 16 640) := ⟨16, source, id⟩ :: consumers

theorem allBanks_inj : ∀ b ∈ allBanks, Function.Injective b.rg := by
  intro b hb
  rcases List.mem_cons.mp hb with he | hb
  · subst b; exact source_inj
  · exact consumers_inj b hb

theorem allBanks_pairwise : allBanks.Pairwise (fun b c => ∀ r s, b.rg r ≠ c.rg s) := by
  apply List.pairwise_cons.mpr
  exact ⟨fun b hb r s => (consumers_source b hb s r).symm, consumers_pairwise⟩

theorem allBanks_range (b : ChirpBankTarget 16 640) (hb : b ∈ allBanks) (r : TblR b.vars) :
    176 ≤ (b.rg r).val ∧ (b.rg r).val < 369 := by
  rcases List.mem_cons.mp hb with he | hb
  · subst b; exact bank_range (ForwardBankPlacement.source r)
  · exact consumer_range b hb r

def clearBanks : Pr P 640 Q A U := chirpBankFamilyClear allBanks

theorem clearBanks_cost (W w : ℕ) : chirpBankFamilyClearCost W w allBanks = 218 * W + 12 * w + 243 := by
  simp only [allBanks, consumers, ForwardBankPlacement.consumers, chirpForwardConsumers,
    List.map_cons, List.map_nil, liftConsumer, chirpBankFamilyClearCost]
  omega

/-- Clear every source/consumer variable and header, restoring all bank roles to empty. -/
theorem clearBanks_exec (W w : ℕ) (z : TblSt 16 A) (hz : z.acc = [])
    (v : HS 640 Q A U) (S : Stacks 640 A)
    (hsrc : tblHolds source S (tblRho W (List.replicate W tick) (List.replicate w tick) z))
    (hbanks : ∀ b ∈ consumers, tblHolds b.rg S
      (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩)) :
    ∃ v', v'.user = v.user ∧
      Exec body clearBanks (mk v S) (218 * W + 12 * w + 243)
        (mk v' { S with R := chirpBankFamilyClearR allBanks S.R }) ∧
      (∀ b ∈ allBanks, ∀ r, chirpBankFamilyClearR allBanks S.R (b.rg r) = []) := by
  have h : ∀ b ∈ allBanks, tblHolds b.rg S
      (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩) := by
    intro b hb
    rcases List.mem_cons.mp hb with he | hb
    · subst b
      have he : (⟨z.val, []⟩ : TblSt 16 A) = z := by cases z; simp_all
      change tblHolds source S (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨z.val, []⟩)
      rw [he]
      exact hsrc
    · exact hbanks b hb
  simpa only [clearBanks_cost, clearBanks] using chirpBankFamilyClear_exec (body := body)
    allBanks allBanks_inj allBanks_pairwise W w z.val v S h

/-- The full bank release keeps the returned output tape. -/
theorem clearBanks_output (R : Regs 640 A) :
    chirpBankFamilyClearR allBanks R (output.nr .out) = R (output.nr .out) := by
  apply chirpBankFamilyClearR_off
  intro b hb r h
  have hr := (allBanks_range b hb r).1
  have ho : (output.nr .out).val < 146 := (OutputPlacement.layout.nr .out).isLt
  have hv := congrArg Fin.val h
  omega

theorem clearBanks_readOutput (p wo t : ℕ) (S : Stacks 640 A) :
    readOutput p wo t { S with R := chirpBankFamilyClearR allBanks S.R } = readOutput p wo t S := by
  funext k
  dsimp only [readOutput]
  rw [clearBanks_output]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
