module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineCounters

/-! # Complete retained arithmetic preparation for the fixed forward line -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def prepare : Pr P 640 Q A U := .seq arithmeticSetup counters

/-- Arithmetic preparation retains every binary bank required by counter installation. -/
theorem arithmetic_bank (w q s t α m M Γ : ℕ) (R : Regs 640 A) (i : Fin 193) :
    tablesR w q s t α m M Γ (readinessR q w R) (bankTape i) = R (bankTape i) :=
  (tables_off _ _ _ _ _ _ _ _ _ _ (bank_ports i).1 (bank_ports i).2.1
    (bank_ports i).2.2.1 (bank_ports i).2.2.2).trans (readiness_bankTape q w R i)

/-- One executed setup generates readiness, all four coefficient streams and all nine output controls. -/
theorem prepare_exec (W w q s t α m M Γ B p l : ℕ) (hwW : w ≤ W)
    (hw1 : 1 ≤ w) (hroom : 4 * w + 2 < 2 ^ W)
    (hpq : p ≤ q) (hwidth : q + l + Γ + 5 ≤ w)
    (hcrop : t * (p + l + Γ + 5) < 2 ^ W)
    (size : ChirpTableSize W q B) (hΓq : Γ ≤ q) (hqΓ : 13 ≤ q - Γ)
    (hqW : q < W) (hαW : 2 * α < 2 ^ W) (hst : s ≤ t)
    (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hmB : m ≤ B)
    (hMB : M ≤ B) (hprod : M * m ≤ B) (hm0 : 1 ≤ m) (hshape : 4 * m + 1 ≤ B)
    (ht0 : 0 < t) (hα0 : 0 < α)
    (hgate : ∀ b < m, 4 * chirpEN s t b ≤ (q - Γ - 1) * chirpED t α)
    (st : TblSt 48 A) (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t)
    (hα : st.val 36 = α) (hm : st.val 45 = m) (hM : st.val 43 = M) (hΓ : st.val 46 = Γ)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0)
    (h37 : st.val 37 = 0) (h38 : st.val 38 = 0) (h42 : st.val 42 = 0) (h44 : st.val 44 = 0)
    (hfit : ∀ i, st.val i < 2 ^ W) (hacc : st.acc = [])
    (v : HS 640 Q A U) (S : Stacks 640 A)
    (hS : tblHolds coefficient S (tblRho W (List.replicate W tick) (List.replicate w tick) st))
    (hMulBank : tblHolds multiplier S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![q, w, 0, 0, 0], []⟩))
    (hDimBank : tblHolds dimensions S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![p, q, l, Γ, w, t, 0, 0, 0, 0, 0, 0, 0, 0], []⟩))
    (hDimFit : ∀ i : Fin 6, (![p, q, l, Γ, w, t] : Fin 6 → ℕ) i < 2 ^ W) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (3 * chirpMultiplierSetupCost W w q w +
        (chirpTableScheduleCost W w q m M false + chirpTableScheduleCost W w q m M true +
        chirpOutputFactorSetupCost W w q Γ m)) + countersCost W p q l Γ w t ∧
      Exec body prepare (mk v S) n (mk v' { S with R := countersR p q l Γ w t (tablesR w q s t α m M Γ (readinessR q w S.R)) }) := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := arithmeticSetup_exec (body := body)
    W w q s t α m M Γ B hwW hw1 hroom size hΓq hqΓ hqW hαW hst hsB htB hαB hmB hMB
    hprod hm0 hshape ht0 hα0 hgate st hq hs ht hα hm hM hΓ howned h37 h38 h42 h44 hfit hacc v S hS hMulBank
  let S₁ : Stacks 640 A := { S with R := tablesR w q s t α m M Γ (readinessR q w S.R) }
  have hb : tblHolds dimensions S₁ (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![p, q, l, Γ, w, t, 0, 0, 0, 0, 0, 0, 0, 0], []⟩) := by
    intro i
    exact (arithmetic_bank w q s t α m M Γ S.R (ForwardBankPlacement.output i)).trans (hDimBank i)
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := counters_exec (body := body) W p q l Γ w t hwW hpq hwidth hcrop
    hDimFit v₁ S₁ hb
  exact ⟨v₂, n₁ + n₂, hu₂.trans hu₁, Nat.add_le_add hn₁ hn₂, Exec.seq he₁ he₂⟩

private theorem outputBank_processor (i : Fin 22) (r : CR) : output.bank i ≠ processor r := by
  intro h
  have hb : (output.bank i).val < 146 := (OutputPlacement.layout.bank i).isLt
  have hp := processor_range r
  have hv := congrArg Fin.val h
  omega

private theorem outputBank_kernel (i : Fin 22) : output.bank i ≠ batch .srcY := by
  intro h
  have hb : (output.bank i).val < 146 := (OutputPlacement.layout.bank i).isLt
  have hv := congrArg Fin.val h
  simp only [batch, Function.comp_apply, productTape, Fixed.batchReg] at hv
  omega

/-- All output control/work tapes remain fresh until the last setup phase. -/
theorem arithmetic_outputBank (w q s t α m M Γ : ℕ) (R : Regs 640 A) (i : Fin 22) :
    tablesR w q s t α m M Γ (readinessR q w R) (output.bank i) = R (output.bank i) :=
  (tables_off _ _ _ _ _ _ _ _ _ _ (outputBank_processor i .ys) (outputBank_kernel i)
    (output.bank_cr i .ys) (output.bank_nr i .ys)).trans
    (readiness_off q w R _ (fun r _ => outputBank_processor i r)
      (fun r _ => output.bank_cr i r) (fun r _ => output.bank_nr i r))

/-- The complete executed preparation establishes every arithmetic and output-counter interface. -/
theorem prepare_state (p q l Γ w t s α m M : ℕ) (S : Stacks 640 A)
    (hproc : ∀ r, S.R (processor r) = [])
    (hcr : ∀ r, S.R (output.cr r) = []) (hnr : ∀ r, S.R (output.nr r) = [])
    (hclean : CClean output.mul S) (hK0 : S.R (batch .srcY) = [])
    (hbank : ∀ i, S.R (output.bank i) = []) :
    let S' : Stacks 640 A := { S with R := (countersR p q l Γ w t
      (tablesR w q s t α m M Γ (readinessR q w S.R))) }
    Ready (fun r => S'.R (processor r)) w q ∧
      S'.R (processor .ys) = chirpScheduledStream A w q s t α m M false ∧
      S'.R (batch .srcY) = chirpScheduledStream A w q s t α m M true ∧
      ChirpOutputState output S' q w [] (chirpOutputFactors s t α q Γ m) (chirpNormalization q α) ∧
      (∀ i, (S'.R (output.dim i)).length = chirpOutputDimensionCount p q l Γ w t i) ∧
      (∀ i : Fin 22, 9 ≤ i.val → S'.R (output.bank i) = []) := by
  let S₁ : Stacks 640 A := { S with R := tablesR w q s t α m M Γ (readinessR q w S.R) }
  have ha := arithmeticSetup_prepared w q s t α m M Γ S hproc hcr hnr hclean hK0
  have hwork (i : Fin 22) : S₁.R (output.bank i) = [] :=
    (arithmetic_outputBank w q s t α m M Γ S.R i).trans (hbank i)
  have hc := counters_prepared p q l Γ w t s α m S₁ ha.1 ha.2.2.2
    (fun i => hwork (Fin.castLE (by decide) i)) (fun i _ => hwork i)
  exact ⟨hc.1, (hc.2.1 .ys).trans ha.2.1, hc.2.2.1.trans ha.2.2.1,
    hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
