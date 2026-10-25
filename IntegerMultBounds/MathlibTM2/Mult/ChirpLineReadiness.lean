module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineControls
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputMultiplierSetup

/-! # Execute readiness setup for all three fixed-line multipliers

One retained five-variable bank is reused for the operand producer and both
output passes. Only the nine readiness counters change.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

theorem multiplier_inj : Function.Injective multiplier :=
  bankTape_inj.comp (ForwardBankPlacement.place_injective _ (by decide))

theorem bank_processor (i : Fin 193) (r : CR) : bankTape i ≠ processor r := by
  intro h
  have hb := bank_range i
  have hp := processor_range r
  have hv := congrArg Fin.val h
  omega

theorem bank_output (i : Fin 193) (r : CR) : bankTape i ≠ output.cr r ∧ bankTape i ≠ output.nr r := by
  have hb := bank_range i
  have hc : (output.cr r).val < 146 := (OutputPlacement.layout.cr r).isLt
  have hn : (output.nr r).val < 146 := (OutputPlacement.layout.nr r).isLt
  constructor <;> intro h <;> have hv := congrArg Fin.val h <;> omega

theorem multiplier_processor (i : TblR 5) (r : CR) : multiplier i ≠ processor r := bank_processor _ r

theorem processor_output (r s : CR) : processor r ≠ output.cr s ∧ processor r ≠ output.nr s := by
  have hp := processor_range r
  have hc : (output.cr s).val < 146 := (OutputPlacement.layout.cr s).isLt
  have hn : (output.nr s).val < 146 := (OutputPlacement.layout.nr s).isLt
  constructor <;> intro h <;> have hv := congrArg Fin.val h <;> omega

theorem multiplier_output (i : TblR 5) (r : CR) : multiplier i ≠ output.cr r ∧ multiplier i ≠ output.nr r := bank_output _ r

def readiness : Pr P 640 Q A U :=
  .seq (chirpMultiplierSetup multiplier processor) (chirpOutputMultiplierSetup output multiplier)

def readinessR (q w : ℕ) (R : Regs 640 A) : Regs 640 A :=
  chirpOutputMultiplierR output q w
    (unaryCopiesR (chirpMultiplierDimensionValues q w) R (chirpMultiplierAssignments processor))

/-- Compute every multiplier counter from the retained q,w words, restoring the binary bank. -/
theorem readiness_exec (W q w : ℕ) (hw : 1 ≤ w) (hwW : w ≤ W)
    (hroom : 4 * w + 2 < 2 ^ W) (hq : q < 2 ^ W)
    (v : HS 640 Q A U) (S : Stacks 640 A)
    (hS : tblHolds multiplier S (tblRho W (List.replicate W tick)
      (List.replicate w tick) ⟨![q, w, 0, 0, 0], []⟩)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 3 * chirpMultiplierSetupCost W w q w ∧
      Exec body readiness (mk v S) n (mk v' { S with R := readinessR q w S.R }) := by
  have hfit : ∀ i : Fin 5, (![q, w, 0, 0, 0] : Fin 5 → ℕ) i < 2 ^ W := by
    intro i
    fin_cases i <;> simp <;> omega
  have hzero : ∀ i : Fin 5, 2 ≤ i.val → (![q, w, 0, 0, 0] : Fin 5 → ℕ) i = 0 := by
    intro i hi
    fin_cases i <;> first | (simp at hi; done) | rfl
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpMultiplierSetup_exec (body := body) multiplier_inj processor
    (fun r _ i => multiplier_processor i r) (List.replicate W _) (List.replicate w _)
    (by simp) (by simp) hwW ⟨![q, w, 0, 0, 0], []⟩ q w rfl rfl hw hroom hzero hfit v S hS
  let S₁ : Stacks 640 A := { S with R :=
    (unaryCopiesR (chirpMultiplierDimensionValues q w) S.R (chirpMultiplierAssignments processor)) }
  have hb : tblHolds multiplier S₁ (tblRho W (List.replicate W tick)
      (List.replicate w tick) ⟨![q, w, 0, 0, 0], []⟩) := by
    intro i
    exact (chirpMultiplierSetup_off processor S.R q w _ (multiplier_processor i .wn)
      (multiplier_processor i .pn) (multiplier_processor i .nn)).trans (hS i)
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpOutputMultiplierSetup_exec (body := body) output multiplier multiplier_inj
    (fun r _ i => multiplier_output i r) (List.replicate W _) (List.replicate w _)
    (by simp) (by simp) hwW ⟨![q, w, 0, 0, 0], []⟩ q w rfl rfl hw hroom hzero hfit v₁ S₁ hb
  exact ⟨v₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

/-- The operand producer's register file is unchanged by the two subsequent output setups. -/
theorem readiness_processor (q w : ℕ) (R : Regs 640 A) (r : CR) :
    readinessR q w R (processor r) =
      unaryCopiesR (chirpMultiplierDimensionValues q w) R (chirpMultiplierAssignments processor) (processor r) := by
  unfold readinessR chirpOutputMultiplierR
  rw [chirpMultiplierSetup_off output.nr _ q w _ (processor_output r .wn).2
    (processor_output r .pn).2 (processor_output r .nn).2]
  exact chirpMultiplierSetup_off output.cr _ q w _ (processor_output r .wn).1
    (processor_output r .pn).1 (processor_output r .nn).1

/-- Fresh arithmetic banks imply actual Ready and output-base contracts after execution. -/
theorem readiness_ready (q w : ℕ) (S : Stacks 640 A)
    (hproc : ∀ r, r ≠ .xs → S.R (processor r) = [])
    (hcr : ∀ r, S.R (output.cr r) = []) (hnr : ∀ r, S.R (output.nr r) = [])
    (hclean : CClean output.mul S) :
    Ready (fun r => readinessR q w S.R (processor r)) w q ∧
      ChirpOutputBase output { S with R := readinessR q w S.R } q w [] := by
  let S₁ : Stacks 640 A := { S with R :=
    (unaryCopiesR (chirpMultiplierDimensionValues q w) S.R (chirpMultiplierAssignments processor)) }
  have hcr₁ (r : CR) : S₁.R (output.cr r) = S.R (output.cr r) :=
    chirpMultiplierSetup_off processor S.R q w _ (processor_output .wn r).1.symm
      (processor_output .pn r).1.symm (processor_output .nn r).1.symm
  have hnr₁ (r : CR) : S₁.R (output.nr r) = S.R (output.nr r) :=
    chirpMultiplierSetup_off processor S.R q w _ (processor_output .wn r).2.symm
      (processor_output .pn r).2.symm (processor_output .nn r).2.symm
  constructor
  · have hf := funext (readiness_processor q w S.R)
    rw [hf]
    exact chirpMultiplierSetup_ready processor processor_inj S.R q w hproc
  · exact chirpOutputMultiplierSetup_base output output_cross S₁ q w []
      (by simpa [cstream] using (hcr₁ .xs).trans (hcr .xs))
      (fun r _ => (hcr₁ r).trans (hcr r)) (fun r => (hnr₁ r).trans (hnr r))
      (fun i => ⟨(hclean i).1, (chirpMultiplierSetup_off processor S.R q w _
        (processor_mul .wn i).symm (processor_mul .pn i).symm (processor_mul .nn i).symm).trans (hclean i).2⟩)

/-- Exact frame for composing table generation and dimension installation after readiness. -/
theorem readiness_off (q w : ℕ) (R : Regs 640 A) (k : Fin 640)
    (hp : ∀ r ∈ [CR.wn, .pn, .nn], k ≠ processor r)
    (hc : ∀ r ∈ [CR.wn, .pn, .nn], k ≠ output.cr r)
    (hn : ∀ r ∈ [CR.wn, .pn, .nn], k ≠ output.nr r) :
    readinessR q w R k = R k := by
  unfold readinessR chirpOutputMultiplierR
  rw [chirpMultiplierSetup_off output.nr _ q w k (hn .wn (by simp))
    (hn .pn (by simp)) (hn .nn (by simp))]
  rw [chirpMultiplierSetup_off output.cr _ q w k (hc .wn (by simp))
    (hc .pn (by simp)) (hc .nn (by simp))]
  exact chirpMultiplierSetup_off processor _ q w k (hp .wn (by simp))
    (hp .pn (by simp)) (hp .nn (by simp))

/-- Readiness setup retains every table-bank tape, not only the multiplier source. -/
theorem readiness_bankTape (q w : ℕ) (R : Regs 640 A) (i : Fin 193) :
    readinessR q w R (bankTape i) = R (bankTape i) :=
  readiness_off q w R _ (fun r _ => bank_processor i r)
    (fun r _ => (bank_output i r).1) (fun r _ => (bank_output i r).2)

/-- The binary source of all three setups is retained with no changed slot. -/
theorem readiness_bank (q w : ℕ) (R : Regs 640 A) (i : TblR 5) :
    readinessR q w R (multiplier i) = R (multiplier i) :=
  readiness_off q w R _ (fun r _ => multiplier_processor i r)
    (fun r _ => (multiplier_output i r).1) (fun r _ => (multiplier_output i r).2)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
