module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorScalarWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth

/-! Generate factor multiplication counters, including topN, from the retained precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryFactorCounterR (q w : ℕ) (R : Regs 224 A) : Regs 224 A :=
  Function.update (Function.update (Function.update R 160 (List.replicate w tick))
    161 (List.replicate q tick)) 162 (List.replicate (Schoenhage.Schedule.topN w) tick)

def boundaryFactorCountersFromWidth : Pr P 224 Q A U :=
  embProg boundaryFactorScalarReg (fun x : Empty => nomatch x) (ScalarPlacement.prepare (P := Empty))

theorem boundaryFactorCountersFromWidth_exec (q w : ℕ) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hq : (S.R 119).length = q) (hwidth : (S.R 223).length = w)
    (hclean : ∀ i : Fin 224, i.val < 26 → S.R i = [])
    (hcounters : S.R 160 = [] ∧ S.R 161 = [] ∧ S.R 162 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ ScalarPlacement.prepareCost q w ∧
      Exec body boundaryFactorCountersFromWidth (mk v S) m
        (mk v' {S with R := boundaryFactorCounterR q w S.R}) := by
  let E := embStk boundaryFactorScalarReg S
  obtain ⟨v₁,m,hu,hm,he⟩ := ScalarPlacement.prepare_exec_of_width
    (P := Empty) (body := fun x => nomatch x) q w hw5 hqw (embDn boundaryFactorScalarReg v) E
    (by simpa [E,embStk,boundaryFactorScalarReg_precision] using hq)
    (by simpa [E,embStk,boundaryFactorScalarReg_width] using hwidth)
    (by
      intro i hi
      apply hclean (boundaryFactorScalarReg i)
      rw [boundaryFactorScalarReg_low i hi]
      exact hi)
    (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simpa [E,embStk,boundaryFactorScalarReg_cm,boundaryFactorReg] using hcounters.1
      · simpa [E,embStk,boundaryFactorScalarReg_cm,boundaryFactorReg] using hcounters.2.1
      · simpa [E,embStk,boundaryFactorScalarReg_cm,boundaryFactorReg] using hcounters.2.2)
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := fun x : Empty => nomatch x) (body' := body)
    boundaryFactorScalarReg_injective (by intro x; cases x) he v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let E₁ : Stacks 117 A := {E with R := Function.update E.R (ScalarPlacement.cr .wn) (List.replicate w tick)}
  let E₂ : Stacks 117 A := {E₁ with R := Function.update E₁.R (ScalarPlacement.cr .pn) (List.replicate q tick)}
  change embOvr boundaryFactorScalarReg {E₂ with R := (Function.update E₂.R (ScalarPlacement.cr .nn)
    (List.replicate (Schoenhage.Schedule.topN w) tick))}.get S = _
  rw [embOvr_updR boundaryFactorScalarReg_injective E₂ S]
  dsimp only [E₂]
  rw [embOvr_updR boundaryFactorScalarReg_injective E₁ S]
  dsimp only [E₁]
  rw [embOvr_updR boundaryFactorScalarReg_injective E S]
  simp only [E,embOvr_stk,boundaryFactorScalarReg_cm,boundaryFactorReg,boundaryFactorCounterR]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
