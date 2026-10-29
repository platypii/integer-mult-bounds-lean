module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingHeaders

/-! Execute scalar-counter setup in the shared-header view. Only the three
private counter tapes change; retained dimension headers are read in place. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

def sharedCouplingCounters : Pr P₀ 168 Q A U :=
  embProg sharedCouplingCoreReg Empty.elim (couplingReadiness (P₀ := Empty))

def sharedCouplingCountersR {A : ℕ} (q w : ℕ) (R : Regs 168 A) : Regs 168 A :=
  Function.update (Function.update (Function.update R (sharedCouplingCoreReg (cr .wn)) (List.replicate w tick))
    (sharedCouplingCoreReg (cr .pn)) (List.replicate q tick))
    (sharedCouplingCoreReg (cr .nn)) (List.replicate (Schoenhage.Schedule.topN w) tick)

theorem sharedCouplingCoreReg_cr (r : CR) : sharedCouplingCoreReg (cr r) = packedCellCoreReg (cr r) := by
  have hr := cr_range r
  apply sharedCouplingReg_work
  · change (cr r).val < 97
    omega
  · intro he
    exact hr.2.2.2 (congrArg (fun k : Fin 168 => k.val) he)

theorem sharedCouplingCountersR_high {A : ℕ} (q w : ℕ) (R : Regs 168 A)
    (k : Fin 168) (hk : 97 ≤ k.val) : sharedCouplingCountersR q w R k = R k := by
  have hn (r : CR) : k ≠ sharedCouplingCoreReg (cr r) := by
    rw [sharedCouplingCoreReg_cr]
    intro he
    have hv := congrArg (fun j : Fin 168 => j.val) he
    have hr := cr_range r
    change k.val = (cr r).val at hv
    omega
  simp [sharedCouplingCountersR,hn]

theorem sharedCouplingCountersR_rhs {A : ℕ} (q w : ℕ) (R : Regs 168 A) :
    sharedCouplingCountersR q w R 93 = R 93 := by
  have hn (r : CR) : (93 : Fin 168) ≠ sharedCouplingCoreReg (cr r) := by
    rw [sharedCouplingCoreReg_cr]
    intro he
    exact (cr_range r).2.2.1 (congrArg (fun j : Fin 168 => j.val) he.symm)
  simp [sharedCouplingCountersR,hn]

theorem sharedCouplingCounters_exec {P q w s t u band a b : ℕ}
    (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (raw : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk sharedCouplingCoreReg S)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCost q w+6*q+4*band+10 ∧
      Exec body sharedCouplingCounters (mk v S) m
        (mk v' {S with R := sharedCouplingCountersR q w S.R}) ∧
      RetainedCouplingReady P q w s t u band a b raw
        (embStk sharedCouplingCoreReg {S with R := sharedCouplingCountersR q w S.R}) := by
  obtain ⟨vi,m,hui,hm,hei,hr⟩ := retainedCouplingCounters_exec
    (body := fun p : Empty => nomatch p) q w hw5 hqw raw
    (embDn sharedCouplingCoreReg v) (embStk sharedCouplingCoreReg S) hready
  obtain ⟨v',hv,hu,he⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    sharedCouplingCoreReg_injective (fun p => nomatch p) hei v rfl S rfl
  let B : Stacks 168 A := {S with R := sharedCouplingCountersR q w S.R}
  have hproj : embStk sharedCouplingCoreReg B =
      {embStk sharedCouplingCoreReg S with R := counterR q w (embStk sharedCouplingCoreReg S).R} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp [B,embStk,sharedCouplingCountersR,counterR,Function.update_apply,
      sharedCouplingCoreReg_injective.eq_iff]
  refine ⟨v',m,hu.trans hui,hm,he.cast rfl ?_,?_⟩
  · apply congrArg (mk v')
    change embOvr sharedCouplingCoreReg
      ({embStk sharedCouplingCoreReg S with R := counterR q w (embStk sharedCouplingCoreReg S).R} : Stacks 117 A).get S = B
    let T := embStk sharedCouplingCoreReg S
    let T₁ : Stacks 117 A := {T with R := Function.update T.R (cr .wn) (List.replicate w tick)}
    let T₂ : Stacks 117 A := {T₁ with R := Function.update T₁.R (cr .pn) (List.replicate q tick)}
    change embOvr sharedCouplingCoreReg
      ({T₂ with R := Function.update T₂.R (cr .nn) (List.replicate (Schoenhage.Schedule.topN w) tick)} : Stacks 117 A).get S = B
    rw [embOvr_updR sharedCouplingCoreReg_injective T₂]
    dsimp only [T₂]
    rw [embOvr_updR sharedCouplingCoreReg_injective T₁]
    dsimp only [T₁]
    rw [embOvr_updR sharedCouplingCoreReg_injective T,embOvr_stk]
    rfl
  · rw [hproj]
    exact hr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
