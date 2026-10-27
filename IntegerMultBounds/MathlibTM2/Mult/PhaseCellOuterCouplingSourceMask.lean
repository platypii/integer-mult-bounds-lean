module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedCouplingSourceMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace

/-! Run the closed geometry mask generator inside the retained outer register bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def outerCouplingSourceMask (boundary : Bool) : Pr P₀ 144 Q A U := embProg groupReg Empty.elim (closedCouplingSourceMask (P₀ := Empty) boundary)

theorem outerCouplingSourceMask_exec (boundary : Bool) {P q w s t u band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ closedCouplingSourceMaskCost s t band a b ∧
      Exec body (outerCouplingSourceMask boundary) (mk v S) n
        (mk v' {S with R := Function.update S.R 109 (couplingSourceMaskSymbols boundary A s t band a b)}) := by
  obtain ⟨v₁,n,hu₁,hn,he₁⟩ := closedCouplingSourceMask_exec boundary (body := fun p : Empty => nomatch p)
    (s := s) (t := t) (band := band) (a := a) (b := b)
    hst haS hbS hbandS (embDn groupReg v) (embStk groupReg S)
    hready.axis hready.period hready.bandwidth hready.lower hready.upper (hready.fresh 115 (by simp))
    (hready.fresh 106 (by simp)) (hready.fresh 108 (by simp))
    (fun r hr => hready.low r (by omega))
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    groupReg_injective (fun p => nomatch p) he₁ v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let B := embStk groupReg S
  rw [embOvr_updR groupReg_injective B S 109
    (couplingSourceMaskSymbols boundary A s t band a b++B.R 109),embOvr_stk]
  have h109 : S.R 109 = [] := by simpa [B,embStk,groupReg] using hready.fresh 109 (by simp)
  simp [B,embStk,groupReg,h109]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
