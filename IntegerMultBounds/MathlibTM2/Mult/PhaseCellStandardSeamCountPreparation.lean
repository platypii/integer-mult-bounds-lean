module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardSeamWidenCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders

/-! Borrow an existing narrow crop count, then generate the replica-wide
widening count. Both original masters survive verbatim. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def standardSeamCountPreparation (cropCount : Fin 117) : Pr P 117 Q A U :=
  .seq (copyWordHeader cropCount 54 27 28) standardSeamWidenCount

theorem standardSeamCountPreparation_exec (cropCount : Fin 117)
    (hreg : [cropCount,15,54,19,27,28].Nodup) (N L w : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hN : (S.R 15).length = N) (hbits : (S.R cropCount).length = L*w)
    (hblank : S.R 54 = [] ∧ S.R 19 = [] ∧ S.R 27 = [] ∧ S.R 28 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (6*(L*w)+6)+(N*(4*(L*w)+9)+4) ∧
      Exec body (standardSeamCountPreparation cropCount) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 54 (S.R cropCount))
          19 (List.replicate (N*L*w) tick))}) := by
  obtain ⟨h54,h19,h27,h28⟩ := hblank
  have hr := hreg
  regs_ne hr
  obtain ⟨u,hu,hcopy⟩ := copyWordHeader_exec (body := body) cropCount 54 27 28
    (by regs_nodup) v S h27 h28
  simp only [h54,List.append_nil,hbits] at hcopy
  let M : Stacks 117 A := {S with R := Function.update S.R 54 (S.R cropCount)}
  obtain ⟨v',n,hv,hn,he⟩ := standardSeamWidenCount_exec (body := body) N L w u M
    (by simpa [M] using hN) (by simpa [M] using hbits)
    (by simpa [M] using h19) (by simpa [M] using h27)
    (by simpa [M] using h28)
  refine ⟨v',(6*(L*w)+6)+n,hv.trans hu,Nat.add_le_add_left hn _,?_⟩
  simpa only [standardSeamCountPreparation,M] using Exec.seq hcopy he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
