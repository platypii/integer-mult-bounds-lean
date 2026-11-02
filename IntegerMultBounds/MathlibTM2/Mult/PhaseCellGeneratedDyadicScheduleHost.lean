module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedDyadicSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicScheduleFits
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableCountedPacketHost

/-! Compute, publish and release an exact dyadic schedule. The reader receives
the forward binary stream and a unary count of stages, with arbitrary tails. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def generatedDyadicScheduleHost : Pr P 117 Q A U :=
  tableCountedPacketHost 3 generatedDyadicScheduleCode

theorem generatedDyadicScheduleHost_exec {W a b C : ℕ} (st : TblSt 16 A)
    (ha : st.val 6 = a) (hb : st.val 7 = b) (hC : st.val 9 = C) (hacc : st.acc = [])
    (hbits : a+b < W) (hfit : C*2^(a+b) < 2^W)
    (hbound : ∀ j, st.val j < 2^W) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate W tick) st)) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (dyadicStageCount (a+b) a b*((a+b)*(4*(a+b)+19)+27)+13)*tblC W W+
        (10*dyadicStageCount (a+b) a b+73)*W+6*dyadicStageCount (a+b) a b+72 ∧
      Exec body generatedDyadicScheduleHost (mk v S) m
        (mk v' {S with R := fun r => if r.val < 31 then [] else if r = 109 then
          (dyadicScheduleValues (a+b) a b C).flatMap (binSyms W)++S.R 109 else if r = 116 then
          List.replicate (dyadicStageCount (a+b) a b) tick++S.R 116 else S.R r}) := by
  have hc := (generatedDyadicScheduleCode_do (W := W) (w := W) st ha hb hC hbits hfit).mono
    (P' := fun F => F.acc = ((dyadicScheduleValues (a+b) a b C).flatMap (fun x => tblPairs A W x 0)).reverse ∧
      F.val 3 = dyadicStageCount (a+b) a b)
    (fun F hF => ⟨by simpa only [hacc,List.append_nil] using hF.2.1,hF.1⟩) le_rfl
  have hr := tableCountedPacketHost_list_exec (body := body) 3
    (dyadicScheduleValues (a+b) a b C) generatedDyadicScheduleCode st hc hbound
    (dyadicScheduleValues_lt a b C W hbits hfit) hA v S hS
  simpa only [generatedDyadicScheduleHost,dyadicScheduleValues_length,←Nat.mul_assoc,Nat.reduceMul] using hr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
