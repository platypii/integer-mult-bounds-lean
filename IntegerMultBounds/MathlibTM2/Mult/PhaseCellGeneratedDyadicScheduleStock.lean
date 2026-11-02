module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedDyadicScheduleHost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDyadicGeneratorBudget
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopiesStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! A paid intermediate-stock certificate for complete metadata generation,
including count export, publication and table release. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem tableCountedPacketHost_native (count : Fin 16) (code : TblCode 16) :
    mnNativePushBound 3 (tableCountedPacketHost (P₀ := P) (Q := Q) (A := A) (U := U) count code) := by
  refine ⟨tblCompile_native _ _,tblUnaryCopies_native _ _,?_,?_⟩
  · simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  · exact mnNativePushBound_mono (by decide : 0 ≤ 3) (clearWords_native originPorts)

theorem generatedDyadicScheduleHost_exec_within {W a b C : ℕ} (st : TblSt 16 A)
    (ha : st.val 6 = a) (hb : st.val 7 = b) (hC : st.val 9 = C) (hacc : st.acc = [])
    (hbits : a+b < W) (hfit : C*2^(a+b) < 2^W)
    (hbound : ∀ j, st.val j < 2^W) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate W tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 32921*(W+1)^5 ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+98763*(W+1)^5)
        depth generatedDyadicScheduleHost (Host.mk v S) m
        (Host.mk v' {S with R := (fun r => if r.val < 31 then [] else if r = 109 then
            (dyadicScheduleValues (a+b) a b C).flatMap (binSyms W)++S.R 109 else if r = 116 then
            List.replicate (dyadicStageCount (a+b) a b) tick++S.R 116 else S.R r)}) := by
  obtain ⟨v',m,hu,hm,he⟩ := generatedDyadicScheduleHost_exec (body := body) st ha hb hC hacc
    hbits hfit hbound hA v S hS
  have ht := hm.trans (Cost.dyadicGeneratorPublicationTime_le a b W hbits)
  refine ⟨v',m,hu,ht,?_⟩
  intro depth
  exact mn_native_exec_within he 3 (tableCountedPacketHost_native 3 generatedDyadicScheduleCode)
    depth _ (by nlinarith only [ht])

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
