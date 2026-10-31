module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationBatch
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Publication uses only native stream operations. Its linear movement bill
bounds every intermediate stock, including retained counters and spectators. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
variable {T Q A : ℕ} {P U : Type}

theorem replicaPublication_pushBound
    (clock padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T) :
    mnNativePushBound 2 (.seq
      (countedLoop clock (replicaPublicationStep (P := P) (Q := Q) (A := A) (U := U)
        padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved))
      (moveR outAcc dst id)) := by
  simp [replicaPublicationStep,retireCountedLine,transferCountedLine,scatterBatch,scatterLoopBody,
    scatterPacket,gatherRead,gatherReadStep,WordCmd.peekRp,discardPrefix,countedLoopBody,countedLoop,unaryProduct,scanP,ucopy,umulSym,
    transfer,moveR,uclear,keepIn,scanR,transferAct,drainR,popDo,whileR,moveStep,peekR,pushN,popPush,
    mnNativePushBound,mnActPush]

def replicaPublicationCost (N s missing L w : ℕ) :=
  N*(replicaPublicationStepCost s missing L w+3)+2+(2*(N*(s*w))+2)

theorem replicaPublicationCost_le (N s missing L w : ℕ) (hs : 1 ≤ s) (hw : 1 ≤ w) :
    replicaPublicationCost N s missing L w ≤ N*(21*(missing*L*w)+87*(s*w))+4 := by
  have hpad : (missing*L)*9 ≤ (missing*L)*w*9 := by
    have hh := Nat.mul_le_mul_left (missing*L) hw
    nlinarith only [hh]
  have hline : s*9 ≤ s*w*9 := by
    have hh := Nat.mul_le_mul_left s hw
    nlinarith only [hh]
  have hsw : 1 ≤ s*w := Nat.mul_pos hs hw
  have hstep : replicaPublicationStepCost s missing L w+3+2*(s*w) ≤
      21*(missing*L*w)+87*(s*w) := by
    dsimp only [replicaPublicationStepCost,retireCountedLineCost,transferCountedLineCost]
    nlinarith only [hpad,hline,hsw]
  have hh := Nat.mul_le_mul_left N hstep
  dsimp only [replicaPublicationCost]
  nlinarith only [hh]

theorem replicaPublication_within_stock {body : P → Pr P T Q A U}
    {clock padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T}
    {v v' : HS T Q A U} {S F : Stacks T A} {n N s missing L w : ℕ}
    (hex : Exec body (.seq
      (countedLoop clock (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved))
      (moveR outAcc dst id)) (mk v S) n (mk v' F))
    (hn : n ≤ replicaPublicationCost N s missing L w) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*replicaPublicationCost N s missing L w)
      depth (.seq
        (countedLoop clock (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved))
        (moveR outAcc dst id)) (mk v S) n (mk v' F) := by
  exact mn_native_exec_within hex 2 (replicaPublication_pushBound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
