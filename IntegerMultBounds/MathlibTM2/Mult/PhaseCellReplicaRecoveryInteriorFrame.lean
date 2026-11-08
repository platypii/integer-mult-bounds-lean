module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryInteriorExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorFrame

/-! The second pass preserves every tape outside its gather/solver banks,
source and destination. In particular, saved boundary fields can stay in place. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type}

theorem replicaRecoveryInterior_on_registers (plan : ReplicaInteriorPlacement T)
    (source dst : Fin T) (allowed : Fin T → Prop) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hg : ∀ i, allowed (plan.gather i)) (hs : ∀ i, allowed (plan.solver i))
    (hsource : allowed source) (hdst : allowed dst) :
    programOn (registersOn allowed) (replicaRecoveryInterior (P := P) (A := A) (U := U) plan source dst hR hQ) := by
  refine ⟨?_,initializedReplicaHaloLoop_on_registers plan dst allowed hR hQ hg hs hdst,?_⟩
  · simp [reverseCopyRows,restoringRowScan,copyPrefix,copyR,copyStep,transfer,transferAct,
      scanP,scanR,drainR,popDo,keepIn,popPush,moveR,moveStep,whileR,peekR,
      programOn,actionOn,registersOn,hg,hsource]
  · simp [realReplicaHaloOutput,realReplicaRows,realPrefix,unaryProduct,transfer,transferAct,
      scanP,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,
      programOn,actionOn,registersOn,hg,hdst]

theorem replicaRecoveryInterior_preserves {body : P → Pr P T Q A U}
    (plan : ReplicaInteriorPlacement T) (source dst outside : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (hg : ∀ i, plan.gather i ≠ outside) (hs : ∀ i, plan.solver i ≠ outside)
    (hsource : source ≠ outside) (hdst : dst ≠ outside)
    {v v' : HS T Q A U} {S F : Stacks T A} {n : ℕ}
    (hex : Exec body (replicaRecoveryInterior plan source dst hR hQ) (mk v S) n (mk v' F)) :
    F.L outside = S.L outside ∧ F.R outside = S.R outside := by
  have h := replicaRecoveryInterior_on_registers (P := P) (A := A) (U := U)
    plan source dst (fun i => i ≠ outside) hR hQ hg hs hsource hdst
  exact ⟨hex.preserves_stack (HK.lt outside) (registersOn_avoids_left h outside (by simp)),
    hex.preserves_stack (HK.rt outside) (registersOn_avoids_right h outside (by simp))⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
