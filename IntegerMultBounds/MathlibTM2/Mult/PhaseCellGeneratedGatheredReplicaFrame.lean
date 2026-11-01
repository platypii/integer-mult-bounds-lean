module

public import IntegerMultBounds.MathlibTM2.Host.RegisterFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedGatheredReplicaInteriorBatch

/-! The generated numerical caller accesses only its two placed banks.
Independent accumulated output is a spectator throughout the numerical phase. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem generatedPrefixHandoff_on_registers
    (cells rowCount width rows words src dst saved tmp : Fin T) (allowed : Fin T → Prop)
    (hoff : ∀ r ∈ [cells,rowCount,width,rows,words,src,dst,saved,tmp], allowed r) :
    programOn (registersOn allowed)
      (generatedPrefixHandoff (P := P) (Q := Q) (A := A) (U := U)
        cells rowCount width rows words src dst saved tmp) := by
  have hcells := hoff cells (by simp)
  have hrowCount := hoff rowCount (by simp)
  have hwidth := hoff width (by simp)
  have hrows := hoff rows (by simp)
  have hwords := hoff words (by simp)
  have hsrc := hoff src (by simp)
  have hdst := hoff dst (by simp)
  have hsaved := hoff saved (by simp)
  have htmp := hoff tmp (by simp)
  simp [generatedPrefixHandoff,unaryProduct,scanP,ucopy,umulSym,takePrefix,transfer,
    clearWords,uclear,moveR,scanR,keepIn,transferAct,drainR,popDo,whileR,
    moveStep,peekR,pushN,popPush,programOn,actionOn,registersOn,hcells,hrowCount,hwidth,hrows,hwords,hsrc,hdst,hsaved,htmp]

-- The unused right-only handoff wrapper can be restored from a2bf2c9e.

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type}

theorem generatedGatheredReplicaInteriorBatch_on_registers (plan : ReplicaInteriorPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (allowed : Fin T → Prop)
    (hg : ∀ i, allowed (plan.gather i)) (hs : ∀ i, allowed (plan.solver i)) :
    programOn (registersOn allowed)
      (generatedGatheredReplicaInteriorBatch (P := P) (A := A) (U := U) plan hR hQ) := by
  simp only [generatedGatheredReplicaInteriorBatch,gatheredReplicaInteriorBatch,
    gatheredReplicaInteriorPreparation,handedReplicaInteriorBatch,programOn]
  refine ⟨embProg_empty_on_registers _ Empty.elim allowed (fun i => hs (weightCacheCoreReg i)) _,
    ⟨⟨embProg_empty_on_registers _ Empty.elim allowed hs _,embProg_empty_on_registers _ Empty.elim allowed hg _⟩,
      ⟨?_,embProg_empty_on_registers _ Empty.elim allowed hs _⟩⟩⟩
  apply generatedPrefixHandoff_on_registers
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hg _ | exact hs _

theorem generatedGatheredReplicaInteriorBatch_avoids_right (plan : ReplicaInteriorPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (outside : Fin T)
    (hg : ∀ i, plan.gather i ≠ outside) (hs : ∀ i, plan.solver i ≠ outside) :
    programOn (fun k => k ≠ HK.rt outside)
      (generatedGatheredReplicaInteriorBatch (P := P) (A := A) (U := U) plan hR hQ) :=
  registersOn_avoids_right (generatedGatheredReplicaInteriorBatch_on_registers plan hR hQ (fun i => i ≠ outside) hg hs) outside (by simp)

theorem generatedGatheredReplicaInteriorBatch_preserves_right
    {body : P → Pr P T Q A U} (plan : ReplicaInteriorPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (outside : Fin T)
    (hg : ∀ i, plan.gather i ≠ outside) (hs : ∀ i, plan.solver i ≠ outside)
    {v v' : HS T Q A U} {S F : Stacks T A} {n : ℕ}
    (hex : Exec body (generatedGatheredReplicaInteriorBatch plan hR hQ) (mk v S) n (mk v' F)) :
    F.R outside = S.R outside :=
  hex.preserves_stack (HK.rt outside) (generatedGatheredReplicaInteriorBatch_avoids_right plan hR hQ outside hg hs)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
