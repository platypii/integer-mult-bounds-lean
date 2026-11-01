module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingCursor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingResidual

/-! A structural staging frame and residual endpoint determine the next cursor.
This language is independent of cached or table-evaluating numerical workers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T A : ℕ} [NeZero s]

structure ReplicaCouplingStageFrame {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (output rhs : Fin T) (S J : Stacks T A) : Prop where
  left : J.L = S.L
  input : J.inp = S.inp
  outStream : J.out = S.out
  right : ∀ k, k ∉ [output,rhs,placement.bank 132,placement.bank 93] → J.R k = S.R k

omit [NeZero s] in
theorem ReplicaCouplingStageFrame.bank_right {plan : ReplicaInteriorPlacement T}
    {placement : ReplicaCouplingPlacement plan} {output rhs : Fin T} {S J : Stacks T A}
    (h : ReplicaCouplingStageFrame placement output rhs S J)
    (houtput : ∀ i, placement.bank i ≠ output) (hrhs : ∀ i, placement.bank i ≠ rhs)
    (k : Fin 168) (h132 : k ≠ 132) (h93 : k ≠ 93) : J.R (placement.bank k) = S.R (placement.bank k) := by
  apply h.right
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨houtput k,hrhs k,placement.bank_injective.ne h132,placement.bank_injective.ne h93⟩

omit [NeZero s] in
theorem ReplicaCouplingStageFrame.ready {plan : ReplicaInteriorPlacement T}
    {placement : ReplicaCouplingPlacement plan} {output rhs : Fin T} {S J : Stacks T A}
    (h : ReplicaCouplingStageFrame placement output rhs S J)
    (houtput : ∀ i, placement.bank i ≠ output) (hrhs : ∀ i, placement.bank i ≠ rhs)
    {precision q w s t u band a b : ℕ} (raw : List (Fin (A+4)))
    (hready : RetainedCouplingReady precision q w s t u band a b raw
      (embStk weightCacheCoreReg (embStk plan.solver S))) :
    RetainedCouplingReady precision q w s t u band a b raw
      (embStk weightCacheCoreReg (embStk plan.solver J)) := by
  apply hready.of_frame (S' := embStk weightCacheCoreReg (embStk plan.solver J))
  · exact congrArg (fun L => L ∘ plan.solver ∘ weightCacheCoreReg) h.left
  · intro k h93 _ _
    change J.R (plan.solver (weightCacheCoreReg k)) = S.R (plan.solver (weightCacheCoreReg k))
    rw [←placement.bank_native k]
    apply h.bank_right houtput hrhs
    · intro hh
      have hv : k.val = 132 := congrArg Fin.val hh
      have hk := k.isLt
      omega
    · intro hh
      exact h93 (Fin.ext (congrArg (fun j : Fin 168 => j.val) hh))

omit [NeZero s] in
theorem ReplicaCouplingStageFrame.geometry {plan : ReplicaInteriorPlacement T}
    {placement : ReplicaCouplingPlacement plan} {output rhs : Fin T} {S J : Stacks T A}
    (h : ReplicaCouplingStageFrame placement output rhs S J)
    (houtput : ∀ i, placement.bank i ≠ output) (hrhs : ∀ i, placement.bank i ≠ rhs)
    {V s t band a b origin N : ℕ}
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N (embStk placement.bank S)) :
    CouplingIntervalMetadata V s t band a b origin N (embStk placement.bank J) := by
  apply hgeometry.of_frame (h.bank_right houtput hrhs 163 (by decide) (by decide))
  intro k hk
  apply h.bank_right houtput hrhs
  all_goals simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
  all_goals rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

omit [NeZero s] in
theorem ReplicaCouplingStageFrame.finish_residual (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} {placement : ReplicaCouplingPlacement plan}
    {output rhs dst : Fin T} {S J : Stacks T A}
    (h : ReplicaCouplingStageFrame placement output rhs S J)
    (houtput : ∀ i, placement.bank i ≠ output) (hrhs : ∀ i, placement.bank i ≠ rhs)
    (hdst : ∀ i, placement.bank i ≠ dst) (houtdst : output ≠ dst) (hrhsdst : rhs ≠ dst)
    (outputTail rhsTail ys : List (Fin (A+4))) (r : ℕ)
    (hcursor : ReplicaCouplingCursor H output rhs outputTail rhsTail (r+1) J) :
    let F := replicaResidualState placement dst (S.R (placement.bank 132)) (S.R (placement.bank 93)) ys J
    ReplicaCouplingCursor H output rhs outputTail rhsTail (r+1) F ∧
      F.R dst = ys++S.R dst ∧ embStk placement.bank F = embStk placement.bank S ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ∉ [output,rhs,dst] → F.R k = S.R k) := by
  dsimp only
  let F := replicaResidualState placement dst (S.R (placement.bank 132)) (S.R (placement.bank 93)) ys J
  have hbankFrame := h.bank_right houtput hrhs
  have hRbank (k : Fin 168) : F.R (placement.bank k) = S.R (placement.bank k) := by
    by_cases h132 : k = 132
    · subst k
      simp [F,replicaResidualState,hdst 132,placement.bank_injective.ne (by decide : (132 : Fin 168) ≠ 93)]
    by_cases h93 : k = 93
    · subst k
      simp [F,replicaResidualState,hdst 93]
    simp only [F,replicaResidualState,Function.update_of_ne (hdst k),
      Function.update_of_ne (placement.bank_injective.ne h93),Function.update_of_ne (placement.bank_injective.ne h132)]
    exact hbankFrame k h132 h93
  refine ⟨?_,?_,Stacks.ext h.input h.outStream (congrArg (fun L => L ∘ placement.bank) h.left) (funext hRbank),
    h.left,h.input,h.outStream,?_⟩
  · apply ReplicaCouplingCursor.of_frame H output rhs outputTail rhsTail (r+1) J F hcursor
    · simp [F,replicaResidualState,houtdst,(houtput 132).symm,(houtput 93).symm]
    · simp [F,replicaResidualState,hrhsdst,(hrhs 132).symm,(hrhs 93).symm]
  · simp only [replicaResidualState,Function.update_self]
    rw [h.right dst (by simp [houtdst.symm,hrhsdst.symm,(hdst 132).symm,(hdst 93).symm])]
  · intro k hk
    by_cases h132 : k = placement.bank 132
    · subst k; exact hRbank 132
    by_cases h93 : k = placement.bank 93
    · subst k; exact hRbank 93
    have hn : k ≠ output ∧ k ≠ rhs ∧ k ≠ dst := by simpa using hk
    simp only [replicaResidualState,Function.update_of_ne hn.2.2,
      Function.update_of_ne h93,Function.update_of_ne h132]
    apply h.right
    simpa using ⟨hn.1,hn.2.1,h132,h93⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
