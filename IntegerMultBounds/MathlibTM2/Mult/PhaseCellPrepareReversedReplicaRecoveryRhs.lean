module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaRecoveryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReverseCopyRows

/-! Copy retained original RHS rows in the same reverse order as the native
boundary projection archive. The original gather queue and all headers restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepareReversedReplicaRecoveryRhs (plan : ReplicaInteriorPlacement T) (rhs : Fin T) : Pr P T Q A U :=
  reverseCopyRows (plan.gather 121) (plan.gather 89) (plan.gather 123) (plan.gather 124)
    (plan.gather 88) rhs (plan.gather 104) (plan.gather 105)

theorem prepareReversedReplicaRecoveryRhs_exec_within (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (rhs : Fin T) (hgd : ∀ k, plan.gather k ≠ rhs)
    (buffers : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaRecoveryRhsHeaders H plan.gather buffers S) (depth : ℕ) :
    let F := {S with R := (Function.update S.R rhs
      (H.Fs.reverse.flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++S.R rhs))}
    ∃ vf m, vf.user = v.user ∧ m ≤ reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)) depth
        (prepareReversedReplicaRecoveryRhs plan rhs) (mk v S) m (mk vf F) ∧
      ReplicaRecoveryRhsHeaders H plan.gather buffers F := by
  dsimp only
  let rows := H.Fs.map (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))
  have hlen : ∀ row ∈ rows, row.length = H.span*H.wordWidth := by
    intro row hr
    obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hr
    simp [length_cstream,packedInterval_length C H.span_fit]
  have hregs : [plan.gather 121,plan.gather 89,plan.gather 123,plan.gather 124,
      plan.gather 88,rhs,plan.gather 104,plan.gather 105].Nodup := by
    simp [List.nodup_cons,hgd,Ne.symm (hgd _),plan.gather_injective.eq_iff]
  obtain ⟨vf,m,hu,hm,he⟩ := reverseCopyRows_exec_within (body := body)
    (plan.gather 121) (plan.gather 89) (plan.gather 123) (plan.gather 124)
    (plan.gather 88) rhs (plan.gather 104) (plan.gather 105) hregs
    (H.span*H.wordWidth) rows hlen buffers.packedRhsTail v S
    (by simpa only [rows,List.length_map] using headers.count) headers.volume
    (by simpa only [rows,List.flatMap_def] using headers.source)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      all_goals exact headers.fresh _ (by simp)) depth
  refine ⟨vf,m,hu,?_,?_,?_⟩
  · simpa only [rows,List.length_map] using hm
  · simpa only [prepareReversedReplicaRecoveryRhs,rows,List.length_map,List.flatMap_def,List.map_reverse] using he
  · apply headers.of_frame H plan.gather buffers S _
    intro k
    exact Function.update_of_ne (hgd k) _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
