module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyRowsOrdered
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealReplicaHaloOutput

/-! Produce the original-order RHS queue needed by complete replica recovery.
The retained source, masters and scratch are restored by the structural scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepareReplicaRecoveryRhs (plan : ReplicaInteriorPlacement T) (rhs reversed : Fin T) : Pr P T Q A U :=
  copyRowsOrdered (plan.gather 121) (plan.gather 89) (plan.gather 123) (plan.gather 124)
    (plan.gather 88) reversed rhs (plan.gather 104) (plan.gather 105)

theorem prepareReplicaRecoveryRhs_exec (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (rhs reversed : Fin T)
    (hgd : ∀ k, plan.gather k ≠ rhs) (hgr : ∀ k, plan.gather k ≠ reversed) (hsep : rhs ≠ reversed)
    (buffers : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaLoopHeaders H plan.gather buffers S) (hblank : S.R reversed = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ copyRowsOrderedCost H.Fs.length (H.span*H.wordWidth) ∧
      Exec body (prepareReplicaRecoveryRhs plan rhs reversed) (mk v S) n
        (mk v' {S with R := Function.update S.R rhs (H.Fs.flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))++S.R rhs)}) := by
  let rows := H.Fs.map (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))
  have hlen : ∀ row ∈ rows, row.length = H.span*H.wordWidth := by
    intro row hrow
    obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hrow
    simp [length_cstream,packedInterval_length F H.span_fit]
  have hregs : [plan.gather 121,plan.gather 89,plan.gather 123,plan.gather 124,
      plan.gather 88,reversed,rhs,plan.gather 104,plan.gather 105].Nodup := by
    simp [List.nodup_cons,hgd,hgr,Ne.symm (hgd _),Ne.symm (hgr _),hsep,Ne.symm hsep,
      plan.gather_injective.eq_iff]
  have hN : (S.R (plan.gather 121)).length = rows.length := by
    simpa [rows,replicaFactoryHeaderValue] using headers.masters (121,113)
      (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  obtain ⟨v',n,hu,hn,he⟩ := copyRowsOrdered_exec (body := body)
    (plan.gather 121) (plan.gather 89) (plan.gather 123) (plan.gather 124)
    (plan.gather 88) reversed rhs (plan.gather 104) (plan.gather 105) hregs
    (H.span*H.wordWidth) rows hlen buffers.packedRhsTail v S hN headers.volume
    (by simpa only [rows,List.flatMap_def] using headers.source)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact headers.fresh _ (by simp)
      · exact headers.fresh _ (by simp)
      · exact hblank
      · exact headers.fresh _ (by simp)
      · exact headers.fresh _ (by simp))
  exact ⟨v',n,hu,by simpa only [rows,List.length_map] using hn,
    by simpa only [prepareReplicaRecoveryRhs,rows,List.flatMap_def] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
