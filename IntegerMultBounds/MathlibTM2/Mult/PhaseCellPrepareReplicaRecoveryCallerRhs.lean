module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaRecoveryRhs

/-! The actual retained gather source produces recovery's owned RHS queue in
the common caller placement. The private controller doubles as restored scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} {P U : Type} {body : P → Pr P 389 Q A U}

def prepareReplicaRecoveryCallerRhs : Pr P 389 Q A U :=
  prepareReplicaRecoveryRhs replicaRecoveryCallerInterior 388 387

theorem prepareReplicaRecoveryCallerRhs_exec (H : ReplicaHaloProblem s)
    (buffers : ReplicaLoopBuffers A) (v : HS 389 Q A U) (S : Stacks 389 A)
    (headers : ReplicaRecoveryRhsHeaders H replicaRecoveryCallerInterior.gather buffers S)
    (hcontroller : S.R 387 = []) (hqueue : S.R 388 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ copyRowsOrderedCost H.Fs.length (H.span*H.wordWidth) ∧
      Exec body prepareReplicaRecoveryCallerRhs (mk v S) n
        (mk v' {S with R := Function.update S.R 388 (H.Fs.flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F)))}) := by
  have hgd (k : Fin 126) : replicaRecoveryCallerInterior.gather k ≠ 388 := by
    rw [replicaRecoveryCallerInterior_gather]
    intro h
    have hv := congrArg (fun k : Fin 389 => k.val) h
    change k.val = 388 at hv
    have hb := k.isLt
    omega
  have hgr (k : Fin 126) : replicaRecoveryCallerInterior.gather k ≠ 387 := by
    rw [replicaRecoveryCallerInterior_gather]
    intro h
    have hv := congrArg (fun k : Fin 389 => k.val) h
    change k.val = 387 at hv
    have hb := k.isLt
    omega
  obtain ⟨v',n,hu,hn,he⟩ := prepareReplicaRecoveryRhs_exec (body := body) H
    replicaRecoveryCallerInterior 388 387 hgd hgr (by decide) buffers v S headers hcontroller
  exact ⟨v',n,hu,hn,by simpa [prepareReplicaRecoveryCallerRhs,hqueue] using he⟩

theorem prepareReplicaRecoveryCallerRhs_worker_frame (S : Stacks 389 A) (words : List (Fin (A+4))) :
    embStk (fun i : Fin 255 => replicaRecoveryCallerReg (Fin.castLE (by decide) i))
      {S with R := Function.update S.R 388 words} =
    embStk (fun i : Fin 255 => replicaRecoveryCallerReg (Fin.castLE (by decide) i)) S := by
  apply embStk_updateR_off
  intro i hi
  have hh : replicaRecoveryCallerReg (Fin.castLE (by decide) i) = replicaRecoveryCallerReg 258 := by
    simpa only [replicaRecoveryCallerReg_rhs] using hi
  have hv := congrArg (fun k : Fin 259 => k.val) (replicaRecoveryCallerReg_injective hh)
  change i.val = 258 at hv
  have hb := i.isLt
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
