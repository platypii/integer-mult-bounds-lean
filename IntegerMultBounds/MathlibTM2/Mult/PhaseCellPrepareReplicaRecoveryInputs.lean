module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageReplicaRecoveryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeedReplicaRecovery

/-! Prepare recovery's owned RHS/output prefixes and disposable headers.
The original RHS queue advances; retained boundary data and factors survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 255 Q A U}

def prepareReplicaRecoveryInputs : Pr P 255 Q A U :=
  .seq stageReplicaRecoveryRhs seedReplicaRecovery

def preparedReplicaRecoveryInputState (S : Stacks 255 A) (xs tail : List (Fin (A+4))) : Stacks 255 A :=
  seededReplicaRecoveryState (stagedReplicaRecoveryRhsState S xs tail)

theorem preparedReplicaRecoveryInputState_frame (S : Stacks 255 A) (xs tail : List (Fin (A+4)))
    (k : Fin 255) (hk : k ∉ [93,110,116,132,167]) :
    (preparedReplicaRecoveryInputState S xs tail).R k = S.R k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
  simp [preparedReplicaRecoveryInputState,seededReplicaRecoveryState,stagedReplicaRecoveryRhsState,
    hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2]

theorem prepareReplicaRecoveryInputs_exec (v : HS 255 Q A U) (S : Stacks 255 A)
    (xs tail : List (Fin (A+4))) (hsrc : S.R 93 = xs++tail)
    (hvolume : (S.R 251).length = xs.length)
    (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (h116 : S.R 116 = []) (h167 : S.R 167 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body prepareReplicaRecoveryInputs (mk v S)
        (14*xs.length+4*(S.R 253).length+6*(S.R 254).length+24)
        (mk v' (preparedReplicaRecoveryInputState S xs tail)) := by
  obtain ⟨v₁,hu₁,he₁⟩ := stageReplicaRecoveryRhs_exec (body := body) v S xs tail hsrc hvolume h0 h104 h105
  let J := stagedReplicaRecoveryRhsState S xs tail
  obtain ⟨v₂,hu₂,he₂⟩ := seedReplicaRecovery_exec (body := body) v₁ J
    (by simpa [J,stagedReplicaRecoveryRhsState] using h0)
    (by simpa [J,stagedReplicaRecoveryRhsState] using h1)
    (by simpa [J,stagedReplicaRecoveryRhsState] using h116)
    (by simpa [J,stagedReplicaRecoveryRhsState] using h167)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ rfl⟩
  simp [J,stagedReplicaRecoveryRhsState]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
