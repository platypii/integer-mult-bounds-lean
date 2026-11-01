module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Stage one original RHS and allocate the two owned prefixes that recovery
overwrites. Their contents are arbitrary; only their lengths are consumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 255 Q A U}

def stageReplicaRecoveryRhs : Pr P 255 Q A U :=
  .seq (takePrefix 251 93 110 104 105) (.seq (ucopy 251 110 0) (ucopy 251 132 0))

def stagedReplicaRecoveryRhsState (S : Stacks 255 A) (xs tail : List (Fin (A+4))) : Stacks 255 A :=
  {S with R := (Function.update (Function.update (Function.update S.R 93 tail)
    110 (List.replicate xs.length tick++(xs++S.R 110)))
    132 (List.replicate xs.length tick++S.R 132))}

theorem stageReplicaRecoveryRhs_exec (v : HS 255 Q A U) (S : Stacks 255 A)
    (xs tail : List (Fin (A+4))) (hsrc : S.R 93 = xs++tail)
    (hvolume : (S.R 251).length = xs.length)
    (h0 : S.R 0 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body stageReplicaRecoveryRhs (mk v S) (14*xs.length+14)
        (mk v' (stagedReplicaRecoveryRhsState S xs tail)) := by
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body) (count := 251) (src := 93) (dst := 110)
    (buf := 104) (tmp := 105) (by decide) v S xs tail hsrc hvolume h104 h105
  let J : Stacks 255 A := {S with R := (Function.update (Function.update S.R 93 tail) 110 (xs++S.R 110))}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 251) (b := 110) (t := 0)
    (by decide) (by decide) (by decide) v₁ J (by simpa [J] using h0)
  let K : Stacks 255 A := {J with R := Function.update J.R 110 (List.replicate xs.length tick++J.R 110)}
  have he₂' : Exec body (ucopy 251 110 0) (mk v₁ J) (4*xs.length+4) (mk v₂ K) := by
    simpa [K,J,hvolume] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec (body := body) (a := 251) (b := 132) (t := 0)
    (by decide) (by decide) (by decide) v₂ K (by simpa [K,J] using h0)
  have he₃' : Exec body (ucopy 251 132 0) (mk v₂ K) (4*xs.length+4)
      (mk v₃ (stagedReplicaRecoveryRhsState S xs tail)) := by
    simpa [K,J,stagedReplicaRecoveryRhsState,hvolume] using he₃
  exact ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁ (Exec.seq he₂' he₃')).cast (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
