module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Fast.Input

/-! Supply disposable recovery headers from the retained boundary count/mask.
Both retained sources survive; recovery may consume its native copies. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 255 Q A U}

def seedReplicaRecovery : Pr P 255 Q A U :=
  .seq (ucopy 253 116 0) (.seq (copyR 254 0 1 id) (moveR 0 167 id))

def seededReplicaRecoveryState (S : Stacks 255 A) : Stacks 255 A :=
  {S with R := (Function.update (Function.update S.R 116 (List.replicate (S.R 253).length tick)) 167 (S.R 254))}

theorem seededReplicaRecoveryState_frame (S : Stacks 255 A) (k : Fin 255)
    (h116 : k ≠ 116) (h167 : k ≠ 167) : (seededReplicaRecoveryState S).R k = S.R k := by
  simp [seededReplicaRecoveryState,h116,h167]

theorem seedReplicaRecovery_exec (v : HS 255 Q A U) (S : Stacks 255 A)
    (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h116 : S.R 116 = []) (h167 : S.R 167 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body seedReplicaRecovery (mk v S) (4*(S.R 253).length+6*(S.R 254).length+10)
        (mk v' (seededReplicaRecoveryState S)) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 253) (b := 116) (t := 0)
    (by decide) (by decide) (by decide) v S h0
  let J : Stacks 255 A := {S with R := Function.update S.R 116 (List.replicate (S.R 253).length tick)}
  have he₁' : Exec body (ucopy 253 116 0) (mk v S) (4*(S.R 253).length+4) (mk v₁ J) := by
    simpa [J,h116] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := copyR_exec (body := body) 254 0 1 (by decide) (by decide) (by decide) id v₁ J
    (by simpa [J] using h1)
  let K : Stacks 255 A := {J with R := Function.update J.R 0 (S.R 254).reverse}
  have he₂' : Exec body (copyR 254 0 1 id) (mk v₁ J) (4*(S.R 254).length+4) (mk v₂ K) := by
    simpa [K,J,h0] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body 0 167 (by decide) id v₂ K
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁' (Exec.seq he₂' he₃)).cast ?_ ?_⟩
  · simp [K,J]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 0
    · subst k; simp [K,J,movedR,seededReplicaRecoveryState,h0]
    · simp [K,J,movedR,seededReplicaRecoveryState,Function.update_apply,hk,h167]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
