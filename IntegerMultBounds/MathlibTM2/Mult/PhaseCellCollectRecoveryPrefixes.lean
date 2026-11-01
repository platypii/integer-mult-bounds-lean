module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishReplicaCouplingRow

/-! Move the two computed recovery prefixes into separate archives and retire
the original RHS. Moving rather than copying keeps the live volume linear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def collectRecoveryPrefixes (volume rhs boundary rhsArchive boundaryArchive saved tmp : Fin T) : Pr P T Q A U :=
  .seq (takePrefix volume rhs rhsArchive saved tmp)
    (finishReplicaCouplingRow volume rhs boundary boundaryArchive saved tmp)

def collectedRecoveryPrefixes (S : Stacks T A) (rhs boundary rhsArchive boundaryArchive : Fin T)
    (rhsWords boundaryWords rhsTail boundaryTail : List (Fin (A+4))) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    rhs rhsTail) boundary boundaryTail) rhsArchive (rhsWords++S.R rhsArchive))
    boundaryArchive (boundaryWords++S.R boundaryArchive))}

theorem collectedRecoveryPrefixes_frame (S : Stacks T A) (rhs boundary rhsArchive boundaryArchive : Fin T)
    (rhsWords boundaryWords rhsTail boundaryTail : List (Fin (A+4))) (k : Fin T)
    (hk : k ∉ [rhs,boundary,rhsArchive,boundaryArchive]) :
    (collectedRecoveryPrefixes S rhs boundary rhsArchive boundaryArchive
      rhsWords boundaryWords rhsTail boundaryTail).R k = S.R k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
  simp [collectedRecoveryPrefixes,hk.1,hk.2.1,hk.2.2.1,hk.2.2.2]

theorem collectRecoveryPrefixes_exec_within (volume rhs boundary rhsArchive boundaryArchive saved tmp : Fin T)
    (hreg : [volume,rhs,boundary,rhsArchive,boundaryArchive,saved,tmp].Nodup) (V : ℕ)
    (rhsWords originalWords boundaryWords rhsTail boundaryTail : List (Fin (A+4)))
    (hR : rhsWords.length = V) (hC : originalWords.length = V) (hY : boundaryWords.length = V)
    (v : HS T Q A U) (S : Stacks T A) (hV : (S.R volume).length = V)
    (hrhs : S.R rhs = rhsWords++(originalWords++rhsTail))
    (hboundary : S.R boundary = boundaryWords++boundaryTail)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(18*V+18)) depth
        (collectRecoveryPrefixes volume rhs boundary rhsArchive boundaryArchive saved tmp)
        (mk v S) (18*V+18)
        (mk v' (collectedRecoveryPrefixes S rhs boundary rhsArchive boundaryArchive
          rhsWords boundaryWords rhsTail boundaryTail)) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body) (count := volume) (src := rhs)
    (dst := rhsArchive) (buf := saved) (tmp := tmp) (by regs_nodup) v S rhsWords
    (originalWords++rhsTail) hrhs (by rw [hV,hR]) hsaved htmp
  let J : Stacks T A := {S with R := (Function.update (Function.update S.R rhs (originalWords++rhsTail))
    rhsArchive (rhsWords++S.R rhsArchive))}
  obtain ⟨v₂,hu₂,he₂⟩ := finishReplicaCouplingRow_exec_within (body := body)
    volume rhs boundary boundaryArchive saved tmp (by regs_nodup) V originalWords boundaryWords
    rhsTail boundaryTail hC hY v₁ J
    (by simpa [J,‹volume ≠ rhs›,‹volume ≠ rhsArchive›] using hV)
    (by simp [J,‹rhs ≠ rhsArchive›])
    (by simpa [J,‹rhs ≠ boundary›.symm,‹boundary ≠ rhsArchive›] using hboundary)
    (by simpa [J,‹rhs ≠ saved›.symm,‹rhsArchive ≠ saved›.symm] using hsaved)
    (by simpa [J,‹rhs ≠ tmp›.symm,‹rhsArchive ≠ tmp›.symm] using htmp) depth
  have he : Exec body (collectRecoveryPrefixes volume rhs boundary rhsArchive boundaryArchive saved tmp)
      (mk v S) (18*V+18)
      (mk v₂ (collectedRecoveryPrefixes S rhs boundary rhsArchive boundaryArchive
        rhsWords boundaryWords rhsTail boundaryTail)) := by
    apply (Exec.seq he₁ he₂.toExec).cast
    · unfold finishReplicaCouplingRowCost
      rw [hR]
      omega
    · apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      simp [J,collectedRecoveryPrefixes,Function.update_apply,‹rhs ≠ boundaryArchive›.symm,
        ‹rhsArchive ≠ boundaryArchive›.symm]
      split_ifs <;> subst_vars <;> simp_all
  exact ⟨v₂,hu₂.trans hu₁,mn_native_exec_within he 2 (by
    simp [collectRecoveryPrefixes,finishReplicaCouplingRow,discardPrefix,takePrefix,transfer,transferAct,
      scanR,drainR,popDo,keepIn,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]) depth _ (le_refl _)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
