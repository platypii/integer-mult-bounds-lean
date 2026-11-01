module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectRecoveryPrefixes
public import IntegerMultBounds.MathlibTM2.Host.AppendRuns

/-! Collection moves both computed rows. At iteration boundaries its stock
decreases by exactly the consumed original RHS, independently of archive size. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type}

theorem collectedRecoveryPrefixes_size (rhs boundary rhsArchive boundaryArchive : Fin T)
    (hreg : [rhs,boundary,rhsArchive,boundaryArchive].Nodup)
    (v w : HS T Q A U) (S : Stacks T A)
    (rhsWords originalWords boundaryWords rhsTail boundaryTail : List (Fin (A+4)))
    (hrhs : S.R rhs = rhsWords++(originalWords++rhsTail))
    (hboundary : S.R boundary = boundaryWords++boundaryTail) :
    mnSize (mk w (collectedRecoveryPrefixes S rhs boundary rhsArchive boundaryArchive
      rhsWords boundaryWords rhsTail boundaryTail))+originalWords.length = mnSize (mk v S) := by
  have hr := hreg
  regs_ne hr
  let F₁ : Stacks T A := {S with R := Function.update S.R rhs rhsTail}
  let F₂ : Stacks T A := {F₁ with R := Function.update F₁.R boundary boundaryTail}
  let F₃ : Stacks T A := {F₂ with R := Function.update F₂.R rhsArchive (rhsWords++F₂.R rhsArchive)}
  have h₁ : mnSize (mk v F₁)+(S.R rhs).length = mnSize (mk v S)+rhsTail.length := by
    simpa only [F₁,mk,update_rt,get_rt] using mn_size_update (mk v S) v (.rt rhs) rhsTail
  have h₂ : mnSize (mk v F₂)+(S.R boundary).length = mnSize (mk v F₁)+boundaryTail.length := by
    have hh : mnSize (mk v F₂)+(F₁.R boundary).length = mnSize (mk v F₁)+boundaryTail.length := by
      simpa only [F₂,mk,update_rt,get_rt] using mn_size_update (mk v F₁) v (.rt boundary) boundaryTail
    have hb : F₁.R boundary = S.R boundary := Function.update_of_ne ‹rhs ≠ boundary›.symm _ _
    rw [hb] at hh
    exact hh
  have h₃ := mn_appendR_size v v F₂ rhsArchive rhsWords
  change mnSize (mk v F₃) = mnSize (mk v F₂)+rhsWords.length at h₃
  have h₄ := mn_appendR_size v w F₃ boundaryArchive boundaryWords
  have hF : {F₃ with R := Function.update F₃.R boundaryArchive (boundaryWords++F₃.R boundaryArchive)} =
      collectedRecoveryPrefixes S rhs boundary rhsArchive boundaryArchive
        rhsWords boundaryWords rhsTail boundaryTail := by
    simp [F₃,F₂,F₁,collectedRecoveryPrefixes,‹rhs ≠ rhsArchive›.symm,
      ‹boundary ≠ rhsArchive›.symm,‹rhs ≠ boundaryArchive›.symm,
      ‹boundary ≠ boundaryArchive›.symm,‹rhsArchive ≠ boundaryArchive›.symm]
  rw [hF] at h₄
  rw [hrhs,List.length_append,List.length_append] at h₁
  rw [hboundary,List.length_append] at h₂
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
