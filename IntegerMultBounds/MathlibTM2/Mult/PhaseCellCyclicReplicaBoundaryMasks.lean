module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaBoundaryMask

/-! Generate both packed boundary masks once from the two retained metadata
banks. No residual rows, coefficient pages or metadata are consumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def cyclicReplicaBoundaryMasks (leftBank rightBank : Fin 168 → Fin T) (leftDst rightDst : Fin T) : Pr P T Q A U :=
  .seq (placedReplicaBoundaryMask leftBank leftDst) (placedReplicaBoundaryMask rightBank rightDst)

theorem cyclicReplicaBoundaryMasks_exec (H K : ReplicaHaloProblem s)
    (leftBank rightBank : Fin 168 → Fin T)
    (hleftInj : Function.Injective leftBank) (hrightInj : Function.Injective rightBank)
    (leftDst rightDst : Fin T) (hsep : leftDst ≠ rightDst)
    (hleftOff : ∀ i, leftBank i ≠ leftDst) (hrightOff : ∀ i, rightBank i ≠ rightDst)
    (hrightLeft : ∀ i, rightBank i ≠ leftDst) (hleftRight : ∀ i, leftBank i ≠ rightDst)
    (v : HS T Q A U) (S : Stacks T A)
    (hleft : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk leftBank S))
    (hright : CouplingIntervalMetadata K.metadataWidth s K.t K.band K.origin (K.origin+K.span) K.origin K.span
      (embStk rightBank S))
    (hleftBlank : ∀ i : Fin 168, i.val < 32 → S.R (leftBank i) = [])
    (hrightBlank : ∀ i : Fin 168, i.val < 32 → S.R (rightBank i) = [])
    (hleftDst : S.R leftDst = []) (hrightDst : S.R rightDst = []) :
    let F : Stacks T A := {S with R := (Function.update (Function.update S.R leftDst
      (couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span)) rightDst
      (couplingSourceIntervalMaskSymbols true A s K.t K.band K.origin (K.origin+K.span) K.origin K.span))}
    ∃ vf m, vf.user = v.user ∧ m ≤ placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K ∧
      Exec body (cyclicReplicaBoundaryMasks leftBank rightBank leftDst rightDst) (mk v S) m
        (mk vf F) ∧ embStk leftBank F = embStk leftBank S ∧ embStk rightBank F = embStk rightBank S := by
  let leftMask := couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := placedReplicaBoundaryMask_exec (body := body)
    H leftBank hleftInj leftDst hleftOff v S hleft hleftBlank
  let J : Stacks T A := {S with R := Function.update S.R leftDst leftMask}
  have he₁' : Exec body (placedReplicaBoundaryMask leftBank leftDst) (mk v S) m₁ (mk v₁ J) := by
    simpa only [J,leftMask,hleftDst,List.append_nil] using he₁
  have hframe (i : Fin 168) : J.R (rightBank i) = S.R (rightBank i) := by
    simp only [J,Function.update_of_ne (hrightLeft i)]
  have hmeta : CouplingIntervalMetadata K.metadataWidth s K.t K.band K.origin (K.origin+K.span) K.origin K.span
      (embStk rightBank J) := hright.of_frame (hframe 163) (fun k _ => hframe k)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := placedReplicaBoundaryMask_exec (body := body)
    K rightBank hrightInj rightDst hrightOff v₁ J hmeta
    (by intro i hi; rw [hframe]; exact hrightBlank i hi)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,(Exec.seq he₁' he₂).cast rfl ?_,?_,?_⟩
  · apply congrArg (mk v₂)
    simp only [J,Function.update_of_ne hsep.symm,hrightDst,List.append_nil,leftMask]
  · refine Stacks.ext rfl rfl rfl ?_
    funext i
    simp [embStk,hleftRight i,hleftOff i]
  · refine Stacks.ext rfl rfl rfl ?_
    funext i
    simp [embStk,hrightOff i,hrightLeft i]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
