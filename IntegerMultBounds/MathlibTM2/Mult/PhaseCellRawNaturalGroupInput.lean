module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledNaturalGroupInput

/-! Ordinary parameters and one ambient line produce the closed solver's input.
The original line is retained inside the borrowed payload suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def rawNaturalGroupPrepare : Pr P₀ 117 Q A U :=
  .seq generateOriginAndGatherControls rawNaturalGather

theorem rawNaturalGroupInputBank_exec (P N q l s t u band L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hgroup : 0 < (naturalLengthGroup s t band L).length)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (v : HS 117 Q A U)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let B := (naturalLengthGroup s t band L).length
    let raw := cstream A (2*q+8) (chirpLine s C)
    let rhs := cstream A (2*q+8) ((List.range B).flatMap
      (cellSourceRows L (naturalGroupOrigin s t band L) (fun _ => C)))
    ∃ v' n, v'.user = v.user ∧
      n ≤ generateOriginAndGatherControlsCost P q s t u band L+rawNaturalGatherCost q s ∧
      Exec body rawNaturalGroupPrepare
        (mk v (naturalGroupInputBank P N q l s t u band L raw borrowed outTail inp out)) n
        (mk v' (batchInputBank P N q l s t u band L B
          (fun n => (naturalGroupOrigin s t band L n).val) rhs (raw++borrowed) outTail inp out)) := by
  dsimp only
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generateNaturalGroupInputBank_exec (body := body)
    P N q l s t u band L hP hs hst hu hgroup hband hL hLs hA C v borrowed outTail inp out
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := gatherControlledNaturalGroupInputBank_exec (body := body)
    P N q l s t u band L hst hgroup C v₁ borrowed outTail inp out
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
