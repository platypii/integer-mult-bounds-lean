module

public import IntegerMultBounds.MathlibTM2.Host.OrderedMove
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingReady

/-! Load the current full iterate without reversing its coefficient stream.
Only the iterate archive and periodic source change; the scalar core survives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast ScalarPlacement

def periodicIterateBank {A : ℕ} (S : Stacks 242 A) : Stacks 242 A :=
  {S with R := Function.update (Function.update S.R 132 []) 141 (S.R 132)}

theorem periodicIterateBank_core {A : ℕ} (S : Stacks 242 A) :
    embStk (Fin.castLE (by decide : 117 ≤ 242)) (periodicIterateBank S) =
      embStk (Fin.castLE (by decide : 117 ≤ 242)) S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have hi := i.isLt
  simp [periodicIterateBank,embStk,Fin.ext_iff,show i.val ≠ 132 by omega,show i.val ≠ 141 by omega]

private theorem periodicIterateBank_frame {A : ℕ} (S : Stacks 242 A) (k : Fin 242)
    (h132 : k ≠ 132) (h141 : k ≠ 141) : (periodicIterateBank S).R k = S.R k := by
  simp [periodicIterateBank,h132,h141]

theorem periodicLoadIterate_exec {Q A precision q w s t u band a b W N : ℕ}
    {P U : Type} {body : P → Pr P 242 Q A U}
    (raw : List (Fin (A+4))) (v : HS 242 Q A U) (S : Stacks 242 A)
    (h107 : S.R 107 = []) (h141 : S.R 141 = [])
    (hready : RetainedCouplingReady precision q w s t u band a b raw
      (embStk (Fin.castLE (by decide : 117 ≤ 242)) S))
    (hbank : PackedPreparedBank q w W N S) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveRightOrdered 132 107 141) (mk v S) (4*(S.R 132).length+4)
        (mk v' (periodicIterateBank S)) ∧
      RetainedCouplingReady precision q w s t u band a b raw
        (embStk (Fin.castLE (by decide : 117 ≤ 242)) (periodicIterateBank S)) ∧
      PackedPreparedBank q w W N (periodicIterateBank S) ∧
      ∀ bo hf df, PackedBoundaryFactorPages bo hf df S →
        PackedBoundaryFactorPages bo hf df (periodicIterateBank S) := by
  obtain ⟨v',hu,he⟩ := moveRightOrdered_exec (body := body) 132 107 141
    (by decide) (by decide) (by decide) v S h107
  refine ⟨v',hu,?_,?_,?_,?_⟩
  · simpa only [h141,List.append_nil,periodicIterateBank] using he
  · rw [periodicIterateBank_core]
    exact hready
  · apply hbank.of_runtime_frame (F := periodicIterateBank S) rfl
    · intro k hk
      apply periodicIterateBank_frame
      all_goals intro he; have hv := congrArg (fun i : Fin 242 => i.val) he; omega
    · exact periodicIterateBank_frame S 119 (by decide) (by decide)
    · intro k hk _
      apply periodicIterateBank_frame
      all_goals intro he; have hv := congrArg (fun i : Fin 242 => i.val) he; omega
  · intro bo hf df hpages
    apply hpages.of_solution_frame
    intro k hk _
    apply periodicIterateBank_frame
    all_goals intro he; have hv := congrArg (fun i : Fin 242 => i.val) he; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
