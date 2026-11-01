module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoverySetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPeripheralReady

/-! Restore the second pass's peripheral language after consuming the first-pass
archive. Only port 125 is reset; the remaining gather/cache/output data survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
variable {s A : ℕ} [NeZero s]

theorem ReplicaRecoveryPeripheralReady.of_prepared_archives (H : ReplicaHaloProblem s)
    (buffers : ReplicaLoopBuffers A) {S F : Stacks 392 A}
    (h : ReplicaRecoveryPeripheralReady H buffers {S with R := Function.update S.R 125 []})
    (hL : F.L = S.L) (hin : F.inp = S.inp) (hout : F.out = S.out) (h125 : F.R 125 = [])
    (hframe : ∀ k, k ≠ 125 → (∀ i, replicaRecoverySetupWorkerReg i ≠ k) → F.R k = S.R k) :
    ReplicaRecoveryPeripheralReady H buffers F := by
  have hworkerOff (k : Fin 392) (hk : ∀ i, replicaRecoveryPreparationCallerReg i ≠ k) :
      ∀ i, replicaRecoverySetupWorkerReg i ≠ k := by
    intro i he
    exact hk (Fin.castLE (by decide : 255 ≤ 258) i)
      ((replicaRecoveryPreparationCallerReg_worker i).trans he)
  have hgatherOff (i : Fin 255) (j : Fin 126) :
      replicaRecoverySetupWorkerReg i ≠ Fin.castLE (by decide : 126 ≤ 392) j := by
    intro he
    exact replicaRecoveryPreparationCallerReg_gather_disjoint (Fin.castLE (by decide : 255 ≤ 258) i) j
      ((replicaRecoveryPreparationCallerReg_worker i).trans he)
  apply h.of_preparation_frame H buffers
  · refine Stacks.ext hin hout (congrArg (fun L => L ∘ Fin.castLE (by decide : 126 ≤ 392)) hL) ?_
    funext j
    change F.R (Fin.castLE (by decide : 126 ≤ 392) j) = Function.update S.R 125 [] _
    by_cases hj : (Fin.castLE (by decide : 126 ≤ 392) j) = 125
    · rw [hj,Function.update_self]
      exact h125
    · rw [Function.update_of_ne hj]
      exact hframe _ hj (fun i => hgatherOff i j)
  · intro k hk
    refine ⟨congrFun hL k,?_⟩
    by_cases he : k = 125
    · subst k
      simpa only [Function.update_self] using h125
    · change F.R k = Function.update S.R 125 [] k
      rw [Function.update_of_ne he]
      exact hframe k he (hworkerOff k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
