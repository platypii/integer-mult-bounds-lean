module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCellRuntime
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBatchPlacement

/-! The restored recovery core is the ordinary interior initializer's released
native bank. Its two borrowed suffixes are kept explicit, rather than assumed blank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

theorem ReplicaRecoveryCoreReady.released_native (H : ReplicaHaloProblem s) (W : ℕ) (S : Stacks 248 A)
    (h : ReplicaRecoveryCoreReady H W S) (rhsTail outputTail : List (Fin (A+4)))
    (hleft : ∀ i : Fin 117, S.L (Fin.castLE (by decide : 117 ≤ 248) i) = [])
    (h93 : S.R 93 = outputTail) (h110 : S.R 110 = rhsTail) (h116 : S.R 116 = []) :
    embStk (Fin.castLE (by decide : 117 ≤ 248)) S =
      releasedCellBank [] rhsTail outputTail S.inp S.out := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    exact hleft i
  · funext i
    by_cases h93i : i = 93
    · subst i
      exact h93
    by_cases h110i : i = 110
    · subst i
      exact h110
    by_cases h116i : i = 116
    · subst i
      exact h116
    have hi := i.isLt
    have h93v : i.val ≠ 93 := by intro he; exact h93i (Fin.ext he)
    have h110v : i.val ≠ 110 := by intro he; exact h110i (Fin.ext he)
    have hn := h.native i h93i h110i h116i
    simp only [embStk,releasedCellBank,Function.comp_apply,h93v,h110v,if_false,List.nil_append]
    exact hn

theorem replicaRecoveryPreparationCaller_native_view (F : Stacks 392 A) :
    embStk (Fin.castLE (by decide : 117 ≤ 258)) (embStk replicaRecoveryPreparationCallerReg F) =
      embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver F) := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    exact congrArg F.L (replicaRecoveryPreparationCallerReg_native i)
  · funext i
    exact congrArg F.R (replicaRecoveryPreparationCallerReg_native i)

theorem replicaRecoveryPreparationCaller_released (H : ReplicaHaloProblem s) (W : ℕ) (F : Stacks 392 A)
    (hcore : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 258))
      (embStk replicaRecoveryPreparationCallerReg F)))
    (rhsTail outputTail : List (Fin (A+4)))
    (hleft : ∀ i : Fin 117, F.L (replicaRecoveryPreparationCallerReg (Fin.castLE (by decide) i)) = [])
    (h93 : F.R (replicaRecoveryPreparationCallerReg 93) = outputTail)
    (h110 : F.R (replicaRecoveryPreparationCallerReg 110) = rhsTail)
    (h116 : F.R (replicaRecoveryPreparationCallerReg 116) = []) :
    embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver F) =
      releasedCellBank [] rhsTail outputTail F.inp F.out := by
  have hh := hcore.released_native H W _ rhsTail outputTail hleft h93 h110 h116
  change embStk (Fin.castLE (by decide : 117 ≤ 258)) (embStk replicaRecoveryPreparationCallerReg F) = _ at hh
  rw [replicaRecoveryPreparationCaller_native_view] at hh
  exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
