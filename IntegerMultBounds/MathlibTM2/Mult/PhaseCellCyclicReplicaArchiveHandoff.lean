module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassPost
public import IntegerMultBounds.MathlibTM2.Host.OrderedMoveStock

/-! Move the two actual cached residual archives into the shared solver bank.
The source metadata and original RHS queues survive; tape stock does not grow. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 834 Q A U}

def cyclicReplicaArchiveHandoff : Pr P 834 Q A U :=
  moveRightPairOrdered (left.plan.gather 125) (right.plan.gather 125)
    (factorReg 174) (factorReg 169) (factorReg 172)

def cyclicReplicaArchiveHandoffState (S : Stacks 834 A) : Stacks 834 A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    (left.plan.gather 125) []) (factorReg 169) (S.R (left.plan.gather 125)++S.R (factorReg 169)))
    (right.plan.gather 125) []) (factorReg 172) (S.R (right.plan.gather 125)++S.R (factorReg 172)))}

theorem cyclicReplicaArchiveHandoff_exec_within (v : HS 834 Q A U) (S : Stacks 834 A)
    (htmp : S.R (factorReg 174) = []) (depth B : ℕ) (hb : mnSize (mk v S)+depth ≤ B) :
    ∃ vf, vf.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ B) depth cyclicReplicaArchiveHandoff (mk v S)
        (4*((S.R (left.plan.gather 125)).length+(S.R (right.plan.gather 125)).length)+8)
        (mk vf (cyclicReplicaArchiveHandoffState S)) := by
  exact moveRightPairOrdered_exec_within (body := body)
    (left.plan.gather 125) (right.plan.gather 125) (factorReg 174) (factorReg 169) (factorReg 172)
    (by decide) v S htmp depth B hb

theorem cyclicReplicaArchiveHandoff_read (S : Stacks 834 A) (k : Fin 834)
    (hl : k ≠ left.plan.gather 125) (hr : k ≠ right.plan.gather 125)
    (h169 : k ≠ factorReg 169) (h172 : k ≠ factorReg 172) :
    (cyclicReplicaArchiveHandoffState S).R k = S.R k := by
  simp only [cyclicReplicaArchiveHandoffState,Function.update_of_ne h172,Function.update_of_ne hr,
    Function.update_of_ne h169,Function.update_of_ne hl]

theorem cyclicReplicaArchiveHandoff_factor (S : Stacks 834 A) :
    embStk factorReg (cyclicReplicaArchiveHandoffState S) =
      {embStk factorReg S with R := (Function.update (Function.update (embStk factorReg S).R 169
        (S.R (left.plan.gather 125)++S.R (factorReg 169))) 172
        (S.R (right.plan.gather 125)++S.R (factorReg 172)))} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have hl : factorReg i ≠ left.plan.gather 125 := by
    intro h; have hv := congrArg Fin.val h; change 600+i.val = 125 at hv; omega
  have hr : factorReg i ≠ right.plan.gather 125 := by
    intro h; have hv := congrArg Fin.val h; change 600+i.val = 425 at hv; omega
  simp [embStk,cyclicReplicaArchiveHandoffState,Function.update_apply,
    factorReg_injective.eq_iff,hl,hr]

theorem cyclicReplicaArchiveHandoff_archives (S : Stacks 834 A) :
    (cyclicReplicaArchiveHandoffState S).R (factorReg 169) = S.R (left.plan.gather 125)++S.R (factorReg 169) ∧
    (cyclicReplicaArchiveHandoffState S).R (factorReg 172) = S.R (right.plan.gather 125)++S.R (factorReg 172) := by
  constructor
  · simp [cyclicReplicaArchiveHandoffState,
      show factorReg 169 ≠ factorReg 172 by decide,
      show factorReg 169 ≠ right.plan.gather 125 by decide]
  · simp [cyclicReplicaArchiveHandoffState]

theorem cyclicReplicaArchiveHandoff_banks (S : Stacks 834 A) :
    embStk left.coupling.bank (cyclicReplicaArchiveHandoffState S) = embStk left.coupling.bank S ∧
    embStk right.coupling.bank (cyclicReplicaArchiveHandoffState S) = embStk right.coupling.bank S := by
  constructor
  · refine Stacks.ext rfl rfl rfl ?_
    funext i
    apply cyclicReplicaArchiveHandoff_read
    · exact left.coupling.bank_gather_disjoint i 125
    · intro h; exact disjoint _ (h ▸ CachedReplicaPassPlacement.Owns.bank i) (.gather 125)
    · intro h; exact (factor_disjoint 169).1 (h ▸ CachedReplicaPassPlacement.Owns.bank i)
    · intro h; exact (factor_disjoint 172).1 (h ▸ CachedReplicaPassPlacement.Owns.bank i)
  · refine Stacks.ext rfl rfl rfl ?_
    funext i
    apply cyclicReplicaArchiveHandoff_read
    · intro h; exact disjoint _ (.gather 125) (h ▸ CachedReplicaPassPlacement.Owns.bank i)
    · exact right.coupling.bank_gather_disjoint i 125
    · intro h; exact (factor_disjoint 169).2 (h ▸ CachedReplicaPassPlacement.Owns.bank i)
    · intro h; exact (factor_disjoint 172).2 (h ▸ CachedReplicaPassPlacement.Owns.bank i)

theorem cyclicReplicaArchiveHandoff_gather (S : Stacks 834 A) :
    (∀ i : Fin 126, i ≠ 125 → (cyclicReplicaArchiveHandoffState S).R (left.plan.gather i) = S.R (left.plan.gather i)) ∧
    (∀ i : Fin 126, i ≠ 125 → (cyclicReplicaArchiveHandoffState S).R (right.plan.gather i) = S.R (right.plan.gather i)) := by
  constructor
  · intro i hi
    apply cyclicReplicaArchiveHandoff_read
    · exact left.plan.gather_injective.ne hi
    · intro h; exact disjoint _ (h ▸ CachedReplicaPassPlacement.Owns.gather i) (.gather 125)
    · intro h; exact (factor_disjoint 169).1 (h ▸ CachedReplicaPassPlacement.Owns.gather i)
    · intro h; exact (factor_disjoint 172).1 (h ▸ CachedReplicaPassPlacement.Owns.gather i)
  · intro i hi
    apply cyclicReplicaArchiveHandoff_read
    · intro h; exact disjoint _ (.gather 125) (h ▸ CachedReplicaPassPlacement.Owns.gather i)
    · exact right.plan.gather_injective.ne hi
    · intro h; exact (factor_disjoint 169).2 (h ▸ CachedReplicaPassPlacement.Owns.gather i)
    · intro h; exact (factor_disjoint 172).2 (h ▸ CachedReplicaPassPlacement.Owns.gather i)

theorem cyclicReplicaArchiveHandoff_recoveryRhs {s : ℕ} (H K : ReplicaHaloProblem s)
    (leftBuffers rightBuffers : ReplicaLoopBuffers A) (S : Stacks 834 A)
    (hl : ReplicaRecoveryRhsHeaders H left.plan.gather leftBuffers S)
    (hr : ReplicaRecoveryRhsHeaders K right.plan.gather rightBuffers S) :
    ReplicaRecoveryRhsHeaders H left.plan.gather leftBuffers (cyclicReplicaArchiveHandoffState S) ∧
    ReplicaRecoveryRhsHeaders K right.plan.gather rightBuffers (cyclicReplicaArchiveHandoffState S) := by
  exact ⟨ReplicaRecoveryRhsHeaders.of_archive_frame H left.plan.gather leftBuffers S _ hl
      (cyclicReplicaArchiveHandoff_gather S).1,
    ReplicaRecoveryRhsHeaders.of_archive_frame K right.plan.gather rightBuffers S _ hr
      (cyclicReplicaArchiveHandoff_gather S).2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
