module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryMasks

/-! Generate both recovery masks once in the two new mask slots. Every tape of
the existing cached boundary caller is preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "recoveryBank" => CyclicRecoveryPlacement.bank
local notation "extendCaller" => CyclicRecoveryPlacement.extend
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 840 Q A U}

def cyclicRecoveryLeftBank (i : Fin 168) : Fin 840 := extendCaller (CyclicReplicaPlacement.left.coupling.bank i)
def cyclicRecoveryRightBank (i : Fin 168) : Fin 840 := extendCaller (CyclicReplicaPlacement.right.coupling.bank i)

def cyclicRecoveryMasks : Pr P 840 Q A U :=
  cyclicReplicaBoundaryMasks cyclicRecoveryLeftBank cyclicRecoveryRightBank (recoveryBank 239) (recoveryBank 238)

def cyclicRecoveryMaskState {s : ℕ} (H K : ReplicaHaloProblem s) (S : Stacks 840 A) : Stacks 840 A :=
  {S with R := (Function.update (Function.update S.R (recoveryBank 239)
    (couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span))
    (recoveryBank 238)
    (couplingSourceIntervalMaskSymbols true A s K.t K.band K.origin (K.origin+K.span) K.origin K.span))}

theorem cyclicRecoveryMaskState_old {s : ℕ} (H K : ReplicaHaloProblem s) (S : Stacks 840 A) :
    embStk extendCaller (cyclicRecoveryMaskState H K S) = embStk extendCaller S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  have h239 : extendCaller k ≠ recoveryBank 239 := by
    intro he; have hv := congrArg (fun j : Fin 840 => j.val) he
    change k.val = 839 at hv
    have := k.isLt; omega
  have h238 : extendCaller k ≠ recoveryBank 238 := by
    intro he; have hv := congrArg (fun j : Fin 840 => j.val) he
    change k.val = 838 at hv
    have := k.isLt; omega
  simp only [cyclicRecoveryMaskState,embStk,Function.comp_apply,
    Function.update_of_ne h238,Function.update_of_ne h239]

theorem cyclicRecoveryMaskState_bank_read {s : ℕ} (H K : ReplicaHaloProblem s)
    (S : Stacks 840 A) (i : Fin 240) (h238 : i ≠ 238) (h239 : i ≠ 239) :
    (cyclicRecoveryMaskState H K S).R (recoveryBank i) = S.R (recoveryBank i) := by
  simp only [cyclicRecoveryMaskState,
    Function.update_of_ne (CyclicRecoveryPlacement.bank_injective.ne h238),
    Function.update_of_ne (CyclicRecoveryPlacement.bank_injective.ne h239)]

theorem cyclicRecoveryMaskState_values {s : ℕ} (H K : ReplicaHaloProblem s) (S : Stacks 840 A) :
    (cyclicRecoveryMaskState H K S).R (recoveryBank 239) =
      couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span ∧
    (cyclicRecoveryMaskState H K S).R (recoveryBank 238) =
      couplingSourceIntervalMaskSymbols true A s K.t K.band K.origin (K.origin+K.span) K.origin K.span := by
  constructor
  · simp [cyclicRecoveryMaskState,show recoveryBank 239 ≠ recoveryBank 238 by decide]
  · simp [cyclicRecoveryMaskState]

theorem cyclicRecoveryMasks_exec {s : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
    (v : HS 840 Q A U) (S : Stacks 840 A)
    (hl : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk cyclicRecoveryLeftBank S))
    (hr : CouplingIntervalMetadata K.metadataWidth s K.t K.band K.origin (K.origin+K.span) K.origin K.span
      (embStk cyclicRecoveryRightBank S))
    (hlblank : ∀ i : Fin 168, i.val < 32 → S.R (cyclicRecoveryLeftBank i) = [])
    (hrblank : ∀ i : Fin 168, i.val < 32 → S.R (cyclicRecoveryRightBank i) = [])
    (h239 : S.R (recoveryBank 239) = []) (h238 : S.R (recoveryBank 238) = []) :
    ∃ vf m, vf.user = v.user ∧ m ≤ placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K ∧
      Exec body cyclicRecoveryMasks (mk v S) m (mk vf (cyclicRecoveryMaskState H K S)) ∧
      embStk extendCaller (cyclicRecoveryMaskState H K S) = embStk extendCaller S := by
  have offLeft (i : Fin 168) (j : Fin 240) : cyclicRecoveryLeftBank i ≠ recoveryBank j :=
    (CyclicRecoveryPlacement.bank_left_disjoint j _ (.bank i)).symm
  have offRight (i : Fin 168) (j : Fin 240) : cyclicRecoveryRightBank i ≠ recoveryBank j :=
    (CyclicRecoveryPlacement.bank_right_disjoint j _ (.bank i)).symm
  obtain ⟨vf,m,hu,hm,he,_,_⟩ := cyclicReplicaBoundaryMasks_exec (body := body) H K
    cyclicRecoveryLeftBank cyclicRecoveryRightBank
    ((Fin.castLE_injective _).comp CyclicReplicaPlacement.left.coupling.bank_injective)
    ((Fin.castLE_injective _).comp CyclicReplicaPlacement.right.coupling.bank_injective)
    (recoveryBank 239) (recoveryBank 238) (by decide)
    (fun i => offLeft i 239) (fun i => offRight i 238)
    (fun i => offRight i 239) (fun i => offLeft i 238)
    v S hl hr hlblank hrblank h239 h238
  exact ⟨vf,m,hu,hm,he,cyclicRecoveryMaskState_old H K S⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
