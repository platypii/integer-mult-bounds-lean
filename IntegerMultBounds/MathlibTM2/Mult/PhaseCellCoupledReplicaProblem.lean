module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaProblemOfAxis
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryHaloRecoveryPrecision
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingRowValue
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaProblemLayout

/-! The computed coupling rows are ordinary replica inputs. A conserved precision
allowance reuses the first pass's format independently of the piece's boundary size. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

namespace RecoveryAxisBounds
variable {s t p u l : ℕ} [NeZero s] {α d : ℝ}

noncomputable def coupledReplicaProblem (axis : RecoveryAxisBounds s t p u l α d)
    (firstTarget rhsExp target boundaryExp origin span : ℕ) (hfit : origin+span ≤ s)
    (rows : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt)))
    (hallowance : firstTarget+rhsExp = target+
      recoveryRhsExponent p rhsExp boundaryExp (couplingCountExponent p u))
    (hF : ∀ row ∈ rows, ∀ i,
      ‖value (executionPrecision p l firstTarget rhsExp) (row.2 i)‖ ≤ (2 : ℝ)^rhsExp)
    (hY : ∀ row ∈ rows, ∀ i,
      ‖value (executionPrecision p l firstTarget rhsExp) (row.1 i)‖ ≤ (2 : ℝ)^boundaryExp) :
    ReplicaHaloProblem s := by
  let e := recoveryRhsExponent p rhsExp boundaryExp (couplingCountExponent p u)
  let rhs := fun row : (ZMod s → GaussianInt) × (ZMod s → GaussianInt) =>
    guardedCouplingRowField (2^15*p) (executionPrecision p l firstTarget rhsExp)
      t u (PhaseCellBand.width p u) origin (origin+span) true row.1 row.2
  have hp : 0 < p := by have := axis.hp; omega
  have htheta : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity) axis.hθ
  have hq := (executionSizing_of_allowance p l firstTarget rhsExp target e hallowance).1
  apply axis.replicaProblem target e origin span hfit (rows.map rhs)
  intro F hmem i
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hmem
  rw [← hq]
  exact guardedCouplingRowField_norm true hp axis.hst axis.hαu
    htheta axis.hgap axis.hbudget row.1 row.2
    (couplingCountExponent_spec p u) (hF row hr) (fun j _ => hY row hr j) i

theorem coupledReplicaProblem_sizing (axis : RecoveryAxisBounds s t p u l α d)
    (firstTarget rhsExp target boundaryExp origin span : ℕ) (hfit : origin+span ≤ s)
    (rows : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt)))
    (hallowance : firstTarget+rhsExp = target+
      recoveryRhsExponent p rhsExp boundaryExp (couplingCountExponent p u)) hF hY :
    let H := axis.coupledReplicaProblem firstTarget rhsExp target boundaryExp origin span hfit rows hallowance hF hY
    H.precision = executionPrecision p l firstTarget rhsExp ∧
      H.stage = executionStagePrecision p l firstTarget rhsExp ∧
      H.wordWidth = executionWidth p l firstTarget rhsExp ∧ H.Fs.length = rows.length := by
  have h := executionSizing_of_allowance p l firstTarget rhsExp target
    (recoveryRhsExponent p rhsExp boundaryExp (couplingCountExponent p u)) hallowance
  exact ⟨h.1.symm,h.2.1.symm,h.2.2.symm,List.length_map _⟩

/-- Use the joint Schur boundary count for both pieces, including an empty piece. -/
theorem cyclicRecovery_allowance (target rowCount : ℕ) :
    initialSchurTarget p u (boundaryTableBits p target 2 rowCount) 2+2 =
      boundaryHaloRecoveryTarget p target rowCount+
        recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u) :=
  (boundaryHaloRecoveryTarget_allowance p u target 2 rowCount).symm

/-- The two physical pieces share the joint boundary's precision allowance. -/
noncomputable def cyclicPieceRecoveryProblem (axis : RecoveryAxisBounds s t p u l α d)
    (target rowCount origin span : ℕ) (hfit : origin+span ≤ s)
    (rows : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt)))
    (hF : ∀ row ∈ rows, ∀ i,
      ‖value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 rowCount) 2) 2)
        (row.2 i)‖ ≤ (2 : ℝ)^2)
    (hY : ∀ row ∈ rows, ∀ i,
      ‖value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 rowCount) 2) 2)
        (row.1 i)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) : ReplicaHaloProblem s :=
  axis.coupledReplicaProblem (initialSchurTarget p u (boundaryTableBits p target 2 rowCount) 2) 2
    (boundaryHaloRecoveryTarget p target rowCount) (stableInteriorExponent p 2) origin span hfit rows
    (cyclicRecovery_allowance target rowCount) hF hY

theorem cyclicPieceRecoveryProblem_sizing (axis : RecoveryAxisBounds s t p u l α d)
    (target rowCount origin span : ℕ) (hfit : origin+span ≤ s) rows hF hY :
    let H := axis.cyclicPieceRecoveryProblem target rowCount origin span hfit rows hF hY
    let T := initialSchurTarget p u (boundaryTableBits p target 2 rowCount) 2
    H.precision = executionPrecision p l T 2 ∧ H.stage = executionStagePrecision p l T 2 ∧
      H.wordWidth = executionWidth p l T 2 ∧ H.Fs.length = rows.length :=
  axis.coupledReplicaProblem_sizing _ _ _ _ _ _ hfit rows
    (cyclicRecovery_allowance target rowCount) hF hY

theorem cyclicPieceRecoveryProblem_layout (axis : RecoveryAxisBounds s t p u l α d)
    (target rowCount origin span : ℕ) (hfit : origin+span ≤ s)
    (Fs : List (ZMod s → GaussianInt)) hFs rows hF hY (hlen : rows.length = Fs.length) :
    let T := initialSchurTarget p u (boundaryTableBits p target 2 rowCount) 2
    let H := axis.replicaProblem T 2 origin span hfit Fs hFs
    H.SameLayout (axis.cyclicPieceRecoveryProblem target rowCount origin span hfit rows hF hY) := by
  obtain ⟨hq,hstage,hw,hcount⟩ := axis.cyclicPieceRecoveryProblem_sizing
    target rowCount origin span hfit rows hF hY
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,hq,hstage,hw,hcount.trans hlen⟩

end RecoveryAxisBounds
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
