module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPreparedResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactorFrame

/-! The reusable physical workspace needed by normalization, solve and unscale.
Factor data and RHS semantics are supplied separately. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

structure PackedBoundarySolveWorkspace {A : ℕ} (q : ℕ) (S : Stacks 242 A) : Prop where
  left : ∀ i : Fin 224, (embStk packedBoundaryFactorReg S).L (preparedBoundaryCoreReg i) = []
  mul : ∀ i : Fin 64, (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)).R
    (boundaryFactorMulReg i) = []
  precision : ((embStk packedBoundaryFactorReg S).R 119).length = q
  exponent : (embStk packedBoundaryFactorReg S).R 223 = []
  scalar : (embStk packedBoundaryFactorReg S).R 184 = []
  table : (embStk packedBoundaryFactorReg S).R 220 = []
  padding : (embStk packedBoundaryFactorReg S).R 221 = []
  swap : (embStk packedBoundaryFactorReg S).R 225 = []

/-- The numerical bank shared by successive packed inputs. Input encoding and
output ownership are separate obligations of the batch cursor. -/
structure PackedPreparedBank {A : ℕ} (q w W N : ℕ) (S : Stacks 242 A) : Prop where
  ready : BoundarySolveReady (boundaryFactorState
    (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S))) q w W N
  workspace : PackedBoundarySolveWorkspace q S

/-- Recovery restores native arithmetic scratch and preserves the retained
precision and high workspace. Its consumed solution buffer is irrelevant. -/
theorem PackedBoundarySolveWorkspace.of_recovery_frame {A q : ℕ} {S F : Stacks 242 A}
    (h : PackedBoundarySolveWorkspace q S) (hleft : F.L = S.L)
    (hmul : ∀ i : Fin 64, F.R ⟨i.val,by omega⟩ = [])
    (hprecision : F.R 119 = S.R 119)
    (hhigh : ∀ k : Fin 242, 168 ≤ k.val → k ≠ 238 → F.R k = S.R k) :
    PackedBoundarySolveWorkspace q F := by
  constructor
  · intro i
    change F.L _ = []
    rw [hleft]
    exact h.left i
  · intro i
    have hi := i.isLt
    simpa [embStk,preparedBoundaryCoreReg,packedBoundaryFactorReg,boundaryFactorMulReg,
      Fin.ext_iff,show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
      show i.val ≠ 206 by omega,show i.val < 154 by omega] using hmul i
  · change (F.R 119).length = q
    rw [hprecision]
    exact h.precision
  · exact (hhigh 237 (by decide) (by decide)).trans h.exponent
  · exact (hhigh 198 (by decide) (by decide)).trans h.scalar
  · exact (hhigh 234 (by decide) (by decide)).trans h.table
  · exact (hhigh 235 (by decide) (by decide)).trans h.padding
  · exact (hhigh 239 (by decide) (by decide)).trans h.swap

/-- Recovery may consume the solution and replace the RHS while retaining the
bank needed by the next input. -/
theorem PackedPreparedBank.of_recovery_frame {A q w W N : ℕ} {S F : Stacks 242 A}
    (h : PackedPreparedBank q w W N S) (hleft : F.L = S.L)
    (hmul : ∀ i : Fin 64, F.R ⟨i.val,by omega⟩ = [])
    (hprecision : F.R 119 = S.R 119)
    (hhigh : ∀ k : Fin 242, 168 ≤ k.val → k ≠ 238 → F.R k = S.R k) :
    PackedPreparedBank q w W N F := by
  constructor
  · rw [packedBoundaryFactorState_of_solution_frame S F hhigh]
    exact h.ready.update_vk _
  · exact h.workspace.of_recovery_frame hleft hmul hprecision hhigh

/-- A low runtime call can reuse the prepared factor bank when its physical
frame preserves multiplier scratch, precision and the high factor workspace. -/
theorem PackedPreparedBank.of_runtime_frame {A q w W N : ℕ} {S F : Stacks 242 A}
    (h : PackedPreparedBank q w W N S) (hleft : F.L = S.L)
    (hlow : ∀ k : Fin 242, k.val < 64 → F.R k = S.R k)
    (hprecision : F.R 119 = S.R 119)
    (hhigh : ∀ k : Fin 242, 168 ≤ k.val → k ≠ 238 → F.R k = S.R k) :
    PackedPreparedBank q w W N F := by
  apply h.of_recovery_frame hleft ?_ hprecision hhigh
  intro i
  rw [hlow _ i.isLt]
  have hi := i.isLt
  simpa [embStk,preparedBoundaryCoreReg,packedBoundaryFactorReg,boundaryFactorMulReg,
    Fin.ext_iff,show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
    show i.val ≠ 206 by omega,show i.val < 154 by omega] using h.workspace.mul i

/-- Publishing a solved RHS preserves the numerical workspace. -/
theorem PackedBoundarySolveWorkspace.publish {A q : ℕ} {S : Stacks 242 A}
    (h : PackedBoundarySolveWorkspace q S) (output : List (Fin (A+4))) :
    PackedBoundarySolveWorkspace q
      {S with R := (Function.update (Function.update S.R 143 []) 238 (output++S.R 238))} := by
  constructor
  · exact h.left
  · intro i
    have hi := i.isLt
    simpa [embStk,preparedBoundaryCoreReg,packedBoundaryFactorReg,boundaryFactorMulReg,
      Fin.ext_iff,show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
      show i.val ≠ 206 by omega,show i.val < 154 by omega,
      show i.val ≠ 238 by omega] using h.mul i
  · exact h.precision
  · exact h.exponent
  · exact h.scalar
  · exact h.table
  · exact h.padding
  · exact h.swap

/-- The boundary solve publishes its solution while retaining a complete bank
for recovery and the next input. -/
theorem PackedPreparedBank.publish {A q w W N : ℕ} {S : Stacks 242 A}
    (h : PackedPreparedBank q w W N S) (output : List (Fin (A+4))) :
    PackedPreparedBank q w W N
      {S with R := Function.update (Function.update S.R 143 []) 238 (output++S.R 238)} := by
  exact ⟨packedPreparedResidualSolve_ready S output h.ready,h.workspace.publish output⟩

/-- The retained numerical state supplies every old-bank temporary used by
boundary recovery. The remaining inverse-fold counters live in fresh ports. -/
theorem packedBoundaryRecovery_clean {A q w W N : ℕ} {S : Stacks 242 A}
    (hwork : PackedBoundarySolveWorkspace q S)
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S))) q w W N) :
    ∀ i ∈ ([231,239,198,237,222,225,215,229] : List (Fin 242)), S.R i = [] := by
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hready.empty .dout (by decide)
  · exact hwork.swap
  · exact hwork.scalar
  · exact hwork.exponent
  · exact hready.empty .ya (by decide)
  · exact hready.empty .xs (by decide)
  · exact hready.empty .tC (by decide)
  · exact hready.empty .ac2 (by decide)

/-- Recovery uses the solver's retained word width directly. -/
theorem packedBoundaryRecovery_width {A q w W N : ℕ} {S : Stacks 242 A}
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S))) q w W N) :
    (S.R 174).length = w :=
  hready.ready.wn

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {A Q : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

/-- Input-independent numerical certificate for one computed Schur system. -/
structure PreparedBoundaryColumns (A p bits q w W : ℕ) {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (columns : List (ZMod s → GaussianInt)) : Prop where
  length : columns.length = B.card
  format : ColumnFamilyFormat w columns
  stage : StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
    (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
    (2+(B.card : ℝ)*(1/(2 : ℝ)^bits))

/-- Run the existing boundary kernel directly from the reusable bank contract. -/
theorem packedPreparedResidualSolve_bank_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hp : 2 ≤ p) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    PreparedBoundaryColumns A p bits q w W B columns →
    ∀ (b : List GaussianInt), b.length = B.card →
    (∀ x ∈ b, |gv q x.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q x.im| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    ∀ (v : HS 242 Q A U) (S : Stacks 242 A),
    let T := embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)
    let σ := boundaryFactorState T
    PackedPreparedBank q w W B.card S →
    σ .vk = cstream A w b →
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt))) S →
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedResidualSolveCost q w B.card W ∧
      Exec body (packedPreparedResidualSolve hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 143 []) 238
          (cstream A w ((bandSolveVec q W Lc Uc rcs (b.map (normalizeBoundaryWord q (q/2-1)))).map
            (unscaleBoundaryWord q))++S.R 238))}) := by
  dsimp only
  intro hcolumns b hb hbound v S hbank hvk hpages
  exact packedPreparedResidualSolve_exec hQ hA p u l target rhsExp B W columns hp hcolumns.length
    hcolumns.format hcolumns.stage b hb hbound v S hbank.workspace.left hbank.workspace.mul
    hbank.ready hvk hpages.lower hpages.upper hpages.reciprocal hbank.workspace.precision hbank.workspace.exponent
    hbank.workspace.scalar hbank.workspace.table hbank.workspace.padding hbank.workspace.swap

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
