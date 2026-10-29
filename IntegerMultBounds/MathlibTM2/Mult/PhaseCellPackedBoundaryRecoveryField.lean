module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryBoundaryPublish

/-! Execute inverse folding and local boundary publication from the boundary
solver's retained state. The first interior buffer is reused for recovery. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedBoundaryRecoveryField : Pr P 248 Q A U :=
  .seq packedBoundarySolutionUnfold packedRecoveryBoundaryBuffer

def packedBoundaryRecoveryFieldCost (V N n w : ℕ) : ℕ :=
  ScalarPlacement.moveCountedLineCost n w +
    (generatedBoundaryUnfoldCost n w+n*(12*w+9)+12) +
    (packedRecoveryDestinationCost V N w+(N*(6*w+10)+6))

theorem packedBoundaryRecoveryField_exec {s t origin N : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (V band a b q w W : ℕ) (hNV : N < 2^V)
    (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (solution : List GaussianInt) (hlen : solution.length = (haloBoundary s t band a b).card)
    (solutionTail words outputTail : List (Fin (A+4))) (hwords : words.length = N*w)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hwork : PackedBoundarySolveWorkspace q (embStk packedBoundaryRecoveryBase S))
    (hready : BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg
      (embStk packedBoundaryFactorReg (embStk packedBoundaryRecoveryBase S)))) q w W
      (haloBoundary s t band a b).card)
    (h143 : S.R 143 = []) (hcount : S.R 116 = List.replicate (haloBoundary s t band a b).card tick)
    (hsrc : S.R 238 = cstream A w solution++solutionTail)
    (hN : S.R 165 = binSyms V N)
    (hmask : S.R 167 = couplingSourceIntervalMaskSymbols true A s t band a b origin N)
    (houtput : S.R 132 = words++outputTail)
    (hfreshL : ∀ i : Fin 248, 242 ≤ i.val → S.L i = [])
    (hfreshR : ∀ i : Fin 248, 242 ≤ i.val → S.R i = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ packedBoundaryRecoveryFieldCost V N (haloBoundary s t band a b).card w ∧
      Exec body packedBoundaryRecoveryField (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          238 solutionTail) 246 (List.replicate N tick)) 132
          (cstream A w (packedInterval origin N
            (boundarySolutionField (haloBoundary s t band a b) solution))++outputTail))}) := by
  let B := haloBoundary s t band a b
  let G := boundarySolutionField B solution
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := packedBoundaryRecoveryUnfold_exec hA q w W B solution hlen
    solutionTail v S hwork hready h143 hcount hsrc hfreshL hfreshR
  let S₁ : Stacks 248 A := {S with R := (Function.update (Function.update (Function.update S.R
    238 solutionTail) 231 []) 245 (cstream A w ((bOrder s B).map G)))}
  have hlow (i : Fin 64) : S.R ⟨i.val,by omega⟩ = [] := by
    have hi := i.isLt
    simpa [embStk,packedBoundaryRecoveryBase,preparedBoundaryCoreReg,
      packedBoundaryFactorReg,boundaryFactorMulReg,Fin.ext_iff,
      show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
      show i.val ≠ 206 by omega,show i.val < 154 by omega] using hwork.mul i
  have hclean₁ : ∀ i ∈ ([0,1,2,246,247,242,243,244] : List (Fin 248)), S₁.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [S₁] using hlow 0
    · simpa [S₁] using hlow 1
    · simpa [S₁] using hlow 2
    · simpa [S₁] using hfreshR 246 (by decide)
    · simpa [S₁] using hfreshR 247 (by decide)
    · simpa [S₁] using hfreshR 242 (by decide)
    · simpa [S₁] using hfreshR 243 (by decide)
    · simpa [S₁] using hfreshR 244 (by decide)
  have hw : (S.R 174).length = w := packedBoundaryRecovery_width hready
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedRecoveryBoundaryBuffer_exec hst hA V band a b w hNV
    hb hfit hB G (boundarySolutionField_off B solution) words outputTail hwords v₁ S₁
    (by simpa [S₁] using hN) (by simpa [S₁] using hw) (by simp [S₁,B])
    (by simpa [S₁] using hmask) (by simpa [S₁] using houtput) hclean₁
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  have h231 : S.R 231 = [] := packedBoundaryRecovery_clean hwork hready 231 (by decide)
  have h245 := hfreshR 245 (by decide)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h132 : i = 132 <;> by_cases h246 : i = 246 <;>
    by_cases hi231 : i = 231 <;> by_cases hi245 : i = 245 <;>
    simp [S₁,h132,h246,hi231,hi245,h231,h245,G,B]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
