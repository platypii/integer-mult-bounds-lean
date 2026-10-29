module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryCoupling

/-! Generate the actual local recovery RHS from the computed folded boundary
solution, reusing the retained coefficient page and original RHS. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

noncomputable def packedBoundaryRecoveryRhs (hQ : SS.states ≤ Q) : Pr P 248 Q A U :=
  .seq packedBoundaryRecoveryInputs (packedRecoveryCoupling hQ)

theorem packedBoundaryRecoveryRhs_exec (hQ : SS.states ≤ Q) {s t origin N : ℕ} [NeZero s]
    (hst : s < t) (hA : 96 ≤ A) (V band a b precision q w W : ℕ) (hNV : N < 2^V)
    (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (solution : List GaussianInt) (hlen : solution.length = (haloBoundary s t band a b).card)
    (C : ZMod s → GaussianInt)
    (hfits : ∀ z ∈ solution, Fits w z)
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
    (residual rhsTail : List (Fin (A+4)))
    (hresidual : residual.length = N*w)
    (hrhsSource : S.R 110 = residual++(cstream A w (packedInterval origin N C)++rhsTail))
    (hfreshL : ∀ i : Fin 248, 242 ≤ i.val → S.L i = [])
    (hfreshR : ∀ i : Fin 248, 242 ≤ i.val → S.R i = [])
    (hheaders : CouplingMasterHeaders precision q w s t u band a b (embStk packedRecoveryRuntimeReg S))
    (hnative : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → i ≠ 116 → S.R ⟨i.val,by omega⟩ = [])
    (hclean : ∀ k ∈ ([127,135,158,166] : List (Fin 248)), S.R k = [])
    (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (hlocalOrigin : origin = a) (hlocalEnd : b = a+N)
    (hsep : N+band ≤ s) (haS : a ≤ s) (hbandS : band ≤ s)
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval precision q s t u band a b origin N))
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval precision q s t u band a b origin N).length)
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords precision q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : origin+(N+2*band)+s < 2^V)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N (embStk packedRecoveryRuntimeReg S)) :
    let G := boundarySolutionField (haloBoundary s t band a b) solution
    ∃ v' n, v'.user = v.user ∧
      n ≤ packedBoundaryRecoveryInputsCost V N (haloBoundary s t band a b).card w+
        preparedSharedLocalFeedCouplingIntervalCost true precision q w s t u band a b origin N V ∧
      Exec body (packedBoundaryRecoveryRhs hQ) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update
          (Function.update S.R 238 solutionTail) 132
            (cstream A w (packedInterval origin N G)++outputTail))
          110 (cstream A w (packedInterval origin N
            (guardedCouplingRowField precision q t u band a b true G C))++
            (cstream A w (packedInterval origin N C)++rhsTail))) 116 []) 167 [])}) := by
  dsimp only
  let B := haloBoundary s t band a b
  let G := boundarySolutionField B solution
  let rhs := cstream A w (packedInterval origin N C)
  have hrhs : rhs.length = N*w := by simp [rhs,length_cstream,packedInterval_length C hfit]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := packedBoundaryRecoveryInputs_exec (body := body)
    hst (by omega) V band a b q w W hNV hb hfit hB solution hlen solutionTail words outputTail hwords
    v S hwork hready h143 hcount hsrc hN hmask houtput residual rhs rhsTail hresidual hrhs
    hrhsSource hfreshL hfreshR
  let S₁ : Stacks 248 A := {S with R := (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update S.R 238 solutionTail) 132
      (cstream A w (packedInterval origin N G)++outputTail))
    110 (rhs++rhsTail)) 93 (rhs++S.R 93)) 116 []) 167 [])}
  have hwork₁ : PackedBoundarySolveWorkspace q (embStk packedBoundaryRecoveryBase S₁) := by
    constructor
    · exact hwork.left
    · intro i
      have hi := i.isLt
      simpa [S₁,embStk,packedBoundaryRecoveryBase,preparedBoundaryCoreReg,packedBoundaryFactorReg,
        boundaryFactorMulReg,Fin.ext_iff,show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
        show i.val ≠ 206 by omega,show i.val < 154 by omega,
        show i.val ≠ 93 by omega,show i.val ≠ 110 by omega,show i.val ≠ 116 by omega,
        show i.val ≠ 132 by omega,show i.val ≠ 167 by omega,show i.val ≠ 238 by omega] using hwork.mul i
    · exact hwork.precision
    · exact hwork.exponent
    · exact hwork.scalar
    · exact hwork.table
    · exact hwork.padding
    · exact hwork.swap
  have hheaders₁ := hheaders.of_frame (F := embStk packedRecoveryRuntimeReg S₁) (by
    intro k hk
    simp only [couplingMasterPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have hnative₁ : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → S₁.R ⟨i.val,by omega⟩ = [] := by
    intro i h93i h110i
    by_cases h116i : i = 116
    · subst i; simp [S₁]
    have hi := i.isLt
    simpa [S₁,Fin.ext_iff,show i.val ≠ 93 from fun he => h93i (Fin.ext he),
      show i.val ≠ 110 from fun he => h110i (Fin.ext he),
      show i.val ≠ 116 from fun he => h116i (Fin.ext he),
      show i.val ≠ 132 by omega,show i.val ≠ 167 by omega,show i.val ≠ 238 by omega]
      using hnative i h93i h110i h116i
  have hgeometry₁ : CouplingIntervalMetadata V s t band a b origin N (embStk packedRecoveryRuntimeReg S₁) := by
    constructor
    · exact hgeometry.width
    · intro k hk
      simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hgeometry.encoded _ (by decide)
  have hclean₁ : ∀ k ∈ ([127,143,166,158,135,167] : List (Fin 248)), S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [S₁] using hclean 127 (by decide)
    · simpa [S₁] using h143
    · simpa [S₁] using hclean 166 (by decide)
    · simpa [S₁] using hclean 158 (by decide)
    · simpa [S₁] using hclean 135 (by decide)
    · simp [S₁]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedRecoveryCoupling_exec (body := body) hQ hA hw5 hqw hst G C
    hfit outputTail [] (S.R 93) v₁ S₁ hwork₁ hheaders₁ hnative₁ hlocalOrigin hlocalEnd hsep
    (by simp [S₁,hlocalOrigin]) hrows (by simpa [S₁] using hpage) (by simp [S₁,rhs])
    (boundarySolutionField_fits w B solution hlen hfits) has V h139 haS hb hbandS hwide hfitV
    hgeometry₁ hclean₁
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h110 : i = 110
  · subst i; simp [S₁,rhs,G,B]
  by_cases h93 : i = 93
  · subst i; simp [S₁]
  · simp [S₁,rhs,G,B,h110,h93,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
