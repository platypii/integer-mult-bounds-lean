module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryRhsInput

/-! The complete local handoff from the computed boundary solution to recovery
coupling inputs, retaining factors and caller-owned suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedBoundaryRecoveryInputs : Pr P 248 Q A U :=
  .seq packedBoundaryRecoveryField packedRecoveryRhsInput

def packedBoundaryRecoveryInputsCost (V N n w : ℕ) : ℕ :=
  packedBoundaryRecoveryFieldCost V N n w+packedRecoveryRhsInputCost N n w

theorem packedBoundaryRecoveryInputs_exec {s t origin N : ℕ} [NeZero s]
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
    (residual rhs rhsTail : List (Fin (A+4)))
    (hresidual : residual.length = N*w) (hrhs : rhs.length = N*w)
    (hrhsSource : S.R 110 = residual++(rhs++rhsTail))
    (hfreshL : ∀ i : Fin 248, 242 ≤ i.val → S.L i = [])
    (hfreshR : ∀ i : Fin 248, 242 ≤ i.val → S.R i = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ packedBoundaryRecoveryInputsCost V N (haloBoundary s t band a b).card w ∧
      Exec body packedBoundaryRecoveryInputs (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update S.R 238 solutionTail) 132
            (cstream A w (packedInterval origin N
              (boundarySolutionField (haloBoundary s t band a b) solution))++outputTail))
          110 (rhs++rhsTail)) 93 (rhs++S.R 93)) 116 []) 167 [])}) := by
  let B := haloBoundary s t band a b
  let G := boundarySolutionField B solution
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := packedBoundaryRecoveryField_exec (body := body)
    hst hA V band a b q w W hNV hb hfit hB solution hlen solutionTail words outputTail hwords
    v S hwork hready h143 hcount hsrc hN hmask houtput hfreshL hfreshR
  let S₁ : Stacks 248 A := {S with R := (Function.update (Function.update (Function.update S.R
    238 solutionTail) 246 (List.replicate N tick)) 132
      (cstream A w (packedInterval origin N G)++outputTail))}
  have hclean₁ : ∀ i ∈ ([247,242,243,244] : List (Fin 248)), S₁.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simpa [S₁] using hfreshR _ (by decide)
  have hw : (S.R 174).length = w := packedBoundaryRecovery_width hready
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedRecoveryRhsInput_exec N B.card w residual rhs rhsTail
    hresidual hrhs v₁ S₁ (by simp [S₁]) (by simpa [S₁] using hw)
    (by simp [S₁,hcount,B]) (by simp [S₁,hmask])
    (by simpa [S₁] using hrhsSource) hclean₁
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  have h246 := hfreshR 246 (by decide)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h116 : i = 116
  · subst i; simp
  by_cases h167 : i = 167
  · subst i; simp
  by_cases h93 : i = 93
  · subst i; simp [S₁]
  by_cases h110 : i = 110
  · subst i; simp [S₁]
  by_cases h132 : i = 132
  · subst i; simp [S₁,G,B]
  by_cases hi246 : i = 246
  · subst i; simp [h246]
  · simp [S₁,G,B,h116,h167,h93,h110,h132,hi246]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
