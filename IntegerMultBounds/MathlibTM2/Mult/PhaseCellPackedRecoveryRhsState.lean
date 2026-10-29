module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryInteriorReady

/-! The exact recovery-RHS poststate supplies the second interior solve's
initializer. Retained headers and released scratch are transported once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

def packedRecoveryRhsState {A s : ℕ} (w a b : ℕ) (Y R C : ZMod s → GaussianInt)
    (solutionTail outputTail rhsTail : List (Fin (A+4))) (S : Stacks 248 A) : Stacks 248 A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update
    (Function.update S.R 238 solutionTail) 132 (cstream A w (packedInterval a (b-a) Y)++outputTail))
    110 (cstream A w (packedInterval a (b-a) R)++
      (cstream A w (packedInterval a (b-a) C)++rhsTail))) 116 []) 167 [])}

theorem packedRecoveryInteriorReady_after_rhs {A precision stage q l s t u band a b V w : ℕ} [NeZero s]
    (hab : a ≤ b) (hb : b ≤ s) (Y R C : ZMod s → GaussianInt)
    (solutionTail outputTail rhsTail : List (Fin (A+4))) (S : Stacks 248 A)
    (hwork : PackedBoundarySolveWorkspace q (embStk packedBoundaryRecoveryBase S))
    (hheaders : CouplingMasterHeaders precision q w s t u band a b (embStk packedRecoveryRuntimeReg S))
    (hstage : (S.R 118).length = stage) (hlevel : (S.R 120).length = l)
    (hnative : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → i ≠ 116 → S.R ⟨i.val,by omega⟩ = [])
    (hmeta : CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedRecoveryRuntimeReg S))
    (hclean : ∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 248)), S.R k = [])
    (hfresh : ∀ k : Fin 248, 242 ≤ k.val → S.R k = []) :
    PackedRecoveryInteriorReady precision stage q l s t u band a b V w
      (cstream A w (packedInterval a (b-a) R)++(cstream A w (packedInterval a (b-a) C)++rhsTail))
      (cstream A w (packedInterval a (b-a) Y)) outputTail
      (packedRecoveryRhsState w a b Y R C solutionTail outputTail rhsTail S) := by
  let F := packedRecoveryRhsState w a b Y R C solutionTail outputTail rhsTail S
  have hworkF : PackedBoundarySolveWorkspace q (embStk packedBoundaryRecoveryBase F) := by
    constructor
    · exact hwork.left
    · intro i
      have hi := i.isLt
      simpa [F,packedRecoveryRhsState,embStk,packedBoundaryRecoveryBase,preparedBoundaryCoreReg,
        packedBoundaryFactorReg,boundaryFactorMulReg,Fin.ext_iff,
        show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,show i.val ≠ 206 by omega,
        show i.val < 154 by omega,show i.val ≠ 238 by omega,show i.val ≠ 132 by omega,
        show i.val ≠ 110 by omega,show i.val ≠ 116 by omega,show i.val ≠ 167 by omega] using hwork.mul i
    · exact hwork.precision
    · exact hwork.exponent
    · exact hwork.scalar
    · exact hwork.table
    · exact hwork.padding
    · exact hwork.swap
  have hheadersF := hheaders.of_frame (F := embStk packedRecoveryRuntimeReg F) (by
    intro k hk
    simp only [couplingMasterPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have hnativeF : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → F.R ⟨i.val,by omega⟩ = [] := by
    intro i h93 h110
    by_cases h116 : i = 116
    · subst i; simp [F,packedRecoveryRhsState]
    have hi := i.isLt
    simpa [F,packedRecoveryRhsState,Fin.ext_iff,
      show i.val ≠ 93 from fun he => h93 (Fin.ext he),
      show i.val ≠ 110 from fun he => h110 (Fin.ext he),
      show i.val ≠ 116 from fun he => h116 (Fin.ext he),
      show i.val ≠ 132 by omega,show i.val ≠ 167 by omega,show i.val ≠ 238 by omega]
      using hnative i h93 h110 h116
  have hmetaF : CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedRecoveryRuntimeReg F) := by
    constructor
    · exact hmeta.width
    · intro k hk
      simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hmeta.encoded _ (by decide)
  have hcleanF : ∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 248)), F.R k = [] := by
    intro k hk
    have hc := hclean k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [F,packedRecoveryRhsState] using hc
  have hfreshF : ∀ k : Fin 248, 242 ≤ k.val → F.R k = [] := by
    intro k hk
    simpa [F,packedRecoveryRhsState,Function.update_apply,Fin.ext_iff,
      show k.val ≠ 238 by omega,show k.val ≠ 132 by omega,show k.val ≠ 110 by omega,
      show k.val ≠ 116 by omega,show k.val ≠ 167 by omega] using hfresh k hk
  exact packedRecoveryInteriorReady_of_retained _ _ outputTail F hworkF hheadersF hstage hlevel
    hnativeF (by simp [F,packedRecoveryRhsState]) hmetaF (by simp [F,packedRecoveryRhsState])
    (by simp only [length_cstream,packedInterval_length Y (show a+(b-a) ≤ s by omega)]) hcleanF hfreshF

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
