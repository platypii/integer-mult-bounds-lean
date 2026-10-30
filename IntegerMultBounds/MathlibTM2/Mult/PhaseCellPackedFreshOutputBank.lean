module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedFreshOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryRetainedPorts

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- The packed output is disjoint from the retained factors and arithmetic bank. -/
theorem PackedPreparedBank.update_output {A q w W N : ℕ} {S : Stacks 248 A}
    (h : PackedPreparedBank q w W N (embStk packedBoundaryRecoveryBase S))
    (output : List (Fin (A+4))) :
    PackedPreparedBank q w W N
      (embStk packedBoundaryRecoveryBase {S with R := Function.update S.R 132 output}) := by
  apply h.of_recovery_frame
  · rfl
  · intro i
    have hi := i.isLt
    have hm := h.workspace.mul i
    simpa [embStk,packedBoundaryRecoveryBase,preparedBoundaryCoreReg,packedBoundaryFactorReg,
      boundaryFactorMulReg,Fin.ext_iff,show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,
      show i.val ≠ 206 by omega,show i.val < 154 by omega,show i.val ≠ 132 by omega] using hm
  · rfl
  · intro k hk hne
    have h132 : packedBoundaryRecoveryBase k ≠ 132 := by
      intro he; have hv := congrArg Fin.val he; change k.val = 132 at hv; omega
    exact Function.update_of_ne h132 _ _

theorem PackedHaloRetainedHeaders.update_output
    {A P stage q l s t u band a b V w : ℕ} {S : Stacks 248 A}
    (h : PackedHaloRetainedHeaders P stage q l s t u band a b V w
      (embStk packedRecoveryRuntimeReg S)) (output : List (Fin (A+4))) :
    PackedHaloRetainedHeaders P stage q l s t u band a b V w
      (embStk packedRecoveryRuntimeReg {S with R := Function.update S.R 132 output}) := by
  apply h.of_frame
  intro k hk
  have h132 : packedRecoveryRuntimeReg k ≠ 132 := by
    intro he
    apply (haloRetainedHeaderPorts_safe k hk).2.1
    apply Fin.ext
    simpa [packedRecoveryRuntimeReg] using congrArg (fun i : Fin 248 => i.val) he
  exact Function.update_of_ne h132 _ _

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

theorem packedFreshOutput_prepared_exec (V N w q W boundaryCount : ℕ) (hNV : N < 2^V)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hN : S.R 165 = binSyms V N)
    (hclean : ∀ i ∈ ([0,1,2,246,247,242,243] : List (Fin 248)), S.R i = [])
    (hbank : PackedPreparedBank q w W boundaryCount (embStk packedBoundaryRecoveryBase S)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedFreshOutputCost V N w ∧
      Exec body packedFreshOutput (mk v S) n
        (mk v' {S with R := Function.update S.R 132 (cstream A w (List.replicate N 0)++S.R 132)}) ∧
      PackedPreparedBank q w W boundaryCount (embStk packedBoundaryRecoveryBase
        {S with R := Function.update S.R 132 (cstream A w (List.replicate N 0)++S.R 132)}) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase S) →
        PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase
          {S with R := Function.update S.R 132 (cstream A w (List.replicate N 0)++S.R 132)})) := by
  obtain ⟨v',n,hu,hn,he⟩ := packedFreshOutput_exec V N w hNV v S hN hbank.ready.ready.wn hclean
  refine ⟨v',n,hu,hn,he,hbank.update_output _,?_⟩
  intro bo hf df hpages
  apply hpages.of_solution_frame
  intro k hk hne
  have h132 : packedBoundaryRecoveryBase k ≠ 132 := by
    intro he; have hv := congrArg Fin.val he; change k.val = 132 at hv; omega
  exact Function.update_of_ne h132 _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
