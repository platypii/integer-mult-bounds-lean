module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloNextInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth

/-! Prepare coupling directly from the restored factor-factory bank. The width
is generated from retained precision; no interior solve is required. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast ScalarPlacement

def periodicCouplingWidthBank {A : ℕ} (q : ℕ) (S : Stacks 242 A) : Stacks 242 A :=
  {S with R := Function.update S.R 130 (List.replicate (2*q+8) tick)}

theorem periodicCouplingWidth_bank {A q W N : ℕ} {S : Stacks 242 A}
    (h : PackedPreparedBank q (2*q+8) W N S) :
    PackedPreparedBank q (2*q+8) W N (periodicCouplingWidthBank q S) := by
  apply h.of_runtime_frame (F := periodicCouplingWidthBank q S) rfl
  · intro k hk
    have hn : k ≠ 130 := by intro he; have := congrArg Fin.val he; omega
    simp [periodicCouplingWidthBank,hn]
  · simp [periodicCouplingWidthBank]
  · intro k hk _
    have hn : k ≠ 130 := by intro he; have := congrArg Fin.val he; omega
    simp [periodicCouplingWidthBank,hn]

theorem periodicCouplingWidth_factorPages {A q : ℕ} {S : Stacks 242 A}
    {bo hf df : List (Fin (A+4))} (h : PackedBoundaryFactorPages bo hf df S) :
    PackedBoundaryFactorPages bo hf df (periodicCouplingWidthBank q S) := by
  apply h.of_solution_frame
  intro k hk _
  have hn : k ≠ 130 := by intro he; have := congrArg Fin.val he; omega
  simp [periodicCouplingWidthBank,hn]

theorem periodicCouplingWidth_exec {Q A precision stage q l s t u band a b V W N : ℕ}
    {P U : Type} {body : P → Pr P 242 Q A U}
    (v : HS 242 Q A U) (S : Stacks 242 A)
    (h : PackedHaloBetweenInputs precision stage q l s t u band a b V (2*q+8) W N
      (extendStacks (by decide) S)) :
    ∃ v', v'.user = v.user ∧
      Exec body (generateWordWidth 119 130 135) (mk v S) (8*q+9)
        (mk v' (periodicCouplingWidthBank q S)) ∧
      CouplingReady precision q (2*q+8) s t u band a b (S.R 110)
        (embStk sharedCouplingCoreReg
          (embStk (Fin.castLE (by decide : 168 ≤ 242)) (periodicCouplingWidthBank q S))) := by
  have hbank := h.bank
  simp only [packedBoundaryRecoveryBase,embStk_extendStacks] at hbank
  obtain ⟨v',hu,he⟩ := generateWordWidth_exec (body := body)
    (precision := 119) (width := 130) (tmp := 135) (by decide) q v S
    hbank.workspace.precision (h.scratch 130 (by decide)) (h.scratch 135 (by decide))
  refine ⟨v',hu,he,?_⟩
  let T := embStk (Fin.castLE (by decide : 168 ≤ 242)) (periodicCouplingWidthBank q S)
  have hnative : embStk packedCellCoreReg T =
      releasedCellBank [] (S.R 110) (S.R 93) S.inp S.out := by
    have hh := h.native_bank (S.R 110) rfl
    refine Stacks.ext rfl rfl ?_ ?_
    · funext i
      have hhL := h.left_low (⟨i.val,by have := i.isLt; omega⟩ : Fin 248)
        (by change i.val < 140; have := i.isLt; omega)
      simpa [T,embStk,packedCellCoreReg,periodicCouplingWidthBank,extendStacks,releasedCellBank,Fin.castLE,
        show i.val < 242 by have := i.isLt; omega] using hhL
    · funext i
      have hhR := congrArg (fun F : Stacks 117 A => F.R i) hh
      have hi := i.isLt
      have hn : (⟨i.val,by omega⟩ : Fin 242) ≠ 130 := by
        intro heq; have hv : i.val = 130 := congrArg Fin.val heq; omega
      simpa [T,embStk,packedCellCoreReg,packedRecoveryRuntimeReg,periodicCouplingWidthBank,
        extendStacks,show i.val < 242 by omega,hn] using hhR
  apply sharedCouplingHeaders_ready T [] (S.R 110) (S.R 93) S.inp S.out hnative
  · simpa [T,embStk,periodicCouplingWidthBank,packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.precision
  · simpa [T,embStk,periodicCouplingWidthBank,packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.fraction
  · simpa [T,embStk,periodicCouplingWidthBank,packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.axis
  · simpa [T,embStk,periodicCouplingWidthBank,packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.period
  · simpa [T,embStk,periodicCouplingWidthBank,packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.parameter
  · simpa [T,embStk,periodicCouplingWidthBank,packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.bandwidth
  · simpa [T,embStk,periodicCouplingWidthBank,packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.lower
  · simpa [T,embStk,periodicCouplingWidthBank,packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.upper
  · simp [T,embStk,periodicCouplingWidthBank]
  · intro k hk
    have hi : k.val < 140 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    have hhL := h.left_low (⟨k.val,by omega⟩ : Fin 248) hi
    simpa [T,embStk,periodicCouplingWidthBank,extendStacks,Fin.castLE,show k.val < 242 by omega] using hhL

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
