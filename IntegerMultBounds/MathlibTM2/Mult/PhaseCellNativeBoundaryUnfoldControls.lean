module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeBoundaryUnfoldWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualBatchRecoveryInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolveReady

/-! Recover inverse-fold controls and numerical scratch from the shared solver
endpoint. Only private and newly allocated workspace needs separate framing. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem nativeBoundaryUnfold_controls {A q w W N : ℕ} (S : Stacks 240 A)
    (hwork : NativeBoundaryUnfoldWorkspace N (embStk (Fin.castLE (by decide : 234 ≤ 240)) S))
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk (Fin.castLE (by decide : 224 ≤ 240)) S)) q w W N) :
    (S.R 116).length = N ∧ (S.R 192).length = N ∧ (S.R 160).length = w ∧ S.R 217 = [] ∧
    (∀ i ∈ ([(184 : Fin 240),223,208,211,201,215]), S.R i = []) ∧
    (∀ i : Fin 64, (embStk sharedPageBoundaryUnfoldReg S).R (boundaryFactorMulReg i) = []) := by
  refine ⟨hwork.count,?_,?_,?_,?_,?_⟩
  · simpa [boundaryFactorState,embStk,boundaryFactorReg] using hready.sn
  · simpa [boundaryFactorState,embStk,boundaryFactorReg] using hready.ready.wn
  · simpa [boundaryFactorState,embStk,boundaryFactorReg] using hready.empty .dout (by simp [boundarySolveScratch])
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hwork.scalar
    · exact hwork.exponent
    · simpa [boundaryFactorState,embStk,boundaryFactorReg] using hready.empty .ya (by simp [boundarySolveScratch])
    · simpa [boundaryFactorState,embStk,boundaryFactorReg] using hready.empty .xs (by simp [boundarySolveScratch])
    · simpa [boundaryFactorState,embStk,boundaryFactorReg] using hready.empty .tC (by simp [boundarySolveScratch])
    · simpa [boundaryFactorState,embStk,boundaryFactorReg] using hready.empty .ac2 (by simp [boundarySolveScratch])
  · intro i
    have hreg : sharedPageBoundaryUnfoldReg (boundaryFactorMulReg i) = (⟨i.val,by have := i.isLt; omega⟩ : Fin 240) := by
      apply Fin.ext
      have hi := i.isLt
      change (if i.val = 189 then 234 else if i.val = 191 then 235 else
        if i.val = 198 then 236 else if i.val = 204 then 237 else i.val) = i.val
      split_ifs <;> omega
    simpa only [embStk,Function.comp_apply,hreg,Fin.castLE] using hwork.mul i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
