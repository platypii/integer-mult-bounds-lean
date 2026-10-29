module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactorFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorStock

/-! The packed halo program occupies the low bank beside retained factors. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

def packedHaloRuntimeReg (i : Fin 168) : Fin 242 := ⟨i.val,by omega⟩

theorem packedHaloRuntimeReg_injective : Function.Injective packedHaloRuntimeReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 242 => k.val) he)

theorem packedHaloRuntime_high_frame {A : ℕ} (S : Stacks 242 A) (F : Stacks 168 A)
    (k : Fin 242) (hk : 168 ≤ k.val) :
    (embOvr packedHaloRuntimeReg F.get S).L k = S.L k ∧
      (embOvr packedHaloRuntimeReg F.get S).R k = S.R k := by
  apply embOvr_off
  intro i he
  have hv := congrArg (fun j : Fin 242 => j.val) he
  change i.val = k.val at hv
  have hi := i.isLt
  omega

/-- The complete halo program can run between factor generation and solve. -/
theorem packedBoundarySolveReady_halo {A q w W N : ℕ} (S : Stacks 242 A) (F : Stacks 168 A)
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S))) q w W N) :
    BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg
      (embStk packedBoundaryFactorReg (embOvr packedHaloRuntimeReg F.get S)))) q w W N := by
  exact packedBoundarySolveReady_of_high_frame _ _
    (fun k hk => (packedHaloRuntime_high_frame S F k hk).2) hready

theorem packedBoundaryFactorStock_of_high_frame {A D : ℕ} (S F : Stacks 242 A)
    (hframe : ∀ i : Fin 242, 168 ≤ i.val → F.R i = S.R i)
    (hstock : BoundaryFactorStock (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)) D) :
    BoundaryFactorStock (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F)) D := by
  apply hstock.of_frame
  intro i hi hn
  apply hframe
  exact (packedBoundaryFactorReg_high_range (preparedBoundaryCoreReg i) hi
    (fun he => hn (Fin.ext (congrArg (fun k : Fin 226 => k.val) he)))).1

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
