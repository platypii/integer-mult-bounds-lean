module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedExportCyclicResidualRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryMasks
public import IntegerMultBounds.MathlibTM2.Host.EmbedBaseUpdate

/-! Generated masks disappear when the owned residual-export controls retire.
This is a structural bank/frame fact, independent of the replica data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T A : ℕ}

def cyclicResidualMaskState (H K : ReplicaHaloProblem s) (e : Fin 234 → Fin T) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update S.R (e 170)
    (couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span)) (e 173)
    (couplingSourceIntervalMaskSymbols true A s K.t K.band K.origin (K.origin+K.span) K.origin K.span))}

theorem cyclicResidualMaskState_projection (H K : ReplicaHaloProblem s)
    (e : Fin 234 → Fin T) (he : Function.Injective e) (S : Stacks T A) :
    embStk e (cyclicResidualMaskState H K e S) =
      {embStk e S with R := (Function.update (Function.update (embStk e S).R 170
        (couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span)) 173
        (couplingSourceIntervalMaskSymbols true A s K.t K.band K.origin (K.origin+K.span) K.origin K.span))} := by
  let J : Stacks T A := {S with R := (Function.update S.R (e 170)
    (couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span))}
  change embStk e {J with R := Function.update J.R (e 173) _} = _
  rw [embStk_updateR he]
  dsimp only [J]
  rw [embStk_updateR he]

theorem exportedCyclicResidualRows_maskState (H K : ReplicaHaloProblem s)
    (e : Fin 234 → Fin T) (he : Function.Injective e) (S : Stacks T A) (rows : List (Fin (A+4))) :
    exportedCyclicResidualRows (embStk e (cyclicResidualMaskState H K e S)) rows =
      exportedCyclicResidualRows (embStk e S) rows := by
  rw [cyclicResidualMaskState_projection H K e he S]
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k ∈ cyclicResidualRowsRetired
  · simp [exportedCyclicResidualRows,hk]
  · have h170 : k ≠ 170 := by intro h; subst k; exact hk (by simp [cyclicResidualRowsRetired])
    have h173 : k ≠ 173 := by intro h; subst k; exact hk (by simp [cyclicResidualRowsRetired])
    simp [exportedCyclicResidualRows,hk,h170,h173,Function.update_apply]

theorem exportedCyclicResidualRows_maskFrame (H K : ReplicaHaloProblem s)
    (e : Fin 234 → Fin T) (he : Function.Injective e) (S : Stacks T A) (rows : List (Fin (A+4))) :
    embOvr e (exportedCyclicResidualRows (embStk e (cyclicResidualMaskState H K e S)) rows).get
        (cyclicResidualMaskState H K e S) =
      embOvr e (exportedCyclicResidualRows (embStk e S) rows).get S := by
  rw [exportedCyclicResidualRows_maskState H K e he S rows]
  let f := (exportedCyclicResidualRows (embStk e S) rows).get
  let J : Stacks T A := {S with R := (Function.update S.R (e 170)
    (couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span))}
  change embOvr e f {J with R := Function.update J.R (e 173) _} = embOvr e f S
  rw [embOvr_base_updateR]
  dsimp only [J]
  rw [embOvr_base_updateR]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
