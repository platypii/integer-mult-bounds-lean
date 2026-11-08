module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedNativeCyclicBoundaryBatch
public import IntegerMultBounds.MathlibTM2.Host.ConsumeRuns

/-! Boundary projection replaces boundary words by window words. This exact
endpoint balance is independent of projection time and retained factor stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem placedNativeCyclicBoundaryBatchState_size {s Q A : ℕ} [NeZero s] {U : Type}
    (t band a n w : ℕ) (ha : a < s) (hn : n ≤ s) (rows : List (List GaussianInt))
    (hlens : ∀ row ∈ rows, row.length = (cyclicPrincipalBoundary s t band a n).card)
    (v vf : HS 840 Q A U) (S : Stacks 840 A) (tail : List (Fin (A+4)))
    (hsource : S.R (CyclicRecoveryPlacement.bank 224) = rows.flatMap (cstream A w)++tail) :
    let B := cyclicPrincipalBoundary s t band a n
    let fields := fun solution =>
      cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
        cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
    mnSize (mk vf (placedNativeCyclicBoundaryBatchState S tail (rows.reverse.flatMap fields)))+
      rows.length*(B.card*w) = mnSize (mk v S)+rows.length*(n*w) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t band a n
  let fields := fun solution =>
    cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
      cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
  have hinput : (rows.flatMap (cstream A w)).length = rows.length*(B.card*w) := by
    rw [List.length_flatMap]
    simp only [length_cstream]
    have hm : rows.map (fun row => row.length*w) = rows.map (fun _ => B.card*w) := by
      apply List.map_congr_left
      intro row hr
      rw [hlens row hr]
    rw [hm]
    simp
  have hout : (rows.reverse.flatMap fields).length = rows.length*(n*w) :=
    nativeCyclicBoundaryBatch_fields_length A w t band a n ha hn rows
  have h := mn_consume_appendR_size v vf S (CyclicRecoveryPlacement.bank 224)
    (CyclicRecoveryPlacement.bank 132) (by decide) (rows.flatMap (cstream A w))
    tail (rows.reverse.flatMap fields) hsource
  have hstate : {S with R := (Function.update (Function.update S.R (CyclicRecoveryPlacement.bank 224) tail)
      (CyclicRecoveryPlacement.bank 132) ((rows.reverse.flatMap fields)++S.R (CyclicRecoveryPlacement.bank 132)))} =
      placedNativeCyclicBoundaryBatchState S tail (rows.reverse.flatMap fields) := by
    unfold placedNativeCyclicBoundaryBatchState
    rw [Function.update_comm (by decide : CyclicRecoveryPlacement.bank 224 ≠ CyclicRecoveryPlacement.bank 132)]
  rw [hstate,hinput,hout] at h
  exact h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
