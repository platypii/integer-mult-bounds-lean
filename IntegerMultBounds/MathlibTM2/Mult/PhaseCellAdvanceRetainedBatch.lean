module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicLayout
public import IntegerMultBounds.MathlibTM2.Routing.RetainedFieldBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLineStock

/-! Consume the restored target batch after publishing its source packet.
The retained replica and byte-volume masters generate and retire the count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  Routing.RetainedHaloTensor
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def advanceRetainedBatch : Pr P tapes Q A U :=
  retireCountedLine (aux 7) (selector (LocalRecoveryLayout.batch 1))
    (selector (LocalRecoveryLayout.batch 2)) caller.count caller.saved caller.tmp

private theorem advance_regs : [aux 7,selector (LocalRecoveryLayout.batch 1),
    selector (LocalRecoveryLayout.batch 2),caller.count,caller.saved,caller.tmp].Nodup := by
  simp [caller,selector,aux,port_injective.eq_iff,LocalRecoveryLayout.batch_injective.eq_iff]

theorem retainedBatch_length {ι : Type} [DecidableEq ι] (A w : ℕ) (grid : ι → Axis)
    (retained : Finset ι) (before middle : List (Sum ι ι)) (i : ι) (a k : ℕ)
    (f : (ι → ℕ) → GaussianInt) :
    (Routing.RetainedFieldBatch.batch A w grid retained before middle i a k f).length =
      (middle.map (Routing.RetainedTensorEnumeration.width grid retained)).prod*
        (localLength grid retained i*w) := by
  simp [Routing.RetainedFieldBatch.batch,List.length_flatMap,length_cstream,
    List.map_const',List.sum_replicate]

theorem advanceRetainedBatch_exec {ι : Type} [DecidableEq ι] (grid : ι → Axis)
    (retained : Finset ι) (before middle : List (Sum ι ι)) (i : ι) (a k w : ℕ)
    (f : (ι → ℕ) → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hN : (S.R (aux 7)).length = (middle.map (Routing.RetainedTensorEnumeration.width grid retained)).prod)
    (hvolume : (S.R (selector (LocalRecoveryLayout.batch 1))).length = localLength grid retained i*w)
    (hqueue : S.R (selector (LocalRecoveryLayout.batch 2)) =
      Routing.RetainedFieldBatch.batch A w grid retained before middle i a k f++tail)
    (hblank : ∀ r ∈ [caller.count,caller.saved,caller.tmp], S.R r = []) (depth : ℕ) :
    let N := (middle.map (Routing.RetainedTensorEnumeration.width grid retained)).prod
    let volume := localLength grid retained i*w
    ∃ v' n, v'.user = v.user ∧ n ≤ retireCountedLineCost N volume ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*retireCountedLineCost N volume)
        depth advanceRetainedBatch (mk v S) n
        (mk v' {S with R := Function.update S.R (selector (LocalRecoveryLayout.batch 2)) tail}) := by
  exact retireCountedLine_exec_within _ _ _ _ _ _ advance_regs _ _ _ tail
    (retainedBatch_length A w grid retained before middle i a k f) v S hN hvolume hqueue
    (hblank _ (by simp)) (hblank _ (by simp)) (hblank _ (by simp)) depth

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
