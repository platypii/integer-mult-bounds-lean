import IntegerMultBounds.Machine.ActiveRepairLateOriginalPipelineEndpoint
import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineBudgetArithmetic

/-! Full paid budgets for the actual original-input later repair endpoint.
Sparse-count absorption includes preparation, sorting, reinsertion and every
cleanup word. Flags and keys are the literal current-rank key computation. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateOriginalPipelineBudget
noncomputable section
open ActiveRepairLateKeyOriginalData ActiveRepairLateKeyOriginalValid
open ActiveRepairEarlyOriginalPipelineBudgetWords ActiveRepairEarlyOriginalPipelineBudgetArithmetic

def holes (d : Data) (rs : List Partition.Record) :=
  Reinsert.holes (ActiveRepairLateOriginalPipelineCleanup.flagged d rs)
def constant := ActiveRepairLateKeyOriginalRun.constant+1000
def volumeConstant (D : ℕ) := constant*(2+2*D)

theorem sorted_volume (d : Data) (rs : List Partition.Record) :
    (ActiveRepairLateOriginalPipelineCleanup.sortedWord d rs).length=
      (ActiveRepairLateOriginalPipelineRun.extracted d d.geom.addressBits rs).length :=
  TapeRadixSort.volume_sort _ _

theorem index_le (d : Data) (rs : List Partition.Record) :
    ActiveRepairLateOriginalPipelineCleanup.index d rs≤d.geom.addressBits := by
  unfold ActiveRepairLateOriginalPipelineCleanup.index TapeRadixSort.completed
  split <;> omega

theorem model_cost (d : Data) (rs : List Partition.Record) :
    ActiveRepairLateOriginalPipelineEndpoint.cost d rs=
      modelCost ActiveRepairLateKeyOriginalRun.constant d.geom.addressBits rs.length
        (DropFlag.encode rs).length
        (ActiveRepairLateOriginalPipelineRun.extracted d d.geom.addressBits rs).length
        (Partition.encode (ActiveRepairLateOriginalPipelineCleanup.flagged d rs)).length
        (Partition.encode (ActiveRepairLateOriginalPipelineCleanup.replacements d rs)).length
        (Partition.encode (ActiveRepairLateOriginalPipelineCleanup.repaired d rs)).length
        (ActiveRepairLateOriginalPipelineCleanup.index d rs) (holes d rs) := by
  unfold ActiveRepairLateOriginalPipelineEndpoint.cost ActiveRepairLateOriginalPipelineRun.cost
    ActiveRepairLateOriginalPipelineCleanup.cost modelCost
  rw [sorted_volume]
  unfold holes ActiveRepairLateOriginalPipelineRun.holes
    ActiveRepairLateOriginalPipelineCleanup.flagged
  ring

theorem cost_bound (d : Data) (rs : List Partition.Record) (R : ℕ)
    (hN : 0<rs.length) (hw : ∀ r ∈ rs,r.payload.length≤R) :
    ActiveRepairLateOriginalPipelineEndpoint.cost d rs≤
      constant*(rs.length*R+rs.length*(d.geom.addressBits+1)+
        holes d rs*(d.geom.addressBits+1)*(R+d.geom.addressBits+1)) := by
  have hv := volumes d.geom.addressBits R rs
    (ActiveRepairLateOriginalScan.flag d d.geom.addressBits)
    (ActiveRepairLateOriginalScan.bits d d.geom.addressBits) hw
    (ActiveRepairLateOriginalScan.bits_length d d.geom.addressBits)
  obtain ⟨hS,hF,hE,hP,hI,hH⟩ := hv
  rw [model_cost]
  exact paid_bound _ _ _ _ _ _ _ _ _ _ _ hN hS hE hF hP hI (index_le d rs) hH

theorem cost_linear (d : Data) (rs : List Partition.Record) (R D : ℕ)
    (hN : 0<rs.length) (hw : ∀ r ∈ rs,r.payload.length≤R)
    (hR : d.geom.addressBits+1≤R)
    (hH : holes d rs*(d.geom.addressBits+1)≤D*rs.length) :
    ActiveRepairLateOriginalPipelineEndpoint.cost d rs≤volumeConstant D*(rs.length*R) := by
  have hh := Nat.mul_le_mul_left constant
    (volume_absorb rs.length R d.geom.addressBits (holes d rs) D hR hH)
  exact (cost_bound d rs R hN hw).trans (by simpa only [volumeConstant,Nat.mul_assoc] using hh)

theorem runs_with_bound (d : Data) (h : Valid d) (rs : List Partition.Record) (R : ℕ)
    (hN : 0<rs.length) (hw : ∀ r ∈ rs,r.payload.length≤R) :
    HoareTime (ActiveRepairLateOriginalPipelineEndpoint.program d.side)
      (fun v => v=ActiveRepairLateOriginalPipelineEndpoint.input d rs)
      (fun v => v=ActiveRepairLateOriginalPipelineEndpoint.output d rs)
      (constant*(rs.length*R+rs.length*(d.geom.addressBits+1)+
        holes d rs*(d.geom.addressBits+1)*(R+d.geom.addressBits+1))) :=
  (ActiveRepairLateOriginalPipelineEndpoint.runs d h rs).consequence
    (fun _ h => h) (fun _ h => h) (cost_bound d rs R hN hw)

theorem runs_linear (d : Data) (h : Valid d) (rs : List Partition.Record) (R D : ℕ)
    (hN : 0<rs.length) (hw : ∀ r ∈ rs,r.payload.length≤R)
    (hR : d.geom.addressBits+1≤R)
    (hH : holes d rs*(d.geom.addressBits+1)≤D*rs.length) :
    HoareTime (ActiveRepairLateOriginalPipelineEndpoint.program d.side)
      (fun v => v=ActiveRepairLateOriginalPipelineEndpoint.input d rs)
      (fun v => v=ActiveRepairLateOriginalPipelineEndpoint.output d rs) (volumeConstant D*(rs.length*R)) :=
  (ActiveRepairLateOriginalPipelineEndpoint.runs d h rs).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear d rs R D hN hw hR hH)

end
end IntegerMultBounds.Machine.ActiveRepairLateOriginalPipelineBudget
