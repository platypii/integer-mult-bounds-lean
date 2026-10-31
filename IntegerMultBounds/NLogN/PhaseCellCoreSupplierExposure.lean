module

public import IntegerMultBounds.NLogN.PhaseCellCoreSupplierSchedule

/-! Route the selected numerical tasks through the two ordered movement classes.
The shared full-period task adds at most one source traversal. This is a
schedule ledger; the physical grouped gather must realize these traversals. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

/-- A proper supplier belongs to one of the two ordered gather classes.
Its endpoint key is retained: movement grouping does not merge numerical setup. -/
theorem coreSupplierSchedule_movement (s width band n : ℕ) (hw : 0 < width)
    (task : CoreSupplierTask) (htask : task ∈ coreSupplierSchedule s width band n)
    (hne : task.endpoints ≠ (0,s)) :
    ∃ k ∈ coreIndices s width, task.cores = [k] ∧
      k ∈ coreGatherIndices s width (n*band) (task.endpoints.2-task.endpoints.1) ∧
      task.endpoints.2-task.endpoints.1 ∈ coreGatherLengths s width (n*band) := by
  obtain ⟨k,hk,hcores,hkey⟩ := coreSupplierSchedule_proper s width band n hw task htask hne
  have hgroup : k ∈ coreSetupGroup s width band n task.endpoints :=
    (mem_coreSetupGroup ..).mpr ⟨hk,hkey⟩
  have hmove := coreSetupGroup_in_movement s width band n k task.endpoints hne hgroup
  exact ⟨k,hk,hcores,hmove,coreGatherLengths_cover s width (n*band) _ k hw hmove⟩

/-- Two ordered proper-halo passes and the optional shared seam pass have a
constant source-traversal bill, independently of the number of owned cores.
Payload emission and numerical setup are separate charges. -/
theorem coreSupplierSchedule_traversal_bound (s width band n replicas W : ℕ) :
    replicas*((coreGatherLengths s width (n*band)).map (fun _ => 12*s*W)).sum+
      (if (0,s) ∈ coreSetupKeyList s width band n then replicas*(12*s*W) else 0) ≤
        36*replicas*s*W := by
  have hbulk := Nat.mul_le_mul_left replicas (coreGather_traversal_bound s width (n*band) W)
  have hseam : (if (0,s) ∈ coreSetupKeyList s width band n then replicas*(12*s*W) else 0) ≤
      replicas*(12*s*W) := by split <;> omega
  calc
    _ ≤ replicas*(24*s*W)+replicas*(12*s*W) := Nat.add_le_add hbulk hseam
    _ = _ := by ring

end IntegerMultBounds.NLogN.PhaseCellMatrix
