module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportBoundaryGeometrySequence
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamCropPlan

/-! The generated controls discharge a concrete retained crop plan's readiness.
Mathematical core indices select fixed slot ports; no crop data is assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A : ℕ}

def boundaryCoreSlot (s width k : ℕ) : Fin 3 :=
  if k = boundaryCropIndex s width 0 then 0 else if k = boundaryCropIndex s width 1 then 1 else 2

theorem boundaryCoreSlot_index (s width : ℕ) (hw : 0 < width) (hroom : 3*width < s) (slot : Fin 3) :
    boundaryCoreSlot s width (boundaryCropIndex s width slot) = slot := by
  have hinj := boundaryCropIndex_injective s width hw hroom
  fin_cases slot <;> simp [boundaryCoreSlot,hinj.eq_iff]

def generatedBoundaryCropPlan (s width : ℕ) : SeamCropPlan 117 94 where
  clock := 15
  clockSave := 66
  sourceSave := 67
  dst := 95
  savedSkip := 68
  saved := 69
  tmp := 70
  rows := 16
  width := 17
  retireCount := 71
  trash := 72
  retireTmp := 73
  skip k := boundarySeamCropSkip (boundaryCoreSlot s width k)
  count k := boundarySeamCropCount (boundaryCoreSlot s width k)

theorem generatedBoundaryCropPlan_common (s width : ℕ) : (generatedBoundaryCropPlan s width).commonPorts.Nodup := by
  change ([(15:Fin 117),66,67,94,95,68,69,70,16,17,71,72,73]).Nodup
  decide +kernel

theorem generatedBoundaryCropPlan_regs (s width k : ℕ) : ((generatedBoundaryCropPlan s width).cropPorts k).Nodup := by
  have h : ∀ slot : Fin 3, ([(15:Fin 117),66,67,boundarySeamCropSkip slot,boundarySeamCropCount slot,
      94,95,68,69,70,16,17,71,72,73]).Nodup := by decide +kernel
  exact h (boundaryCoreSlot s width k)

theorem generatedBoundaryCropPlan_ready (p s width N : ℕ) [NeZero s]
    (hw : 0 < width) (hroom : 3*width < s) (S : Stacks 117 A)
    (hclock : (S.R 15).length = N) (hrows : (S.R 16).length = s)
    (hword : (S.R 17).length = 2*p+13)
    (hclean : ∀ i ∈ (generatedBoundaryCropPlan s width).cleanPorts, S.R i = []) :
    (generatedBoundaryCropPlan s width).Ready p s width N (boundaryCropSchedule s width)
      (exportBoundaryGeometryState s width (2*p+13) [0,1,2] S) := by
  let F := exportBoundaryGeometryState s width (2*p+13) [0,1,2] S
  have hread (i : Fin 117) (hi : i.val < 60 ∨ 66 ≤ i.val) : F.R i = S.R i := by
    apply exportBoundaryGeometryState_off
    intro slot hslot
    have hb : ∀ slot : Fin 3, (boundarySeamCropSkip slot).val ≤ 65 ∧ (boundarySeamCropCount slot).val ≤ 65 := by
      decide +kernel
    have hl := boundarySeamCropPorts_lower slot
    constructor <;> intro he <;> have hv := congrArg Fin.val he <;> have hu := hb slot <;> omega
  have hslot (k : ℕ) (hk : k ∈ boundaryCropSchedule s width) : ∃ slot, boundaryCropIndex s width slot = k := by
    rw [boundaryCropSchedule_eq_reverse_slots] at hk
    exact List.mem_ofFn.mp (List.mem_reverse.mp hk)
  have hmem (slot : Fin 3) : slot ∈ [(0:Fin 3),1,2] := by fin_cases slot <;> simp
  refine ⟨generatedBoundaryCropPlan_common s width,fun k _ => generatedBoundaryCropPlan_regs s width k,
    ?_,?_,?_,?_,?_,?_⟩
  · exact (congrArg List.length (hread 15 (Or.inl (by decide)))).trans hclock
  · intro k hk
    obtain ⟨slot,rfl⟩ := hslot k hk
    change (F.R (boundarySeamCropSkip (boundaryCoreSlot s width (boundaryCropIndex s width slot)))).length = _
    rw [boundaryCoreSlot_index s width hw hroom]
    have h := exportBoundaryGeometryState_skip s width (2*p+13) [0,1,2] (by decide) S slot (hmem slot)
    exact (congrArg List.length h).trans (List.length_replicate ..)
  · intro k hk
    obtain ⟨slot,rfl⟩ := hslot k hk
    change (F.R (boundarySeamCropCount (boundaryCoreSlot s width (boundaryCropIndex s width slot)))).length = _
    rw [boundaryCoreSlot_index s width hw hroom]
    have h := exportBoundaryGeometryState_count s width (2*p+13) [0,1,2] (by decide) S slot (hmem slot)
    exact (congrArg List.length h).trans (List.length_replicate ..)
  · exact (congrArg List.length (hread 16 (Or.inl (by decide)))).trans hrows
  · exact (congrArg List.length (hread 17 (Or.inl (by decide)))).trans hword
  · intro i hi
    have hports : ∀ i ∈ (generatedBoundaryCropPlan s width).cleanPorts, 66 ≤ i.val := by
      change ∀ i ∈ [(66:Fin 117),67,68,69,70,71,72,73], 66 ≤ i.val
      decide +kernel
    exact (hread i (Or.inr (hports i hi))).trans (hclean i hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
