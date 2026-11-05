module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryCropReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamCropPorts

/-! Execute the actual boundary crop archive from generated controls and a
certified full-line solver output, returning the physical-order seam bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {Q A s : ℕ} [NeZero s] {P U : Type}

/-- Geometry changes header values, not the crop instructions or slot ports. -/
def generatedBoundaryCropProgram : Pr P 117 Q A U :=
  .seq ((generatedBoundaryCropPlan 0 0).boundaryProgram boundarySeamCropSkip boundarySeamCropCount) (uclear 94)

theorem generatedBoundaryCropProgram_eq (s width : ℕ) (hw : 0 < width) (hroom : 3*width < s) :
    (.seq ((generatedBoundaryCropPlan s width).program (boundaryCropSchedule s width)) (uclear 94) : Pr P 117 Q A U) =
      generatedBoundaryCropProgram := by
  rw [SeamCropPlan.program_boundary_eq (generatedBoundaryCropPlan s width) s width
    boundarySeamCropSkip boundarySeamCropCount]
  · rfl
  · intro slot
    change boundarySeamCropSkip (boundaryCoreSlot s width (boundaryCropIndex s width slot)) = _
    rw [boundaryCoreSlot_index s width hw hroom]
  · intro slot
    change boundarySeamCropCount (boundaryCoreSlot s width (boundaryCropIndex s width slot)) = _
    rw [boundaryCoreSlot_index s width hw hroom]

theorem generatedBoundaryCropRun_exec (body : P → Pr P 117 Q A U)
    (p width : ℕ) (hw : 0 < width) (hroom : 3*width < s)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (output : List (Fin (A+4))) (hproduced : ExactCoreProduced p s (fun _ => 0) J r output)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hclock : (S.R 15).length = r.inputs.length) (hrows : (S.R 16).length = s)
    (hword : (S.R 17).length = 2*p+13)
    (hclean : ∀ i ∈ (generatedBoundaryCropPlan s width).cleanPorts, S.R i = [])
    (hsource : S.R 94 = []) (depth : ℕ) :
    let F := exportBoundaryGeometryState s width (2*p+13) [0,1,2] S
    let volume := r.inputs.length*s*(2*p+13)
    ∃ banks : List (List (List GaussianInt)), ∃ v' n, v'.user = v.user ∧
      n ≤ 242*volume+45 ∧
      List.Forall₂ (SeamCropRows p width r J) (boundaryCropSchedule s width).reverse banks ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v {F with R := Function.update F.R 94 output})+depth+(480*volume+86)) depth
        generatedBoundaryCropProgram
        (mk v {F with R := Function.update F.R 94 output}) n
        (mk v' {F with R := (Function.update F.R 95
          ((banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++F.R 95))}) := by
  dsimp only
  let F := exportBoundaryGeometryState s width (2*p+13) [0,1,2] S
  have hready := generatedBoundaryCropPlan_ready p s width r.inputs.length hw hroom S hclock hrows hword hclean
  have hstart : ∀ k ∈ boundaryCropSchedule s width, coreStart width k ≤ s := by
    intro k hk
    exact ((boundaryCropSchedule_spec s width hw hroom).2.2 k hk).2.1.le
  have hFsource : F.R 94 = [] := by
    have h := exportBoundaryGeometryState_off s width (2*p+13) [0,1,2] S 94 (by decide +kernel)
    exact h.trans hsource
  obtain ⟨rows,v',n,hu,hn,hrows,he⟩ := (generatedBoundaryCropPlan s width).archiveRetire_exec_within
    (body := body) p width r J (boundaryCropSchedule s width) output hproduced hstart v F hready hFsource depth
  rw [generatedBoundaryCropProgram_eq s width hw hroom] at he
  have hcost := SeamCropPlan.archiveRetire_three_cost (boundaryCropSchedule s width)
    (by simp [boundaryCropSchedule]) (r.inputs.length*s*(2*p+13))
  refine ⟨rows.reverse,v',n,hu,hn.trans hcost.1,List.rel_reverse hrows,?_⟩
  exact he.mono (by intro d z hz; dsimp only [F] at *; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
