module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryCropPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryGeometryState
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEmbeddedGeneratedBoundaryCropRun

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type}
noncomputable section

theorem callerBoundaryCrop_geometryState (src : Fin 2 → Fin T) (widthSource : Fin T)
    (s width w : ℕ) (S : Stacks (MachineTapes T) A) :
    rightUpdates ((boundaryGeometryWrites s width w [0,1,2]).map
      (fun (i,xs) => (boundaryCropRegister T src i,xs))) S =
      callerBoundaryGeometryState widthSource s width w S := by
  rw [map_boundaryGeometryWrites _ (boundaryGeometryRegister T widthSource)
    (boundaryCropRegister_skip_agrees T src widthSource)
    (boundaryCropRegister_count_agrees T src widthSource)]
  rfl

/-- Crop a certified shared-solver output using the actual generated caller
controls and retained rulers; no independent crop-readiness assumption remains. -/
theorem callerGeneratedBoundaryCropRun_exec (body : P → Pr P (MachineTapes T) Q A U)
    (src : Fin 2 → Fin T) (hsrc : Function.Injective src) (widthSource : Fin T)
    (p width : ℕ) (hw : 0 < width) (hroom : 3*width < s)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (output : List (Fin (A+4))) (hproduced : ExactCoreProduced p s (fun _ => 0) J r output)
    (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hclock : (S.R (unarySource T (src 0))).length = r.inputs.length)
    (hrows : (S.R (unarySource T (src 1))).length = s)
    (hword : (S.R (fullHeader T (.publication 3))).length = 2*p+13)
    (hprivate : ∀ i : Fin PackedTranspose.tapeCount,
      S.R (Fin.natAdd ((T+headerCount)+175) i) = []) (depth : ℕ) :
    let e := boundaryCropRegister T src
    let F := callerBoundaryGeometryState widthSource s width (2*p+13) S
    let volume := r.inputs.length*s*(2*p+13)
    ∃ banks : List (List (List GaussianInt)), ∃ v' n, v'.user = v.user ∧
      n ≤ 242*volume+45 ∧
      List.Forall₂ (SeamCropRows p width r J) (boundaryCropSchedule s width).reverse banks ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v {F with R := Function.update F.R (e 94) output})+depth+(480*volume+86)) depth
        (embProg e (fun f : Empty => nomatch f) generatedBoundaryCropProgram)
        (mk v {F with R := Function.update F.R (e 94) output}) n
        (mk v' {F with R := (Function.update F.R (e 95)
          ((banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++S.R (e 95)))}) := by
  have hblank (i : Fin 117) (hi : ∀ j, boundaryCropKeys j ≠ i) :
      S.R (boundaryCropRegister T src i) = [] := by
    rw [boundaryCropRegister_private T src i hi]
    exact hprivate _
  have hclean : ∀ i ∈ (generatedBoundaryCropPlan s width).cleanPorts,
      S.R (boundaryCropRegister T src i) = [] := by
    intro i hi
    apply hblank
    have hcheck : ∀ i ∈ [(66:Fin 117),67,68,69,70,71,72,73],
      ∀ j, boundaryCropKeys j ≠ i := by decide +kernel
    exact hcheck i hi
  have hsource := hblank 94 (by decide +kernel)
  have hex := embeddedGeneratedBoundaryCropRun_exec body (boundaryCropRegister T src)
    (boundaryCropRegister_injective T src hsrc) p width hw hroom r J output hproduced v S
    (by simpa only [boundaryCropRegister_clock] using hclock)
    (by simpa only [boundaryCropRegister_rows] using hrows)
    (by simpa only [boundaryCropRegister_word] using hword) hclean hsource depth
  dsimp only at hex ⊢
  rw [callerBoundaryCrop_geometryState src widthSource] at hex
  exact hex

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
