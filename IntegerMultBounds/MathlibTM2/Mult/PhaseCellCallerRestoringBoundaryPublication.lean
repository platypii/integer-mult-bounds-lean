module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPreparedBoundaryRetirement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPreparedBoundaryPublication

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T Q A s : ℕ} [NeZero s] {P U : Type}
noncomputable section

def callerRestoringBoundaryPublication (src : Fin 11 → Fin T) (widthSource : Fin T) : Pr P (MachineTapes T) Q A U :=
  .seq (callerPreparedBoundaryPublication src widthSource) callerPreparedBoundaryRetirement

theorem callerRestoringBoundaryPublication_exec (body : P → Pr P (MachineTapes T) Q A U)
    (src : Fin 11 → Fin T) (widthSource : Fin T)
    (p u l target t scalarWidth W D radius width band n : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (proper : CorePublicationClass s width) (hr : 0 < n*band) (hrw : n*band ≤ width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band)))
    (outputTail : List (Fin (A+4))) (S : Stacks (MachineTapes T) A)
    (hraw : ∀ i, (S.R (unarySource T (src i))).length =
      globalValues p u l target s t scalarWidth W r.inputs.length radius width i)
    (hD : (S.R (unarySource T widthSource)).length = D)
    (hscalars : ∀ i, S.R (globals T i) = binSyms D
      (globalValues p u l target s t scalarWidth W r.inputs.length radius width i))
    (hzero : S.R (fullHeader T .zero) = [])
    (hblank : ∀ i : Fin 6, S.R (fullHeader T (.publication (Fin.castAdd 1 i))) = [])
    (hprivate : ∀ i : Fin tapeCount, S.R (Fin.natAdd ((T+headerCount)+175) i) = [])
    (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p width r J) (boundaryCropSchedule s width).reverse banks)
    (ambient : List (List (Fin (A+4))))
    (hgood : List.Forall₂ (fun target line => line.length = s*W ∧
      ∀ k ∈ proper.indices,
        (∀ i ∈ ownedCore s width k, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead p W line) target (3/(2:ℝ)^p))
      (seamPublicationTargets p r J) ambient)
    (hdst : S.R (fullHeader T .output) = ambient.flatten++outputTail)
    (depth : ℕ) (v : HS (MachineTapes T) Q A U) :
    let F := callerPreparedBoundaryState widthSource p s width S
    let archive := (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++S.R (fullHeader T (.publication 6))
    let G := {F with R := Function.update F.R (fullHeader T (.publication 6)) archive}
    let pairs := boundarySeamMasterCopies (boundaryArchiveSource T) (boundaryArchiveDestination T)
      (seamMasterSources T src widthSource)
    let loadCost := (pairs.map (fun pair => 6*(F.R pair.1).length+6)).sum+1
    let retireCost := 2*(pairs.map (fun pair => (F.R pair.1).length)).sum+2*pairs.length+1
    let clearCost := 2*((callerPreparedTemporaryHeaders T).map (fun i => (F.R i).length)).sum+
      2*(callerPreparedTemporaryHeaders T).length+1
    ∃ output : List (List (Fin (A+4))),
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r J) output ∧
      ∃ v' m, v'.user = v.user ∧
        m ≤ (loadCost+(3*boundarySeamBudget r.inputs.length D s W+1)+retireCost)+clearCost ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v G)+depth+
          (2*loadCost+13*boundarySeamBudget r.inputs.length D s W)) depth
          (callerRestoringBoundaryPublication src widthSource) (mk v G) m
          (mk v' {S with R := Function.update S.R (fullHeader T .output) (output.flatten++outputTail)}) := by
  dsimp only
  let F := callerPreparedBoundaryState widthSource p s width S
  let clearCost := 2*((callerPreparedTemporaryHeaders T).map (fun i => (F.R i).length)).sum+
    2*(callerPreparedTemporaryHeaders T).length+1
  obtain ⟨output,haccuracy,v₁,m,hu₁,hm,he₁⟩ := callerPreparedBoundaryPublication_exec body src widthSource
    p u l target t scalarWidth W D radius width band n hA hW hwidth hroom hvolumeFit seedValue hvalues hfit
    r J proper hr hrw hproper outputTail S hraw hD hscalars hprivate banks hbanks ambient hgood hdst depth v
  let archive := (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++S.R (fullHeader T (.publication 6))
  have hload := congrArg List.sum (seamMasterCopies_archive_map (boundaryArchiveSource T)
    (boundaryArchiveDestination T) src widthSource F archive (fun xs => 6*xs.length+6))
  have hretire := congrArg List.sum (seamMasterCopies_archive_map (boundaryArchiveSource T)
    (boundaryArchiveDestination T) src widthSource F archive List.length)
  dsimp only [F,archive] at hload hretire
  rw [hload,hretire] at hm
  rw [hload] at he₁
  obtain ⟨v₂,hu₂,he₂⟩ := callerPreparedBoundaryRetire_exec body widthSource p s width S hzero hblank
    (output.flatten++outputTail) v₁ depth
  refine ⟨output,haccuracy,v₂,m+clearCost,hu₂.trans hu₁,Nat.add_le_add_right hm clearCost,?_⟩
  have hpoint := he₁.final
  apply ExecWithin.seq he₁
  exact he₂.mono (by
    intro d z hz
    omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
