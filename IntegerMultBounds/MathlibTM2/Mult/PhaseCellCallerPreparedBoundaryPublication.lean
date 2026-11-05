module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPreparedBoundaryWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamCallerPublication

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T Q A s : ℕ} [NeZero s] {P U : Type}
noncomputable section

def boundaryArchiveSource (T : ℕ) : Fin ((T+headerCount)+175) := Fin.castAdd 175 (header T (.publication 6))
def boundaryArchiveDestination (T : ℕ) : Fin ((T+headerCount)+175) := Fin.castAdd 175 (header T .output)

def callerPreparedBoundaryPublication (src : Fin 11 → Fin T) (widthSource : Fin T) : Pr P (MachineTapes T) Q A U :=
  boundarySeamCallerPublication (boundaryArchiveSource T) (boundaryArchiveDestination T)
    (seamMasterSources T src widthSource)

theorem callerPreparedBoundaryPublication_exec (body : P → Pr P (MachineTapes T) Q A U)
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
    let loadCost := (pairs.map (fun pair => 6*(G.R pair.1).length+6)).sum+1
    let retireCost := 2*(pairs.map (fun pair => (G.R pair.1).length)).sum+2*pairs.length+1
    ∃ output : List (List (Fin (A+4))),
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r J) output ∧
      ∃ v' m, v'.user = v.user ∧
        m ≤ loadCost+(3*boundarySeamBudget r.inputs.length D s W+1)+retireCost ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v G)+depth+
          (2*loadCost+13*boundarySeamBudget r.inputs.length D s W)) depth
          (callerPreparedBoundaryPublication src widthSource) (mk v G) m
          (mk v' {F with R := (Function.update (Function.update F.R
            (fullHeader T (.publication 6)) (S.R (fullHeader T (.publication 6))))
            (fullHeader T .output) (output.flatten++outputTail))}) := by
  dsimp only
  let F := callerPreparedBoundaryState widthSource p s width S
  let archive := (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++S.R (fullHeader T (.publication 6))
  let G : Stacks (MachineTapes T) A := {F with R := Function.update F.R (fullHeader T (.publication 6)) archive}
  let source := boundaryArchiveSource T
  let destination := boundaryArchiveDestination T
  have hne : source ≠ destination := by
    intro he
    have hh := congrArg (Fin.castAdd tapeCount) he
    exact ((fullHeader_injective T).ne (by intro h; cases h) : fullHeader T (.publication 6) ≠ fullHeader T .output) hh
  have hprivateG (i : Fin tapeCount) : G.R (Fin.natAdd ((T+headerCount)+175) i) = [] := by
    dsimp only [G]
    have hne6 : Fin.natAdd ((T+headerCount)+175) i ≠ fullHeader T (.publication 6) :=
      (prefix_ne_routing (Fin.castAdd 175 (header T (.publication 6))) i).symm
    rw [Function.update_of_ne hne6]
    dsimp only [F,callerPreparedBoundaryState]
    rw [callerBoundaryGeometryState_private]
    exact (Function.update_of_ne (prefix_ne_routing (Fin.castAdd 175 (header T (.publication 3))) i).symm _ _).trans (hprivate i)
  have hdstRead : G.R (fullHeader T .output) = S.R (fullHeader T .output) := by
    dsimp only [G]
    rw [Function.update_of_ne ((fullHeader_injective T).ne (by intro h; cases h) : fullHeader T .output ≠ fullHeader T (.publication 6))]
    dsimp only [F,callerPreparedBoundaryState]
    rw [callerBoundaryGeometryState_off_header_bank widthSource s width (2*p+13) _ _
      ((fullHeader_injective T).ne (by intro h; cases h))
      (fun _ => (fullHeader_injective T).ne (by intro h; cases h))]
    exact Function.update_of_ne ((fullHeader_injective T).ne (by intro h; cases h) : fullHeader T .output ≠ fullHeader T (.publication 3)) _ _
  have hwords := callerPreparedBoundaryState_masterWords p u l target t scalarWidth W D r.inputs.length radius width
    src widthSource seedValue hvalues S hraw hD hscalars archive
  obtain ⟨output,haccuracy,v',m,hu,hm,hstock,he⟩ := boundarySeamCallerPublication_exec body source destination hne
    (seamMasterSources T src widthSource) p width W D band n hA hW hwidth hroom hvolumeFit seedValue hvalues hfit
    r J proper hr hrw hproper (S.R (fullHeader T (.publication 6))) outputTail G
    (fun i => G.R (Fin.castAdd tapeCount (seamMasterSources T src widthSource i))) hwords (fun _ => rfl)
    (by intro i hs hd; rw [seamRegister_private source destination i hs hd]; exact hprivateG _)
    banks hbanks ambient hgood
    (by rw [seamRegister_source]; exact Function.update_self _ _ _)
    (by rw [seamRegister_destination]; exact hdstRead.trans hdst) depth v
  simp only [seamRegister_source,seamRegister_destination] at he
  have hend : ({G with R := (Function.update (Function.update G.R (fullHeader T (.publication 6))
      (S.R (fullHeader T (.publication 6))))) (fullHeader T .output) (output.flatten++outputTail)} : Stacks (MachineTapes T) A) =
      {F with R := (Function.update (Function.update F.R (fullHeader T (.publication 6))
        (S.R (fullHeader T (.publication 6))))) (fullHeader T .output) (output.flatten++outputTail)} := by
    simp only [G,Function.update_idem]
  change ExecWithin _ _ _ _ _ _ (mk v' {G with R := (Function.update (Function.update G.R
    (fullHeader T (.publication 6)) (S.R (fullHeader T (.publication 6)))) (fullHeader T .output) (output.flatten++outputTail))}) at he
  rw [hend] at he
  dsimp only [source,destination,G,F,archive] at hm he
  refine ⟨output,haccuracy,v',m,hu,?_,?_⟩
  · exact hm
  · exact he

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
