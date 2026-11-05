module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSeamHeaderPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamCallerPublication
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! Prepare original caller headers, publish the certified boundary archive,
and retire every generated header on the same physical caller bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T Q A s : ℕ} [NeZero s] {P U : Type}
noncomputable section

def callerSeamPublishedHeaders (src : Fin 11 → Fin T) (widthSource : Fin T)
    (source destination : Fin ((T+headerCount)+175)) : Pr P (MachineTapes T) Q A U :=
  .seq (seamHeaderPreparation (src 0) widthSource)
    (boundarySeamCallerPublication source destination (seamMasterSources T src widthSource))

def seamHeaderPreparationCost (D p s width : ℕ) : ℕ :=
  (4*p+5)+((2*p+13)*(4*D+10)+4*D+8)+boundaryCountExportCost D s width (2*p+13)+(2*D+2)

def seamHeaderPreparationWorkspace (D p s width : ℕ) : ℕ :=
  13*(4*p+5)+2*(4*D+4)+3*boundaryCountExportCost D s width (2*p+13)

theorem callerSeamPublishedHeaders_exec (body : P → Pr P (MachineTapes T) Q A U)
    (src : Fin 11 → Fin T) (widthSource : Fin T)
    (source destination : Fin ((T+headerCount)+175)) (hne : source ≠ destination)
    (p u l target t B W D radius width band n : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (hw : 0 < width) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (proper : CorePublicationClass s width) (hr : 0 < n*band) (hrw : n*band ≤ width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band)))
    (sourceTail outputTail : List (Fin (A+4))) (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hraw : ∀ i, (S.R (unarySource T (src i))).length =
      globalValues p u l target s t B W r.inputs.length radius width i)
    (hD : (S.R (unarySource T widthSource)).length = D)
    (hscalars : ∀ i, S.R (globals T i) = binSyms D
      (globalValues p u l target s t B W r.inputs.length radius width i))
    (hblank : ∀ i : Fin 4, S.R (fullHeader T (.publication (Fin.castAdd 3 i))) = [])
    (hprivate : ∀ i : Fin tapeCount, S.R (Fin.natAdd ((T+headerCount)+175) i) = [])
    (hsourceOff : ∀ i : Fin 4, Fin.castAdd tapeCount source ≠ fullHeader T (.publication (Fin.castAdd 3 i)))
    (hdestOff : ∀ i : Fin 4, Fin.castAdd tapeCount destination ≠ fullHeader T (.publication (Fin.castAdd 3 i)))
    (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p width r J) (boundaryCropSchedule s width).reverse banks)
    (ambient : List (List (Fin (A+4))))
    (hgood : List.Forall₂ (fun target line => line.length = s*W ∧
      ∀ k ∈ proper.indices,
        (∀ i ∈ ownedCore s width k, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead p W line) target (3/(2:ℝ)^p))
      (seamPublicationTargets p r J) ambient)
    (hsrc : S.R (Fin.castAdd tapeCount source) =
      (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail)
    (hdst : S.R (Fin.castAdd tapeCount destination) = ambient.flatten++outputTail) (depth : ℕ) :
    let M := seamHeadersState p s width S
    let pairs := boundarySeamMasterCopies source destination (seamMasterSources T src widthSource)
    let loadCost := (pairs.map (fun pair => 6*(M.R pair.1).length+6)).sum+1
    let retireCost := 2*(pairs.map (fun pair => (M.R pair.1).length)).sum+2*pairs.length+1
    ∃ output : List (List (Fin (A+4))),
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r J) output ∧
      let F : Stacks (MachineTapes T) A := {M with R := (Function.update
        (Function.update M.R (Fin.castAdd tapeCount source) sourceTail)
        (Fin.castAdd tapeCount destination) (output.flatten++outputTail))}
      ∃ v' m, v'.user = v.user ∧
        m ≤ seamHeaderPreparationCost D p s width+
          (loadCost+(3*boundarySeamBudget r.inputs.length D s W+1)+retireCost) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (seamHeaderPreparationWorkspace D p s width+2*loadCost+13*boundarySeamBudget r.inputs.length D s W))
          depth (callerSeamPublishedHeaders src widthSource source destination) (mk v S) m (mk v' F) := by
  dsimp only
  have hNarrowFit : s*(2*p+13) < 2^D := (Nat.mul_le_mul_left s hW).trans_lt hvolumeFit
  obtain ⟨v₁,a,hv₁,ha,hprep⟩ := seamHeaderPreparation_exec body (src 0) widthSource D p s width hw hroom
    hNarrowFit v S (by simpa [globalValues] using hraw 0) hD
    (by simpa [globalValues] using hscalars 4) (by simpa [globalValues] using hscalars 10)
    hblank hprivate depth
  let M := seamHeadersState p s width S
  let words := fun i => M.R (Fin.castAdd tapeCount (seamMasterSources T src widthSource i))
  have hwords : BoundarySeamHeaderWords (s := s) p width W D r.inputs.length seedValue words :=
    seamHeadersState_masterWords p u l target s t B W D r.inputs.length radius width src widthSource
      seedValue hvalues S hraw hD hscalars
  have hprivateM (i : Fin tapeCount) : M.R (Fin.natAdd ((T+headerCount)+175) i) = [] := by
    have hoff : ∀ j : Fin 4, Fin.natAdd ((T+headerCount)+175) i ≠
        fullHeader T (.publication (Fin.castAdd 3 j)) := by
      intro j
      exact (prefix_ne_routing (Fin.castAdd 175 (header T (.publication (Fin.castAdd 3 j)))) i).symm
    exact (seamHeadersState_off p s width S _ hoff).trans (hprivate i)
  obtain ⟨output,haccuracy,v₂,b,hv₂,hb,hstock,hpub⟩ := boundarySeamCallerPublication_exec body source destination hne
    (seamMasterSources T src widthSource) p width W D band n hA hW hw hroom hvolumeFit
    seedValue hvalues hfit r J proper hr hrw hproper sourceTail outputTail M words hwords (by intro i; rfl)
    (by
      intro i hs hd
      rw [seamRegister_private source destination i hs hd]
      exact hprivateM (publicationReg i)) banks hbanks ambient hgood
    (by
      simp only [seamRegister_source]
      exact (seamHeadersState_off p s width S _ hsourceOff).trans hsrc)
    (by
      simp only [seamRegister_destination]
      exact (seamHeadersState_off p s width S _ hdestOff).trans hdst) depth v₁
  let pairs := boundarySeamMasterCopies source destination (seamMasterSources T src widthSource)
  let loadCost := (pairs.map (fun pair => 6*(M.R pair.1).length+6)).sum+1
  let retireCost := 2*(pairs.map (fun pair => (M.R pair.1).length)).sum+2*pairs.length+1
  refine ⟨output,haccuracy,v₂,a+b,hv₂.trans hv₁,?_,?_⟩
  · have ha' : a ≤ seamHeaderPreparationCost D p s width := ha
    exact Nat.add_le_add ha' hb
  · simp only [seamRegister_source,seamRegister_destination] at hpub
    let F : Stacks (MachineTapes T) A := {M with R := (Function.update
      (Function.update M.R (Fin.castAdd tapeCount source) sourceTail)
      (Fin.castAdd tapeCount destination) (output.flatten++outputTail))}
    have hcombined := execWithin_seq_two_budget body
      (seamHeaderPreparation (src 0) widthSource)
      (boundarySeamCallerPublication source destination (seamMasterSources T src widthSource))
      (mk v S) (mk v₁ M) (mk v₂ F) a b depth
      (seamHeaderPreparationWorkspace D p s width)
      (2*loadCost+13*boundarySeamBudget r.inputs.length D s W) hprep hpub
    exact hcombined.mono (by
      intro d z hz
      exact hz.trans (Nat.add_le_add_left (Nat.add_assoc _ _ _).symm.le _))

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
