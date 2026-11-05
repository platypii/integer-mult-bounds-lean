module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSeamHeaderRetirement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSeamPublishedHeaders
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

def callerSeamCompletion (src : Fin 11 → Fin T) (widthSource : Fin T)
    (source destination : Fin ((T+headerCount)+175)) : Pr P (MachineTapes T) Q A U :=
  .seq (callerSeamPublishedHeaders src widthSource source destination) seamHeadersRetirement

theorem callerSeamCompletion_exec (body : P → Pr P (MachineTapes T) Q A U)
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
      let F : Stacks (MachineTapes T) A := {S with R := (Function.update
        (Function.update S.R (Fin.castAdd tapeCount source) sourceTail)
        (Fin.castAdd tapeCount destination) (output.flatten++outputTail))}
      ∃ v' m, v'.user = v.user ∧
        m ≤ seamHeaderPreparationCost D p s width+
          (loadCost+(3*boundarySeamBudget r.inputs.length D s W+1)+retireCost)+seamHeadersRetireCost p s width ∧
        mnSize (mk v' F) ≤ mnSize (mk v S) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (seamHeaderPreparationWorkspace D p s width+2*loadCost+13*boundarySeamBudget r.inputs.length D s W))
          depth (callerSeamCompletion src widthSource source destination) (mk v S) m (mk v' F) := by
  dsimp only
  obtain ⟨output,haccuracy,u',a,hu,ha,he⟩ := callerSeamPublishedHeaders_exec body src widthSource
    source destination hne p u l target t B W D radius width band n hA hW hw hroom hvolumeFit
    seedValue hvalues hfit r J proper hr hrw hproper sourceTail outputTail v S hraw hD hscalars
    hblank hprivate hsourceOff hdestOff banks hbanks ambient hgood hsrc hdst depth
  obtain ⟨v',hv,hretire⟩ := seamHeadersRetirement_exec body p s width u' S hblank
    (Fin.castAdd tapeCount source) (Fin.castAdd tapeCount destination) hsourceOff hdestOff
    sourceTail (output.flatten++outputTail) depth
  refine ⟨output,haccuracy,v',a+seamHeadersRetireCost p s width,hv.trans hu,?_,?_,?_⟩
  · exact Nat.add_le_add_right ha _
  · apply mn_replace_input_output_size_le v v' S _ _ ((Fin.castAdd_injective _ _).ne hne)
      sourceTail (output.flatten++outputTail)
    · rw [hsrc]; simp only [List.length_append]; omega
    · have hcount : output.length = ambient.length := haccuracy.length_eq.symm.trans hgood.length_eq
      have houtlen : ∀ line ∈ output, line.length = s*W := (List.forall₂_and_left _ _).mp haccuracy.flip |>.1
      have hambient : ∀ line ∈ ambient, line.length = s*W := (List.forall₂_and_left _ _).mp hgood.flip |>.1
      rw [hdst]
      simp only [List.length_append,length_flatten_const _ houtlen,length_flatten_const _ hambient,hcount]
  · have hstock := he.final
    apply ExecWithin.seq he
    exact hretire.mono (by intro d z hz; omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
