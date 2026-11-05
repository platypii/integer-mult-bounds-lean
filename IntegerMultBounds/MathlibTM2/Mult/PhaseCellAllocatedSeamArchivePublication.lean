module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedReplicaPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardSeamArchivePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedSeamPublicationPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardSeamRegisters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringSeamProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringSeamCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamArchiveState
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamArchiveNumericalState
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonPublicationSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamArchiveHandoff
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonPublicationClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonAdvanceControls

/-! Publish actual seam witnesses with derived replica records and an exact
restoring endpoint. The caller supplies ordinary controls, not replica data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type}

theorem allocatedSeamArchivePublication_exec (body : P → Pr P (T+PackedTranspose.tapeCount) Q A U)
    (source destination : Fin T) (hne : source ≠ destination)




    (p coreWidth k W : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (ks : List ℕ) (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p coreWidth r J) (k::ks) banks)
    (hcoreWidth : 0 < coreWidth) (hk : k ∈ coreIndices s coreWidth)
    (ambient : List (List (Fin (A+4)))) (hlen : ambient.length = r.inputs.length)
    (hambient : ∀ line ∈ ambient, line.length = s*W)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS (T+PackedTranspose.tapeCount) Q A U) (S : Stacks (T+PackedTranspose.tapeCount) A)


    (hcore : (S.R ((PackedTranspose.seamRegister source destination) 24)).length = coreLength s coreWidth k*W)
    (hskipMaster : (S.R ((PackedTranspose.seamRegister source destination) 26)).length = coreStart coreWidth k*W)
    (hfresh : ∀ i ∈ (standardSeamPublicationPlan.map (PackedTranspose.seamRegister source destination) (PackedTranspose.seamRegister_injective source destination hne)).support, i ≠ (standardSeamPublicationPlan.map (PackedTranspose.seamRegister source destination) (PackedTranspose.seamRegister_injective source destination hne)).advances → S.R i = [])
    (hsetupTmp : S.R ((PackedTranspose.seamRegister source destination) 27) = []) (hsetupSaved : S.R ((PackedTranspose.seamRegister source destination) 28) = [])


    (hretireTmp : S.R ((PackedTranspose.seamRegister source destination) 29) = [])
    (hwide : (S.R ((PackedTranspose.seamRegister source destination) 17)).length = W) (hword : (S.R ((PackedTranspose.seamRegister source destination) 18)).length = 2*p+13)
    (hcount : (S.R ((PackedTranspose.seamRegister source destination) 19)).length = r.inputs.length*coreLength s coreWidth k*(2*p+13))
    (hsrc : S.R (Fin.castAdd PackedTranspose.tapeCount source) = (banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)
    (hdst : S.R (Fin.castAdd PackedTranspose.tapeCount destination) = ambient.flatten++outputTail)
    (hclock : (S.R ((PackedTranspose.seamRegister source destination) 15)).length = r.inputs.length) (hline : (S.R ((PackedTranspose.seamRegister source destination) 16)).length = s)
    (hblank : ∀ i ∈ [((PackedTranspose.seamRegister source destination) 20),((PackedTranspose.seamRegister source destination) 21),((PackedTranspose.seamRegister source destination) 22),((PackedTranspose.seamRegister source destination) 23)], S.R i = []) (depth : ℕ) :
    ∃ rows rest, banks = rows::rest ∧ SeamCropRows p coreWidth r J k rows ∧
    List.Forall₂ (SeamCropRows p coreWidth r J) ks rest ∧
    let F : Stacks (T+PackedTranspose.tapeCount) A := {S with R := (Function.update
          (Function.update S.R (Fin.castAdd PackedTranspose.tapeCount source)
            ((rest.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)) (Fin.castAdd PackedTranspose.tapeCount destination)
            ((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail))}
    ∃ v' n, v'.user = v.user ∧ n ≤ restoringSeamCost (2*p+13) W r.inputs.length s (coreStart coreWidth k) (coreLength s coreWidth k) ∧
      n ≤ 250*(r.inputs.length+1)*(s*W) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3250*(r.inputs.length+1)*(s*W)) depth
        (restoringSeamPublication (standardSeamPublicationPlan.map (PackedTranspose.seamRegister source destination) (PackedTranspose.seamRegister_injective source destination hne)) ((PackedTranspose.seamRegister source destination) 15) ((PackedTranspose.seamRegister source destination) 16) ((PackedTranspose.seamRegister source destination) 17) ((PackedTranspose.seamRegister source destination) 18) ((PackedTranspose.seamRegister source destination) 19) ((PackedTranspose.seamRegister source destination) 20) ((PackedTranspose.seamRegister source destination) 21) ((PackedTranspose.seamRegister source destination) 22) ((PackedTranspose.seamRegister source destination) 23) ((PackedTranspose.seamRegister source destination) 24) ((PackedTranspose.seamRegister source destination) 17) ((PackedTranspose.seamRegister source destination) 26) ((PackedTranspose.seamRegister source destination) 27) ((PackedTranspose.seamRegister source destination) 28) ((PackedTranspose.seamRegister source destination) 29))
        (mk v S) n (mk v' F) ∧
      mnSize (mk v' F) ≤ mnSize (mk v S) ∧
      SeamArchiveState p coreWidth W r J (Fin.castAdd PackedTranspose.tapeCount source) (Fin.castAdd PackedTranspose.tapeCount destination) sourceTail outputTail S ks F ∧
      (∀ gs : List (CorePublicationClass s coreWidth),
        PublicationBankPending (singletonCorePublication s coreWidth k hk::gs) p W
          (seamPublicationTargets p r J) (3/(2:ℝ)^p) ambient →
        PublicationBankPending gs p W (seamPublicationTargets p r J) (3/(2:ℝ)^p)
          (List.zipWith (fun row line =>
          (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
          (rows.map (List.map (symZ (2*p+13)))) ambient)) ∧
      (∀ classes : ℕ → CorePublicationClass s coreWidth,
        classes k = singletonCorePublication s coreWidth k hk →
        PublicationBankPending ((k::ks).map classes) p W (seamPublicationTargets p r J) (3/(2:ℝ)^p) ambient →
        SeamArchiveNumericalState p coreWidth W r J classes (Fin.castAdd PackedTranspose.tapeCount source) (Fin.castAdd PackedTranspose.tapeCount destination) sourceTail outputTail S ks F) ∧
      ∀ j (hj : j < r.inputs.reverse.length),
        let out := pairedCellRead p W
          (((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail).drop (j*(s*W)))
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r)
            ((1/2 : ℂ) • fun i => value p (r.inputs.reverse[j] i))) (3/(2 : ℝ)^p) := by
  let rg := PackedTranspose.seamRegister source destination
  have hinj := PackedTranspose.seamRegister_injective source destination hne
  have hsrc' : S.R (rg 95) = (banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail := by
    simpa only [rg,PackedTranspose.seamRegister_source] using hsrc
  have hdst' : S.R (rg 96) = ambient.flatten++outputTail := by
    simpa only [rg,PackedTranspose.seamRegister_destination] using hdst
  simpa only [rg,PackedTranspose.seamRegister_source,PackedTranspose.seamRegister_destination] using
    (standardSeamArchivePublication_exec body rg hinj p coreWidth k W hA hW r J ks banks hbanks
      hcoreWidth hk ambient hlen hambient sourceTail outputTail v S hcore hskipMaster
      hfresh hsetupTmp hsetupSaved hretireTmp hwide hword hcount hsrc' hdst' hclock hline hblank depth)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
