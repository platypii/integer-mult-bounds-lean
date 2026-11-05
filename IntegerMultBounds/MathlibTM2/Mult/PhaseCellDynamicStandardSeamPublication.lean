module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedStandardSeamPublication

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement BoundaryCropMetadata
variable {Q A s : ℕ} [NeZero s] {P U : Type}

/-- Generate controls, publish one seam, and release the generated controls. -/
def dynamicStandardSeamPublication (last : Bool) (cropCount : Fin 117) : Pr P 117 Q A U :=
  .seq (standardBoundaryMasterPreparation last cropCount)
    (.seq standardRestoringSeamProgram (clearWords [26,24,54,19]))

def dynamicStandardSeamCost (N narrowWidth D s width k W : ℕ) : ℕ :=
  let L := coreLength s width k
  (64*D+81)+(16*TableVM.tblC D 0+6*(s*W)+22*D+13)+(20*D+21)+
    ((6*(L*narrowWidth)+6)+(N*(4*(L*narrowWidth)+9)+4)) +
    restoringSeamCost narrowWidth W N s (coreStart width k) L +
    (2*(coreStart width k*W+L*W+L*narrowWidth+N*L*narrowWidth)+9)

theorem dynamicStandardSeamPublication_native (last : Bool) (cropCount : Fin 117) :
    mnNativePushBound 13
      (dynamicStandardSeamPublication (P := P) (Q := Q) (A := A) (U := U) last cropCount) := by
  exact ⟨mnNativePushBound_mono (by decide) (standardBoundaryMasterPreparation_native last cropCount),
    ⟨restoringSeamPublication_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      mnNativePushBound_mono (by decide) (clearWords_native _)⟩⟩

theorem dynamicStandardSeamPublication_exec (body : P → Pr P 117 Q A U)
    (p coreWidth k W : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (last : Bool) (cropCount : Fin 117)
    (hcropReg : [cropCount,15,54,19,27,28,24,26].Nodup)
    (D : ℕ) (hroom : 3*coreWidth < s) (hvolumeFit : s*W < 2^D)
    (hindex : BoundaryCropMetadata.index last s coreWidth = k)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,coreWidth,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (ks : List ℕ) (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p coreWidth r J) (k::ks) banks)
    (hcoreWidth : 0 < coreWidth) (hk : k ∈ coreIndices s coreWidth)
    (ambient : List (List (Fin (A+4)))) (hlen : ambient.length = r.inputs.length)
    (hambient : ∀ line ∈ ambient, line.length = s*W)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hwidthRuler : (S.R 58).length = D) (hzero : S.R 59 = [])
    (hwords : ∀ j, S.R (boundarySeedGlobals j) = binSyms D (seedValue (boundarySeedGlobals j)))
    (htableBlank : ∀ r, S.R (boundaryCounterRegister r) = [])
    (hmasters : S.R 26 = [] ∧ S.R 24 = [] ∧ S.R 54 = [] ∧ S.R 19 = [])
    (hbits : (S.R cropCount).length = coreLength s coreWidth k*(2*p+13))
    (hfresh : ∀ i ∈ standardSeamPublicationPlan.support, i ≠ standardSeamPublicationPlan.advances → S.R i = [])
    (hsetupTmp : S.R (27:Fin 117) = []) (hsetupSaved : S.R (28:Fin 117) = [])
    (hretireTmp : S.R (29:Fin 117) = [])
    (hwide : (S.R (17:Fin 117)).length = W) (hword : (S.R (18:Fin 117)).length = 2*p+13)

    (hsrc : S.R (95:Fin 117) = (banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)
    (hdst : S.R (96:Fin 117) = ambient.flatten++outputTail)
    (hclock : (S.R (15:Fin 117)).length = r.inputs.length) (hline : (S.R (16:Fin 117)).length = s)
    (hblank : ∀ i ∈ [(20:Fin 117),(21:Fin 117),(22:Fin 117),(23:Fin 117)], S.R i = []) (depth : ℕ) :
    ∃ rows rest, banks = rows::rest ∧ SeamCropRows p coreWidth r J k rows ∧
    List.Forall₂ (SeamCropRows p coreWidth r J) ks rest ∧
    let F : Stacks 117 A := {S with R := (Function.update
          (Function.update S.R (95:Fin 117)
            ((rest.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)) (96:Fin 117)
            ((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail))}
    ∃ v' n, v'.user = v.user ∧
      n ≤ dynamicStandardSeamCost r.inputs.length (2*p+13) D s coreWidth k W ∧
      Exec body (dynamicStandardSeamPublication last cropCount) (mk v S) n (mk v' F) ∧
      mnSize (mk v' F) ≤ mnSize (mk v S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+13*dynamicStandardSeamCost r.inputs.length (2*p+13) D s coreWidth k W) depth
        (dynamicStandardSeamPublication last cropCount) (mk v S) n (mk v' F) ∧
      (∀ classes : ℕ → CorePublicationClass s coreWidth,
        classes k = singletonCorePublication s coreWidth k hk →
        PublicationBankPending ((k::ks).map classes) p W
          (seamPublicationTargets p r J) (3/(2:ℝ)^p) ambient →
        SeamArchiveNumericalState p coreWidth W r J classes 95 96 sourceTail outputTail S ks F) ∧
      ∀ j (hj : j < r.inputs.reverse.length),
        let out := pairedCellRead p W
          (((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail).drop (j*(s*W)))
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r)
            ((1/2 : ℂ) • fun i => value p (r.inputs.reverse[j] i))) (3/(2 : ℝ)^p) := by
  obtain ⟨u,m,hu,hm,hprep⟩ := standardBoundaryMasterPreparation_exec body last cropCount hcropReg
    r.inputs.length (2*p+13) D s coreWidth W hcoreWidth (by omega) hroom hvolumeFit seedValue hvalues hfit
    v S hwidthRuler hzero hwords htableBlank ⟨hmasters.1,hmasters.2.1⟩ hclock
    (by simpa only [hindex] using hbits)
    ⟨hmasters.2.2.1,hmasters.2.2.2,hsetupTmp,hsetupSaved⟩ depth
  rw [hindex] at hprep hm
  simpa only [preparedStandardSeamPublication,preparedStandardSeamCost,
    dynamicStandardSeamPublication,dynamicStandardSeamCost] using
    preparedStandardSeamPublication_exec body p coreWidth k W hA hW cropCount r J ks banks hbanks
      hcoreWidth hk ambient hlen hambient sourceTail outputTail v S hmasters hbits hfresh
      hsetupTmp hsetupSaved hretireTmp hwide hword hsrc hdst hclock hline hblank depth
      (standardBoundaryMasterPreparation last cropCount)
      ((64*D+81)+(16*TableVM.tblC D 0+6*(s*W)+22*D+13)+(20*D+21)+
        ((6*(coreLength s coreWidth k*(2*p+13))+6)+
          (r.inputs.length*(4*(coreLength s coreWidth k*(2*p+13))+9)+4)))
      (standardBoundaryMasterPreparation_native last cropCount) ⟨u,m,hu,hm,hprep⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
