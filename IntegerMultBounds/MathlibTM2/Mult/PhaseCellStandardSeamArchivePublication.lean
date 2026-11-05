module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedReplicaPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringSeamArchivePublication
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

theorem standardSeamArchivePublication_exec (body : P → Pr P T Q A U)
    (rg : Fin 117 → Fin T) (hinj : Function.Injective rg)




    (p coreWidth k W : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (ks : List ℕ) (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p coreWidth r J) (k::ks) banks)
    (hcoreWidth : 0 < coreWidth) (hk : k ∈ coreIndices s coreWidth)
    (ambient : List (List (Fin (A+4)))) (hlen : ambient.length = r.inputs.length)
    (hambient : ∀ line ∈ ambient, line.length = s*W)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)


    (hcore : (S.R (rg 24)).length = coreLength s coreWidth k*W)
    (hskipMaster : (S.R (rg 26)).length = coreStart coreWidth k*W)
    (hfresh : ∀ i ∈ (standardSeamPublicationPlan.map rg hinj).support, i ≠ (standardSeamPublicationPlan.map rg hinj).advances → S.R i = [])
    (hsetupTmp : S.R (rg 27) = []) (hsetupSaved : S.R (rg 28) = [])


    (hretireTmp : S.R (rg 29) = [])
    (hwide : (S.R (rg 17)).length = W) (hword : (S.R (rg 18)).length = 2*p+13)
    (hcount : (S.R (rg 19)).length = r.inputs.length*coreLength s coreWidth k*(2*p+13))
    (hsrc : S.R (rg 95) = (banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)
    (hdst : S.R (rg 96) = ambient.flatten++outputTail)
    (hclock : (S.R (rg 15)).length = r.inputs.length) (hline : (S.R (rg 16)).length = s)
    (hblank : ∀ i ∈ [(rg 20),(rg 21),(rg 22),(rg 23)], S.R i = []) (depth : ℕ) :
    ∃ rows rest, banks = rows::rest ∧ SeamCropRows p coreWidth r J k rows ∧
    List.Forall₂ (SeamCropRows p coreWidth r J) ks rest ∧
    let F : Stacks T A := {S with R := (Function.update
          (Function.update S.R (rg 95)
            ((rest.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)) (rg 96)
            ((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail))}
    ∃ v' n, v'.user = v.user ∧ n ≤ restoringSeamCost (2*p+13) W r.inputs.length s (coreStart coreWidth k) (coreLength s coreWidth k) ∧
      n ≤ 250*(r.inputs.length+1)*(s*W) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3250*(r.inputs.length+1)*(s*W)) depth
        (restoringSeamPublication (standardSeamPublicationPlan.map rg hinj) (rg 15) (rg 16) (rg 17) (rg 18) (rg 19) (rg 20) (rg 21) (rg 22) (rg 23) (rg 24) (rg 17) (rg 26) (rg 27) (rg 28) (rg 29))
        (mk v S) n (mk v' F) ∧
      mnSize (mk v' F) ≤ mnSize (mk v S) ∧
      SeamArchiveState p coreWidth W r J (rg 95) (rg 96) sourceTail outputTail S ks F ∧
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
        SeamArchiveNumericalState p coreWidth W r J classes (rg 95) (rg 96) sourceTail outputTail S ks F) ∧
      ∀ j (hj : j < r.inputs.reverse.length),
        let out := pairedCellRead p W
          (((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail).drop (j*(s*W)))
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r)
            ((1/2 : ℂ) • fun i => value p (r.inputs.reverse[j] i))) (3/(2 : ℝ)^p) := by
  obtain ⟨hports,hreg,hsetup,hretire,hoff⟩ := standardSeamRegisters_mapped rg hinj
  exact restoringSeamArchivePublication_exec body (standardSeamPublicationPlan.map rg hinj)
    (rg 15) (rg 16) hports (rg 17) (rg 18) (rg 19) (rg 20) (rg 21) (rg 22) (rg 23) hreg
    p coreWidth k W hA hW r J ks banks hbanks hcoreWidth hk ambient hlen hambient
    sourceTail outputTail v S (rg 24) (rg 17) (rg 26) (rg 27) (rg 28) hsetup
    hcore hwide hskipMaster hfresh hsetupTmp hsetupSaved (rg 29) hretire hoff
    hretireTmp hwide hword hcount hsrc hdst hclock hline hblank depth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
