module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedReplicaPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamArchivePublication
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
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {src dst : Fin T}

theorem setupSeamArchivePublication_exec (body : P → Pr P T Q A U)
    (plan : PreparedPublicationPlan T src dst) (clock lineRows : Fin T)
    (hports : (plan.support++[src,dst,clock,lineRows]).Nodup)
    (wide width count work saved tmp extra : Fin T)
    (hreg : [wide,width,count,src,work,saved,tmp,extra].Nodup)
    (p coreWidth k W : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (ks : List ℕ) (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p coreWidth r J) (k::ks) banks)
    (hcoreWidth : 0 < coreWidth) (hk : k ∈ coreIndices s coreWidth)
    (ambient : List (List (Fin (A+4)))) (hlen : ambient.length = r.inputs.length)
    (hambient : ∀ line ∈ ambient, line.length = s*W)
    (sourceTail outputTail borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (coreBits wordWidth setupSkip setupTmp setupSaved : Fin T)
    (hsetupReg : (plan.support++[coreBits,wordWidth,setupSkip,setupTmp,setupSaved]).Nodup)
    (hcore : (S.R coreBits).length = coreLength s coreWidth k*W)
    (hwidthMaster : (S.R wordWidth).length = W)
    (hskipMaster : (S.R setupSkip).length = coreStart coreWidth k*W)
    (hfresh : ∀ i ∈ plan.support, i ≠ plan.advances → S.R i = [])
    (hsetupTmp : S.R setupTmp = []) (hsetupSaved : S.R setupSaved = [])
    (B : Stacks T A)
    (hB : B = singletonPublicationSetupState plan coreBits wordWidth (coreStart coreWidth k) W S)
    (hborrowed : borrowed = S.R plan.advances)
    (skip retireTmp : Fin T) (hretire : [skip,plan.advances,retireTmp,src,dst].Nodup)
    (hretireTmp : B.R retireTmp = [])
    (hskip : (B.R skip).length = coreStart coreWidth k*W)
    (hwide : (B.R wide).length = W) (hword : (B.R width).length = 2*p+13)
    (hcount : (B.R count).length = r.inputs.length*coreLength s coreWidth k*(2*p+13))
    (hsrc : B.R src = (banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)
    (hdst : B.R dst = ambient.flatten++outputTail)
    (hclock : (B.R clock).length = r.inputs.length) (hline : (B.R lineRows).length = s)
    (hblank : ∀ i ∈ [work,saved,tmp,extra], B.R i = []) (depth : ℕ) :
    ∃ rows rest, banks = rows::rest ∧ SeamCropRows p coreWidth r J k rows ∧
    List.Forall₂ (SeamCropRows p coreWidth r J) ks rest ∧
    let bill := widenPackedPrefixCost (2*p+13) W (r.inputs.length*coreLength s coreWidth k)+
      (replicaPublicationCost r.inputs.length s 0 (coreLength s coreWidth k) W+37*s*W+6*r.inputs.length+31)
    let totalBill := (6*(coreLength s coreWidth k*W)+6*W+13)+(1+(4*(coreStart coreWidth k*W)+5))+bill+(4*(coreStart coreWidth k*W)+5)
    ∃ v' n, v'.user = v.user ∧ n ≤ totalBill ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+13*totalBill) depth
        (.seq (singletonPublicationSetup plan coreBits wordWidth setupSkip setupTmp setupSaved)
          (.seq (.seq (widenPackedPrefix wide width count src work saved tmp extra)
          (plan.replicaProgram clock lineRows)) (retireSingletonAdvances skip plan.advances retireTmp)))
        (mk v S) n (mk v' {B with R := (Function.update
          (Function.update (Function.update B.R src
            ((rest.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)) dst
            ((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail)) plan.advances borrowed)}) ∧
      ∀ j (hj : j < r.inputs.reverse.length),
        let out := pairedCellRead p W
          (((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail).drop (j*(s*W)))
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r)
            ((1/2 : ℂ) • fun i => value p (r.inputs.reverse[j] i))) (3/(2 : ℝ)^p) := by
  obtain ⟨u,m,hu,hm,hprepare,hready⟩ := singletonPublicationSetup_exec (body := body) plan
    coreBits wordWidth setupSkip setupTmp setupSaved hsetupReg (singletonCoreWindows hcoreWidth hk)
    (coreStart coreWidth k) W (singletonCoreWindows_origins hcoreWidth hk) v S
    hcore hwidthMaster hskipMaster hfresh hsetupTmp hsetupSaved depth
  rw [←hB] at hprepare hready
  rw [←hborrowed] at hready
  obtain ⟨rows,rest,hbanks',hrows,hrest,u',n,hu',hn,hex,hgood⟩ := seamArchivePublication_exec body
    plan clock lineRows hports wide width count work saved tmp extra hreg p coreWidth k W hA hW
    r J ks banks hbanks hcoreWidth hk ambient hlen hambient sourceTail outputTail borrowed u B
    hready skip retireTmp hretire hretireTmp hskip hwide hword hcount hsrc hdst hclock hline hblank depth
  refine ⟨rows,rest,hbanks',hrows,hrest,u',m+n,hu'.trans hu,?_,?_,hgood⟩
  · omega
  · apply mn_native_exec_within (Exec.seq hprepare.toExec hex.toExec) 13
    · exact ⟨mnNativePushBound_mono (by decide)
        (singletonPublicationSetup_native plan coreBits wordWidth setupSkip setupTmp setupSaved),
        ⟨⟨widenPackedPrefix_native _ _ _ _ _ _ _ _,
          mnNativePushBound_mono (by decide) (plan.replica_native clock lineRows)⟩,
          mnNativePushBound_mono (by decide) (retireSingletonAdvances_native skip plan.advances retireTmp)⟩⟩
    · omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
