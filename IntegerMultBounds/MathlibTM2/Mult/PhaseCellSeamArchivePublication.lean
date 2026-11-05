module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedReplicaPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamPublicationRetirement
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

theorem seamArchivePublication_exec (body : P → Pr P T Q A U)
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
    (hready : plan.Ready (singletonCoreWindows hcoreWidth hk) W 0 borrowed S)
    (skip retireTmp : Fin T) (hretire : [skip,plan.advances,retireTmp,src,dst].Nodup)
    (hretireTmp : S.R retireTmp = [])
    (hskip : (S.R skip).length = coreStart coreWidth k*W)
    (hwide : (S.R wide).length = W) (hword : (S.R width).length = 2*p+13)
    (hcount : (S.R count).length = r.inputs.length*coreLength s coreWidth k*(2*p+13))
    (hsrc : S.R src = (banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)
    (hdst : S.R dst = ambient.flatten++outputTail)
    (hclock : (S.R clock).length = r.inputs.length) (hline : (S.R lineRows).length = s)
    (hblank : ∀ i ∈ [work,saved,tmp,extra], S.R i = []) (depth : ℕ) :
    ∃ rows rest, banks = rows::rest ∧ SeamCropRows p coreWidth r J k rows ∧
    List.Forall₂ (SeamCropRows p coreWidth r J) ks rest ∧
    let bill := widenPackedPrefixCost (2*p+13) W (r.inputs.length*coreLength s coreWidth k)+
      (replicaPublicationCost r.inputs.length s 0 (coreLength s coreWidth k) W+37*s*W+6*r.inputs.length+31)
    ∃ v' n, v'.user = v.user ∧ n ≤ bill+(4*(coreStart coreWidth k*W)+5) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        13*(bill+(4*(coreStart coreWidth k*W)+5))) depth
        (.seq (.seq (widenPackedPrefix wide width count src work saved tmp extra)
          (plan.replicaProgram clock lineRows)) (retireSingletonAdvances skip plan.advances retireTmp))
        (mk v S) n (mk v' {S with R := (Function.update
          (Function.update (Function.update S.R src
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
  obtain ⟨rows,rest,hbanks',hrows,hrest,hbytes⟩ := seamArchiveHandoff p coreWidth k ks r J banks hbanks sourceTail
  refine ⟨rows,rest,hbanks',hrows,hrest,?_⟩
  simpa only [singletonPublicationReplicas_class_output] using
    (seamPublication_retire_exec body plan clock lineRows hports wide width count work saved tmp extra
    hreg p coreWidth k W hA hW r J rows hrows (singletonCoreWindows hcoreWidth hk) (singletonCoreWindows_origins hcoreWidth hk) ambient hlen hambient
    ((rest.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)
    outputTail borrowed v S hready skip retireTmp hretire hretireTmp hskip hwide hword hcount
    (hsrc.trans hbytes) hdst hclock hline hblank depth)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
