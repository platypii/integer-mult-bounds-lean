module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedReplicaPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamPublicationRun
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

theorem seamPublication_retire_exec (body : P → Pr P T Q A U)
    (plan : PreparedPublicationPlan T src dst) (clock lineRows : Fin T)
    (hports : (plan.support++[src,dst,clock,lineRows]).Nodup)
    (wide width count work saved tmp extra : Fin T)
    (hreg : [wide,width,count,src,work,saved,tmp,extra].Nodup)
    (p coreWidth k W : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (rows : List (List GaussianInt)) (hrows : SeamCropRows p coreWidth r J k rows)
    (windows : PublicationWindows s (coreLength s coreWidth k)) (hwindow : windows.origins = [coreStart coreWidth k])
    (ambient : List (List (Fin (A+4)))) (hlen : ambient.length = r.inputs.length)
    (hambient : ∀ line ∈ ambient, line.length = s*W)
    (sourceTail outputTail borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : plan.Ready windows W 0 borrowed S)
    (skip retireTmp : Fin T) (hretire : [skip,plan.advances,retireTmp,src,dst].Nodup)
    (hretireTmp : S.R retireTmp = [])
    (hskip : (S.R skip).length = coreStart coreWidth k*W)
    (hwide : (S.R wide).length = W) (hword : (S.R width).length = 2*p+13)
    (hcount : (S.R count).length = r.inputs.length*coreLength s coreWidth k*(2*p+13))
    (hsrc : S.R src = cstream A (2*p+13) rows.flatten++sourceTail)
    (hdst : S.R dst = ambient.flatten++outputTail)
    (hclock : (S.R clock).length = r.inputs.length) (hline : (S.R lineRows).length = s)
    (hblank : ∀ i ∈ [work,saved,tmp,extra], S.R i = []) (depth : ℕ) :
    let replicas := singletonPublicationReplicas (rows.map (List.map (symZ (2*p+13)))) ambient
    let bill := widenPackedPrefixCost (2*p+13) W (r.inputs.length*coreLength s coreWidth k)+
      (replicaPublicationCost r.inputs.length s 0 (coreLength s coreWidth k) W+37*s*W+6*r.inputs.length+31)
    ∃ v' n, v'.user = v.user ∧ n ≤ bill+(4*(coreStart coreWidth k*W)+5) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        13*(bill+(4*(coreStart coreWidth k*W)+5))) depth
        (.seq (.seq (widenPackedPrefix wide width count src work saved tmp extra)
          (plan.replicaProgram clock lineRows)) (retireSingletonAdvances skip plan.advances retireTmp))
        (mk v S) n (mk v' {S with R := (Function.update
          (Function.update (Function.update S.R src sourceTail) dst
            (replicas.flatMap (PublicationReplica.output windows W)++outputTail)) plan.advances borrowed)}) ∧
      ∀ j (hj : j < r.inputs.reverse.length),
        let out := pairedCellRead p W
          ((replicas.flatMap (PublicationReplica.output windows W)++outputTail).drop (j*(s*W)))
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r)
            ((1/2 : ℂ) • fun i => value p (r.inputs.reverse[j] i))) (3/(2 : ℝ)^p) := by
  dsimp only
  obtain ⟨u,n,hu,hn,hex,hgood⟩ := seamPublication_exec body plan clock lineRows hports
    wide width count work saved tmp extra hreg p coreWidth k W hA hW r J rows hrows
    windows hwindow ambient hlen hambient sourceTail outputTail borrowed v S hready
    hwide hword hcount hsrc hdst hclock hline hblank depth
  let output := (singletonPublicationReplicas (rows.map (List.map (symZ (2*p+13)))) ambient).flatMap
    (PublicationReplica.output windows W)++outputTail
  let F : Stacks T A := {S with R := (Function.update (Function.update S.R src sourceTail) dst output)}
  have hr := hretire
  regs_ne hr
  have hadv : S.R plan.advances = gatherControls A [(S.R skip).length,0]++borrowed := by
    simpa [hwindow,originAdvances,hskip] using hready.advances
  obtain ⟨u',hu',he⟩ := retireSingletonAdvances_exec (body := body) skip plan.advances retireTmp
    ‹skip ≠ plan.advances› ‹skip ≠ retireTmp› ‹plan.advances ≠ retireTmp› u F
    (by simpa [F,Function.update_of_ne, *,Ne.symm] using hretireTmp) borrowed
    (by simpa [F,Function.update_of_ne, *,Ne.symm] using hadv)
  have hlen : (F.R skip).length = coreStart coreWidth k*W := by
    simpa [F,Function.update_of_ne, *,Ne.symm] using hskip
  rw [hlen] at he
  refine ⟨u',n+(4*(coreStart coreWidth k*W)+5),hu'.trans hu,by omega,?_,hgood⟩
  apply mn_native_exec_within (Exec.seq hex.toExec he) 13
  · exact ⟨⟨widenPackedPrefix_native _ _ _ _ _ _ _ _,
      mnNativePushBound_mono (by decide) (plan.replica_native clock lineRows)⟩,
      mnNativePushBound_mono (by decide) (retireSingletonAdvances_native skip plan.advances retireTmp)⟩
  · omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
