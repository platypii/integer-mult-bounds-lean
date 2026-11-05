module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedReplicaPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamPublicationAccuracy

/-! Publish actual seam witnesses with derived replica records and an exact
restoring endpoint. The caller supplies ordinary controls, not replica data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {src dst : Fin T}

theorem seamPublication_exec (body : P → Pr P T Q A U)
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
    (hwide : (S.R wide).length = W) (hword : (S.R width).length = 2*p+13)
    (hcount : (S.R count).length = r.inputs.length*coreLength s coreWidth k*(2*p+13))
    (hsrc : S.R src = cstream A (2*p+13) rows.flatten++sourceTail)
    (hdst : S.R dst = ambient.flatten++outputTail)
    (hclock : (S.R clock).length = r.inputs.length) (hline : (S.R lineRows).length = s)
    (hblank : ∀ i ∈ [work,saved,tmp,extra], S.R i = []) (depth : ℕ) :
    let replicas := singletonPublicationReplicas (rows.map (List.map (symZ (2*p+13)))) ambient
    let bill := widenPackedPrefixCost (2*p+13) W (r.inputs.length*coreLength s coreWidth k)+
      (replicaPublicationCost r.inputs.length s 0 (coreLength s coreWidth k) W+37*s*W+6*r.inputs.length+31)
    ∃ v' n, v'.user = v.user ∧ n ≤ bill ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+13*bill) depth
        (.seq (widenPackedPrefix wide width count src work saved tmp extra) (plan.replicaProgram clock lineRows))
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R src sourceTail) dst
          (replicas.flatMap (PublicationReplica.output windows W)++outputTail))}) ∧
      ∀ j (hj : j < r.inputs.reverse.length),
        let out := pairedCellRead p W
          ((replicas.flatMap (PublicationReplica.output windows W)++outputTail).drop (j*(s*W)))
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r)
            ((1/2 : ℂ) • fun i => value p (r.inputs.reverse[j] i))) (3/(2 : ℝ)^p) := by
  dsimp only
  let replicas := singletonPublicationReplicas (rows.map (List.map (symZ (2*p+13)))) ambient
  obtain ⟨hn,ha,heq,hpairs,hvalid⟩ := seamPublicationReplicas_spec p coreWidth k W r J rows hrows
    windows (by simp [hwindow]) ambient hlen hambient
  change replicas.length = r.inputs.length at hn
  have hvolume : rows.flatten.length = r.inputs.length*coreLength s coreWidth k := by
    simpa only [List.length_map] using hrows.commonWidth_volume p coreWidth k r J rows
  have hdest : S.R dst = replicas.flatMap PublicationReplica.ambient++outputTail := by
    rw [List.flatMap_def,ha]
    exact hdst
  obtain ⟨v',F,n,hu,hcost,hex,hs,hd,hi,ho,hl,hframe⟩ := widenedReplicaPublication_exec body plan clock lineRows hports
    wide width count work saved tmp extra hreg windows (2*p+13) W (by omega) hW
    rows.flatten replicas hvalid heq sourceTail outputTail borrowed v S hready hwide hword
    (by simpa only [hvolume] using hcount) hsrc hdest (by simpa only [hn] using hclock) hline hblank
  rw [hvolume,hn] at hcost
  have hend : F = {S with R := (Function.update (Function.update S.R src sourceTail) dst
      (replicas.flatMap (PublicationReplica.output windows W)++outputTail))} := by
    refine Stacks.ext hi ho hl ?_
    funext i
    by_cases hd' : i = dst
    · subst i; simpa using hd
    by_cases hs' : i = src
    · subst i; simpa [plan.src_ne_dst] using hs
    · simpa only [Function.update_of_ne hd',Function.update_of_ne hs'] using hframe i hs' hd'
  rw [hend] at hex
  refine ⟨v',n,hu,hcost,widenedReplicaPublication_within body plan clock lineRows wide width count work saved tmp extra
    v v' S _ n _ depth hex hcost,?_⟩
  intro j hj
  exact seamPublication_accurate p coreWidth k W hA hW r J rows hrows windows hwindow
    ambient hlen hambient outputTail _ rfl j hj

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
