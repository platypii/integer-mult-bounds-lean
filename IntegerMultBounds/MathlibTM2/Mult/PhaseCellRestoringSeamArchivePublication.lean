module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedReplicaPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupSeamArchivePublication
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
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {src dst : Fin T}

theorem restoringSeamArchivePublication_exec (body : P → Pr P T Q A U)
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
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (coreBits wordWidth skip setupTmp setupSaved : Fin T)
    (hsetupReg : (plan.support++[coreBits,wordWidth,skip,setupTmp,setupSaved]).Nodup)
    (hcore : (S.R coreBits).length = coreLength s coreWidth k*W)
    (hwidthMaster : (S.R wordWidth).length = W)
    (hskipMaster : (S.R skip).length = coreStart coreWidth k*W)
    (hfresh : ∀ i ∈ plan.support, i ≠ plan.advances → S.R i = [])
    (hsetupTmp : S.R setupTmp = []) (hsetupSaved : S.R setupSaved = [])
    (retireTmp : Fin T) (hretire : [skip,plan.advances,retireTmp,src,dst].Nodup)
    (hoff : ∀ i ∈ [retireTmp,skip,wide,width,count,src,dst,clock,lineRows,work,saved,tmp,extra],
      i ∉ [plan.count,plan.window,plan.wordWidth,plan.advances])
    (hretireTmp : S.R retireTmp = [])
    (hwide : (S.R wide).length = W) (hword : (S.R width).length = 2*p+13)
    (hcount : (S.R count).length = r.inputs.length*coreLength s coreWidth k*(2*p+13))
    (hsrc : S.R src = (banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)
    (hdst : S.R dst = ambient.flatten++outputTail)
    (hclock : (S.R clock).length = r.inputs.length) (hline : (S.R lineRows).length = s)
    (hblank : ∀ i ∈ [work,saved,tmp,extra], S.R i = []) (depth : ℕ) :
    ∃ rows rest, banks = rows::rest ∧ SeamCropRows p coreWidth r J k rows ∧
    List.Forall₂ (SeamCropRows p coreWidth r J) ks rest ∧
    let F : Stacks T A := {S with R := (Function.update
          (Function.update S.R src
            ((rest.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)) dst
            ((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail))}
    ∃ v' n, v'.user = v.user ∧ n ≤ restoringSeamCost (2*p+13) W r.inputs.length s (coreStart coreWidth k) (coreLength s coreWidth k) ∧
      n ≤ 250*(r.inputs.length+1)*(s*W) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3250*(r.inputs.length+1)*(s*W)) depth
        (restoringSeamPublication plan clock lineRows wide width count work saved tmp extra coreBits wordWidth skip setupTmp setupSaved retireTmp)
        (mk v S) n (mk v' F) ∧
      mnSize (mk v' F) ≤ mnSize (mk v S) ∧
      SeamArchiveState p coreWidth W r J src dst sourceTail outputTail S ks F ∧
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
        SeamArchiveNumericalState p coreWidth W r J classes src dst sourceTail outputTail S ks F) ∧
      ∀ j (hj : j < r.inputs.reverse.length),
        let out := pairedCellRead p W
          (((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail).drop (j*(s*W)))
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r)
            ((1/2 : ℂ) • fun i => value p (r.inputs.reverse[j] i))) (3/(2 : ℝ)^p) := by
  dsimp only [restoringSeamCost]
  let B := singletonPublicationSetupState plan coreBits wordWidth (coreStart coreWidth k) W S
  have hB : B = singletonPublicationSetupState plan coreBits wordWidth (coreStart coreWidth k) W S := rfl
  let borrowed := S.R plan.advances
  have hborrowed : borrowed = S.R plan.advances := rfl
  have hframe (i : Fin T)
      (hi : i ∈ [retireTmp,skip,wide,width,count,src,dst,clock,lineRows,work,saved,tmp,extra]) :
      B.R i = S.R i := by
    rw [hB]
    exact singletonPublicationSetupState_off plan coreBits wordWidth (coreStart coreWidth k) W S i (hoff i hi)
  obtain ⟨rows,rest,hbanks',hrows,hrest,u,n,hu,hn,hex,hgood⟩ := setupSeamArchivePublication_exec body
    plan clock lineRows hports wide width count work saved tmp extra hreg p coreWidth k W hA hW
    r J ks banks hbanks hcoreWidth hk ambient hlen hambient sourceTail outputTail borrowed v S
    coreBits wordWidth skip setupTmp setupSaved hsetupReg hcore hwidthMaster hskipMaster
    hfresh hsetupTmp hsetupSaved B hB hborrowed skip retireTmp hretire
    (by rw [hframe _ (by simp)]; exact hretireTmp)
    (by rw [hframe _ (by simp)]; exact hskipMaster)
    (by rw [hframe _ (by simp)]; exact hwide)
    (by rw [hframe _ (by simp)]; exact hword)
    (by rw [hframe _ (by simp)]; exact hcount)
    (by rw [hframe _ (by simp)]; exact hsrc)
    (by rw [hframe _ (by simp)]; exact hdst)
    (by rw [hframe _ (by simp)]; exact hclock)
    (by rw [hframe _ (by simp)]; exact hline)
    (by intro i hi; rw [hframe i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp)]; exact hblank i hi) depth
  let source := (rest.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail
  let output := (List.zipWith (fun row line =>
    (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
    (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail
  have hblanks : S.R plan.count = [] ∧ S.R plan.window = [] ∧ S.R plan.wordWidth = [] := by
    have hr := plan.hreg
    regs_ne hr
    exact ⟨hfresh _ (by simp [PreparedPublicationPlan.support]) (by assumption),
      hfresh _ (by simp [PreparedPublicationPlan.support]) (Ne.symm (by assumption)),
      hfresh _ (by simp [PreparedPublicationPlan.support]) (Ne.symm (by assumption))⟩
  obtain ⟨u',hu',he⟩ := retireSingletonDimensions_after_setup (body := body) plan coreBits wordWidth
    (coreStart coreWidth k) W u S
    hblanks.1 hblanks.2.1 hblanks.2.2 source output
  rw [←hB,←hborrowed] at he
  have hlast := hex.final
  have hclear := retireSingletonDimensions_within plan u u' _ _ _ depth he
  have hvolume := restoringSeamCost_le (2*p+13) W r.inputs.length s
    (coreStart coreWidth k) (coreLength s coreWidth k) (NeZero.pos s) (by omega) hW
    (coreStart_lt_of_mem hk).le (by unfold coreLength; omega)
  refine ⟨rows,rest,hbanks',hrows,hrest,u',n+(2*(1+(S.R coreBits).length+(S.R wordWidth).length)+7),hu'.trans hu,by omega,?_,?_,?_,?_,?_,?_,hgood⟩
  · dsimp only [restoringSeamCost] at hvolume
    omega
  apply mn_native_exec_within (Exec.seq hex.toExec he) 13
  · exact restoringSeamPublication_native plan clock lineRows wide width count work saved tmp extra coreBits wordWidth skip setupTmp setupSaved retireTmp
  · dsimp only [restoringSeamCost] at hvolume
    nlinarith [hcore,hwidthMaster]
  · apply mn_replace_input_output_size_le v u' S src dst plan.src_ne_dst source output
    · rw [hsrc,hbanks']
      simp only [List.map_cons,List.flatten_cons,List.length_append]
      dsimp only [source]
      simp only [List.length_append]
      omega
    · have hrowCount : rows.length = r.inputs.length := by
        simpa only [List.length_reverse] using hrows.2.length_eq.symm
      have hwideRows : ∀ row ∈ rows.map (List.map (symZ (2*p+13))),
          row.length = coreLength s coreWidth k := by
        intro row hr
        obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hr
        simpa only [List.length_map] using hrows.1 xs hxs
      have hlen := singletonPublication_class_length hcoreWidth hk W
        (rows.map (List.map (symZ (2*p+13)))) ambient
        (by simp [hrowCount,hlen]) hwideRows hambient
      rw [hdst]
      simpa only [output,List.length_append,hlen]
  · have hstep := SeamArchiveState.step p coreWidth W k r J src dst plan.src_ne_dst
      sourceTail outputTail S ks rows rest hrows hrest (singletonCoreWindows hcoreWidth hk)
      (by simp) ambient hlen hambient
    have hstart : ({S with R := (Function.update (Function.update S.R src
        (((rows::rest).map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail))
        dst (ambient.flatten++outputTail))} : Stacks T A) = S := by
      rw [←hbanks',←hsrc,←hdst]
      simp
    have hrstart := congrArg Stacks.R hstart
    dsimp only at hrstart
    simpa only [hrstart,singletonPublicationReplicas_class_output] using hstep
  · intro gs hInv
    exact seamPublication_bank_pending hcoreWidth hk gs p W hA hW r J rows hrows ambient hInv
  · intro classes hclass hpending
    have hstep := SeamArchiveNumericalState.step p coreWidth W k hcoreWidth hk hA hW r J
      classes hclass src dst plan.src_ne_dst sourceTail outputTail S ks rows rest hrows hrest ambient hpending
    have hstart : ({S with R := (Function.update (Function.update S.R src
        (((rows::rest).map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail))
        dst (ambient.flatten++outputTail))} : Stacks T A) = S := by
      rw [←hbanks',←hsrc,←hdst]
      simp
    have hrstart := congrArg Stacks.R hstart
    dsimp only at hrstart
    simpa only [hrstart] using hstep

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
