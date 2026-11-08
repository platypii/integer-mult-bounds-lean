module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedTargetCoreRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryHandoff

/-! Generate the owned-prefix counter from retained selection dimensions, execute
principal recovery and crop J_k. No byte counter is supplied by the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedRecoveryPlan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def croppedTime (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (d : InverseMasterInput s) (r : RawRecoveryJob s) (offset rows N : ℕ) :=
  d.timeCost+recoveryLifecycleTime b plan.work r N+preparedPairRecoveryOutputCost r N+
    generatedRecoveryCropCost r.problem.precision r.problem.origin (r.problem.origin+r.problem.span) offset rows N+
    retireRecoveryMastersCost r.problem

noncomputable def croppedReserve (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (d : InverseMasterInput s) (r : RawRecoveryJob s) (offset rows N Cprog : ℕ) :=
  d.stock+recoveryLifecycleStock b plan.work r N Cprog+8*preparedPairRecoveryOutputCost r N+
    8*generatedRecoveryCropCost r.problem.precision r.problem.origin (r.problem.origin+r.problem.span) offset rows N

-- The supplied-counter route is recoverable from commit 221f84ae.
noncomputable def generatedRoutedTargetCoreProgram (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (crop : RecoveryCropPlacement plan) (rowCount symbols count source saved tmp : Fin T) : Pr P T Q A U :=
  .seq (generatedTakePrefix plan.replicas rowCount plan.packet symbols count source (plan.work 124) saved tmp) (plan.croppedProgram b crop)

theorem generated_routed_target_owned_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (crop : RecoveryCropPlacement plan)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    (d : InverseMasterInput s) (r : RawRecoveryJob s) (hmastersEq : recoveryMasterValues r.problem = d.masters)
    (L k radius targetOrigin targetSpan : ℕ)
    (hcore : r.problem.origin+radius = cut s r.problem.t L k)
    (hspan : r.problem.span = rows s r.problem.t L k+2*radius)
    (Fs : List (ZMod r.problem.t → GaussianInt))
    (hfields : r.inputFields = complexComponentFields (selectedRhsFields s Fs))
    (hwindow : ∀ j < r.problem.span, targetOrigin ≤ nearestNatural s r.problem.t (r.problem.origin+j) ∧
      nearestNatural s r.problem.t (r.problem.origin+j) < targetOrigin+targetSpan)
    (Zs : List (ZMod s → ℂ)) (hlen : Zs.length = Fs.length)
    (htargets : (List.finRange r.problem.Fs.length).reverse.map (fun j => r.solution j.val) = complexComponentTargets Zs)
    (wl : List (Fin (A+4))) (hwl : wl.length = d.B) (v : HS T Q A U) (S : Stacks T A)
    (hready : plan.CroppedReady crop d r Fs.length radius (rows s r.problem.t L k) wl S)
    (rowCount symbols count source saved tmp : Fin T)
    (hreg : [plan.replicas,rowCount,plan.packet,symbols,count,source,plan.work 124,saved,tmp].Nodup)
    (hoff : ∀ j, plan.cropSupport crop j → source ≠ j) (hsourceOut : source ≠ crop.reg 12)
    (tail : List (Fin (A+4)))
    (hsource : S.R source = selectedWindowPayload (s := s) A r.W r.problem.origin r.problem.span targetOrigin targetSpan Fs++tail)
    (hrows : (S.R rowCount).length = r.problem.span)
    (hinput : S.R (plan.work 124) = []) (hblank : ∀ j ∈ [symbols,count,saved,tmp], S.R j = []) :
    ∃ Gs : List (ZMod s → GaussianInt), Gs.length = Fs.length ∧
    ∃ v' n, v'.user = v.user ∧ n ≤
      (generatedTakePrefixCost Fs.length r.problem.span r.W)+
        plan.croppedTime b d r radius (rows s r.problem.t L k) Fs.length ∧
      Exec body (plan.generatedRoutedTargetCoreProgram b crop rowCount symbols count source saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) (crop.reg 12)
          ((Gs.reverse.map (fun D => cstream A r.problem.wordWidth
            (packedInterval (cut s r.problem.t L k) (rows s r.problem.t L k) D))).flatten++S.R (crop.reg 12)))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s (cut s r.problem.t L k) (cut s r.problem.t L (k+1)))
        (packedIntervalRead r.problem.precision r.problem.wordWidth (cut s r.problem.t L k)
          (cstream A r.problem.wordWidth (packedInterval (cut s r.problem.t L k) (rows s r.problem.t L k) D)++S.R (crop.reg 12)))
        z (1/(2 : ℝ)^r.target+1/(2 : ℝ)^r.target)) Zs.reverse Gs.reverse ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
          (2*(generatedTakePrefixCost Fs.length r.problem.span r.W)+
            plan.croppedReserve b d r radius (rows s r.problem.t L k) Fs.length Cprog)) depth
          (plan.generatedRoutedTargetCoreProgram b crop rowCount symbols count source saved tmp) (Host.mk v S) n
          (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) (crop.reg 12)
            ((Gs.reverse.map (fun D => cstream A r.problem.wordWidth
              (packedInterval (cut s r.problem.t L k) (rows s r.problem.t L k) D))).flatten++S.R (crop.reg 12)))}) := by
  let payload := selectedWindowPayload (s := s) A r.W r.problem.origin r.problem.span targetOrigin targetSpan Fs
  let H := plan.inputState source payload tail S
  have hr := hreg
  regs_ne hr
  have hlenPayload : payload.length = Fs.length*(r.problem.span*r.W) := by
    simpa only [payload,Nat.mul_assoc] using selectedWindowPayload_length A r.W r.problem.origin
      r.problem.span targetOrigin targetSpan Fs r.problem.span_fit hwindow
  obtain ⟨v₁,n₁,hu₁,hn₁,hreadyH,hsize,he₁,htrace₁⟩ := hready.generatedTakePrefix_exec (body := body)
    rowCount symbols count source saved tmp hreg hoff payload tail hlenPayload v hsource hrows hinput hblank
  have hout : H.R (crop.reg 12) = S.R (crop.reg 12) := by
    have hne : crop.reg 12 ≠ plan.work 124 := fun he => (crop.external 12 (by simp)).1 (List.mem_ofFn.mpr ⟨124,he.symm⟩)
    simp [H,inputState,hne,hsourceOut.symm]
  obtain ⟨Gs,hGs,v₂,n₂,hu₂,hn₂,he₂,hgood,htrace₂⟩ := plan.selected_target_owned_exec (body := body)
    b crop hreplicaCount hreplicaSpare d r hmastersEq L k radius targetOrigin targetSpan hcore hspan Fs hfields
    hwindow Zs hlen htargets wl hwl v₁ H hreadyH.precision hreadyH.packet hreadyH.replicas hreadyH.values
    hreadyH.width hreadyH.scalar hreadyH.masters hreadyH.masterScratch hreadyH.blank hreadyH.left
    (by simp [H,inputState,payload]) hreadyH.scratch hreadyH.clock hreadyH.saved hreadyH.savedClock
    hreadyH.offset hreadyH.rows
  let output := (Gs.reverse.map (fun D => cstream A r.problem.wordWidth
    (packedInterval (cut s r.problem.t L k) (rows s r.problem.t L k) D))).flatten
  have hsourceWork : ∀ i, source ≠ plan.work i := by
    intro i
    by_cases hi : i = 124
    · subst i; exact ‹source ≠ plan.work 124›
    · exact hoff _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨i,hi,rfl⟩))))
  have hblank : ∀ i, S.R (plan.work i) = [] := by
    intro i; by_cases hi : i = 124
    · subst i; exact hinput
    · exact hready.blank i hi
  have hfinal : {H with R := (Function.update
      (fun j => if j ∈ List.ofFn plan.work then [] else H.R j) (crop.reg 12) (output++H.R (crop.reg 12)))} =
      {S with R := (Function.update (Function.update S.R source tail) (crop.reg 12) (output++S.R (crop.reg 12)))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    change Function.update (fun j => if j ∈ List.ofFn plan.work then [] else H.R j) (crop.reg 12)
      (output++H.R (crop.reg 12)) j = Function.update (Function.update S.R source tail) (crop.reg 12)
      (output++S.R (crop.reg 12)) j
    by_cases hjout : j = crop.reg 12
    · subst j; simp only [Function.update_self,hout]
    simp only [Function.update_of_ne hjout]
    by_cases hjwork : j ∈ List.ofFn plan.work
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hjwork
      rw [ite_eq_left (List.mem_ofFn.mpr ⟨i,rfl⟩),Function.update_of_ne (hsourceWork i).symm,hblank i]
    · have hjpayload : j ≠ plan.work 124 := fun he => hjwork (he ▸ List.mem_ofFn.mpr ⟨124,rfl⟩)
      rw [ite_eq_right hjwork]
      change Function.update (Function.update S.R source tail) (plan.work 124) payload j = _
      rw [Function.update_of_ne hjpayload]
  rw [hfinal] at he₂
  refine ⟨Gs,hGs,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    Exec.seq he₁ he₂,?_,?_⟩
  · simpa only [hout] using hgood
  · intro Cprog hpush hbody depth
    have ht₂ := htrace₂ Cprog hpush hbody 0
    rw [hfinal] at ht₂
    have ht := mn_seq_within_add (htrace₁ 0) ht₂
    simpa only [Nat.zero_add,generatedRoutedTargetCoreProgram] using ht.shift depth (J := fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
      (2*(generatedTakePrefixCost Fs.length r.problem.span r.W)+plan.croppedReserve b d r radius (rows s r.problem.t L k) Fs.length Cprog))
      (by intro j z hz; dsimp only [croppedReserve]; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedRecoveryPlan
