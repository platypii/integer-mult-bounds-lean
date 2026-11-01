module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPairedRecoveryExec

/-! One computed complex call generates masters once, recovers scalar fields,
pairs the actual output and restores every owned setup bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace ComputedRecoveryPlan
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def complexProgram (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (e : Fin 8 → Fin T) : Pr P T Q A U :=
  .seq (plan.retainedProgram b) (.seq (preparedPairRecoveryOutput e plan.replicas plan.count plan.result plan.spare)
    (clearWords (List.ofFn plan.master.masters)))

theorem complex_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (e : Fin 8 → Fin T) (he : Function.Injective e)
    (hpairReg : [plan.replicas,e 5,plan.count,plan.result,plan.spare,e 7,e 6].Nodup)
    (hpairMaster : e 0 = plan.master.masters 2 ∧ e 1 = plan.master.masters 8 ∧ e 2 = plan.master.masters 9)
    (hpairWork : ∀ k ∈ ([(3 : Fin 8),4,5,6,7]), e k ∈ List.ofFn plan.work)
    (d : InverseMasterInput s) (r : RawRecoveryJob s)
    (hmastersEq : recoveryMasterValues r.problem = d.masters)
    (Fs : List (ZMod s → GaussianInt)) (hfields : r.inputFields = complexComponentFields Fs)
    (Zs : List (ZMod s → ℂ)) (hlen : Zs.length = Fs.length)
    (htargets : (List.finRange r.problem.Fs.length).reverse.map (fun j => r.solution j.val) = complexComponentTargets Zs)
    (wl : List (Fin (A+4))) (hwl : wl.length = d.B) (v : HS T Q A U) (S : Stacks T A)
    (hp : (S.R plan.precision).length = r.problem.p) (hW : (S.R plan.packet).length = r.W)
    (hN : (S.R plan.replicas).length = Fs.length)
    (hvalues : ∀ i, (S.R (plan.master.parameters i)).length = d.values i)
    (hwidth : S.R (plan.master.scalar .wr) = wl)
    (hscalar : ∀ k : TblR 25, k ≠ .wr → S.R (plan.master.scalar k) = [])
    (hmasters : ∀ i, S.R (plan.master.masters i) = [])
    (hmasterScratch : ∀ k ∈ [plan.master.word,plan.master.saved,plan.master.tmp,plan.master.queue], S.R k = [])
    (hblank : ∀ i, i ≠ 124 → S.R (plan.work i) = []) (hleft : ∀ i, S.L (plan.work i) = [])
    (hpayload : S.R (plan.work 124) = cstream A r.W (Fs.map (packedInterval r.problem.origin r.problem.span)).flatten)
    (hscratch : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = [])
    (hclock : S.R plan.clock = []) (hsaved : S.R plan.saved = []) (hsavedClock : S.R plan.savedClock = []) :
    ∃ Gs : List (ZMod s → GaussianInt), Gs.length = Fs.length ∧
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ d.timeCost+recoveryLifecycleTime b plan.work r Fs.length+
        preparedPairRecoveryOutputCost r Fs.length+retireRecoveryMastersCost r.problem ∧
      Exec body (plan.complexProgram b e) (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update
          (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) plan.result
          ((Gs.map (fun D => cstream A r.problem.wordWidth
            (packedInterval r.problem.origin r.problem.span D))).flatten++S.R plan.result))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
        (PhaseCellDiscreteGeometry.haloVertices s r.problem.origin (r.problem.origin+r.problem.span))
        (packedIntervalRead r.problem.precision r.problem.wordWidth r.problem.origin
          (cstream A r.problem.wordWidth (packedInterval r.problem.origin r.problem.span D)++S.R plan.result))
        z (1/(2 : ℝ)^r.target+1/(2 : ℝ)^r.target)) Zs Gs ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
          (d.stock+recoveryLifecycleStock b plan.work r Fs.length Cprog+
            8*preparedPairRecoveryOutputCost r Fs.length)) depth
          (plan.complexProgram b e) (Host.mk v S) steps
          (Host.mk v' {S with R := (Function.update
            (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) plan.result
            ((Gs.map (fun D => cstream A r.problem.wordWidth
              (packedInterval r.problem.origin r.problem.span D))).flatten++S.R plan.result))}) := by
  obtain ⟨Gs,hGs,v₂,F,n,hu,hn,hI,hO,hL,hframe,hmastersLength,hex,hgood,htrace⟩ :=
    plan.complex_retained_exec b e he hpairReg hpairMaster hpairWork d r hmastersEq Fs hfields Zs hlen htargets
      wl hwl v S hp hW hN hvalues hwidth hscalar hmasters hmasterScratch hblank hleft hpayload
      hscratch hclock hsaved hsavedClock
  let stream := (Gs.map (fun D => cstream A r.problem.wordWidth
    (packedInterval r.problem.origin r.problem.span D))).flatten++S.R plan.result
  let K : Stacks T A := {F with R := (Function.update
    (fun k => if k ∈ List.ofFn plan.work then [] else F.R k) plan.result stream)}
  have hmasterNe (i : Fin 10) : plan.master.masters i ≠ plan.result := by
    intro hi; exact plan.master_controls i (by simp [hi])
  have hmasterOff (i : Fin 10) : plan.master.masters i ∉ List.ofFn plan.work := by
    intro hm
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
    exact plan.master_work i j hj.symm
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) (List.ofFn plan.master.masters)
    (List.nodup_ofFn.mpr plan.master.masters_injective) v₂ K
  have hKmaster (i : Fin 10) : (K.R (plan.master.masters i)).length = recoveryMasterValues r.problem i := by
    simpa only [K,Function.update_of_ne (hmasterNe i),ite_eq_right (hmasterOff i)] using hmastersLength i
  have hcleanup : 2*((List.ofFn plan.master.masters).map (fun k => (K.R k).length)).sum+
      2*(List.ofFn plan.master.masters).length+1 = retireRecoveryMastersCost r.problem := by
    simp only [List.map_ofFn,Function.comp_def,hKmaster,List.length_ofFn,retireRecoveryMastersCost,Nat.reduceMul]
  rw [hcleanup] at he₃
  have hfinal : {K with R := fun k => if k ∈ List.ofFn plan.master.masters then [] else K.R k} =
      {S with R := (Function.update (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) plan.result stream)} := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hI
    · exact hO
    · exact hL
    funext k
    change (if k ∈ List.ofFn plan.master.masters then [] else K.R k) =
      Function.update (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) plan.result stream k
    by_cases hm : k ∈ List.ofFn plan.master.masters
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      simp only [hm,ite_true,Function.update_of_ne (hmasterNe i),ite_eq_right (hmasterOff i),hmasters]
    · rw [ite_eq_right hm]
      change Function.update (fun k => if k ∈ List.ofFn plan.work then [] else F.R k) plan.result stream k = _
      by_cases hr : k = plan.result
      · subst k; simp only [Function.update_self]
      · rw [Function.update_of_ne hr,Function.update_of_ne hr]
        by_cases hw : k ∈ List.ofFn plan.work
        · simp only [hw,ite_true]
        · simp only [hw,ite_false]
          exact hframe k (by intro i hi; exact hm (List.mem_ofFn.mpr ⟨i,hi⟩))
  rw [hfinal] at he₃
  have hex' : Exec body (plan.complexProgram b e) (Host.mk v S) (n+retireRecoveryMastersCost r.problem)
      (Host.mk v₃ {S with R := (Function.update
        (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) plan.result stream)}) := by
    unfold retainedComplexProgram at hex
    cases hex with
    | seq hex₁ hex₂ =>
      simpa only [complexProgram,Nat.add_assoc] using Exec.seq hex₁ (Exec.seq hex₂ he₃)
  refine ⟨Gs,hGs,v₃,n+retireRecoveryMastersCost r.problem,hu₃.trans hu,?_,hex',hgood,?_⟩
  · exact Nat.add_le_add_right hn _
  · intro Cprog hpush hbody depth
    have ht := htrace Cprog hpush hbody depth
    have ht₃ := mn_native_exec_within he₃ 0 (clearWords_native _) depth _ (by
      simpa only [Nat.zero_mul,Nat.add_zero] using ht.final)
    simpa only [retainedComplexProgram,complexProgram] using (ExecWithin.seq ht ht₃).seq_assoc

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
