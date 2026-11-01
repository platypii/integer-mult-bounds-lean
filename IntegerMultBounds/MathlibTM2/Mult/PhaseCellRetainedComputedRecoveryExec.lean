module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedRecoveryBudgets

/-! Execute computed recovery while retaining numerical masters for complex
output assembly. Scalar workspace and the private recovery bank restore. -/
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

noncomputable def retainedProgram (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U) : Pr P T Q A U :=
  .seq (restoredSupplierMasters plan.master.scalar plan.master.parameters plan.master.masters
    plan.master.word plan.master.saved plan.master.tmp plan.master.queue plan.master.carry)
    (complexRecoveryFromSeeds b plan.seedSources plan.work plan.src plan.saved plan.count plan.tmp
      plan.spare plan.result plan.clock plan.savedClock)

theorem exec_retained (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (d : InverseMasterInput s) (r : RawRecoveryJob s)
    (hmastersEq : recoveryMasterValues r.problem = d.masters)
    (Fs : List (ZMod s → GaussianInt)) (hfields : r.inputFields = complexComponentFields Fs)
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
    ∃ v', ∃ F : Stacks T A, ∃ steps outputs, v'.user = v.user ∧
      steps ≤ d.timeCost+recoveryLifecycleTime b plan.work r Fs.length ∧
      List.Forall₂ RawRecoveryJob.output [r] outputs ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ k, (∀ i, plan.master.masters i ≠ k) → F.R k = S.R k) ∧
      (∀ i, (F.R (plan.master.masters i)).length = recoveryMasterValues r.problem i) ∧
      Exec body (plan.retainedProgram b) (Host.mk v S) steps
        (Host.mk v' {F with R := (Function.update
          (fun k => if k ∈ List.ofFn plan.work then [] else F.R k) plan.result (outputs.reverse.flatten++F.R plan.result))}) ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
          (d.stock+recoveryLifecycleStock b plan.work r Fs.length Cprog)) depth
          (plan.retainedProgram b) (Host.mk v S) steps (Host.mk v' {F with R := (Function.update
          (fun k => if k ∈ List.ofFn plan.work then [] else F.R k) plan.result (outputs.reverse.flatten++F.R plan.result))}) := by
  obtain ⟨v₁,F,n₁,hu₁,hn₁,he₁,hseed,hI,hO,hL,hframe⟩ := generateRecoverySeedSources_exec (body := body)
    plan.master.scalar plan.master.scalar_injective plan.master.parameters plan.master.masters
    plan.master.masters_injective plan.master.separate plan.master.word plan.master.saved plan.master.tmp
    plan.master.queue plan.master.carry plan.master.regs plan.master.queue_off
    d.hst d.has d.hbs d.hband d.band_room d.geometry_room d.precision_room d.values_fit
    r.problem hmastersEq plan.precision plan.packet plan.replicas r.W Fs.length plan.master_seeds
    wl hwl v S hp hW hN hvalues hwidth hscalar hmasters hmasterScratch 0
  change n₁ ≤ d.timeCost at hn₁
  change ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+0+d.stock) 0 _ _ _ _ at he₁
  have hcontrol (k : Fin T) (hk : k ∈ [plan.src,plan.saved,plan.count,plan.tmp,plan.spare,plan.result,plan.clock,plan.savedClock]) :
      F.R k = S.R k := by
    apply hframe
    intro i heq
    exact plan.master_controls i (heq.symm ▸ hk)
  obtain ⟨v₂,n₂,outputs,hu₂,hn₂,hcert,he₂,htrace₂⟩ := complexRecoveryFromSeeds_exec (body := body) b r Fs hfields
    plan.work plan.work_injective plan.src plan.saved plan.count plan.tmp plan.spare plan.result plan.clock plan.savedClock
    plan.regs plan.separate plan.seedSources plan.seedSources_work plan.seedSources_tmp v₁ F hseed
    (by intro i hi; rw [hframe _ (fun j => plan.master_work j i)]; exact hblank i hi)
    (by intro i; simpa only [hL] using hleft i)
    (by rw [hframe _ (fun j => plan.master_work j 124)]; exact hpayload)
    (by
      intro k hk
      rw [hcontrol k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp only [List.mem_cons,eq_self,or_true,true_or])]
      exact hscratch k hk)
    (by rw [hcontrol plan.clock (by simp)]; exact hclock)
    (by rw [hcontrol plan.saved (by simp)]; exact hsaved)
    (by rw [hcontrol plan.savedClock (by simp)]; exact hsavedClock)
  have hcopy := recoverySeedCopyCost_eq r.problem r.W Fs.length plan.seedSources plan.work F hseed
  rw [hcopy] at hn₂ htrace₂
  change n₂ ≤ recoveryLifecycleTime b plan.work r Fs.length at hn₂
  let M : Stacks T A := {F with R := (Function.update
    (fun k => if k ∈ List.ofFn plan.work then [] else F.R k) plan.result (outputs.reverse.flatten++F.R plan.result))}
  have hmasterLengths (i : Fin 10) : (F.R (plan.master.masters i)).length = recoveryMasterValues r.problem i := by
    have hm : recoveryMasterPort i ∈ recoverySeedHeaderPorts := recoverySeedHeaderPorts_perm.mem_iff.mpr
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    simpa only [seedSources,recoverySeedSources_master,recoverySeedHeader_master] using hseed (recoveryMasterPort i) hm
  refine ⟨v₂,F,n₁+n₂,outputs,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hcert,hI,hO,hL,hframe,
    hmasterLengths,Exec.seq he₁.toExec he₂,?_⟩
  intro Cprog hpush hbody depth
  have ht₂ := htrace₂ Cprog hpush hbody 0
  change ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v₁ F)+0+
    recoveryLifecycleStock b plan.work r Fs.length Cprog) 0 _ _ _ _ at ht₂
  have ht := mn_seq_within_add he₁ ht₂
  have hshift := ht.shift depth (J := fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
    (d.stock+recoveryLifecycleStock b plan.work r Fs.length Cprog)) (by intro j z hz; omega)
  simpa only [Nat.zero_add,retainedProgram] using hshift

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
