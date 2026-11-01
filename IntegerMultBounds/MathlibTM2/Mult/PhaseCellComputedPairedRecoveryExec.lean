module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedComputedRecoveryExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPairRecoveryOutput

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
  obtain ⟨v₁,F,n₁,outputs,hu₁,hn₁,hcert,hI,hO,hL,hframe,hmastersLength,he₁,htrace₁⟩ :=
    plan.exec_retained b d r hmastersEq Fs hfields wl hwl v S hp hW hN hvalues hwidth hscalar
      hmasters hmasterScratch hblank hleft hpayload hscratch hclock hsaved hsavedClock
  obtain ⟨word,hword,hwords⟩ : ∃ word, r.output word ∧ outputs.reverse.flatten = word := by
    cases hcert with
    | cons h hs => cases hs; exact ⟨_,h,by simp⟩
  let M : Stacks T A := {F with R := (Function.update
    (fun k => if k ∈ List.ofFn plan.work then [] else F.R k) plan.result (outputs.reverse.flatten++F.R plan.result))}
  have hmasterNe (i : Fin 10) : plan.master.masters i ≠ plan.result := by
    intro hi; exact plan.master_controls i (by simp [hi])
  have hmasterOff (i : Fin 10) : plan.master.masters i ∉ List.ofFn plan.work := by
    intro hm
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
    exact plan.master_work i j hj.symm
  have hMmaster (i : Fin 10) : (M.R (plan.master.masters i)).length = recoveryMasterValues r.problem i := by
    simpa only [M,Function.update_of_ne (hmasterNe i),ite_eq_right (hmasterOff i)] using hmastersLength i
  have hworkNe (k : Fin T) (hk : k ∈ List.ofFn plan.work) : k ≠ plan.result := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
    intro hi
    exact plan.separate i (by simp [hi])
  have hcontrol (k : Fin T) (hk : k ∈ [plan.replicas,plan.count,plan.spare]) : M.R k = S.R k := by
    have hm : ∀ i, plan.master.masters i ≠ k := by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact plan.master_seeds i (by simp [hi])
      · exact plan.master_controls i (by simp [hi])
      · exact plan.master_controls i (by simp [hi])
    have hw : k ∉ List.ofFn plan.work := by
      intro hw
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with hi | hi | hi
      · exact (plan.seed_work i).2.2 hi.symm
      · exact plan.separate i (by simp [hi])
      · exact plan.separate i (by simp [hi])
    have hr : k ≠ plan.result := by
      have hr := hpairReg
      regs_ne hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> first | assumption | exact Ne.symm (by assumption)
    simp only [M,Function.update_of_ne hr,ite_eq_right hw,hframe k hm]
  have hresult : F.R plan.result = S.R plan.result := hframe _ (fun i => hmasterNe i)
  obtain ⟨Gs,hGs,v₂,n₂,hu₂,hn₂,he₂,hgood⟩ := r.prepared_pair_output_exec e he plan.replicas plan.count
    plan.result plan.spare hpairReg (by have := b.hA; omega) hword Zs htargets (S.R plan.result) v₁ M
    (by rw [hpairMaster.1]; exact hMmaster 2)
    (by rw [hpairMaster.2.1]; exact hMmaster 8)
    (by rw [hpairMaster.2.2]; exact hMmaster 9)
    (by
      intro k hk
      have hm := hpairWork k hk
      simp only [M,Function.update_of_ne (hworkNe _ hm),hm,ite_true])
    (by rw [hcontrol _ (by simp),hlen]; exact hN)
    (by simp only [M,Function.update_self,hwords,hresult])
    (by rw [hcontrol _ (by simp)]; exact hscratch _ (by simp))
    (by rw [hcontrol _ (by simp)]; exact hscratch _ (by simp))
  rw [hlen] at hn₂
  let stream := (Gs.map (fun D => cstream A r.problem.wordWidth
    (packedInterval r.problem.origin r.problem.span D))).flatten++S.R plan.result
  let K : Stacks T A := {F with R := (Function.update
    (fun k => if k ∈ List.ofFn plan.work then [] else F.R k) plan.result stream)}
  have hK : {M with R := Function.update M.R plan.result stream} = K := by
    simp only [M,K,Function.update_idem]
  change Exec body _ _ _ (Host.mk v₂ {M with R := Function.update M.R plan.result stream}) at he₂
  rw [hK] at he₂
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
  refine ⟨Gs,hGs.trans hlen,v₃,n₁+(n₂+retireRecoveryMastersCost r.problem),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁ (Exec.seq he₂ he₃),hgood,?_⟩
  · simpa only [Nat.add_assoc] using Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ (retireRecoveryMastersCost r.problem))
  · intro Cprog hpush hbody depth
    have ht₁ := htrace₁ Cprog hpush hbody 0
    have ht₂ := preparedPairRecoveryOutput_within_stock he₂ hn₂ 0
    have ht₁₂ := mn_seq_within_add ht₁ ht₂
    have ht₃ := mn_native_exec_within he₃ 0 (clearWords_native _) 0 _ (by
      simpa only [Nat.zero_mul,Nat.add_zero] using ht₁₂.final)
    have ht := (ExecWithin.seq ht₁₂ ht₃).seq_assoc
    have hshift := ht.shift depth (J := fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
      (d.stock+recoveryLifecycleStock b plan.work r Fs.length Cprog+8*preparedPairRecoveryOutputCost r Fs.length))
      (by intro j z hz; omega)
    simpa only [complexProgram,Nat.zero_add,Nat.add_assoc] using hshift

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
