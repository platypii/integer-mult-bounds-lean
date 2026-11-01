module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPairedRecoveryExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryPairPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryCropPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCropNormalizeRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedJobMasterInput

/-! One fixed local program generates masters once, recovers and pairs fields,
crops and normalizes output, then restores all owned banks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace ComputedRecoveryPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def normalizedProgram (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (link : RecoveryCropNormalizeLink normalize queue) : Pr P T Q A U :=
  .seq (plan.retainedComplexProgram b plan.pairPlacement)
    (.seq (normalize.cropProgram queue link) (clearWords (List.ofFn plan.master.masters)))

noncomputable def normalizedTimeCost (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (r : PackedNormalizedJob A s) : ℕ :=
  r.masterInput.timeCost+recoveryLifecycleTime b plan.work r.rawRecoveryJob r.Fs.length+
    preparedPairRecoveryOutputCost r.rawRecoveryJob r.Fs.length+
    RecoveryNormalizePlan.cropTimeCost r r.Fs.length+retireRecoveryMastersCost r.rawRecoveryJob.problem

noncomputable def normalizedStock (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (r : PackedNormalizedJob A s) (Cprog : ℕ) : ℕ :=
  r.masterInput.stock+recoveryLifecycleStock b plan.work r.rawRecoveryJob r.Fs.length Cprog+
    8*preparedPairRecoveryOutputCost r.rawRecoveryJob r.Fs.length+RecoveryNormalizePlan.cropStock r r.Fs.length

theorem normalized_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (crop : RecoveryCropPlacement plan) (link : RecoveryCropNormalizeLink normalize queue)
    (hreg : link.reg = crop.reg)
    (hsupportMaster : ∀ k, normalize.support queue k → ∀ i, plan.master.masters i ≠ k)
    (hsupportPayload : ∀ k, normalize.support queue k → k ≠ plan.work 124)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    (r : PackedNormalizedJob A s) (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore)
    (v : HS T Q A U) (S : Stacks T A)
    (hready : normalize.UnaryReady queue r r.Fs.length wl S)
    (hp : (S.R plan.precision).length = r.p) (hW : (S.R plan.packet).length = r.W)
    (hN : (S.R plan.replicas).length = r.Fs.length)
    (hvalues : ∀ i, (S.R (plan.master.parameters i)).length = r.masterInput.values i)
    (hwidth : S.R (plan.master.scalar .wr) = wl)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (plan.master.scalar i) = [])
    (hmasters : ∀ i, S.R (plan.master.masters i) = [])
    (hmasterScratch : ∀ k ∈ [plan.master.word,plan.master.saved,plan.master.tmp,plan.master.queue], S.R k = [])
    (hblank : ∀ i, i ≠ 124 → S.R (plan.work i) = []) (hleft : ∀ i, S.L (plan.work i) = [])
    (hpayload : S.R (plan.work 124) = cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten)
    (hscratch : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = [])
    (hclock : S.R plan.clock = []) (hsaved : S.R plan.saved = []) (hsavedClock : S.R plan.savedClock = [])
    (hoffset : (S.R (crop.reg 3)).length = r.radius)
    (hrows : (S.R (crop.reg 4)).length = coreLength s r.coreWidth r.k) :
    ∃ Es : List (ZMod s → GaussianInt), Es.length = r.Fs.length ∧
    ∃ v' n, v'.user = v.user ∧ n ≤ plan.normalizedTimeCost b r ∧
      Exec body (plan.normalizedProgram b normalize queue link) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) normalize.src
          ((Es.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++S.R normalize.src))}) ∧
      List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
        (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
          (cstream A r.W (ownedCoreWords r.coreWidth r.k D)++S.R normalize.src)) (r.rowTarget F) r.rowError) r.Fs.reverse Es ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+plan.normalizedStock b r Cprog)
          depth (plan.normalizedProgram b normalize queue link) (Host.mk v S) n
          (Host.mk v' {S with R := (Function.update (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) normalize.src
            ((Es.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++S.R normalize.src))}) := by
  obtain ⟨Gs,hGs,v₁,F,n₁,hu₁,hn₁,hI,hO,hL,hframe,hmastersLength,he₁,hgood,htrace₁⟩ :=
    plan.complex_retained_exec b plan.pairPlacement plan.pairPlacement_injective
      (plan.pairPlacement_regs hreplicaCount hreplicaSpare) plan.pairPlacement_masters plan.pairPlacement_work
      r.masterInput r.rawRecoveryJob r.rawRecoveryJob_masterValues r.Fs rfl
      (r.Fs.map (componentSolution r.localSolution)) (List.length_map _) r.rawRecoveryJob_solutionOrder
      wl hwl v S hp hW hN hvalues hwidth hscalar hmasters hmasterScratch hblank hleft hpayload hscratch hclock hsaved hsavedClock
  let M : Stacks T A := {F with R := (Function.update
    (fun k => if k ∈ List.ofFn plan.work then [] else F.R k) plan.result
    ((Gs.map (fun D => cstream A r.rawRecoveryJob.problem.wordWidth
      (packedInterval r.rawRecoveryJob.problem.origin r.rawRecoveryJob.problem.span D))).flatten++S.R plan.result))}
  have hsource : link.reg 11 = plan.result := (congrFun hreg 11).trans crop.source
  have hdest : normalize.src = crop.reg 12 := link.source.trans (congrFun hreg 12)
  have hmasterNe (i : Fin 10) : plan.master.masters i ≠ plan.result := by
    intro hi; exact plan.master_controls i (by simp [hi])
  have hmasterOff (i : Fin 10) : plan.master.masters i ∉ List.ofFn plan.work := by
    intro hm
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
    exact plan.master_work i j hj.symm
  have hresultOff : plan.result ∉ List.ofFn plan.work := by
    intro hm
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
    exact plan.separate j (by simp [hj])
  have hMmaster (i : Fin 10) : (M.R (plan.master.masters i)).length = recoveryMasterValues r.rawRecoveryJob.problem i := by
    simpa only [M,Function.update_of_ne (hmasterNe i),ite_eq_right (hmasterOff i)] using hmastersLength i
  have hMsupport (k : Fin T) (hk : normalize.support queue k) : M.R k = S.R k := by
    have hr : k ≠ plan.result := by simpa only [hsource] using (link.support_off k hk).2.1
    simp only [M,Function.update_of_ne hr]
    by_cases hw : k ∈ List.ofFn plan.work
    · rw [ite_eq_left hw]
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      exact (hblank i (by intro hi; subst i; exact hsupportPayload _ hk rfl)).symm
    · rw [ite_eq_right hw]
      exact hframe k (hsupportMaster k hk)
  have hreadyM := hready.of_frame hMsupport
  have hMframe (k : Fin T) (hw : k ∉ List.ofFn plan.work)
      (hm : ∀ i, plan.master.masters i ≠ k) (hr : k ≠ plan.result) : M.R k = S.R k := by
    simp only [M,Function.update_of_ne hr,ite_eq_right hw,hframe k hm]
  have hMexternal (k : Fin 19) (hk : k ∈ ([(3 : Fin 19),4,12])) : M.R (crop.reg k) = S.R (crop.reg k) :=
    hMframe _ (crop.external k hk).1 (crop.external k hk).2.1 (crop.external k hk).2.2
  have hrepWork : plan.replicas ∉ List.ofFn plan.work := by
    intro hm; obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm; exact (plan.seed_work j).2.2 hj.symm
  have hrepMaster (i : Fin 10) : plan.master.masters i ≠ plan.replicas := by
    intro hi; exact plan.master_seeds i (by simp [hi])
  obtain ⟨hqProfile,horigin,hspan,hword,_,_,htarget⟩ := r.rawRecoveryJob_profile
  have hmasterRegs : link.reg 0 = plan.master.masters 2 ∧ link.reg 1 = plan.master.masters 8 ∧
      link.reg 2 = plan.master.masters 9 := by simpa only [hreg] using crop.masters
  have hrepReg : link.reg 5 = plan.replicas := (congrFun hreg 5).trans crop.replicas
  obtain ⟨hlen, v₂,n₂,hu₂,hn₂,he₂,hglobal,htrace₂⟩ := normalize.crop_exec queue link (by have := b.hA; omega) r Gs
    (S.R plan.result) wl hwl v₁ M (by simpa only [hGs] using hreadyM)
    (by rw [hmasterRegs.1]; simpa [recoveryMasterValues,masterHeaderValues,hqProfile] using hMmaster 2)
    (by rw [hmasterRegs.2.1]; simpa [recoveryMasterValues,masterHeaderValues,horigin] using hMmaster 8)
    (by rw [hmasterRegs.2.2]; simpa [recoveryMasterValues,masterHeaderValues,horigin,hspan,
        Nat.add_sub_of_le r.bounds.hab] using hMmaster 9)
    (by rw [congrFun hreg 3,hMexternal 3 (by simp)]; exact hoffset)
    (by rw [congrFun hreg 4,hMexternal 4 (by simp)]; exact hrows)
    (by rw [hrepReg,hMframe _ hrepWork hrepMaster plan.seed_result.2.2,hGs]; exact hN)
    (by
      intro k hk
      have hm : link.reg k ∈ List.ofFn plan.work := by rw [congrFun hreg k]; exact crop.scratch k hk
      have hr : link.reg k ≠ plan.result := by intro hr; exact hresultOff (hr ▸ hm)
      simp only [M,Function.update_of_ne hr,hm,ite_true])
    (by simp only [M,hsource,Function.update_self,hword,horigin,hspan])
    (by simpa only [hqProfile,hword,horigin,hspan,htarget,component_error_bit,
        Nat.add_sub_of_le r.bounds.hab] using hgood)
  rw [hGs] at hlen hn₂
  let Es := Gs.reverse.map (fun D i => finalRoundWord (2*r.q+8) r.q r.p (inverseNormalizationShift r.p) (D i))
  let stream := (Es.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++S.R normalize.src
  have hdst : M.R normalize.src = S.R normalize.src := by rw [hdest]; exact hMexternal 12 (by simp)
  let K : Stacks T A := {F with R := (Function.update
    (Function.update (fun k => if k ∈ List.ofFn plan.work then [] else F.R k) plan.result (S.R plan.result)) normalize.src stream)}
  have hK : {M with R := (Function.update (Function.update M.R (link.reg 11) (S.R plan.result)) normalize.src
      ((Es.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++M.R normalize.src))} = K := by
    rw [hdst]
    simp only [M,K,stream,hsource,Function.update_idem]
  change Exec body _ _ _ (Host.mk v₂ {M with R := (Function.update
    (Function.update M.R (link.reg 11) (S.R plan.result)) normalize.src
    ((Es.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++M.R normalize.src))}) at he₂
  rw [hK] at he₂
  have hmasterDest (i : Fin 10) : plan.master.masters i ≠ normalize.src := by
    rw [hdest]; exact (crop.external 12 (by simp)).2.1 i
  have hKmaster (i : Fin 10) : (K.R (plan.master.masters i)).length = recoveryMasterValues r.rawRecoveryJob.problem i := by
    simpa only [K,Function.update_of_ne (hmasterDest i),Function.update_of_ne (hmasterNe i),
      ite_eq_right (hmasterOff i)] using hmastersLength i
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) (List.ofFn plan.master.masters)
    (List.nodup_ofFn.mpr plan.master.masters_injective) v₂ K
  have hcleanup : 2*((List.ofFn plan.master.masters).map (fun k => (K.R k).length)).sum+
      2*(List.ofFn plan.master.masters).length+1 = retireRecoveryMastersCost r.rawRecoveryJob.problem := by
    simp only [List.map_ofFn,Function.comp_def,hKmaster,List.length_ofFn,retireRecoveryMastersCost,Nat.reduceMul]
  rw [hcleanup] at he₃
  have hfinal : {K with R := fun k => if k ∈ List.ofFn plan.master.masters then [] else K.R k} =
      {S with R := Function.update (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) normalize.src stream} := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hI
    · exact hO
    · exact hL
    funext k
    change (if k ∈ List.ofFn plan.master.masters then [] else K.R k) =
      Function.update (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) normalize.src stream k
    by_cases hm : k ∈ List.ofFn plan.master.masters
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      simp only [hm,ite_true,Function.update_of_ne (hmasterDest i),ite_eq_right (hmasterOff i),hmasters]
    · rw [ite_eq_right hm]
      change Function.update (Function.update (fun k => if k ∈ List.ofFn plan.work then [] else F.R k)
        plan.result (S.R plan.result)) normalize.src stream k = _
      by_cases hd : k = normalize.src
      · subst k; simp only [Function.update_self]
      · rw [Function.update_of_ne hd,Function.update_of_ne hd]
        by_cases hr : k = plan.result
        · subst k; simp only [Function.update_self,ite_eq_right hresultOff]
        · rw [Function.update_of_ne hr]
          by_cases hw : k ∈ List.ofFn plan.work
          · simp only [hw,ite_true]
          · simp only [hw,ite_false]
            exact hframe k (by intro i hi; exact hm (List.mem_ofFn.mpr ⟨i,hi⟩))
  rw [hfinal] at he₃
  refine ⟨Es,hlen,v₃,n₁+(n₂+retireRecoveryMastersCost r.rawRecoveryJob.problem),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁ (Exec.seq he₂ he₃),?_,?_⟩
  · unfold normalizedTimeCost
    simpa only [Nat.add_assoc] using Nat.add_le_add hn₁
      (Nat.add_le_add_right hn₂ (retireRecoveryMastersCost r.rawRecoveryJob.problem))
  · simpa only [hdst] using hglobal
  · intro Cprog hpush hbody depth
    have ht₁ := htrace₁ Cprog hpush hbody 0
    have ht₂ := htrace₂ 0
    rw [hGs] at ht₂
    change ExecWithin body _ 0 _ _ n₂ (Host.mk v₂ {M with R := (Function.update
      (Function.update M.R (link.reg 11) (S.R plan.result)) normalize.src
      ((Es.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++M.R normalize.src))}) at ht₂
    rw [hK] at ht₂
    have ht₁₂ := mn_seq_within_add ht₁ ht₂
    have ht₃ := mn_native_exec_within he₃ 0 (clearWords_native _) 0 _ (by
      simpa only [Nat.zero_mul,Nat.add_zero] using ht₁₂.final)
    have ht := (ExecWithin.seq ht₁₂ ht₃).seq_assoc
    have hshift := ht.shift depth (J := fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+plan.normalizedStock b r Cprog)
      (by intro d z hz; unfold normalizedStock; omega)
    simpa only [normalizedProgram,Nat.zero_add,Nat.add_assoc] using hshift

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
