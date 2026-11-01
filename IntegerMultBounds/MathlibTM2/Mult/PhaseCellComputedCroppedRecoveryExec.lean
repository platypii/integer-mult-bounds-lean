module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPairedRecoveryExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryPairPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryCropPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedGeneratedRecoveryCrop

/-! Generate masters once, recover and pair complex fields, crop the owned
intervals, and restore the intermediate source and setup banks. -/
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

noncomputable def croppedProgram (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (crop : RecoveryCropPlacement plan) : Pr P T Q A U :=
  .seq (plan.retainedComplexProgram b plan.pairPlacement)
    (.seq (embProg crop.reg Empty.elim generatedRecoveryCrop) (clearWords (List.ofFn plan.master.masters)))

theorem cropped_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (crop : RecoveryCropPlacement plan)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    (d : InverseMasterInput s) (r : RawRecoveryJob s)
    (hmastersEq : recoveryMasterValues r.problem = d.masters)
    (Fs : List (ZMod s → GaussianInt)) (hfields : r.inputFields = complexComponentFields Fs)
    (Zs : List (ZMod s → ℂ)) (hlen : Zs.length = Fs.length)
    (htargets : (List.finRange r.problem.Fs.length).reverse.map (fun j => r.solution j.val) = complexComponentTargets Zs)
    (offset rows : ℕ) (hpart : offset+rows ≤ r.problem.span)
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
    (hclock : S.R plan.clock = []) (hsaved : S.R plan.saved = []) (hsavedClock : S.R plan.savedClock = [])
    (hoffset : (S.R (crop.reg 3)).length = offset) (hrows : (S.R (crop.reg 4)).length = rows) :
    ∃ Gs : List (ZMod s → GaussianInt), Gs.length = Fs.length ∧
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ d.timeCost+recoveryLifecycleTime b plan.work r Fs.length+preparedPairRecoveryOutputCost r Fs.length+
        generatedRecoveryCropCost r.problem.precision r.problem.origin (r.problem.origin+r.problem.span) offset rows Fs.length+
        retireRecoveryMastersCost r.problem ∧
      Exec body (plan.croppedProgram b crop) (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update
          (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) (crop.reg 12)
          ((Gs.reverse.map (fun D => cstream A r.problem.wordWidth
            (packedInterval (r.problem.origin+offset) rows D))).flatten++S.R (crop.reg 12)))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
        (haloVertices s (r.problem.origin+offset) (r.problem.origin+offset+rows))
        (packedIntervalRead r.problem.precision r.problem.wordWidth (r.problem.origin+offset)
          (cstream A r.problem.wordWidth (packedInterval (r.problem.origin+offset) rows D)++S.R (crop.reg 12)))
        z (1/(2 : ℝ)^r.target+1/(2 : ℝ)^r.target)) Zs.reverse Gs.reverse ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
          (d.stock+recoveryLifecycleStock b plan.work r Fs.length Cprog+8*preparedPairRecoveryOutputCost r Fs.length+
            8*generatedRecoveryCropCost r.problem.precision r.problem.origin (r.problem.origin+r.problem.span) offset rows Fs.length))
          depth (plan.croppedProgram b crop) (Host.mk v S) steps
          (Host.mk v' {S with R := (Function.update
            (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) (crop.reg 12)
            ((Gs.reverse.map (fun D => cstream A r.problem.wordWidth
              (packedInterval (r.problem.origin+offset) rows D))).flatten++S.R (crop.reg 12)))}) := by
  obtain ⟨Gs,hGs,v₁,F,n₁,hu₁,hn₁,hI,hO,hL,hframe,hmastersLength,he₁,hgood,htrace₁⟩ :=
    plan.complex_retained_exec b plan.pairPlacement plan.pairPlacement_injective
      (plan.pairPlacement_regs hreplicaCount hreplicaSpare) plan.pairPlacement_masters plan.pairPlacement_work
      d r hmastersEq Fs hfields Zs hlen htargets wl hwl v S hp hW hN hvalues hwidth hscalar hmasters
      hmasterScratch hblank hleft hpayload hscratch hclock hsaved hsavedClock
  let M : Stacks T A := {F with R := (Function.update
    (fun k => if k ∈ List.ofFn plan.work then [] else F.R k) plan.result
    ((Gs.map (fun D => cstream A r.problem.wordWidth
      (packedInterval r.problem.origin r.problem.span D))).flatten++S.R plan.result))}
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
  have hMmaster (i : Fin 10) : (M.R (plan.master.masters i)).length = recoveryMasterValues r.problem i := by
    simpa only [M,Function.update_of_ne (hmasterNe i),ite_eq_right (hmasterOff i)] using hmastersLength i
  have hMframe (k : Fin T) (hw : k ∉ List.ofFn plan.work)
      (hm : ∀ i, plan.master.masters i ≠ k) (hr : k ≠ plan.result) : M.R k = S.R k := by
    simp only [M,Function.update_of_ne hr,ite_eq_right hw,hframe k hm]
  have hMexternal (k : Fin 19) (hk : k ∈ ([(3 : Fin 19),4,12])) : M.R (crop.reg k) = S.R (crop.reg k) :=
    hMframe _ (crop.external k hk).1 (crop.external k hk).2.1 (crop.external k hk).2.2
  have hw : 2*r.problem.precision+8 = r.problem.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  have hrepWork : plan.replicas ∉ List.ofFn plan.work := by
    intro hm
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
    exact (plan.seed_work j).2.2 hj.symm
  have hrepMaster (i : Fin 10) : plan.master.masters i ≠ plan.replicas := by
    intro hi; exact plan.master_seeds i (by simp [hi])
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,haccuracy,htrace₂⟩ := placedGeneratedRecoveryCrop_exec (body := body)
    crop.reg crop.injective r.problem.precision r.problem.origin (r.problem.origin+r.problem.span) offset rows
    (by simpa only [Nat.add_sub_cancel_left] using r.problem.span_fit)
    (by simpa only [Nat.add_sub_cancel_left] using hpart) Zs Gs
    (1/(2 : ℝ)^r.target+1/(2 : ℝ)^r.target) (S.R plan.result) v₁ M
    (by rw [crop.masters.1]; exact hMmaster 2)
    (by rw [crop.masters.2.1]; exact hMmaster 8)
    (by rw [crop.masters.2.2]; exact hMmaster 9)
    (by rw [hMexternal 3 (by simp)]; exact hoffset)
    (by rw [hMexternal 4 (by simp)]; exact hrows)
    (by rw [crop.replicas,hMframe _ hrepWork hrepMaster plan.seed_result.2.2,hGs]; exact hN)
    (by
      intro k hk
      have hm := crop.scratch k hk
      have hr : crop.reg k ≠ plan.result := by intro hr; exact hresultOff (hr ▸ hm)
      simp only [M,Function.update_of_ne hr,hm,ite_true])
    (by simp only [crop.source,M,Function.update_self,Nat.add_sub_cancel_left,hw])
    (by simpa only [Nat.add_sub_cancel_left,hw] using hgood)
  rw [hGs] at hn₂
  have hdst := hMexternal 12 (by simp)
  let stream := (Gs.reverse.map (fun D => cstream A r.problem.wordWidth
    (packedInterval (r.problem.origin+offset) rows D))).flatten++S.R (crop.reg 12)
  let K : Stacks T A := {F with R := (Function.update
    (Function.update (fun k => if k ∈ List.ofFn plan.work then [] else F.R k) plan.result (S.R plan.result))
      (crop.reg 12) stream)}
  have hK : {M with R := (Function.update (Function.update M.R (crop.reg 11) (S.R plan.result)) (crop.reg 12)
      ((Gs.reverse.map (fun D => cstream A (2*r.problem.precision+8)
        (packedInterval (r.problem.origin+offset) rows D))).flatten++M.R (crop.reg 12)))} = K := by
    rw [hdst]
    simp only [M,K,stream,crop.source,Function.update_idem,hw]
  rw [hK] at he₂
  have hcropMaster (i : Fin 10) : plan.master.masters i ≠ crop.reg 12 := (crop.external 12 (by simp)).2.1 i
  have hKmaster (i : Fin 10) : (K.R (plan.master.masters i)).length = recoveryMasterValues r.problem i := by
    simpa only [K,Function.update_of_ne (hcropMaster i),Function.update_of_ne (hmasterNe i),
      ite_eq_right (hmasterOff i)] using hmastersLength i
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) (List.ofFn plan.master.masters)
    (List.nodup_ofFn.mpr plan.master.masters_injective) v₂ K
  have hcleanup : 2*((List.ofFn plan.master.masters).map (fun k => (K.R k).length)).sum+
      2*(List.ofFn plan.master.masters).length+1 = retireRecoveryMastersCost r.problem := by
    simp only [List.map_ofFn,Function.comp_def,hKmaster,List.length_ofFn,retireRecoveryMastersCost,Nat.reduceMul]
  rw [hcleanup] at he₃
  have hfinal : {K with R := fun k => if k ∈ List.ofFn plan.master.masters then [] else K.R k} =
      {S with R := Function.update (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) (crop.reg 12) stream} := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hI
    · exact hO
    · exact hL
    funext k
    change (if k ∈ List.ofFn plan.master.masters then [] else K.R k) =
      Function.update (fun k => if k ∈ List.ofFn plan.work then [] else S.R k) (crop.reg 12) stream k
    by_cases hm : k ∈ List.ofFn plan.master.masters
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      simp only [hm,ite_true,Function.update_of_ne (hcropMaster i),ite_eq_right (hmasterOff i),hmasters]
    · rw [ite_eq_right hm]
      change Function.update (Function.update (fun k => if k ∈ List.ofFn plan.work then [] else F.R k)
        plan.result (S.R plan.result)) (crop.reg 12) stream k = _
      by_cases hd : k = crop.reg 12
      · subst k; simp only [Function.update_self]
      · rw [Function.update_of_ne hd,Function.update_of_ne hd]
        by_cases hr : k = plan.result
        · subst k; simp only [Function.update_self,ite_eq_right hresultOff]
        · rw [Function.update_of_ne hr]
          by_cases hw' : k ∈ List.ofFn plan.work
          · simp only [hw',ite_true]
          · simp only [hw',ite_false]
            exact hframe k (by intro i hi; exact hm (List.mem_ofFn.mpr ⟨i,hi⟩))
  rw [hfinal] at he₃
  refine ⟨Gs,hGs,v₃,n₁+(n₂+retireRecoveryMastersCost r.problem),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁ (Exec.seq he₂ he₃),?_,?_⟩
  · simpa only [Nat.add_assoc] using Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ (retireRecoveryMastersCost r.problem))
  · simpa only [hw,hdst] using haccuracy
  · intro Cprog hpush hbody depth
    have ht₁ := htrace₁ Cprog hpush hbody 0
    have ht₂ := htrace₂ 0
    rw [hGs,hK] at ht₂
    have ht₁₂ := mn_seq_within_add ht₁ ht₂
    have ht₃ := mn_native_exec_within he₃ 0 (clearWords_native _) 0 _ (by
      simpa only [Nat.zero_mul,Nat.add_zero] using ht₁₂.final)
    have ht := (ExecWithin.seq ht₁₂ ht₃).seq_assoc
    have hshift := ht.shift depth (J := fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
      (d.stock+recoveryLifecycleStock b plan.work r Fs.length Cprog+8*preparedPairRecoveryOutputCost r Fs.length+
        8*generatedRecoveryCropCost r.problem.precision r.problem.origin (r.problem.origin+r.problem.span) offset rows Fs.length))
      (by intro j z hz; omega)
    simpa only [croppedProgram,Nat.zero_add,Nat.add_assoc] using hshift

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
