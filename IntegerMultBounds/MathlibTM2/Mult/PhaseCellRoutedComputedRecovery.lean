module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedRecoveryReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefixStock

/-! Consume an owned routed halo, execute computed ordered recovery, and return
all local workspace to the caller without copying the remaining archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
namespace ComputedRecoveryPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def routedPayload (r : PackedNormalizedJob A s) : List (Fin (A+4)) :=
  cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten

noncomputable def routedState (plan : ComputedRecoveryPlan T) (r : PackedNormalizedJob A s)
    (source : Fin T) (tail : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update S.R source tail) (plan.work 124) (routedPayload r))}

noncomputable def routedProgram (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (crop : RecoveryCropPlacement plan) (link : RecoveryCropNormalizeLink normalize queue)
    (count source saved tmp : Fin T) : Pr P T Q A U :=
  .seq (takePrefix count source (plan.work 124) saved tmp)
    (.seq (plan.normalizedProgram b normalize queue link) (embProg crop.orderPlacement Empty.elim restoreReplicaOrder))

theorem routed_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (crop : RecoveryCropPlacement plan) (link : RecoveryCropNormalizeLink normalize queue)
    (hreg : link.reg = crop.reg)
    (hsupportMaster : ∀ k, normalize.support queue k → ∀ i, plan.master.masters i ≠ k)
    (hsupportPayload : ∀ k, normalize.support queue k → k ≠ plan.work 124)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    (r : PackedNormalizedJob A s) (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore)
    (v : HS T Q A U) (S : Stacks T A) (count source saved tmp : Fin T)
    (hports : [count,source,plan.work 124,saved,tmp].Nodup)
    (hsourceWork : ∀ i, source ≠ plan.work i) (hsourceResult : source ≠ plan.result)
    (tail : List (Fin (A+4)))
    (hready : plan.LocalReady normalize queue crop r wl (plan.routedState r source tail S))
    (hblank : ∀ i, S.R (plan.work i) = [])
    (hsource : S.R source = routedPayload r++tail)
    (hcount : (S.R count).length = (routedPayload r).length)
    (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hpacketRows : plan.packet ≠ crop.reg 4) (hpacketReplicas : plan.packet ≠ plan.replicas)
    (hpacketDestination : plan.packet ≠ crop.reg 12) :
    ∃ word v' n, r.output word ∧ v'.user = v.user ∧
      n ≤ (6*(routedPayload r).length+6)+(plan.normalizedTimeCost b r+
        restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W) ∧
      Exec body (plan.routedProgram b normalize queue crop link count source saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) plan.result (word++S.R plan.result))}) ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          (2*(6*(routedPayload r).length+6)+(plan.normalizedStock b r Cprog+
            2*restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W))) depth
          (plan.routedProgram b normalize queue crop link count source saved tmp) (Host.mk v S) n
          (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) plan.result (word++S.R plan.result))}) := by
  let H := plan.routedState r source tail S
  obtain ⟨v₁,hu₁,htake⟩ := takePrefix_exec_within (body := body) count source (plan.work 124) saved tmp
    hports (routedPayload r) tail v S hsource hcount hsaved htmp 0
  simp only [hblank 124,List.append_nil] at htake
  obtain ⟨word,v₂,n₂,houtput,hu₂,hn₂,hex₂,htrace₂⟩ := LocalReady.ordered_exec plan b normalize queue crop link hreg
    hsupportMaster hsupportPayload hreplicaCount hreplicaSpare r wl hwl v₁ H hready
    hpacketRows hpacketReplicas hpacketDestination
  have hnormalize : normalize.src = crop.reg 12 := link.source.trans (congrFun hreg 12)
  have hnormalizeWork : normalize.src ∉ List.ofFn plan.work := by
    rw [hnormalize]; exact (crop.external 12 (by simp)).1
  have hnormalizePayload : normalize.src ≠ plan.work 124 := by
    intro he; exact hnormalizeWork (List.mem_ofFn.mpr ⟨124,he.symm⟩)
  have hresultPayload : plan.result ≠ plan.work 124 := by
    intro he; exact plan.separate 124 (by simp [he.symm])
  have hclean : (fun k => if k ∈ List.ofFn plan.work then [] else H.R k) = Function.update S.R source tail := by
    funext k
    by_cases hw : k ∈ List.ofFn plan.work
    · rw [ite_eq_left hw]
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      rw [Function.update_of_ne (hsourceWork i).symm]
      exact (hblank i).symm
    · rw [ite_eq_right hw]
      have hk : k ≠ plan.work 124 := by intro he; exact hw (List.mem_ofFn.mpr ⟨124,he.symm⟩)
      exact Function.update_of_ne hk _ _
  have hn : H.R normalize.src = (Function.update S.R source tail) normalize.src := by
    exact Function.update_of_ne hnormalizePayload _ _
  have hr : H.R plan.result = S.R plan.result := by
    simp only [H,routedState,Function.update_of_ne hresultPayload,Function.update_of_ne hsourceResult.symm]
  have hfinal : orderedFinal plan normalize crop.orderPlacement H word =
      {S with R := (Function.update (Function.update S.R source tail) plan.result (word++S.R plan.result))} := by
    change {S with R := (Function.update (Function.update
      (fun k => if k ∈ List.ofFn plan.work then [] else H.R k) normalize.src (H.R normalize.src))
      (crop.orderPlacement 7) (word++H.R (crop.orderPlacement 7)))} = _
    rw [crop.orderPlacement_ports.2.2.2.2,hclean,hn,Function.update_eq_self,hr]
  rw [hfinal] at hex₂
  refine ⟨word,v₂,(6*(routedPayload r).length+6)+n₂,houtput,hu₂.trans hu₁,
    Nat.add_le_add_left hn₂ _,Exec.seq htake.toExec hex₂,?_⟩
  intro Cprog hpush hbody depth
  have ht₂ := htrace₂ Cprog hpush hbody 0
  rw [hfinal] at ht₂
  have ht := mn_seq_within_add htake ht₂
  simpa only [routedProgram,Nat.zero_add] using ht.shift depth
    (J := fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
      (2*(6*(routedPayload r).length+6)+(plan.normalizedStock b r Cprog+
        2*restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W)))
    (by intro d z hz; omega)

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
