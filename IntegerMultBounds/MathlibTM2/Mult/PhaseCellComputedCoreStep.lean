module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedComputedRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadSupplierEndpoints

/-! A fixed computed core step reads and retires its own endpoint headers. -/
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

noncomputable def coreEndpointState (plan : ComputedRecoveryPlan T) (r : PackedNormalizedJob A s)
    (origins : Fin T) (tail : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update S.R origins tail)
    (plan.master.parameters 6) (List.replicate r.a tick)) (plan.master.parameters 7) (List.replicate r.b tick))}

noncomputable def coreProgram (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (crop : RecoveryCropPlacement plan) (link : RecoveryCropNormalizeLink normalize queue)
    (width halo origins binary endpointWork endpointSaved endpointTmp count source saved tmp : Fin T) : Pr P T Q A U :=
  .seq (readSupplierEndpoints width halo origins binary (plan.master.parameters 6) (plan.master.parameters 7)
      endpointWork endpointSaved endpointTmp)
    (.seq (plan.routedProgram b normalize queue crop link count source saved tmp)
      (clearWords [plan.master.parameters 6,plan.master.parameters 7]))

theorem core_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (crop : RecoveryCropPlacement plan) (link : RecoveryCropNormalizeLink normalize queue)
    (hreg : link.reg = crop.reg)
    (hsupportMaster : ∀ k, normalize.support queue k → ∀ i, plan.master.masters i ≠ k)
    (hsupportPayload : ∀ k, normalize.support queue k → k ≠ plan.work 124)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    (r : PackedNormalizedJob A s) (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore)
    (v : HS T Q A U) (S : Stacks T A)
    (width halo origins binary endpointWork endpointSaved endpointTmp count source saved tmp : Fin T)
    (hreader : [width,halo,origins,binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp].Nodup)
    (hports : [count,source,plan.work 124,saved,tmp].Nodup)
    (hframe : [origins,plan.master.parameters 6,plan.master.parameters 7,source,plan.result].Nodup)
    (hsourceWork : ∀ i, source ≠ plan.work i) (horiginsWork : ∀ i, origins ≠ plan.work i)
    (V : ℕ) (hfit : r.a < 2^V) (originTail tail : List (Fin (A+4)))
    (hwidth : (S.R width).length = V) (hhalo : (S.R halo).length = r.b-r.a)
    (horigins : S.R origins = binSyms V r.a++originTail)
    (hreaderBlank : ∀ k ∈ [binary,plan.master.parameters 6,plan.master.parameters 7,
      endpointWork,endpointSaved,endpointTmp], S.R k = [])
    (hready : plan.LocalReady normalize queue crop r wl
      (plan.routedState r source tail (plan.coreEndpointState r origins originTail S)))
    (hblank : ∀ i, S.R (plan.work i) = [])
    (hsource : S.R source = routedPayload r++tail)
    (hcount : (S.R count).length = (routedPayload r).length)
    (htakeOff : ∀ k ∈ [count,saved,tmp], k ≠ origins ∧ k ≠ plan.master.parameters 6 ∧ k ≠ plan.master.parameters 7)
    (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hpacketRows : plan.packet ≠ crop.reg 4) (hpacketReplicas : plan.packet ≠ plan.replicas)
    (hpacketDestination : plan.packet ≠ crop.reg 12) :
    ∃ word v' n, r.output word ∧ v'.user = v.user ∧
      n ≤ readSupplierEndpointsCost V r.a (r.b-r.a)+
        ((6*(routedPayload r).length+6)+(plan.normalizedTimeCost b r+
          restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W))+(2*(r.a+r.b)+5) ∧
      Exec body (plan.coreProgram b normalize queue crop link width halo origins binary endpointWork
        endpointSaved endpointTmp count source saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
          source tail) plan.result (word++S.R plan.result))}) ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          (3*readSupplierEndpointsCost V r.a (r.b-r.a)+
            (2*(6*(routedPayload r).length+6)+(plan.normalizedStock b r Cprog+
              2*restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W)))) depth
          (plan.coreProgram b normalize queue crop link width halo origins binary endpointWork
            endpointSaved endpointTmp count source saved tmp) (Host.mk v S) n
          (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
            source tail) plan.result (word++S.R plan.result))}) := by
  have hr := hframe
  regs_ne hr
  let E := plan.coreEndpointState r origins originTail S
  have hstable (k : Fin T) (ho : k ≠ origins) (ha : k ≠ plan.master.parameters 6)
      (hb : k ≠ plan.master.parameters 7) : E.R k = S.R k := by
    simp only [E,coreEndpointState,Function.update_of_ne hb,Function.update_of_ne ha,Function.update_of_ne ho]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readSupplierEndpoints_exec_within (body := body)
    width halo origins binary (plan.master.parameters 6) (plan.master.parameters 7)
    endpointWork endpointSaved endpointTmp hreader V r.a (r.b-r.a) hfit originTail v S
    hwidth hhalo horigins hreaderBlank 0
  rw [Nat.add_sub_of_le r.bounds.hab] at he₁
  obtain ⟨word,v₂,n₂,houtput,hu₂,hn₂,hex₂,htrace₂⟩ := plan.routed_exec b normalize queue crop link hreg
    hsupportMaster hsupportPayload hreplicaCount hreplicaSpare r wl hwl v₁ E count source saved tmp hports
    hsourceWork ‹source ≠ plan.result› tail hready
    (by intro i; rw [hstable _ (horiginsWork i).symm (plan.parameters_work 6 i).symm
      (plan.parameters_work 7 i).symm]; exact hblank i)
    (by rw [hstable source ‹origins ≠ source›.symm ‹plan.master.parameters 6 ≠ source›.symm
      ‹plan.master.parameters 7 ≠ source›.symm]; exact hsource)
    (by rw [hstable count (htakeOff count (by simp)).1 (htakeOff count (by simp)).2.1
      (htakeOff count (by simp)).2.2]; exact hcount)
    (by rw [hstable saved (htakeOff saved (by simp)).1 (htakeOff saved (by simp)).2.1
      (htakeOff saved (by simp)).2.2]; exact hsaved)
    (by rw [hstable tmp (htakeOff tmp (by simp)).1 (htakeOff tmp (by simp)).2.1
      (htakeOff tmp (by simp)).2.2]; exact htmp)
    hpacketRows hpacketReplicas hpacketDestination
  let F : Stacks T A := {E with R := (Function.update (Function.update E.R source tail) plan.result (word++E.R plan.result))}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [plan.master.parameters 6,plan.master.parameters 7]
    (by simp [‹plan.master.parameters 6 ≠ plan.master.parameters 7›]) v₂ F
  have hlength : (2*(([plan.master.parameters 6,plan.master.parameters 7].map (fun k => (F.R k).length)).sum)+
      2*[plan.master.parameters 6,plan.master.parameters 7].length+1) = 2*(r.a+r.b)+5 := by
    simp_all [F,E,coreEndpointState,ne_comm]

  have hfinal : {F with R := (fun k => if k ∈ [plan.master.parameters 6,plan.master.parameters 7] then [] else F.R k)} =
      {S with R := (Function.update (Function.update (Function.update S.R origins originTail) source tail)
        plan.result (word++S.R plan.result))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have ha := hreaderBlank (plan.master.parameters 6) (by simp)
    have hb := hreaderBlank (plan.master.parameters 7) (by simp)
    by_cases h6 : k = plan.master.parameters 6
    · subst k; simp_all [F,E,coreEndpointState,ne_comm]
    · by_cases h7 : k = plan.master.parameters 7
      · subst k; simp_all [F,E,coreEndpointState,ne_comm]
      · by_cases hkresult : k = plan.result
        · subst k; simp_all [F,E,coreEndpointState,ne_comm]
        · by_cases hksource : k = source
          · subst k; simp_all [F,E,coreEndpointState,ne_comm]
          · simp_all [F,E,coreEndpointState,ne_comm]

  rw [hlength,hfinal] at he₃
  refine ⟨word,v₃,n₁+(n₂+(2*(r.a+r.b)+5)),houtput,hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁.toExec (Exec.seq hex₂ he₃),?_⟩
  · omega
  · intro Cprog hpush hbody depth
    have ht₂ := htrace₂ Cprog hpush hbody 0
    have ht₁₂ := mn_seq_within_add he₁ ht₂
    have ht₃ := mn_native_exec_within he₃ 0 (clearWords_native _) 0 _ (by
      simpa only [Nat.zero_mul,Nat.add_zero] using ht₁₂.final)
    have ht := (ExecWithin.seq ht₁₂ ht₃).seq_assoc
    simpa only [coreProgram,Nat.zero_add,Nat.add_assoc] using ht.shift depth
      (J := fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (3*readSupplierEndpointsCost V r.a (r.b-r.a)+
          (2*(6*(routedPayload r).length+6)+(plan.normalizedStock b r Cprog+
            2*restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W))))
      (by intro d z hz; omega)

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
