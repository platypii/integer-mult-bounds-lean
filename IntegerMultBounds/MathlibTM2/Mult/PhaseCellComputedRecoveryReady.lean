module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCropOrderedRecovery

/-! Ordinary local recovery readiness and its structural frame rule. The
support excludes the accumulated result and external archive/loop tapes. -/
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

def localControls (plan : ComputedRecoveryPlan T) (crop : RecoveryCropPlacement plan) : List (Fin T) :=
  [plan.precision,plan.packet,plan.replicas,plan.master.word,plan.master.saved,plan.master.tmp,
    plan.master.queue,plan.count,plan.tmp,plan.spare,plan.clock,plan.saved,plan.savedClock,crop.reg 3,crop.reg 4]

def localSupport (plan : ComputedRecoveryPlan T) (normalize : RecoveryNormalizePlan T)
    (queue : RecoveryParameterQueue normalize) (crop : RecoveryCropPlacement plan) (k : Fin T) : Prop :=
  normalize.support queue k ∨ (∃ i, plan.master.scalar i = k) ∨ k ∈ List.ofFn plan.work ++
    List.ofFn plan.master.parameters ++ List.ofFn plan.master.masters ++ plan.localControls crop

theorem localSupport_result (plan : ComputedRecoveryPlan T) (normalize : RecoveryNormalizePlan T)
    (queue : RecoveryParameterQueue normalize) (crop : RecoveryCropPlacement plan)
    (link : RecoveryCropNormalizeLink normalize queue) (hreg : link.reg = crop.reg) :
    ¬ plan.localSupport normalize queue crop plan.result := by
  intro hk
  rcases hk with hn | hs | hl
  · have hsource : link.reg 11 = plan.result := (congrFun hreg 11).trans crop.source
    exact (link.support_off _ hn).2.1 hsource.symm
  · obtain ⟨i,hi⟩ := hs; exact plan.scalar_result i hi
  · simp only [List.mem_append,List.mem_ofFn] at hl
    rcases hl with ((hw | hv) | hm) | hc
    · obtain ⟨i,hi⟩ := hw; exact plan.separate i (by simp [hi])
    · obtain ⟨i,hi⟩ := hv; exact plan.parameters_result i hi
    · obtain ⟨i,hi⟩ := hm; exact plan.master_controls i (by simp [hi])
    · have hr := plan.regs
      regs_ne hr
      simp only [localControls,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact plan.seed_result.1 h.symm
      · exact plan.seed_result.2.1 h.symm
      · exact plan.seed_result.2.2 h.symm
      · exact plan.aux_result (by simp [h])
      · exact plan.aux_result (by simp [h])
      · exact plan.aux_result (by simp [h])
      · exact plan.aux_result (by simp [h])
      · exact ‹plan.count ≠ plan.result› h.symm
      · exact ‹plan.tmp ≠ plan.result› h.symm
      · exact ‹plan.spare ≠ plan.result› h.symm
      · exact ‹plan.result ≠ plan.clock› h
      · exact ‹plan.saved ≠ plan.result› h.symm
      · exact ‹plan.result ≠ plan.savedClock› h
      · exact (crop.external 3 (by simp)).2.2 h.symm
      · exact (crop.external 4 (by simp)).2.2 h.symm

structure LocalReady (plan : ComputedRecoveryPlan T) (normalize : RecoveryNormalizePlan T)
    (queue : RecoveryParameterQueue normalize) (crop : RecoveryCropPlacement plan)
    (r : PackedNormalizedJob A s) (wl : List (Fin (A+4))) (S : Stacks T A) : Prop where
  normalizeReady : normalize.UnaryReady queue r r.Fs.length wl S
  precision : (S.R plan.precision).length = r.p
  packet : (S.R plan.packet).length = r.W
  replicas : (S.R plan.replicas).length = r.Fs.length
  values : ∀ i, (S.R (plan.master.parameters i)).length = r.masterInput.values i
  width : S.R (plan.master.scalar .wr) = wl
  scalar : ∀ i : TblR 25, i ≠ .wr → S.R (plan.master.scalar i) = []
  masters : ∀ i, S.R (plan.master.masters i) = []
  masterScratch : ∀ k ∈ [plan.master.word,plan.master.saved,plan.master.tmp,plan.master.queue], S.R k = []
  blank : ∀ i, i ≠ 124 → S.R (plan.work i) = []
  left : ∀ i, S.L (plan.work i) = []
  payload : S.R (plan.work 124) = cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten
  scratch : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = []
  clock : S.R plan.clock = []
  saved : S.R plan.saved = []
  savedClock : S.R plan.savedClock = []
  offset : (S.R (crop.reg 3)).length = r.radius
  rows : (S.R (crop.reg 4)).length = coreLength s r.coreWidth r.k

theorem LocalReady.of_frame {plan : ComputedRecoveryPlan T} {normalize : RecoveryNormalizePlan T}
    {queue : RecoveryParameterQueue normalize} {crop : RecoveryCropPlacement plan}
    {r : PackedNormalizedJob A s} {wl : List (Fin (A+4))} {S F : Stacks T A}
    (h : plan.LocalReady normalize queue crop r wl S)
    (hR : ∀ k, plan.localSupport normalize queue crop k → F.R k = S.R k)
    (hL : ∀ i, F.L (plan.work i) = S.L (plan.work i)) :
    plan.LocalReady normalize queue crop r wl F := by
  have hw (i : Fin 392) := hR (plan.work i) (by
    have hi : ∃ j : Fin 392, plan.work j = plan.work i := ⟨i,rfl⟩
    simp only [localSupport,List.mem_append,List.mem_ofFn]
    tauto)
  have hs (i : TblR 25) := hR (plan.master.scalar i) (by
    have hi : ∃ j : TblR 25, plan.master.scalar j = plan.master.scalar i := ⟨i,rfl⟩
    simp only [localSupport,List.mem_append,List.mem_ofFn]
    tauto)
  have hv (i : Fin 8) := hR (plan.master.parameters i) (by
    have hi : ∃ j : Fin 8, plan.master.parameters j = plan.master.parameters i := ⟨i,rfl⟩
    simp only [localSupport,List.mem_append,List.mem_ofFn]
    tauto)
  have hm (i : Fin 10) := hR (plan.master.masters i) (by
    have hi : ∃ j : Fin 10, plan.master.masters j = plan.master.masters i := ⟨i,rfl⟩
    simp only [localSupport,List.mem_append,List.mem_ofFn]
    tauto)
  have hc (k : Fin T) (hk : k ∈ plan.localControls crop) :=
    hR k (Or.inr (Or.inr (by simp only [List.mem_append]; tauto)))
  refine ⟨h.normalizeReady.of_frame (fun k hk => hR k (Or.inl hk)),?_,?_,?_,?_,
    (hs .wr).trans h.width,fun i hi => (hs i).trans (h.scalar i hi),
    fun i => (hm i).trans (h.masters i),?_,fun i hi => (hw i).trans (h.blank i hi),
    fun i => (hL i).trans (h.left i),(hw 124).trans h.payload,?_,?_,?_,?_,?_,?_⟩
  · rw [hc _ (by simp [localControls])]; exact h.precision
  · rw [hc _ (by simp [localControls])]; exact h.packet
  · rw [hc _ (by simp [localControls])]; exact h.replicas
  · intro i; rw [hv i]; exact h.values i
  · intro k hk
    rw [hc k (by simp only [localControls,List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)]
    exact h.masterScratch k hk
  · intro k hk
    rw [hc k (by simp only [localControls,List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)]
    exact h.scratch k hk
  · rw [hc _ (by simp [localControls])]; exact h.clock
  · rw [hc _ (by simp [localControls])]; exact h.saved
  · rw [hc _ (by simp [localControls])]; exact h.savedClock
  · rw [hc _ (by simp [localControls])]; exact h.offset
  · rw [hc _ (by simp [localControls])]; exact h.rows

/-- Archive, accumulated-output and scan-counter changes preserve the local
ordinary-input contract whenever those registers lie outside its support. -/
theorem LocalReady.update_external {plan : ComputedRecoveryPlan T} {normalize : RecoveryNormalizePlan T}
    {queue : RecoveryParameterQueue normalize} {crop : RecoveryCropPlacement plan}
    {r : PackedNormalizedJob A s} {wl : List (Fin (A+4))} {S : Stacks T A}
    (h : plan.LocalReady normalize queue crop r wl S) (k : Fin T) (xs : List (Fin (A+4)))
    (hk : ¬ plan.localSupport normalize queue crop k) :
    plan.LocalReady normalize queue crop r wl {S with R := Function.update S.R k xs} := by
  apply h.of_frame
  · intro i hi
    have hik : i ≠ k := by intro he; subst i; exact hk hi
    exact Function.update_of_ne hik xs S.R
  · intro i; rfl

theorem LocalReady.ordered_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (crop : RecoveryCropPlacement plan) (link : RecoveryCropNormalizeLink normalize queue)
    (hreg : link.reg = crop.reg)
    (hsupportMaster : ∀ k, normalize.support queue k → ∀ i, plan.master.masters i ≠ k)
    (hsupportPayload : ∀ k, normalize.support queue k → k ≠ plan.work 124)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    (r : PackedNormalizedJob A s) (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore)
    (v : HS T Q A U) (S : Stacks T A) (h : plan.LocalReady normalize queue crop r wl S)
    (hpacketRows : plan.packet ≠ crop.reg 4) (hpacketReplicas : plan.packet ≠ plan.replicas)
    (hpacketDestination : plan.packet ≠ crop.reg 12) :
    ∃ word v' n, r.output word ∧ v'.user = v.user ∧
      n ≤ plan.normalizedTimeCost b r+restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W ∧
      Exec body (.seq (plan.normalizedProgram b normalize queue link)
        (embProg crop.orderPlacement Empty.elim restoreReplicaOrder)) (Host.mk v S) n
        (Host.mk v' (orderedFinal plan normalize crop.orderPlacement S word)) ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          (plan.normalizedStock b r Cprog+2*restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W))
          depth (.seq (plan.normalizedProgram b normalize queue link) (embProg crop.orderPlacement Empty.elim restoreReplicaOrder))
          (Host.mk v S) n (Host.mk v' (orderedFinal plan normalize crop.orderPlacement S word)) := by
  exact plan.crop_ordered_exec b normalize queue crop link hreg hsupportMaster hsupportPayload
    hreplicaCount hreplicaSpare r wl hwl v S h.normalizeReady h.precision h.packet h.replicas
    h.values h.width h.scalar h.masters h.masterScratch h.blank h.left h.payload h.scratch
    h.clock h.saved h.savedClock h.offset h.rows hpacketRows hpacketReplicas hpacketDestination

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
