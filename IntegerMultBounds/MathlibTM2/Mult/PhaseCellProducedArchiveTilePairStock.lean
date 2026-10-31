module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProducedArchiveTilePair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTilePairStock

/-! Actual packed production and archive transposition share temporary workspace.
Only the two produced payloads persist across the handoff. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

namespace ScalarPlacement.PackedProducerPlan
variable {t₁ t₂ T Q c₁ c₂ d K s t L₁ L₂ : ℕ} [NeZero s] [NeZero t]

private theorem producer_phase (s a b d p q x : ℕ) (h : x ≤ s+a+d+p) :
    x ≤ s+a+b+d+max p q := by omega

private theorem archive_phase (s t a b d p q x : ℕ) (ht : t = s+a+b) (h : x ≤ t+d+q) :
    x ≤ s+a+b+d+max p q := by omega

theorem produce_transpose_pair_exec_within {P U : Type}
    (producer₁ producer₂ : PackedProducerPlan T Q)
    (batch₁ : PackedExactBatch (prime+K) s t (2^d) L₁)
    (batch₂ : PackedExactBatch (prime+K) s t (2^d) L₂) (hw : batch₂.W = batch₁.W)
    (plan₁ : ArchiveTilePlan t₁ T Q c₁ d (L₁*batch₁.W))
    (plan₂ : ArchiveTilePlan t₂ T Q c₂ d (L₂*batch₁.W))
    (hsrc₁ : producer₁.result = plan₁.src) (hsrc₂ : producer₂.result = plan₂.src)
    (hoff₁ : plan₁.src ∉ plan₂.support) (hoff₂ : plan₂.src ∉ plan₁.support)
    (hsep : producer₁.result ∉ producer₂.support)
    (hflags : ∀ i ∈ [producer₁.result,producer₂.result], producer₁.clock ≠ i ∧ producer₂.clock ≠ i)
    (body : P → Pr P T Q (prime+K) U) (hA : 96 ≤ prime+K)
    (hN₁ : batch₁.records.length ≤ (2^d)^c₁) (hN₂ : batch₂.records.length ≤ (2^d)^c₂)
    (hW₁ : 0 < batch₁.records.length → 0 < L₁*batch₁.W)
    (hW₂ : 0 < batch₂.records.length → 0 < L₂*batch₁.W)
    (rest₁ rest₂ : List (Fin (prime+K+4))) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hready₁ : producer₁.Ready batch₁.records rest₁ S) (hready₂ : producer₂.Ready batch₂.records rest₂ S)
    (hbank₁ : plan₁.BankReady S) (hbank₂ : plan₂.BankReady S)
    (hempty₁ : S.R producer₁.result = []) (hempty₂ : S.R producer₂.result = []) (C depth : ℕ)
    (hpush₁ : mnProgPush (producer₁.program (P := P) (U := U) (A := prime+K)) ≤ C)
    (hpush₂ : mnProgPush (producer₂.program (P := P) (U := U) (A := prime+K)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    ∃ rows₁ : batch₁.Rows, ∃ rows₂ : batch₂.Rows,
    ∃ tile₁ : ArchiveTilePlan.Result L₁ rows₁.values, ∃ tile₂ : ArchiveTilePlan.Result L₂ rows₂.values,
      tile₁.capacity = ArchiveTilePlan.capacity batch₁.records.length ((2^d)^c₁) ∧
      tile₂.capacity = ArchiveTilePlan.capacity batch₂.records.length ((2^d)^c₂) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤
        (producer₁.timeCost (U := U) batch₁.records+producer₂.timeCost (U := U) batch₂.records)+
        (plan₁.conditionalCost batch₁.records.length S+plan₂.conditionalCost batch₂.records.length S) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+
        batch₁.records.length*(2^d*(L₁*batch₁.W))+batch₂.records.length*(2^d*(L₂*batch₁.W))+depth+
        max ((C+1)*max (producer₁.workspace (U := U) batch₁.records) (producer₂.workspace (U := U) batch₂.records))
          (ArchiveTilePlan.capacity batch₁.records.length ((2^d)^c₁)*(2^d*(L₁*batch₁.W))+
            max (plan₁.conditionalStockAllowance batch₁.records.length) (plan₂.conditionalStockAllowance batch₂.records.length)))
        depth (.seq (.seq producer₁.program producer₂.program)
        (.seq (plan₁.conditionalProgram producer₁.clock) (plan₂.conditionalProgram producer₂.clock)))
        (Host.mk v S) n (Host.mk v' {S with L := fun _ => [], R := (Function.update
          (Function.update S.R plan₁.src ((List.ofFn fun j => cstream (prime+K) batch₁.W (List.ofFn fun i => tile₁.padded i j).flatten).flatten))
          plan₂.src ((List.ofFn fun j => cstream (prime+K) batch₁.W (List.ofFn fun i => tile₂.padded i j).flatten).flatten))}) := by
  have hne : plan₂.src ≠ plan₁.src := by
    intro he
    apply hoff₁
    rw [←he]
    simp [ArchiveTilePlan.support,ArchiveTilePlan.roles]
  obtain ⟨rows₁,rows₂,v₁,n₁,hu₁,hn₁,he₁,hs₁⟩ := producer₁.pair_exec producer₂ body hA batch₁ batch₂ rest₁ rest₂ v S hready₁ hready₂ hsep
  let raw₁ := (List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) batch₁.W (rows₁.values i j)).flatten).flatten
  let raw₂ := (List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) batch₁.W (rows₂.values i j)).flatten).flatten
  let M : Stacks T (prime+K) := {S with R := Function.update (Function.update S.R plan₁.src raw₁) plan₂.src raw₂}
  have hempty₁' : S.R plan₁.src = [] := by rw [←hsrc₁]; exact hempty₁
  have hempty₂' : S.R plan₂.src = [] := by rw [←hsrc₂]; exact hempty₂
  have he₁' : Exec body (.seq producer₁.program producer₂.program) (Host.mk v S) n₁ (Host.mk v₁ M) := by
    simpa only [appendOutput,PackedExactBatch.Rows.stream,hw,hsrc₁,hsrc₂,
      Function.update_of_ne hne,hempty₁',hempty₂',List.append_nil,M,raw₁,raw₂] using he₁
  obtain ⟨hr₁,hr₂⟩ := ArchiveTilePlan.ready_pair_source plan₁ plan₂ S hbank₁ hbank₂ hoff₁ hoff₂ batch₁.W rows₁.values rows₂.values
  have hclock (clock : Fin T) (hc : clock ≠ producer₁.result ∧ clock ≠ producer₂.result) : M.R clock = S.R clock := by
    simp only [M,←hsrc₁,←hsrc₂,Function.update_of_ne hc.1,Function.update_of_ne hc.2]
  have hf₁ : (M.R producer₁.clock).head?.isSome = decide (0 < batch₁.records.length) := by
    rw [hclock _ ⟨(hflags _ (by simp)).1,(hflags _ (by simp)).1⟩,←hready₁.hclock]
    cases S.R producer₁.clock <;> rfl
  have hf₂ : (M.R producer₂.clock).head?.isSome = decide (0 < batch₂.records.length) := by
    rw [hclock _ ⟨(hflags _ (by simp)).2,(hflags _ (by simp)).2⟩,←hready₂.hclock]
    cases S.R producer₂.clock <;> rfl
  have ha : producer₂.clock ≠ plan₁.src := by rw [←hsrc₁]; exact (hflags _ (by simp)).2
  obtain ⟨tile₁,tile₂,hcap₁,hcap₂,v₂,n₂,hu₂,hn₂,he₂⟩ := plan₁.conditional_pair_exec_within plan₂ producer₁.clock producer₂.clock hoff₁ ha body (by omega)
    hW₁ hW₂ L₁ L₂ batch₁.W rfl rfl hN₁ hN₂ rows₁.values rows₂.values rows₁.length rows₂.length v₁ M hr₁ hr₂ hf₁ hf₂ depth
  have hcost₁ : plan₁.conditionalCost batch₁.records.length M = plan₁.conditionalCost batch₁.records.length S := by
    have hb (j : Fin (swapT t₁)) : M.R (plan₁.ι j) = S.R (plan₁.ι j) := by
      have ho : plan₁.ι j ≠ plan₂.src := by intro he; exact hoff₂ (he ▸ ArchiveTilePlan.embedded_mem_support plan₁ j)
      simp [M,ho,plan₁.hsourceOff j]
    simp only [ArchiveTilePlan.conditionalCost,ArchiveTilePlan.cost,hb]
  have hcost₂ : plan₂.conditionalCost batch₂.records.length M = plan₂.conditionalCost batch₂.records.length S := by
    have hb (j : Fin (swapT t₂)) : M.R (plan₂.ι j) = S.R (plan₂.ι j) := by
      have ho : plan₂.ι j ≠ plan₁.src := by intro he; exact hoff₁ (he ▸ ArchiveTilePlan.embedded_mem_support plan₂ j)
      simp [M,ho,plan₂.hsourceOff j]
    simp only [ArchiveTilePlan.conditionalCost,ArchiveTilePlan.cost,hb]
  rw [hcost₁,hcost₂] at hn₂
  refine ⟨rows₁,rows₂,tile₁,tile₂,hcap₁,hcap₂,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  let V₁ := batch₁.records.length*(2^d*(L₁*batch₁.W))
  let V₂ := batch₂.records.length*(2^d*(L₂*batch₁.W))
  let production := (C+1)*max (producer₁.workspace (U := U) batch₁.records) (producer₂.workspace (U := U) batch₂.records)
  let archive := ArchiveTilePlan.capacity batch₁.records.length ((2^d)^c₁)*(2^d*(L₁*batch₁.W))+
    max (plan₁.conditionalStockAllowance batch₁.records.length) (plan₂.conditionalStockAllowance batch₂.records.length)
  let bound := mnSize (Host.mk v S)+V₁+V₂+depth+max production archive
  have hraw₁ : rows₁.stream.length = V₁ := by
    simp [PackedExactBatch.Rows.stream,List.length_flatten,List.map_ofFn,List.sum_ofFn,
      rows₁.length,V₁,Nat.mul_assoc,Nat.mul_comm]
  have hraw₂ : rows₂.stream.length = V₂ := by
    simp [PackedExactBatch.Rows.stream,List.length_flatten,List.map_ofFn,List.sum_ofFn,
      rows₂.length,V₂,hw,Nat.mul_assoc,Nat.mul_comm]
  have hp := hs₁ C hpush₁ hpush₂ hbody depth
  obtain ⟨hsteps,hfinal⟩ := hp.toExec.unique he₁'
  have hboundary : mnSize (Host.mk v₁ M) = mnSize (Host.mk v S)+V₁+V₂ := by
    rw [←hfinal]
    have h₁ := producer₁.appendOutput_stock rows₁.stream v v₁ S
    have h₂ := producer₂.appendOutput_stock rows₂.stream v₁ v₁ (producer₁.appendOutput rows₁.stream S)
    rw [h₁,hraw₁,hraw₂] at h₂
    exact h₂
  rw [hsteps,hfinal] at hp
  have hw₁ := hp.mono (J := fun z state => mnSize state+z ≤ bound) (by
    intro z state hc
    rw [hraw₁] at hc
    exact producer_phase _ _ _ _ _ _ _ hc)
  have hw₂ := he₂.mono (J := fun z state => mnSize state+z ≤ bound) (by
    intro z state hc
    have hc' : mnSize state+z ≤ mnSize (Host.mk v₁ M)+depth+archive := by
      simpa only [archive,Nat.add_assoc] using hc
    exact archive_phase _ _ _ _ _ _ _ _ hboundary hc')
  have he := ExecWithin.seq hw₁ hw₂
  simpa only [M,Function.update_comm hne,Function.update_idem] using he

end ScalarPlacement.PackedProducerPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
