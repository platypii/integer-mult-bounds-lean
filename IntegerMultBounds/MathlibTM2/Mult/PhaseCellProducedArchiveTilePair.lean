module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerPair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTilePair

/-! The two producer executions supply the actual payloads of both conditional
archive transposes. Only initial metadata readiness is a caller premise. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

namespace ArchiveTilePlan
variable {t₁ t₂ T Q c₁ c₂ d W₁ W₂ K N₁ N₂ : ℕ}

theorem ready_pair_source
    (plan₁ : ArchiveTilePlan t₁ T Q c₁ d W₁) (plan₂ : ArchiveTilePlan t₂ T Q c₂ d W₂)
    (S : Stacks T (prime+K)) (hbank₁ : plan₁.BankReady S) (hbank₂ : plan₂.BankReady S)
    (hoff₁ : plan₁.src ∉ plan₂.support) (hoff₂ : plan₂.src ∉ plan₁.support)
    (w : ℕ) (rows₁ : Fin N₁ → Fin (2^d) → List GaussianInt)
    (rows₂ : Fin N₂ → Fin (2^d) → List GaussianInt) :
    let M : Stacks T (prime+K) := {S with R := (Function.update
      (Function.update S.R plan₁.src ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows₁ i j)).flatten).flatten))
      plan₂.src ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows₂ i j)).flatten).flatten))}
    plan₁.Ready w rows₁ M ∧ plan₂.Ready w rows₂ M := by
  let F : Stacks T (prime+K) := {S with R := (Function.update S.R plan₁.src
    ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows₁ i j)).flatten).flatten))}
  have hfirst : plan₁.Ready w rows₁ F := hbank₁.ready_source w rows₁
  have hnext : plan₂.BankReady F := hbank₂.of_frame (by
    intro i hi
    exact Function.update_of_ne (by intro he; subst i; exact hoff₁ hi) _ _) rfl
  constructor
  · exact hfirst.of_frame (by
      intro i hi
      exact Function.update_of_ne (by intro he; subst i; exact hoff₂ hi) _ _) rfl
  · exact hnext.ready_source w rows₂
end ArchiveTilePlan

namespace ScalarPlacement.PackedProducerPlan
variable {t₁ t₂ T Q c₁ c₂ d K s t L₁ L₂ : ℕ} [NeZero s] [NeZero t]

theorem produce_transpose_pair_exec {P U : Type}
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
    (hempty₁ : S.R producer₁.result = []) (hempty₂ : S.R producer₂.result = []) :
    ∃ rows₁ : batch₁.Rows, ∃ rows₂ : batch₂.Rows,
    ∃ tile₁ : ArchiveTilePlan.Result L₁ rows₁.values, ∃ tile₂ : ArchiveTilePlan.Result L₂ rows₂.values,
      tile₁.capacity = ArchiveTilePlan.capacity batch₁.records.length ((2^d)^c₁) ∧
      tile₂.capacity = ArchiveTilePlan.capacity batch₂.records.length ((2^d)^c₂) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤
        (producer₁.timeCost (U := U) batch₁.records+producer₂.timeCost (U := U) batch₂.records)+
        (plan₁.conditionalCost batch₁.records.length S+plan₂.conditionalCost batch₂.records.length S) ∧
      Exec body (.seq (.seq producer₁.program producer₂.program)
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
  obtain ⟨tile₁,tile₂,hcap₁,hcap₂,v₂,n₂,hu₂,hn₂,he₂⟩ := plan₁.conditional_pair_exec plan₂ producer₁.clock producer₂.clock hoff₁ ha body (by omega)
    hW₁ hW₂ L₁ L₂ batch₁.W rfl rfl hN₁ hN₂ rows₁.values rows₂.values rows₁.length rows₂.length v₁ M hr₁ hr₂ hf₁ hf₂
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
  have he := Exec.seq he₁' he₂
  simpa only [M,Function.update_comm hne,Function.update_idem] using he

end ScalarPlacement.PackedProducerPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
