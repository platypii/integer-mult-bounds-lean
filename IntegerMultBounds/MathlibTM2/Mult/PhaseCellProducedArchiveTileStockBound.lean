module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProducedArchiveTilePairStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileStockBound

/-! Uniform volume accounting for the actual production/transpose program.
Only selected nonempty capacities contribute to archive workspace. -/
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

private theorem archive_pair_volume (D V₁ V₂ a b : ℕ) (ha : a ≤ D*V₁) (hb : b ≤ D*V₂) :
    V₁+max a b ≤ (D+1)*(V₁+V₂) := by
  have hm : max a b ≤ D*V₁+D*V₂ := max_le (by omega) (by omega)
  nlinarith only [hm]

theorem produce_transpose_pair_exec_within_volume {P U : Type}
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
          ((ArchiveTilePlan.stockCoefficient T+1)*
            (ArchiveTilePlan.capacity batch₁.records.length ((2^d)^c₁)*(2^d*(L₁*batch₁.W))+
              ArchiveTilePlan.capacity batch₂.records.length ((2^d)^c₂)*(2^d*(L₂*batch₁.W)))))
        depth (.seq (.seq producer₁.program producer₂.program)
        (.seq (plan₁.conditionalProgram producer₁.clock) (plan₂.conditionalProgram producer₂.clock)))
        (Host.mk v S) n (Host.mk v' {S with L := fun _ => [], R := (Function.update
          (Function.update S.R plan₁.src ((List.ofFn fun j => cstream (prime+K) batch₁.W (List.ofFn fun i => tile₁.padded i j).flatten).flatten))
          plan₂.src ((List.ofFn fun j => cstream (prime+K) batch₁.W (List.ofFn fun i => tile₂.padded i j).flatten).flatten))}) := by
  obtain ⟨rows₁,rows₂,tile₁,tile₂,hcap₁,hcap₂,v',n,hu,hn,he⟩ := produce_transpose_pair_exec_within
    producer₁ producer₂ batch₁ batch₂ hw plan₁ plan₂ hsrc₁ hsrc₂ hoff₁ hoff₂ hsep hflags body hA
    hN₁ hN₂ hW₁ hW₂ rest₁ rest₂ v S hready₁ hready₂ hbank₁ hbank₂ hempty₁ hempty₂
    C depth hpush₁ hpush₂ hbody
  have ha := ArchiveTilePlan.conditionalStockAllowance_le plan₁ batch₁.records.length hW₁
  have hb := ArchiveTilePlan.conditionalStockAllowance_le plan₂ batch₂.records.length hW₂
  have hreserve := archive_pair_volume _ _ _ _ _ ha hb
  refine ⟨rows₁,rows₂,tile₁,tile₂,hcap₁,hcap₂,v',n,hu,hn,?_⟩
  exact he.mono (by
    intro z state hs
    exact hs.trans (Nat.add_le_add_left (max_le_max (le_refl _) hreserve) _))

end ScalarPlacement.PackedProducerPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
