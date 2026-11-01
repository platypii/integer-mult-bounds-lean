module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateRecoverySeedSources
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexRecoveryFromSeeds

/-! Register wiring for a computed raw recovery supplier. The plans contain
only register maps and separation facts, never solutions or executions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure InverseMasterPlan (T : ℕ) where
  scalar : TblR 25 → Fin T
  scalar_injective : Function.Injective scalar
  parameters : Fin 8 → Fin T
  masters : Fin 10 → Fin T
  masters_injective : Function.Injective masters
  word : Fin T
  saved : Fin T
  tmp : Fin T
  queue : Fin T
  carry : Fin T
  separate : ∀ i r, scalar r ≠ masters i
  regs : ∀ i, [parameters i,scalar .wr,word,saved,tmp,queue].Nodup
  queue_off : ∀ r, scalar r ≠ queue

structure ComputedRecoveryPlan (T : ℕ) where
  master : InverseMasterPlan T
  work : Fin 392 → Fin T
  work_injective : Function.Injective work
  src : Fin T
  saved : Fin T
  count : Fin T
  tmp : Fin T
  spare : Fin T
  result : Fin T
  clock : Fin T
  savedClock : Fin T
  precision : Fin T
  packet : Fin T
  replicas : Fin T
  regs : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup
  separate : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock]
  master_work : ∀ i j, master.masters i ≠ work j
  master_controls : ∀ i, master.masters i ∉ [src,saved,count,tmp,spare,result,clock,savedClock]
  master_seeds : ∀ i, master.masters i ∉ [precision,packet,replicas]
  seed_work : ∀ j, precision ≠ work j ∧ packet ≠ work j ∧ replicas ≠ work j
  seed_tmp : precision ≠ tmp ∧ packet ≠ tmp ∧ replicas ≠ tmp
  seed_result : precision ≠ result ∧ packet ≠ result ∧ replicas ≠ result
  scalar_work : ∀ r i, master.scalar r ≠ work i
  scalar_result : ∀ r, master.scalar r ≠ result
  parameters_work : ∀ j i, master.parameters j ≠ work i
  parameters_result : ∀ j, master.parameters j ≠ result
  aux_work : ∀ k ∈ [master.word,master.saved,master.tmp,master.queue,master.carry], ∀ i, k ≠ work i
  aux_result : result ∉ [master.word,master.saved,master.tmp,master.queue,master.carry]

namespace ComputedRecoveryPlan
variable {T Q A : ℕ} {P U : Type}

def seedSources (plan : ComputedRecoveryPlan T) : Fin 392 → Fin T :=
  recoverySeedSources plan.master.masters plan.precision plan.packet plan.replicas

theorem seedSources_work (plan : ComputedRecoveryPlan T) (i : Fin 392) (j : Fin 392) :
    plan.seedSources i ≠ plan.work j :=
  recoverySeedSources_ne _ _ _ _ _ (fun k => plan.master_work k j)
    (plan.seed_work j).1 (plan.seed_work j).2.1 (plan.seed_work j).2.2 i

theorem seedSources_tmp (plan : ComputedRecoveryPlan T) (i : Fin 392) : plan.seedSources i ≠ plan.tmp := by
  apply recoverySeedSources_ne _ _ _ _ _ _ plan.seed_tmp.1 plan.seed_tmp.2.1 plan.seed_tmp.2.2
  intro k hk
  exact plan.master_controls k (by simp [hk])

noncomputable def program (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U) : Pr P T Q A U :=
  .seq (restoredSupplierMasters plan.master.scalar plan.master.parameters plan.master.masters
    plan.master.word plan.master.saved plan.master.tmp plan.master.queue plan.master.carry)
    (.seq (complexRecoveryFromSeeds b plan.seedSources plan.work plan.src plan.saved plan.count plan.tmp
      plan.spare plan.result plan.clock plan.savedClock) (clearWords (List.ofFn plan.master.masters)))

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
