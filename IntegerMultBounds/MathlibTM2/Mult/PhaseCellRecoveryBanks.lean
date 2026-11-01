module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDefaultRecoveryCropPlacement

/-! One injective bank map supplies the actual recovery, master and crop wiring.
Bank separation is structural; only small control selectors are finite data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM

inductive RecoveryControl where
  | src | saved | count | tmp | spare | result | clock | savedClock
  | precision | packet | replicas
  | masterWord | masterSaved | masterTmp | masterQueue | masterCarry
  | cropOffset | cropRows | cropDst
  deriving DecidableEq

inductive RecoveryBank where
  | scalar (i : TblR 25)
  | parameter (i : Fin 8)
  | master (i : Fin 10)
  | work (i : Fin 392)
  | control (i : RecoveryControl)
  deriving DecidableEq

namespace RecoveryBanks
variable {T : ℕ} (bank : RecoveryBank → Fin T) (hinj : Function.Injective bank)
open RecoveryBank RecoveryControl

def masterPlan : InverseMasterPlan T where
  scalar := fun i => bank (.scalar i)
  scalar_injective := by intro i j h; exact RecoveryBank.scalar.inj (hinj h)
  parameters := fun i => bank (.parameter i)
  masters := fun i => bank (.master i)
  masters_injective := by intro i j h; exact RecoveryBank.master.inj (hinj h)
  word := bank (.control .masterWord)
  saved := bank (.control .masterSaved)
  tmp := bank (.control .masterTmp)
  queue := bank (.control .masterQueue)
  carry := bank (.control .masterCarry)
  separate := by intro i r; simp [hinj.eq_iff]
  regs := by intro i; simp [hinj.eq_iff]
  queue_off := by intro i; simp [hinj.eq_iff]

def plan : ComputedRecoveryPlan T where
  master := masterPlan bank hinj
  work := fun i => bank (.work i)
  work_injective := by intro i j h; exact RecoveryBank.work.inj (hinj h)
  src := bank (.control .src)
  saved := bank (.control .saved)
  count := bank (.control .count)
  tmp := bank (.control .tmp)
  spare := bank (.control .spare)
  result := bank (.control .result)
  clock := bank (.control .clock)
  savedClock := bank (.control .savedClock)
  precision := bank (.control .precision)
  packet := bank (.control .packet)
  replicas := bank (.control .replicas)
  regs := by simp [hinj.eq_iff]
  separate := by intro i; simp [hinj.eq_iff]
  master_work := by intro i j; simp [masterPlan,hinj.eq_iff]
  master_controls := by intro i; simp [masterPlan,hinj.eq_iff]
  master_seeds := by intro i; simp [masterPlan,hinj.eq_iff]
  seed_work := by intro i; simp [hinj.eq_iff]
  seed_tmp := by simp [hinj.eq_iff]
  seed_result := by simp [hinj.eq_iff]
  scalar_work := by intro i j; simp [masterPlan,hinj.eq_iff]
  scalar_result := by intro i; simp [masterPlan,hinj.eq_iff]
  parameters_work := by intro i j; simp [masterPlan,hinj.eq_iff]
  parameters_result := by intro i; simp [masterPlan,hinj.eq_iff]
  aux_work := by intro k hk j; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [masterPlan,hinj.eq_iff]
  aux_result := by simp [masterPlan,hinj.eq_iff]

def externalIndex : Fin 3 → RecoveryControl := ![.cropOffset,.cropRows,.cropDst]
theorem externalIndex_injective : Function.Injective externalIndex := by decide +kernel

def crop : RecoveryCropPlacement (plan bank hinj) :=
  RecoveryCropPlacement.ofBanks (plan bank hinj) (fun i => bank (.control (externalIndex i)))
    (by intro i j h; exact externalIndex_injective (RecoveryBank.control.inj (hinj h)))
    (by intro i j; simp [plan,masterPlan,hinj.eq_iff])
    (by intro i j; simp [plan,hinj.eq_iff])
    (by intro i; fin_cases i <;> simp [plan,externalIndex,hinj.eq_iff])

theorem crop_ports :
    (crop bank hinj).reg 3 = bank (.control .cropOffset) ∧
    (crop bank hinj).reg 4 = bank (.control .cropRows) ∧
    (crop bank hinj).reg 12 = bank (.control .cropDst) := ⟨rfl,rfl,rfl⟩

end RecoveryBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
