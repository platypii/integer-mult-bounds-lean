module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryBanks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedRecoveryReady

/-! Normalization reuses the master's scalar and parameter banks, retained
unary dimensions and cleared recovery scratch. All links are pure wiring. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM
namespace RecoveryBanks
variable {T : ℕ} (bank : RecoveryBank → Fin T) (hinj : Function.Injective bank)

def normalizePortIndex : Fin 4 → Fin 392 := ![200,201,202,203]
theorem normalizePortIndex_injective : Function.Injective normalizePortIndex := by decide +kernel
theorem normalizePortIndex_ne_crop : ∀ i, normalizePortIndex i ≠ 9 := by decide +kernel
theorem normalizePortIndex_ne_payload : ∀ i, normalizePortIndex i ≠ 124 := by decide +kernel

def normalize : RecoveryNormalizePlan T where
  scalar := fun i => bank (.scalar i)
  scalar_injective := by intro i j h; exact RecoveryBank.scalar.inj (hinj h)
  ports := fun i => bank (.work (normalizePortIndex i))
  ports_injective := by intro i j h; exact normalizePortIndex_injective (RecoveryBank.work.inj (hinj h))
  header := bank (.control .masterQueue)
  precision := bank (.control .precision)
  wide := bank (.control .packet)
  rows := bank (.control .cropRows)
  replicas := bank (.control .replicas)
  inputWidth := bank (.work 9)
  count := bank (.work 204)
  src := bank (.control .cropDst)
  work := bank (.work 205)
  saved := bank (.work 206)
  tmp := bank (.work 207)
  sp := bank (.work 208)
  sg := bank (.work 209)
  cy := bank (.work 210)
  regs := by simp [normalizePortIndex,hinj.eq_iff]
  separate := by
    intro k hk i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [hinj.eq_iff]
  ports_off := by intro i j; simp [hinj.eq_iff]
  header_off := by intro i; simp [hinj.eq_iff]

def queue : RecoveryParameterQueue (normalize bank hinj) where
  parameters := fun i => bank (.parameter i)
  word := bank (.control .masterWord)
  saved := bank (.control .masterSaved)
  tmp := bank (.control .masterTmp)
  carry := bank (.control .masterCarry)
  regs := (masterPlan bank hinj).regs

theorem normalize_support_off (k : Fin T) (hk : (normalize bank hinj).support (queue bank hinj) k) :
    k ≠ bank (.work 9) ∧ k ≠ bank (.control .result) ∧ k ≠ bank (.control .cropDst) := by
  rcases hk with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | hk
  · simp [normalize,hinj.eq_iff]
  · simp [queue,hinj.eq_iff]
  · simp [normalize,hinj.eq_iff,normalizePortIndex_ne_crop]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [normalize,queue,hinj.eq_iff]

def link : RecoveryCropNormalizeLink (normalize bank hinj) (queue bank hinj) where
  reg := (crop bank hinj).reg
  injective := (crop bank hinj).injective
  inputWidth := rfl
  source := rfl
  support_off := normalize_support_off bank hinj

theorem normalize_support_masters (k : Fin T) (hk : (normalize bank hinj).support (queue bank hinj) k) :
    ∀ i, (plan bank hinj).master.masters i ≠ k := by
  intro j
  rcases hk with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | hk
  · simp [plan,masterPlan,normalize,hinj.eq_iff]
  · simp [plan,masterPlan,queue,hinj.eq_iff]
  · simp [plan,masterPlan,normalize,hinj.eq_iff]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [plan,masterPlan,normalize,queue,hinj.eq_iff]

theorem normalize_support_payload (k : Fin T) (hk : (normalize bank hinj).support (queue bank hinj) k) :
    k ≠ (plan bank hinj).work 124 := by
  rcases hk with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | hk
  · simp [plan,normalize,hinj.eq_iff]
  · simp [plan,queue,hinj.eq_iff]
  · simp [plan,normalize,hinj.eq_iff,normalizePortIndex_ne_payload]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [plan,normalize,queue,hinj.eq_iff]

end RecoveryBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
