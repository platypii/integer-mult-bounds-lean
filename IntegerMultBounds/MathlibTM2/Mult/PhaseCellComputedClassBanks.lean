module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryBankStagedReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedCoreClassRun

/-! A class owns its geometry bank and stream controls outside the reusable
numerical bank. Register separation follows from the ownership constructors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

inductive ComputedClassControl where
  | width | halo | binary | endpointWork | endpointSaved | endpointTmp
  | count | source | saved | tmp | loopSaved | symbols | prepSaved | prepTmp
  deriving DecidableEq

inductive ComputedClassBank where
  | recovery (i : RecoveryBank)
  | geometry (i : Fin 117)
  | control (i : ComputedClassControl)
  deriving DecidableEq

namespace ComputedClassBanks
variable {T : ℕ} (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)

def recovery : RecoveryBank → Fin T := fun i => bank (.recovery i)
include hinj in
theorem recovery_injective : Function.Injective (recovery bank) := by
  intro i j h; exact ComputedClassBank.recovery.inj (hinj h)
def geometry : Fin 117 → Fin T := fun i => bank (.geometry i)
include hinj in
theorem geometry_injective : Function.Injective (geometry bank) := by
  intro i j h; exact ComputedClassBank.geometry.inj (hinj h)
def control : ComputedClassControl → Fin T := fun i => bank (.control i)

abbrev plan := RecoveryBanks.plan (recovery bank) (recovery_injective bank hinj)
abbrev normalize := RecoveryBanks.normalize (recovery bank) (recovery_injective bank hinj)
abbrev queue := RecoveryBanks.queue (recovery bank) (recovery_injective bank hinj)
abbrev crop := RecoveryBanks.crop (recovery bank) (recovery_injective bank hinj)
abbrev link := RecoveryBanks.link (recovery bank) (recovery_injective bank hinj)

theorem localSupport_range (k : Fin T)
    (hk : (RecoveryBanks.plan (recovery bank) (recovery_injective bank hinj)).localSupport
      (RecoveryBanks.normalize (recovery bank) (recovery_injective bank hinj))
      (RecoveryBanks.queue (recovery bank) (recovery_injective bank hinj))
      (RecoveryBanks.crop (recovery bank) (recovery_injective bank hinj)) k) :
    ∃ i, recovery bank i = k := by
  rcases hk with hn | ⟨i,rfl⟩ | hl
  · rcases hn with ⟨i,rfl⟩ | ⟨i,rfl⟩ | ⟨i,rfl⟩ | hn
    · exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · simp only [List.mem_append,List.mem_ofFn] at hl
    rcases hl with ((⟨i,rfl⟩ | ⟨i,rfl⟩) | ⟨i,rfl⟩) | hl
    · exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
    · simp only [ComputedRecoveryPlan.localControls,List.mem_cons,List.not_mem_nil,or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact ⟨_,rfl⟩

theorem localSupport_external (i : ComputedClassControl) :
    ¬ (RecoveryBanks.plan (recovery bank) (recovery_injective bank hinj)).localSupport
      (RecoveryBanks.normalize (recovery bank) (recovery_injective bank hinj))
      (RecoveryBanks.queue (recovery bank) (recovery_injective bank hinj))
      (RecoveryBanks.crop (recovery bank) (recovery_injective bank hinj)) (control bank i) := by
  intro h
  obtain ⟨j,hj⟩ := localSupport_range bank hinj _ h
  simp [recovery,control,hinj.eq_iff] at hj

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
