import IntegerMultBounds.Machine.ActiveRepairLayoutDensityArithmetic
import IntegerMultBounds.Machine.ActiveRepairLayoutDensityScan

/-! Positive record counts and payload bounds for complete layout streams. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineBudgetCommon
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout Compact

 theorem records_length_pos {X : Type*} {M : ℕ} (e : X ≃ Fin M)
    (S : Equiv.Perm X) (data : X → List Bool) (hM : 0<M) :
    0<(repairRecords e S data).length := by
  simpa only [repairRecords,plain_length] using hM

 theorem records_payloads {X : Type*} {M : ℕ} (e : X ≃ Fin M)
    (S : Equiv.Perm X) (data : X → List Bool) (R : ℕ) (hR : ∀ x,(data x).length≤R) :
    ∀ r ∈ repairRecords e S data,r.payload.length≤R := by
  intro r hr
  simp only [repairRecords,plain,List.mem_map] at hr
  obtain ⟨i,_,rfl⟩ := hr
  exact hR _

 theorem volume_pos (s : Shape) (rows : ℕ) (hr : 0<rows) (hp : s.payload=1) : 0<rows*s.recordWidth := by
  apply Nat.mul_pos hr
  rw [Shape.recordWidth,hp,Nat.mul_one]
  positivity

end
end IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineBudgetCommon
