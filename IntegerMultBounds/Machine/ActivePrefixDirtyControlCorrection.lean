import IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionRun

/-! Clean correction producer from the six original compact-source layout
headers, including real operand production and all physical subtraction costs. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrection
noncomputable section
open ActivePrefixDirtyControlData (Shape values)
open ActivePrefixDirtyControlCorrectionRun
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def constant := 2*ActivePrefixDirtyControl.constant+FixedBasePowerDescriptor.constant 2+300

theorem cost_bound (s : Shape .selected) : cost s≤constant*ActivePrefixDirtyControl.volume s := by
  let V := ActivePrefixDirtyControl.volume s
  have hP : 1≤2^s.W := Nat.one_le_pow _ _ (by decide)
  have hPV : 2^s.W≤V := Nat.le_mul_of_pos_right _ (by omega)
  have hV : 0<V := by omega
  have hW : s.n*s.q+1≤V := Nat.le_mul_of_pos_left _ hP |>.trans (Nat.mul_le_mul_left _ (by omega))
  have hNQ : 2^s.W*(s.n*s.q+1)≤V := Nat.mul_le_mul_left _ (by omega)
  have hlenW := CompactGadgetReservationHeadersCost.length_bound (bits (s.n*s.q))
    (RecursiveChildQuotientsConstant.bits_canonical _) V
    (by rw [RecursiveChildQuotientsConstant.bits_value]; omega) hV
  have hlenN := CompactGadgetReservationHeadersCost.length_bound (bits (2^s.W))
    (RecursiveChildQuotientsConstant.bits_canonical _) V
    (by rw [RecursiveChildQuotientsConstant.bits_value]; exact hPV) hV
  have hpower := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hPV
  unfold cost cleanupCost constant
  change _≤(2*ActivePrefixDirtyControl.constant+FixedBasePowerDescriptor.constant 2+300)*V
  nlinarith

theorem runs_linear (s : Shape .selected) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=bank (ActivePrefixDirtyControlCorrectionBank.base hs))
      (fun v => v=bank (ActivePrefixDirtyControlCorrectionBank.output s hs))
      (constant*ActivePrefixDirtyControl.volume s) :=
  (runs s hs hv hc).consequence (fun _ h => h) (fun _ h => h) (cost_bound s)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrection
