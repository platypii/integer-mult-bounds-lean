import IntegerMultBounds.Machine.CountedTapeRepairEndpoint

/-! Density absorption for the complete paid early repair machine. The setup,
key scans, sort, reinsertion and all final cleanup enter the same volume bound. -/
namespace IntegerMultBounds.Machine.CountedTapeRepairLinear
noncomputable section
open CountedTapeRepairBank
open CountedTapeRepairBudget
open CountedTapeRepairDensity (density)

theorem coefficient_le (q b : ℕ) (Z : List Bool) (w : ℕ) (hk : width q b Z≤w) :
    coefficient q b Z w≤168*(width q b Z+1)*(w+2) := by
  unfold coefficient
  nlinarith

theorem base_le (q b : ℕ) (hbq : b+3≤q) (Z : List Bool) (w C : ℕ)
    (hk : width q b Z≤w) (hv : volume q b Z≤C*(w+2)) :
    base q b Z w≤(6104*C+60)*Compact.PowerTwo.Mi q b Z*(w+2) := by
  have hM : 1≤Compact.PowerTwo.Mi q b Z := by
    rw [Compact.PowerTwo.Mi_eq q b Z (by omega)]
    have hp : 0<2^(Z.length*b)*2^(Z.length*q) := by positivity
    omega
  have hsetup := Nat.mul_le_mul_left 1004 hv
  have hkey := Nat.mul_le_mul_left (5100*Compact.PowerTwo.Mi q b Z) hv
  have hsetup' : 1004*C*(w+2)≤1004*C*Compact.PowerTwo.Mi q b Z*(w+2) := by nlinarith
  have hsmall : 7*width q b Z+88≤44*(w+2) := by omega
  have hsmall' : 44*(w+2)≤44*Compact.PowerTwo.Mi q b Z*(w+2) := by nlinarith
  unfold base keyCost
  nlinarith

theorem full_cost_le (q b : ℕ) (hbq : b+3≤q) (Z : List Bool) (data : Address q b Z → List Bool)
    (w C : ℕ) (hw : ∀ x,(data x).length≤w)
    (hk : width q b Z≤w) (hv : volume q b Z≤C*(w+2))
    (hsmall : density q b Z*(width q b Z+1)≤1) :
    (fullCost q b Z data : ℝ)≤(6104*C+228)*Compact.PowerTwo.Mi q b Z*(w+2) := by
  have h := CountedTapeRepairDensity.full_cost_le q b hbq Z data w hw
  have hc : (coefficient q b Z w : ℝ)≤168*(width q b Z+1)*(w+2) := by
    exact_mod_cast coefficient_le q b Z w hk
  have hb : (base q b Z w : ℝ)≤(6104*C+60)*Compact.PowerTwo.Mi q b Z*(w+2) := by
    exact_mod_cast base_le q b hbq Z w C hk hv
  have hδ : 0≤density q b Z := by unfold density; positivity
  have hs := mul_le_mul_of_nonneg_left hc
    (show 0≤density q b Z*Compact.PowerTwo.Mi q b Z by positivity)
  have ha := mul_le_mul_of_nonneg_left hsmall
    (show 0≤168*(Compact.PowerTwo.Mi q b Z : ℝ)*(w+2) by positivity)
  nlinarith

end
end IntegerMultBounds.Machine.CountedTapeRepairLinear
