import IntegerMultBounds.Machine.CountedLateTapeRepairEndpoint

/-! Density absorption for the complete paid later repair machine. The setup,
key scans, sort, reinsertion and all final cleanup enter the same volume bound. -/
namespace IntegerMultBounds.Machine.CountedLateTapeRepairLinear
noncomputable section
open CountedLateTapeRepairBank
open CountedLateTapeRepairBudget
open CountedLateTapeRepairDensity (density)

theorem coefficient_le (q b : ℕ) (Z : List Bool) (w : ℕ) (hk : width q b Z≤w) :
    coefficient q b Z w≤168*(width q b Z+1)*(w+2) := by
  unfold coefficient
  nlinarith

theorem base_le (q b : ℕ) (hbq : b+3≤q) (Z : List Bool) (w C : ℕ)
    (hk : width q b Z≤w) (hv : volume q b Z≤C*(w+2)) :
    base q b Z w≤(12304*C+60)*Compact.PowerTwo.lateMi q b Z*(w+2) := by
  have hM : 1≤Compact.PowerTwo.lateMi q b Z := by
    rw [Compact.PowerTwo.lateMi_eq q b Z (by omega)]
    have hp : 0<2^(Z.length*q+Z.length*b+Z.length*b) := by positivity
    omega
  have hsetup := Nat.mul_le_mul_left 2004 hv
  have hkey := Nat.mul_le_mul_left (10300*Compact.PowerTwo.lateMi q b Z) hv
  have hsetup' : 2004*C*(w+2)≤2004*C*Compact.PowerTwo.lateMi q b Z*(w+2) := by nlinarith
  have hsmall : 7*width q b Z+88≤44*(w+2) := by omega
  have hsmall' : 44*(w+2)≤44*Compact.PowerTwo.lateMi q b Z*(w+2) := by nlinarith
  unfold base keyCost
  nlinarith

theorem full_cost_le (q b : ℕ) (hbq : b+3≤q) (Z : List Bool) (data : Address q b Z → List Bool)
    (w C : ℕ) (hw : ∀ x,(data x).length≤w)
    (hk : width q b Z≤w) (hv : volume q b Z≤C*(w+2))
    (hsmall : density q b Z*(width q b Z+1)≤1) :
    (fullCost q b Z data : ℝ)≤(12304*C+228)*Compact.PowerTwo.lateMi q b Z*(w+2) := by
  have h := CountedLateTapeRepairDensity.full_cost_le q b hbq Z data w hw
  have hc : (coefficient q b Z w : ℝ)≤168*(width q b Z+1)*(w+2) := by
    exact_mod_cast coefficient_le q b Z w hk
  have hb : (base q b Z w : ℝ)≤(12304*C+60)*Compact.PowerTwo.lateMi q b Z*(w+2) := by
    exact_mod_cast base_le q b hbq Z w C hk hv
  have hδ : 0≤density q b Z := by unfold density; positivity
  have hs := mul_le_mul_of_nonneg_left hc
    (show 0≤density q b Z*Compact.PowerTwo.lateMi q b Z by positivity)
  have ha := mul_le_mul_of_nonneg_left hsmall
    (show 0≤168*(Compact.PowerTwo.lateMi q b Z : ℝ)*(w+2) by positivity)
  nlinarith

/-- A genuine uniform tape execution with its density-absorbed linear bound. -/
theorem runs_linear (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q) (Z : List Bool)
    (hs : Fin 3 → List Bool)
    (hheaders : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hcanonical : ∀ i, GrowingCounterData.Canonical (hs i))
    (data : Address q b Z → List Bool) (w C : ℕ) (hw : ∀ x,(data x).length≤w)
    (hk : width q b Z≤w) (hvol : volume q b Z≤C*(w+2))
    (hsmall : density q b Z*(width q b Z+1)≤1) :
    HoareTime CountedLateTapeRepairEndpoint.program (fun v => v=CountedLateTapeRepairBank.input q b Z hs data)
      (fun v => v=CountedLateTapeRepairCleanupRun.cleaned q b Z hs data)
      ((12304*C+228)*Compact.PowerTwo.lateMi q b Z*(w+2)) := by
  have hcost : fullCost q b Z data≤(12304*C+228)*Compact.PowerTwo.lateMi q b Z*(w+2) := by
    exact_mod_cast full_cost_le q b hbq Z data w C hw hk hvol hsmall
  exact (CountedLateTapeRepairEndpoint.runs q b hb hbq Z hs hheaders hcanonical data).consequence
    (fun _ h => h) (fun _ h => h) hcost


end
end IntegerMultBounds.Machine.CountedLateTapeRepairLinear
