module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedRepairBankFrame

/-! Identify the named preparation stages with the bank in placed execution,
without unfolding that bank inside the complete execution context. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {A : ℕ}

theorem allSourceRepairPrepared_eq (p : Par) (X rb R B : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (E : Stacks inactiveProfileConfigurationT A) :
    allSourceRepairPrepared p X rb R B hG hK active s w E =
      let E₁ : Stacks inactiveProfileConfigurationT A := { E with R := inactiveConfigurationClassifierBank p E.R }
      let W : Stacks inactiveProfileConfigurationT A := { E₁ with R := inactiveProfileWidthBank rb p.wy E₁.R }
      let D := embStk (fieldCore (N := inactiveProfileHeaderT)) W
      let H : Stacks inactiveProfileHeaderT A := { D with R := repairHeaderPairBank p X rb R B inactiveProfileHeaderBank D.R }
      let C₀ := embStk sharedHeaderCore H
      let G : Stacks (liveInactiveProfileT repairT 11) A := { C₀ with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w C₀.R repairAllSourceProfileJobs }
      embStk liveInactiveProfileCore G := rfl

end
end IntegerMultBounds.MathlibTM2.Routing
