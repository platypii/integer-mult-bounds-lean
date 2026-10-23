module

public import IntegerMultBounds.MathlibTM2.Routing.InactiveClassifierFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairAllSourceProfiles
public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderPriceFrame
public import IntegerMultBounds.MathlibTM2.Routing.LiveProfileBankFrame

/-! The prepared bank used by generated/placed repair commutes with record-stream
updates through classifiers, widths, headers and all eleven source profiles. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T N A : ℕ}

theorem repairClassifierGenerated_update (p : Par) (core : Fin repairT → Fin T)
    (bank : Fin T → List (Fin (A + 4))) (str : Fin T) (out : List (Fin (A + 4)))
    (ht : str ≠ core (repairSetupSource (.inr .badMask)))
    (hp : str ≠ core (repairSetupSource (.inr .badPhase))) :
    repairClassifierGenerated p core (Function.update bank str out) =
      Function.update (repairClassifierGenerated p core bank) str out := by
  funext j
  by_cases hj : j = str
  · subst j; simp [repairClassifierGenerated, ht, hp]
  · simp [repairClassifierGenerated, Function.update_apply, hj]

theorem fieldPairGenerated_update (row mask : Fin N) (nr nm : ℕ)
    (bank : Fin (N + 6) → List (Fin (A + 4))) (str : Fin (N + 6)) (out : List (Fin (A + 4)))
    (hr : str ≠ fieldCore row) (hm : str ≠ fieldCore mask) :
    fieldPairGenerated row mask nr nm (Function.update bank str out) =
      Function.update (fieldPairGenerated row mask nr nm bank) str out := by
  funext j
  by_cases hj : j = str
  · subst j; simp [fieldPairGenerated, hr, hm]
  · simp [fieldPairGenerated, Function.update_apply, hj]

noncomputable section
variable (p : Par) (X rb R B : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)

def generatedRepairHeaderInput (E : Stacks inactiveProfileConfigurationT A) : Stacks inactiveProfileHeaderT A :=
  let E₁ : Stacks inactiveProfileConfigurationT A := { E with R := inactiveConfigurationClassifierBank p E.R }
  let W : Stacks inactiveProfileConfigurationT A := { E₁ with R := inactiveProfileWidthBank rb p.wy E₁.R }
  embStk (fieldCore (N := inactiveProfileHeaderT)) W

def generatedRepairProfileInput (D : Stacks inactiveProfileHeaderT A) : Stacks (liveInactiveProfileT repairT 11) A :=
  let H : Stacks inactiveProfileHeaderT A := { D with R := repairHeaderPairBank p X rb R B inactiveProfileHeaderBank D.R }
  embStk sharedHeaderCore H

def generatedRepairCoreInput (C₀ : Stacks (liveInactiveProfileT repairT 11) A) : Stacks repairLiveT A :=
  let G : Stacks (liveInactiveProfileT repairT 11) A := { C₀ with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w C₀.R repairAllSourceProfileJobs }
  embStk liveInactiveProfileCore G

def allSourceRepairPrepared (E : Stacks inactiveProfileConfigurationT A) : Stacks repairLiveT A :=
  generatedRepairCoreInput p X hG hK active s w
    (generatedRepairProfileInput p X rb R B (generatedRepairHeaderInput p rb E))

theorem generatedRepairHeaderInput_updateStream (E : Stacks inactiveProfileConfigurationT A)
    (out : List (Fin (A + 4))) :
    generatedRepairHeaderInput p rb { E with R := Function.update E.R (inactiveConfigurationCore repairHost.src) out } =
      { generatedRepairHeaderInput p rb E with R := Function.update (generatedRepairHeaderInput p rb E).R (inactiveProfileHeaderRaw repairHost.src) out } := by
  have hc (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) :
      inactiveConfigurationClassifierBank p (Function.update bank (inactiveConfigurationCore repairHost.src) out) =
        Function.update (inactiveConfigurationClassifierBank p bank) (inactiveConfigurationCore repairHost.src) out := by
    apply repairClassifierGenerated_update
    · exact inactiveConfigurationCore_injective.ne (repairSetup_source_src _).symm
    · exact inactiveConfigurationCore_injective.ne (repairSetup_source_src _).symm
  have hw (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) :
      inactiveProfileWidthBank rb p.wy (Function.update bank (inactiveConfigurationCore repairHost.src) out) =
        Function.update (inactiveProfileWidthBank rb p.wy bank) (inactiveConfigurationCore repairHost.src) out := by
    dsimp only [inactiveProfileWidthBank, embeddedRepairWidthBank, inactiveConfigurationCore]
    apply fieldPairGenerated_update
    · exact fieldCore_injective.ne (inactiveProfileHeaderRaw_injective.ne (repairSetup_source_src _).symm)
    · exact fieldCore_injective.ne (inactiveProfileHeaderRaw_injective.ne (repairSetup_source_src _).symm)
  let W : Stacks inactiveProfileConfigurationT A := { E with R := inactiveProfileWidthBank rb p.wy (inactiveConfigurationClassifierBank p E.R) }
  unfold generatedRepairHeaderInput
  dsimp only
  rw [hc, hw]
  change embStk fieldCore { W with R := Function.update W.R (fieldCore (inactiveProfileHeaderRaw repairHost.src)) out } = _
  exact embStk_update_stream fieldCore fieldCore_injective W (inactiveProfileHeaderRaw repairHost.src) out

theorem generatedRepairProfileInput_updateStream (D : Stacks inactiveProfileHeaderT A)
    (out : List (Fin (A + 4))) :
    generatedRepairProfileInput p X rb R B { D with R := Function.update D.R (inactiveProfileHeaderRaw repairHost.src) out } =
      { generatedRepairProfileInput p X rb R B D with R := Function.update (generatedRepairProfileInput p X rb R B D).R (inactiveProfileRaw repairHost.src) out } := by
  have hh := repairHeaderPairBank_update p X rb R B inactiveProfileHeaderBank D.R
    (inactiveProfileHeaderRaw repairHost.src) out (fun c k =>
      inactiveProfileHeaderRaw_injective.ne (repairSetup_source_src (.inl (.header c k))).symm)
  let H : Stacks inactiveProfileHeaderT A := { D with R := repairHeaderPairBank p X rb R B inactiveProfileHeaderBank D.R }
  unfold generatedRepairProfileInput
  dsimp only
  rw [hh]
  change embStk sharedHeaderCore { H with R := Function.update H.R (sharedHeaderCore (inactiveProfileRaw repairHost.src)) out } = _
  exact embStk_update_stream sharedHeaderCore sharedHeaderCore_injective H (inactiveProfileRaw repairHost.src) out

theorem generatedRepairCoreInput_updateStream (C₀ : Stacks (liveInactiveProfileT repairT 11) A)
    (out : List (Fin (A + 4))) :
    generatedRepairCoreInput p X hG hK active s w { C₀ with R := Function.update C₀.R (inactiveProfileRaw repairHost.src) out } =
      { generatedRepairCoreInput p X hG hK active s w C₀ with R := Function.update (generatedRepairCoreInput p X hG hK active s w C₀).R (liveDescriptorCore repairHost.src) out } := by
  have hp := liveInactiveProfileBatchBank_update p X hG hK active s repairLiveMode w C₀.R
    repairAllSourceProfileJobs (inactiveProfileRaw repairHost.src) out (fun j _ =>
      liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux _ (.input j)))
  let G : Stacks (liveInactiveProfileT repairT 11) A := { C₀ with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w C₀.R repairAllSourceProfileJobs }
  unfold generatedRepairCoreInput
  dsimp only
  rw [hp]
  change embStk liveInactiveProfileCore { G with R := Function.update G.R (liveInactiveProfileCore (liveDescriptorCore repairHost.src)) out } = _
  exact embStk_update_stream liveInactiveProfileCore liveInactiveProfileCore_injective G (liveDescriptorCore repairHost.src) out

theorem allSourceRepairPrepared_updateStream (E : Stacks inactiveProfileConfigurationT A)
    (out : List (Fin (A + 4))) :
    allSourceRepairPrepared p X rb R B hG hK active s w
        { E with R := Function.update E.R (inactiveConfigurationCore repairHost.src) out } =
      { allSourceRepairPrepared p X rb R B hG hK active s w E with
        R := Function.update (allSourceRepairPrepared p X rb R B hG hK active s w E).R (liveDescriptorCore repairHost.src) out } := by
  simp only [allSourceRepairPrepared, generatedRepairHeaderInput_updateStream,
    generatedRepairProfileInput_updateStream, generatedRepairCoreInput_updateStream]

theorem generatedRepairHeaderInput_blank (E : Stacks inactiveProfileConfigurationT A)
    (hblank : ∀ j, RepairBlank j → E.R (inactiveConfigurationCore j) = []) :
    ∀ j, RepairBlank j → (generatedRepairHeaderInput p rb E).R (inactiveProfileHeaderRaw j) = [] := by
  intro j hj
  change inactiveProfileWidthBank rb p.wy (inactiveConfigurationClassifierBank p E.R)
    (fieldCore (inactiveProfileHeaderRaw j)) = []
  rw [inactiveProfileWidthBank_raw rb p.wy _ j (repairBlank_extraSource j hj .row)
    (repairBlank_extraSource j hj .keyMask)]
  exact (inactiveConfigurationClassifierBank_blank p E.R j hj).trans (hblank j hj)

theorem generatedRepairProfileInput_blank (D : Stacks inactiveProfileHeaderT A)
    (hblank : ∀ j, RepairBlank j → D.R (inactiveProfileHeaderRaw j) = []) :
    ∀ j, RepairBlank j → (generatedRepairProfileInput p X rb R B D).R (inactiveProfileRaw j) = [] := by
  intro j hj
  change repairHeaderPairBank p X rb R B inactiveProfileHeaderBank D.R (inactiveProfileHeaderRaw j) = []
  rw [inactiveProfileHeaderPair_raw_keep p X rb R B D.R j (repairBlank_headerSource j hj)]
  exact hblank j hj

theorem generatedRepairCoreInput_blank (C₀ : Stacks (liveInactiveProfileT repairT 11) A)
    (hblank : ∀ j, RepairBlank j → C₀.R (inactiveProfileRaw j) = []) :
    ∀ j, RepairBlank j → (generatedRepairCoreInput p X hG hK active s w C₀).R (liveDescriptorCore j) = [] := by
  intro j hj
  change liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w C₀.R
    repairAllSourceProfileJobs (inactiveProfileRaw j) = []
  rw [liveInactiveProfileBatch_keep p X hG hK active s repairLiveMode w C₀.R repairAllSourceProfileJobs
    (inactiveProfileRaw j) (fun k _ => liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux j (.input k)))]
  exact hblank j hj

theorem allSourceRepairPrepared_blank (E : Stacks inactiveProfileConfigurationT A)
    (hblank : ∀ j, RepairBlank j → E.R (inactiveConfigurationCore j) = []) :
    ∀ j, RepairBlank j → (allSourceRepairPrepared p X rb R B hG hK active s w E).R (liveDescriptorCore j) = [] := by
  apply generatedRepairCoreInput_blank
  apply generatedRepairProfileInput_blank
  exact generatedRepairHeaderInput_blank p rb E hblank

end
end IntegerMultBounds.MathlibTM2.Routing
