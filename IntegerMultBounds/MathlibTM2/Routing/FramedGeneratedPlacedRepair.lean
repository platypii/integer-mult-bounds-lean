module

public import IntegerMultBounds.MathlibTM2.Routing.JointBankAllSourceProfilesPriced
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreCall
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedFixedProgram
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedPriceFrame
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedRepairBankExpand

/-! Actual generated/placed repair from a fully framed physical-coordinate and
scalar input bank. Loading, execution and raw-bank erasure use a fixed core plus
three shared tapes; no per-call execution callback is assumed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K : ℕ} {P P' P'' U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "ep₀" => inactiveClassifierPlacementEmbed (t₀ := t₀)
local notation "slot₀" => inactiveClassifierPlacementSlot (t₀ := t₀)

local notation "OP₀" => TP₀ + 3
local notation "esc₀" => framedCoreEmbed TP₀
local notation "aux₀" => framedCoreAux TP₀
local notation "str₀" => ep₀ (classifierCore (inactiveConfigurationCore repairHost.src))

theorem framedGeneratedPlacedRepair_exec
    (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (hguard : p.G + 1 < p.K) (scale : ℕ)
    (hscale : (0 : ℝ) < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G))
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (targets : Finset (Fin (p).wy)) (source : Fin (p).wy → Fin (p).wy)
    (hactive : active = profileActive p hK targets)
    (hsources : s = profileSources p hK targets source) (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (keySrc raw activity : Fin repairT) (hreg : [keySrc, raw, activity].Nodup)
    (hkeyHeader : ∀ c k, keySrc ≠ repairRoutingConfig (.header c k))
    (hrawHeader : ∀ c k, raw ≠ repairRoutingConfig (.header c k))
    (hactivityHeader : ∀ c k, activity ≠ repairRoutingConfig (.header c k))
    (hkeyRow : keySrc ≠ repairSetupSource (.inr .row))
    (hkeyMask : keySrc ≠ repairSetupSource (.inr .keyMask))
    (hrawRow : raw ≠ repairSetupSource (.inr .row))
    (hrawMask : raw ≠ repairSetupSource (.inr .keyMask))
    (hactivityRow : activity ≠ repairSetupSource (.inr .row))
    (hactivityMask : activity ≠ repairSetupSource (.inr .keyMask))
    (hkeyBadMask : keySrc ≠ repairSetupSource (.inr .badMask))
    (hkeyBadPhase : keySrc ≠ repairSetupSource (.inr .badPhase))
    (hrawBadMask : raw ≠ repairSetupSource (.inr .badMask))
    (hrawBadPhase : raw ≠ repairSetupSource (.inr .badPhase))
    (hactivityBadMask : activity ≠ repairSetupSource (.inr .badMask))
    (hactivityBadPhase : activity ≠ repairSetupSource (.inr .badPhase))
    (hkeySrc : keySrc ≠ repairHost.src)
    (hrawSrc : raw ≠ repairHost.src)
    (hactivitySrc : activity ≠ repairHost.src)
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hselectorWidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hkfit : (p).K < 2 ^ w.strideBits) (hnfit : p.n < 2 ^ w.indexBits)
    (hwfit : (p).wy + 2 * (p).wc + X < 2 ^ w.coordinateBits)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (S : Stacks T₀ (prime + K))
    (data : RepairPendingMaskData p X rb wb wm wp wk R B
      (fun _ _ => []) (fun i => S.R (e₀ (liveDescriptorCore i))))
    (hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = [])
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (hinput : ∀ j, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hkey : S.R (liveZSourceActivity keySrc) = sourceCoordinateInputWords w.indexBits w.strideBits
      (profileCoordinateInputs p hK targets source))
    (hrawBlank : S.R (liveZSourceActivity raw) = [])
    (hactivity : S.R (liveZSourceActivity activity) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten)
    (D : Stacks inactiveProfileHeaderT (prime + K)) (hproject : embStk sharedHeaderCore D = S)
    (headerBody : P → Pr P inactiveProfileHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (outerBody f))
    (Lrow Lwidth : ℕ) (hRfit : R < 2 ^ Lrow) (hwidthFit : (p).wc < 2 ^ Lwidth)
    (hrowInput : D.R (sharedHeaderBinary 0) = binSyms Lrow R)
    (hwidthInput : D.R (sharedHeaderBinary 1) = binSyms Lwidth (p).wc)
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → D.R (sharedHeaderWork r) = [])
    (E : Stacks inactiveProfileConfigurationT (prime + K)) (hE : embStk (fieldCore (N := inactiveProfileHeaderT)) E = D)
    (widthBody : P → Pr P inactiveProfileConfigurationT Q (prime + K) U)
    (hwidthBody : ∀ f, widthBody f = embProg (fieldCore (N := inactiveProfileHeaderT)) id (headerBody f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p).wy < 2 ^ Lm)
    (hrowWidth : E.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : E.R (fieldAux 1) = binSyms Lm (p).wy)
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → E.R (fieldAux i) = [])
    (hrow : E.R (fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .row)))) = [])
    (hmask : E.R (fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))) = [])
    (classifierBody : P → Pr P inactiveClassifierT Q (prime + K) U)
    (hclassifier : ∀ f, classifierBody f = embProg classifierCore id (widthBody f))
    (F : Stacks inactiveClassifierT (prime + K)) (hF : embStk classifierCore F = E)
    (LK Ln Lo Lt : ℕ) (hsegment : (p).K < 2 ^ LK) (hcountFit : p.n < 2 ^ Ln)
    (hoffset : p.ρ + 1 < 2 ^ Lo) (htop : p.m < 2 ^ Lt)
    (hsegmentInput : F.R (classifierAux 0) = binSyms LK (p).K)
    (hrunInput : F.R (classifierAux 1) = binSyms LK (p).G)
    (hcountInput : F.R (classifierAux 10) = binSyms Ln p.n)
    (hoffsetInput : F.R (classifierAux 13) = binSyms Lo (p.ρ + 1))
    (hphaseOffsetInput : F.R (classifierAux 14) = binSyms Lo p.ρ)
    (htopInput : F.R (classifierAux 15) = binSyms Lt p.m)
    (hclassifierScratch : ∀ i : Fin 16, 2 ≤ i.val → i.val ≠ 10 → i.val < 13 → F.R (classifierAux i) = [])
    (htemporary : F.R (classifierCore inactiveClassifierTemporary) = [])
    (hphase : F.R (classifierCore inactiveClassifierPhase) = [])
    (ι : P → P')
    (placementBody : P' → Pr P' TP₀ Q (prime + K) U)
    (hplacementBody : ∀ f, placementBody (ι f) = embProg ep₀ ι (classifierBody f))
    (M : Stacks TP₀ (prime + K)) (houterProject : embStk ep₀ M = F)
    (Hslot : ℕ) (hplacementFit : 9 * Hslot ≤ fieldsLen (selectiveLen p X))
    (slotWidth : ℕ) (hslotWidth : slotWidth ≤ Hslot) (reservoir : Fin 3)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQplacement : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ TP₀)
    (rowBits : List Bool) (Lcp Lp : ℕ) (hwidthPlacement : fieldsLen (selectiveLen p X) < 2 ^ Lcp) (hBin : B < 2 ^ Lp)
    (hrowCanonical : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (bankWords : Fin (swapT t₀) → List (Fin (prime + K + 4)))
    (hpay0 : bankWords (reg pay) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → bankWords j = [])
    (hhdr0 : ∀ k, bankWords (reg (hd k)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) → ∀ x ∈ bankWords (reg i), x ≠ blank ∧ x.val < prime + 4)
    (hleft : ∀ j, M.L j = [])
    (hplacementBank : M.R = sharedScheduleInputBank (classifierCore (inactiveConfigurationCore repairHost.src)) F.R
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p X)) Hslot hplacementFit slotWidth hslotWidth reservoir)
      bankWords Lcp Lp B rowBits l.flatten)
    (κ : P' → P'') (schedulerBody : P'' → Pr P'' OP₀ Q (prime + K) U)
    (hscheduler : ∀ f, schedulerBody (κ f) = embProg esc₀ κ (placementBody f))
    (delimiter : Fin (prime + K + 4)) (scan : Fin (prime + K + 4) → Bool)
    (hstop : scan delimiter = false)
    (hmeta : ∀ j, j ≠ str₀ → ∀ x ∈ M.R j, scan x = true)
    (rest : List (Fin (prime + K + 4))) (v : HS OP₀ Q (prime + K) U) (O : Stacks OP₀ (prime + K))
    (hinp : O.inp = M.inp) (hout : O.out = M.out)
    (hcoreL : ∀ j, O.L (esc₀ j) = M.L j)
    (hstreamOuter : O.R (esc₀ str₀) = M.R str₀)
    (hinputOuter : O.R (aux₀ 0) = delimitedBankFrames delimiter (framedCoreJobs esc₀ str₀ M.R) ++ rest)
    (htmpOuter : O.R (aux₀ 1) = [])
    (hblankOuter : ∀ j, j ≠ str₀ → O.R (esc₀ j) = []) :
    let calls := binaryScheduleCalls slot₀ inactiveClassifierPlacementSlot_injective hd pay hhd hpay hQplacement hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p X)) Hslot hplacementFit slotWidth hslotWidth reservoir) hR hB rowBits Lcp Lp
      hwidthPlacement hBin hrowCanonical hrowNe hrowValue
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p X)) Hslot hplacementFit slotWidth hslotWidth reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p X)) Hslot hplacementFit slotWidth hslotWidth reservoir R true
    let l₀ := moveRecs forward l
    ∃ (v' : HS OP₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (allSourcePlacedRepairPrice p X rb hG hK active s
        scale wb wm wp wk R B Lrow Lwidth Lr Lm LK Ln Lo Lt w calls
        (reservoirExchangeOrder false) (reservoirExchangeOrder true) M E) +
        (6 * (delimitedBankFrames delimiter (framedCoreJobs esc₀ str₀ M.R)).length +
          2 * (framedCoreJobs esc₀ str₀ M.R).length + 2 : ℕ) ∧
      Exec schedulerBody (framedCoreCallProgram str₀ delimiter scan κ (allSourcePlacedFixedProgram keySrc raw activity hQ hA hd pay hhd hQplacement hT ι)) (mk v O) steps
        (mk v' { O with R := delimitedCallAdvanced O.R (aux₀ 0) (aux₀ 2) (esc₀ str₀) (delimitedBankFrames delimiter (framedCoreJobs esc₀ str₀ M.R)) rest (moveRecs backward (moveRecs (selectiveIdealPerm hK active s R hs) l₀)).flatten }) := by
  let calls := binaryScheduleCalls slot₀ inactiveClassifierPlacementSlot_injective hd pay hhd hpay hQplacement hT
    (reservoirExchangeSpecs (fieldsLen (selectiveLen p X)) Hslot hplacementFit slotWidth hslotWidth reservoir) hR hB rowBits Lcp Lp
    hwidthPlacement hBin hrowCanonical hrowNe hrowValue
  let forward := reservoirExchangeAction (fieldsLen (selectiveLen p X)) Hslot hplacementFit slotWidth hslotWidth reservoir R false
  let backward := reservoirExchangeAction (fieldsLen (selectiveLen p X)) Hslot hplacementFit slotWidth hslotWidth reservoir R true
  let l₀ := moveRecs forward l
  rw [← allSourcePlacedProgram_eq hd pay hhd hpay hQplacement hT
    (reservoirExchangeSpecs (fieldsLen (selectiveLen p X)) Hslot hplacementFit slotWidth hslotWidth reservoir)
    hR hB rowBits Lcp Lp hwidthPlacement hBin hrowCanonical hrowNe hrowValue
    keySrc raw activity hQ hA Lr Lm rb p.wy ι]
  apply framedCoreCall_exec placementBody schedulerBody κ hscheduler str₀ delimiter scan hstop M.R hmeta
    rest (moveRecs backward (moveRecs (selectiveIdealPerm hK active s R hs) l₀)).flatten v O hinputOuter htmpOuter hblankOuter
    (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg ep₀ ι (.seq (classifierPairProgram classifierBankReg
          (classifierBankRepeat inactiveClassifierTemporary inactiveClassifierPhase) classifierBankPad)
        (.seq (embProg classifierCore id (.seq (binaryFieldBatch (fieldPairJobs (inactiveProfileHeaderRaw (repairSetupSource (.inr .row)))
          (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask))) Lr Lm rb (p).wy))
        (.seq (embProg (fieldCore (N := inactiveProfileHeaderT)) id (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq (liveCoordinateProfilesProgram keySrc raw activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw)))))
          (metadataClean [fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .row))),
            fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))]))))
          (metadataClean [classifierCore inactiveClassifierTemporary, classifierCore inactiveClassifierPhase])))) (binaryExchangeChain calls (reservoirExchangeOrder true)))) (allSourcePlacedRepairPrice p X rb hG hK active s
        scale wb wm wp wk R B Lrow Lwidth Lr Lm LK Ln Lo Lt w calls
        (reservoirExchangeOrder false) (reservoirExchangeOrder true) M E)
  intro u
  have hRun := jointBankAllSourceProfilesPriced_exec
    p X rb hG hK hguard scale hscale hn hradix hgap active
    s targets source hactive hsources body liveBody hlive outerBody houter keySrc raw
    activity hreg hkeyHeader hrawHeader hactivityHeader hkeyRow hkeyMask hrawRow hrawMask hactivityRow hactivityMask hkeyBadMask
    hkeyBadPhase hrawBadMask hrawBadPhase hactivityBadMask hactivityBadPhase hkeySrc hrawSrc hactivitySrc w hwidth hselectorWidthFit hkfit
    hnfit hwfit hQ hA hR hB hrb hs u S data hempty
    hL hblank hfit hbank hdesc hinput hkey hrawBlank hactivity hcount hscratch l
    hl hlen hsrc D hproject headerBody hheader Lrow Lwidth hRfit hwidthFit hrowInput
    hwidthInput hwork E hE widthBody hwidthBody Lr Lm hr hm hrowWidth hmaskWidth
    hwidthScratch hrow hmask classifierBody hclassifier F hF LK Ln Lo Lt hsegment
    hcountFit hoffset htop hsegmentInput hrunInput hcountInput hoffsetInput hphaseOffsetInput htopInput hclassifierScratch htemporary hphase
    ι placementBody hplacementBody M houterProject Hslot hplacementFit slotWidth hslotWidth reservoir hd pay
    hhd hpay hQplacement hT rowBits Lcp Lp hwidthPlacement hBin hrowCanonical hrowNe hrowValue
    bankWords hpay0 hpriv hhdr0 hother hleft hplacementBank
  have hLL : O.L ∘ esc₀ = M.L := funext hcoreL
  simpa only [embStk, hinp, hout, hLL, hstreamOuter, Function.update_eq_self] using hRun

end
end IntegerMultBounds.MathlibTM2.Routing
