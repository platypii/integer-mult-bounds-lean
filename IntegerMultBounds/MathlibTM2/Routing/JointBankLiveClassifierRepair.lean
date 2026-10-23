module

public import IntegerMultBounds.MathlibTM2.Routing.PlacedLiveClassifierRepair
public import IntegerMultBounds.MathlibTM2.Routing.LiveClassifierPlacementLayout
public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleInput
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleCalls
public import IntegerMultBounds.MathlibTM2.Routing.PlacementAround
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Derive placement readiness from concrete words in the enlarged live classifier
bank, then execute placement, generated-input repair and inverse placement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {t₀ Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

local notation "T₀" => liveClassifierPlacementT t₀
local notation "e₀" => liveClassifierPlacementEmbed (t₀ := t₀)
local notation "slot₀" => liveClassifierPlacementSlot (t₀ := t₀)

theorem jointBankLiveClassifierRepair_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (headerBody : P → Pr P repairLiveHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (liveBody f))
    (outerBody : P → Pr P liveHeaderConfigurationT Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg (fieldCore (N := repairLiveHeaderT)) id (headerBody f))
    (classifierBody : P → Pr P liveClassifierT Q (prime + K) U)
    (hclassifier : ∀ f, classifierBody f = embProg classifierCore id (outerBody f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (w : LiveDescriptorWidths)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T₀ Q (prime + K) U) (S : Stacks liveHeaderConfigurationT (prime + K))
    (data : RepairPendingMaskData p₀ X rb wb wm wp wk R B (fun _ _ => []) (fun i => S.R (fieldCore (repairLiveHeaderRaw i))))
    (hready : LiveDescriptorReady p₀ X hG₀ hK₀ active s repairLiveMode w (fun i => S.R (fieldCore (sharedHeaderCore i))))
    (hempty : ∀ key, S.R (fieldCore (repairLiveHeaderRaw (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (fieldCore (repairLiveHeaderRaw j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (fieldCore (repairLiveHeaderRaw j)) = [])
    (hdesc : ∀ key, S.R (fieldCore (repairLiveHeaderRaw (repairDescriptorSource key))) = [])
    (Lrow Lwidth : ℕ) (hRfit : R < 2 ^ Lrow) (hwidthFit : (p₀).wc < 2 ^ Lwidth)
    (hrowInput : S.R (fieldCore (sharedHeaderBinary 0)) = binSyms Lrow R)
    (hwidthInput : S.R (fieldCore (sharedHeaderBinary 1)) = binSyms Lwidth (p₀).wc)
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → S.R (fieldCore (sharedHeaderWork r)) = [])
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm (p₀).wy)
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R (fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R (fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .keyMask)))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (fieldCore (repairLiveHeaderRaw repairHost.src)) = l.flatten)
    (D : Stacks liveClassifierT (prime + K)) (hproject : embStk classifierCore D = S)
    (LK Ln Lo Lt : ℕ) (hsegment : (p₀).K < 2 ^ LK) (hcount : n < 2 ^ Ln)
    (hoffset : ρ + 1 < 2 ^ Lo) (htop : m < 2 ^ Lt)
    (hsegmentInput : D.R (classifierAux 0) = binSyms LK (p₀).K)
    (hrunInput : D.R (classifierAux 1) = binSyms LK (p₀).G)
    (hcountInput : D.R (classifierAux 10) = binSyms Ln n)
    (hoffsetInput : D.R (classifierAux 13) = binSyms Lo (ρ + 1))
    (hphaseOffsetInput : D.R (classifierAux 14) = binSyms Lo ρ)
    (htopInput : D.R (classifierAux 15) = binSyms Lt m)
    (hclassifierScratch : ∀ i : Fin 16, 2 ≤ i.val → i.val ≠ 10 → i.val < 13 → D.R (classifierAux i) = [])
    (htemporary : D.R (classifierCore liveClassifierTemporary) = [])
    (hphase : D.R (classifierCore liveClassifierPhase) = [])
    (ι : P → P')
    (placementBody : P' → Pr P' T₀ Q (prime + K) U)
    (hplacementBody : ∀ f, placementBody (ι f) = embProg e₀ ι (classifierBody f))
    (E : Stacks T₀ (prime + K)) (houterProject : embStk e₀ E = D)
    (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p₀ X))
    (slotWidth : ℕ) (hslotWidth : slotWidth ≤ H) (reservoir : Fin 3)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQplacement : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T₀)
    (rowBits : List Bool) (Lc Lp : ℕ) (hwidthPlacement : fieldsLen (selectiveLen p₀ X) < 2 ^ Lc) (hBin : B < 2 ^ Lp)
    (hrowCanonical : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (bankWords : Fin (swapT t₀) → List (Fin (prime + K + 4)))
    (hpay0 : bankWords (reg pay) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → bankWords j = [])
    (hhdr0 : ∀ k, bankWords (reg (hd k)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) → ∀ x ∈ bankWords (reg i), x ≠ blank ∧ x.val < prime + 4)
    (hleft : ∀ j, E.L j = [])
    (hbank : E.R = sharedScheduleInputBank (classifierCore (liveHeaderConfigurationCore repairHost.src)) D.R
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir)
      bankWords Lc Lp B rowBits l.flatten) :
    let calls := binaryScheduleCalls slot₀ liveClassifierPlacementSlot_injective hd pay hhd hpay hQplacement hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir) hR hB rowBits Lc Lp
      hwidthPlacement hBin hrowCanonical hrowNe hrowValue
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir R true
    let l₁ := moveRecs forward l
    let S₁ : Stacks liveHeaderConfigurationT (prime + K) := { S with R := Function.update S.R (liveHeaderConfigurationCore repairHost.src) l₁.flatten }
    let M : Stacks liveHeaderConfigurationT (prime + K) := { S₁ with R := liveHeaderConfigurationClassifierBank p₀ S₁.R }
    let W : Stacks liveHeaderConfigurationT (prime + K) := { M with R := liveHeaderWidthBank rb (p₀).wy M.R }
    let C := embStk (fieldCore (N := repairLiveHeaderT)) W
    ∃ (v' : HS T₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls E (reservoirExchangeOrder false) +
        ((binaryTemporaryMaskCost p₀ LK Ln Lo Lt + binaryPhaseMaskCost p₀ LK Ln Lo Lt : ℕ) +
        ((((Lr * (4 * rb + 11) + 8 * rb + 12) +
        (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) : ℝ) +
        liveHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lrow Lwidth w C +
        (2 * rb + 2 * (p₀).wy + 5 : ℕ)) + (4 * ((p₀).wy + 1) + 5 : ℕ)) + binaryExchangeChainCost calls E (reservoirExchangeOrder true) ∧
      Exec placementBody (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg e₀ ι (.seq (classifierPairProgram classifierBankReg
          (classifierBankRepeat liveClassifierTemporary liveClassifierPhase) classifierBankPad)
        (.seq (embProg classifierCore id (.seq (binaryFieldBatch (liveHeaderWidthJobs Lr Lm rb (p₀).wy))
        (.seq (embProg (fieldCore (N := repairLiveHeaderT)) id (liveHeaderRepairProgram hQ hA))
          (metadataClean [fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .row))),
            fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .keyMask)))]))))
          (metadataClean [classifierCore liveClassifierTemporary, classifierCore liveClassifierPhase])))) (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v E) steps
        (mk v' { E with R := Function.update E.R (e₀ (classifierCore (liveHeaderConfigurationCore repairHost.src))) (moveRecs backward (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁)).flatten }) := by
  let spec := reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir
  let calls := binaryScheduleCalls slot₀ liveClassifierPlacementSlot_injective hd pay hhd hpay hQplacement hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir) hR hB rowBits Lc Lp
      hwidthPlacement hBin hrowCanonical hrowNe hrowValue
  have hstream : D.R (classifierCore (liveHeaderConfigurationCore repairHost.src)) = l.flatten := by
    rw [← hproject] at hsrc
    exact hsrc
  have hplacement (r : BinaryScheduleReg t₀ 3) :
      E.R (slot₀ r) = binaryScheduleInputWords spec bankWords Lc Lp B rowBits l.flatten r := by
    rw [hbank]
    exact sharedScheduleInputBank_schedule (classifierCore (liveHeaderConfigurationCore repairHost.src)) D.R
      spec bankWords Lc Lp B rowBits l.flatten hstream r
  have hplacementReady : ∀ j, (calls j).Ready E := binaryScheduleCalls_ready slot₀ liveClassifierPlacementSlot_injective
    hd pay hhd hpay hQplacement hT spec hR hB rowBits Lc Lp hwidthPlacement hBin hrowCanonical hrowNe hrowValue
    bankWords hpay0 hpriv hhdr0 hother E hleft l.flatten hplacement
  have houterSrc : E.R (e₀ (classifierCore (liveHeaderConfigurationCore repairHost.src))) = l.flatten := by
    have hc := sharedScheduleInputBank_core (classifierCore (liveHeaderConfigurationCore repairHost.src)) D.R
      spec bankWords Lc Lp B rowBits l.flatten (classifierCore (liveHeaderConfigurationCore repairHost.src))
    rw [hbank]
    exact hc.trans hstream
  exact placedLiveClassifierRepair_exec ρ n m X rb scale active s body liveBody hlive
    headerBody hheader outerBody houter classifierBody hclassifier Lr Lm hr hm w hQ hA hscale hn hR hB hrb hs v S
    data hready hempty hL hblank hdesc Lrow Lwidth hRfit hwidthFit hrowInput hwidthInput hwork
    hrowWidth hmaskWidth hwidthScratch hrow hmask l hl hlen hsrc D hproject
    LK Ln Lo Lt hsegment hcount hoffset htop hsegmentInput hrunInput hcountInput hoffsetInput
    hphaseOffsetInput htopInput hclassifierScratch htemporary hphase
    e₀ liveClassifierPlacementEmbed_injective ι placementBody hplacementBody E houterProject
    (slot₀ .tmp) H hplacementFit slotWidth hslotWidth reservoir calls
    (binaryScheduleCalls_spec slot₀ liveClassifierPlacementSlot_injective hd pay hhd hpay hQplacement hT spec hR hB
      rowBits Lc Lp hwidthPlacement hBin hrowCanonical hrowNe hrowValue) hplacementReady houterSrc

end
end IntegerMultBounds.MathlibTM2.Routing
