module

public import IntegerMultBounds.MathlibTM2.Routing.PlacedLiveHeaderRepair
public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderPlacementLayout
public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleInput
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleCalls
public import IntegerMultBounds.MathlibTM2.Routing.PlacementAround
public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderInputFrame
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Derive placement readiness from concrete shared-bank words, then execute
placement, generated-header live repair and inverse placement. Only the stream changes. -/

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

local notation "T₀" => liveHeaderPlacementT t₀
local notation "e₀" => liveHeaderPlacementEmbed (t₀ := t₀)
local notation "slot₀" => liveHeaderPlacementSlot (t₀ := t₀)

theorem jointBankLiveHeaderRepair_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (headerBody : P → Pr P repairLiveHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (liveBody f))
    (w : LiveDescriptorWidths)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T₀ Q (prime + K) U) (S : Stacks repairLiveHeaderT (prime + K))
    (data : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B (fun _ _ => []) (fun i => S.R (repairLiveHeaderRaw i)))
    (hready : LiveDescriptorReady p₀ X hG₀ hK₀ active s repairLiveMode w (embStk sharedHeaderCore S).R)
    (hempty : ∀ key, S.R (repairLiveHeaderRaw (repairSetupTarget key)) = [])
    (hL : ∀ j, S.L (repairLiveHeaderRaw j) = [])
    (hblank : ∀ j, RepairBlank j → S.R (repairLiveHeaderRaw j) = [])
    (hdesc : ∀ key, S.R (repairLiveHeaderRaw (repairDescriptorSource key)) = [])
    (Lrow Lwidth : ℕ) (hRfit : R < 2 ^ Lrow) (hwidthFit : (p₀).wc < 2 ^ Lwidth)
    (hrowInput : S.R (sharedHeaderBinary 0) = binSyms Lrow R)
    (hwidthInput : S.R (sharedHeaderBinary 1) = binSyms Lwidth (p₀).wc)
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → S.R (sharedHeaderWork r) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (repairLiveHeaderRaw repairHost.src) = l.flatten)
    (ι : P → P')
    (outerBody : P' → Pr P' T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody (ι f) = embProg e₀ ι (headerBody f))
    (S' : Stacks T₀ (prime + K)) (houterProject : embStk e₀ S' = S)
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
    (hleft : ∀ j, S'.L j = [])
    (hbank : S'.R = sharedScheduleInputBank (repairLiveHeaderRaw repairHost.src) S.R
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir)
      bankWords Lc Lp B rowBits l.flatten) :
    let calls := binaryScheduleCalls slot₀ liveHeaderPlacementSlot_injective hd pay hhd hpay hQplacement hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir) hR hB rowBits Lc Lp
      hwidthPlacement hBin hrowCanonical hrowNe hrowValue
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir R true
    let l₁ := moveRecs forward l
    let C₁ : Stacks repairLiveHeaderT (prime + K) := { S with R := Function.update S.R (repairLiveHeaderRaw repairHost.src) l₁.flatten }
    ∃ (v' : HS T₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls S' (reservoirExchangeOrder false) +
        liveHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lrow Lwidth w C₁ +
        binaryExchangeChainCost calls S' (reservoirExchangeOrder true) ∧
      Exec outerBody (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg e₀ ι (liveHeaderRepairProgram hQ hA)) (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v S') steps (mk v' { S' with R := Function.update S'.R (e₀ (repairLiveHeaderRaw repairHost.src)) (moveRecs backward (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁)).flatten }) := by
  let spec := reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir
  let calls := binaryScheduleCalls slot₀ liveHeaderPlacementSlot_injective hd pay hhd hpay hQplacement hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir) hR hB rowBits Lc Lp
      hwidthPlacement hBin hrowCanonical hrowNe hrowValue
  have hstream : S.R (repairLiveHeaderRaw repairHost.src) = l.flatten := hsrc
  have hplacement (r : BinaryScheduleReg t₀ 3) :
      S'.R (slot₀ r) = binaryScheduleInputWords spec bankWords Lc Lp B rowBits l.flatten r := by
    rw [hbank]
    exact sharedScheduleInputBank_schedule (repairLiveHeaderRaw repairHost.src) S.R
      spec bankWords Lc Lp B rowBits l.flatten hstream r
  have hplacementReady : ∀ j, (calls j).Ready S' := binaryScheduleCalls_ready slot₀ liveHeaderPlacementSlot_injective
    hd pay hhd hpay hQplacement hT spec hR hB rowBits Lc Lp hwidthPlacement hBin hrowCanonical hrowNe hrowValue
    bankWords hpay0 hpriv hhdr0 hother S' hleft l.flatten hplacement
  have houterSrc : S'.R (e₀ (repairLiveHeaderRaw repairHost.src)) = l.flatten := by
    have hc := sharedScheduleInputBank_core (repairLiveHeaderRaw repairHost.src) S.R
      spec bankWords Lc Lp B rowBits l.flatten (repairLiveHeaderRaw repairHost.src)
    rw [hbank]
    exact hc.trans hstream
  exact placedLiveHeaderRepair_exec ρ n m X rb scale active s body liveBody hlive headerBody hheader
    w hQ hA hscale hn hR hB hrb hs v S data hready hempty hL hblank hdesc
    Lrow Lwidth hRfit hwidthFit hrowInput hwidthInput hwork l hl hlen hsrc
    e₀ liveHeaderPlacementEmbed_injective ι outerBody houter S' houterProject
    (slot₀ .tmp) H hplacementFit slotWidth hslotWidth reservoir calls
    (binaryScheduleCalls_spec slot₀ liveHeaderPlacementSlot_injective hd pay hhd hpay hQplacement hT spec hR hB
      rowBits Lc Lp hwidthPlacement hBin hrowCanonical hrowNe hrowValue) hplacementReady houterSrc

end
end IntegerMultBounds.MathlibTM2.Routing
