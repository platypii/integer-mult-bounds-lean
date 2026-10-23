module

public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderRepair
public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderWidthFrame
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Execute generated-header live repair on the bank produced by row/key-mask
field generation, deriving every readiness condition from the initial bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {Q K : ℕ} {P U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem liveWidthRepairGenerated_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (headerBody : P → Pr P repairLiveHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (liveBody f))
    (w : LiveDescriptorWidths)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS repairLiveHeaderT Q (prime + K) U) (S : Stacks liveHeaderConfigurationT (prime + K))
    (data : RepairPendingConfigurationData p₀ X rb wb wm wp wk R B (fun _ _ => []) (fun i => S.R (fieldCore (repairLiveHeaderRaw i))))
    (hready : LiveDescriptorReady p₀ X hG₀ hK₀ active s repairLiveMode w (fun i => S.R (fieldCore (sharedHeaderCore i))))
    (hempty : ∀ key, S.R (fieldCore (repairLiveHeaderRaw (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (fieldCore (repairLiveHeaderRaw j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (fieldCore (repairLiveHeaderRaw j)) = [])
    (hdesc : ∀ key, S.R (fieldCore (repairLiveHeaderRaw (repairDescriptorSource key))) = [])
    (Lrow Lwidth : ℕ) (hRfit : R < 2 ^ Lrow) (hwidthFit : (p₀).wc < 2 ^ Lwidth)
    (hrowInput : S.R (fieldCore (sharedHeaderBinary 0)) = binSyms Lrow R)
    (hwidthInput : S.R (fieldCore (sharedHeaderBinary 1)) = binSyms Lwidth (p₀).wc)
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → S.R (fieldCore (sharedHeaderWork r)) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (fieldCore (repairLiveHeaderRaw repairHost.src)) = l.flatten) :
    let W : Stacks liveHeaderConfigurationT (prime + K) := { S with R := liveHeaderWidthBank rb (p₀).wy S.R }
    let C := embStk (fieldCore (N := repairLiveHeaderT)) W
    ∃ (v' : HS repairLiveHeaderT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ liveHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lrow Lwidth w C ∧
      Exec headerBody (liveHeaderRepairProgram hQ hA) (mk v C) steps
        (mk v' { C with R := Function.update C.R (repairLiveHeaderRaw repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let W : Stacks liveHeaderConfigurationT (prime + K) := { S with R := liveHeaderWidthBank rb (p₀).wy S.R }
  let C := embStk (fieldCore (N := repairLiveHeaderT)) W
  have hd := data.liveHeaderWidthBank_data p₀ X rb
  have hkeep := liveHeaderWidthBank_core (A := prime + K) rb (p₀).wy S.R
  have hworkKeep := liveHeaderWidthBank_work (A := prime + K) rb (p₀).wy S.R
  apply liveHeaderRepair_exec ρ n m X rb scale active s body liveBody hlive headerBody hheader
    w hQ hA hscale hn hR hB hrb hs v C hd (hready.liveHeaderWidths rb (p₀).wy)
  · intro key
    exact (liveHeaderWidthBank_targets rb (p₀).wy S.R key).trans (hempty key)
  · exact hL
  · intro j hj
    exact (liveHeaderWidthBank_blank rb (p₀).wy S.R j hj).trans (hblank j hj)
  · intro key
    exact (liveHeaderWidthBank_descriptors rb (p₀).wy S.R key).trans (hdesc key)
  · exact hRfit
  · exact hwidthFit
  · dsimp only [C, W, embStk, Function.comp_apply]
    exact (hworkKeep (.binary 0)).trans hrowInput
  · dsimp only [C, W, embStk, Function.comp_apply]
    exact (hworkKeep (.binary 1)).trans hwidthInput
  · intro r hr
    dsimp only [C, W, embStk, Function.comp_apply]
    exact (hworkKeep r).trans (hwork r hr)
  · exact hl
  · exact hlen
  · exact (hkeep repairHost.src (repairSetup_source_src (.inr .row)).symm
      (repairSetup_source_src (.inr .keyMask)).symm).trans hsrc

end
end IntegerMultBounds.MathlibTM2.Routing
