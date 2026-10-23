module

public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderRepairMoved
public import IntegerMultBounds.MathlibTM2.Routing.PlacementAround
public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderInputFrame
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Generate all ten headers, compile all eleven live-profile descriptors, execute
exact repair and erase all generated configuration. Only the stream changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {t₀ T Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem placedLiveHeaderRepair_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (headerBody : P → Pr P repairLiveHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (liveBody f))
    (w : LiveDescriptorWidths)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T Q (prime + K) U) (S : Stacks repairLiveHeaderT (prime + K))
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
    (e : Fin repairLiveHeaderT → Fin T) (he : Function.Injective e) (ι : P → P')
    (outerBody : P' → Pr P' T Q (prime + K) U)
    (houter : ∀ f, outerBody (ι f) = embProg e ι (headerBody f))
    (S' : Stacks T (prime + K)) (hproject : embStk e S' = S)
    (tmp : Fin T) (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p₀ X))
    (slotWidth : ℕ) (hslotWidth : slotWidth ≤ H) (reservoir : Fin 3)
    (calls : Fin 3 → BinaryExchangeCall t₀ T Q (fieldsLen (selectiveLen p₀ X)) R B
      (e (repairLiveHeaderRaw repairHost.src)) tmp)
    (hspec : ∀ j, (calls j).spec = reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir j)
    (hplacement : ∀ j, (calls j).Ready S')
    (houterSrc : S'.R (e (repairLiveHeaderRaw repairHost.src)) = l.flatten) :
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir R true
    let l₁ := moveRecs forward l
    let C₁ : Stacks repairLiveHeaderT (prime + K) := { S with R := Function.update S.R (repairLiveHeaderRaw repairHost.src) l₁.flatten }
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls S' (reservoirExchangeOrder false) +
        liveHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lrow Lwidth w C₁ +
        binaryExchangeChainCost calls S' (reservoirExchangeOrder true) ∧
      Exec outerBody (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg e ι (liveHeaderRepairProgram hQ hA)) (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v S') steps (mk v' { S' with R := Function.update S'.R (e (repairLiveHeaderRaw repairHost.src)) (moveRecs backward (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁)).flatten }) := by
  let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit slotWidth hslotWidth reservoir R false
  let l₁ := moveRecs forward l
  let S₁ : Stacks T (prime + K) := { S' with R := Function.update S'.R (e (repairLiveHeaderRaw repairHost.src)) l₁.flatten }
  let C₁ : Stacks repairLiveHeaderT (prime + K) := { S with R := Function.update S.R (repairLiveHeaderRaw repairHost.src) l₁.flatten }
  apply placementAround_exec outerBody _ tmp H hplacementFit slotWidth hslotWidth reservoir calls hspec v S' hplacement
    l hl hlen houterSrc (embProg e ι (liveHeaderRepairProgram hQ hA)) (selectiveIdealPerm hK₀ active s R hs)
    (liveHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lrow Lwidth w C₁)
  intro u
  obtain ⟨u₁, k, hu₁, hk, hx⟩ := liveHeaderRepairMoved_exec ρ n m X rb scale active s
    body liveBody hlive headerBody hheader w hQ hA hscale hn hR hB hrb hs (embDn e u) S
    data hready hempty hL hblank hdesc Lrow Lwidth hRfit hwidthFit hrowInput hwidthInput hwork l hl hlen hsrc forward
  have hp : embStk e S₁ = C₁ := by
    dsimp only [S₁, C₁]
    rw [embStk_update_stream e he, hproject]
  change Exec headerBody _ (mk (embDn e u) C₁) k
    (mk u₁ { C₁ with R := Function.update C₁.R (repairLiveHeaderRaw repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁).flatten }) at hx
  rw [← hp] at hx
  obtain ⟨u₂, hu₂, hx₂⟩ := exec_emb_stream e he ι headerBody outerBody houter _ u S₁ u₁ k
    (repairLiveHeaderRaw repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁).flatten hx
  rw [embDn_user] at hu₁
  exact ⟨u₂, k, hu₂.trans hu₁, hk, hx₂⟩

end
end IntegerMultBounds.MathlibTM2.Routing
