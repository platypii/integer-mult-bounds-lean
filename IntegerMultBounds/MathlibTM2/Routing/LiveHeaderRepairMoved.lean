module

public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderRepair
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

variable {Q K : ℕ} {P U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem liveHeaderRepairMoved_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (headerBody : P → Pr P repairLiveHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (liveBody f))
    (w : LiveDescriptorWidths)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS repairLiveHeaderT Q (prime + K) U) (S : Stacks repairLiveHeaderT (prime + K))
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
    (_hsrc : S.R (repairLiveHeaderRaw repairHost.src) = l.flatten)
    (π : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p₀ X)))) :
    let l₁ := moveRecs π l
    let S₁ : Stacks repairLiveHeaderT (prime + K) := { S with R := Function.update S.R (repairLiveHeaderRaw repairHost.src) l₁.flatten }
    ∃ (v' : HS repairLiveHeaderT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ liveHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lrow Lwidth w S₁ ∧
      Exec headerBody (liveHeaderRepairProgram hQ hA) (mk v S₁) steps
        (mk v' { S₁ with R := Function.update S₁.R (repairLiveHeaderRaw repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁).flatten }) := by
  let l₁ := moveRecs π l
  let S₁ : Stacks repairLiveHeaderT (prime + K) := { S with R := Function.update S.R (repairLiveHeaderRaw repairHost.src) l₁.flatten }
  have hkeep (i : Fin repairLiveHeaderT) (hi : i ≠ repairLiveHeaderRaw repairHost.src) : S₁.R i = S.R i := by
    dsimp only [S₁]
    exact Function.update_of_ne hi _ _
  apply liveHeaderRepair_exec ρ n m X rb scale active s body liveBody hlive headerBody hheader w
    hQ hA hscale hn hR hB hrb hs v S₁
  · exact data.updateLiveHeaderStream p₀ X rb l₁.flatten
  · exact hready.updateHeaderStream p₀ X l₁.flatten
  · intro key
    rw [hkeep _ (repairLiveHeaderRaw_injective.ne (repairSetup_target_src key))]
    exact hempty key
  · exact hL
  · intro j hj
    rw [hkeep _ (repairLiveHeaderRaw_injective.ne (repairBlank_src j hj))]
    exact hblank j hj
  · intro key
    rw [hkeep _ (repairLiveHeaderRaw_injective.ne (show repairDescriptorSource key ≠ repairHost.src from ?_))]
    · exact hdesc key
    · rw [repairDescriptorSource_eq]; exact repairSetup_source_src _
  · exact hRfit
  · exact hwidthFit
  · dsimp only [S₁]
    rw [liveHeaderBinary_updateStream]; exact hrowInput
  · dsimp only [S₁]
    rw [liveHeaderBinary_updateStream]; exact hwidthInput
  · intro r hr
    dsimp only [S₁]
    rw [liveHeaderWork_updateStream]; exact hwork r hr
  · exact length_moveRecs π l
  · intro r hr; exact hlen r (mem_moveRecs π hl hr)
  · simp [S₁, l₁]

end
end IntegerMultBounds.MathlibTM2.Routing
