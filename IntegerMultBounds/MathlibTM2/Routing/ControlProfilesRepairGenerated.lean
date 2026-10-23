module

public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveControlProfiles
public import IntegerMultBounds.MathlibTM2.Routing.RepairControlProfileClean
public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderRepairProgram
public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderInputFrame

/-! Exact repair runs on the generated inactive-profile bank. Every readiness
fact is derived from the original bank with those nine profile tapes blank. -/

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
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

theorem controlProfilesRepairGenerated_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (w : LiveDescriptorWidths)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS repairLiveT Q (prime + K) U) (S : Stacks T₀ (prime + K))
    (data : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (fun i => S.R (e₀ (liveDescriptorCore i))))
    (hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = [])
    (hfit : ∀ j, LiveDescriptorBounds p₀ X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairControlProfileJobs, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p₀ X hG₀ hK₀ active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten) :
    let G : Stacks T₀ (prime + K) := { S with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w S.R repairControlProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS repairLiveT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C ∧
      Exec liveBody (liveRepairProgram hQ hA) (mk v C) steps
        (mk v' { C with R := Function.update C.R (liveDescriptorCore repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let G : Stacks T₀ (prime + K) := { S with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w S.R repairControlProfileJobs }
  let C := embStk e₀ G
  have hraw := repairLiveControlProfiles_core p₀ X hG₀ hK₀ active s w S.R
  have hready := repairLiveControlProfiles_ready p₀ X hG₀ hK₀ active s w S.R hfit hbank
  apply exactSelectiveLive_exec ρ n m X rb scale active s body liveBody hlive w
    hQ hA hscale hn hR hB hrb hs v C
  · apply data.congr p₀ X rb
    intro key
    exact hraw (repairSetupSource key)
  · intro key
    exact (hraw (repairSetupTarget key)).trans (hempty key)
  · exact hL
  · intro j hj
    exact (hraw j).trans (hblank j hj)
  · exact hfit
  · intro r
    dsimp only [C, G, embStk, Function.comp_apply]
    exact hready.bank r
  · intro d
    exact (hraw (repairDescriptorSource d)).trans (hdesc d)
  · exact hl
  · exact hlen
  · exact (hraw repairHost.src).trans hsrc

end
end IntegerMultBounds.MathlibTM2.Routing
