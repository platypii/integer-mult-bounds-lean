module

public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderRepairProgram
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Execute live-profile repair on the generated-header bank, deriving all
readiness from the initial inputs. Header generation and erasure are charged by
the outer LiveHeaderRepair theorem. -/

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

theorem liveHeaderRepairGenerated_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (w : LiveDescriptorWidths)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS repairLiveT Q (prime + K) U) (S : Stacks repairLiveHeaderT (prime + K))
    (data : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B (fun _ _ => []) (fun i => S.R (repairLiveHeaderRaw i)))
    (hready : LiveDescriptorReady p₀ X hG₀ hK₀ active s repairLiveMode w (embStk sharedHeaderCore S).R)
    (hempty : ∀ key, S.R (repairLiveHeaderRaw (repairSetupTarget key)) = [])
    (hL : ∀ j, S.L (repairLiveHeaderRaw j) = [])
    (hblank : ∀ j, RepairBlank j → S.R (repairLiveHeaderRaw j) = [])
    (hdesc : ∀ key, S.R (repairLiveHeaderRaw (repairDescriptorSource key)) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (repairLiveHeaderRaw repairHost.src) = l.flatten) :
    let G : Stacks repairLiveHeaderT (prime + K) := { S with R := repairHeaderPairBank (T := repairLiveHeaderT) (A := prime + K) p₀ X rb R B repairLiveHeaderBank S.R }
    let C := embStk sharedHeaderCore G
    ∃ (v' : HS repairLiveT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C ∧
      Exec liveBody (liveRepairProgram hQ hA) (mk v C) steps
        (mk v' { C with R := Function.update C.R (liveDescriptorCore repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let G : Stacks repairLiveHeaderT (prime + K) := { S with R := repairHeaderPairBank (T := repairLiveHeaderT) (A := prime + K) p₀ X rb R B repairLiveHeaderBank S.R }
  let C := embStk sharedHeaderCore G
  have dataG : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B (repairCanonicalHeaders p₀ X rb R B)
      (embStk liveDescriptorCore C).R := RepairPendingDescriptorData.liveHeaders p₀ X rb R B data
  have readyG : LiveDescriptorReady p₀ X hG₀ hK₀ active s repairLiveMode w C.R :=
    LiveDescriptorReady.liveHeaders p₀ X rb R B hready
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := exactSelectiveLive_exec ρ n m X rb scale active s body liveBody hlive w
    hQ hA hscale hn hR hB hrb hs v C dataG
    (by
      intro key
      change repairHeaderPairBank (T := repairLiveHeaderT) (A := prime + K) p₀ X rb R B repairLiveHeaderBank S.R (repairLiveHeaderRaw (repairSetupTarget key)) = []
      rw [repairLiveHeaderPair_targets]; exact hempty key)
    (by intro j; exact hL j)
    (by
      intro j hj
      change repairHeaderPairBank (T := repairLiveHeaderT) (A := prime + K) p₀ X rb R B repairLiveHeaderBank S.R (repairLiveHeaderRaw j) = []
      rw [repairLiveHeaderPair_blank p₀ X rb R B S.R j hj]; exact hblank j hj)
    readyG.bounds readyG.bank
    (by
      intro key
      change repairHeaderPairBank (T := repairLiveHeaderT) (A := prime + K) p₀ X rb R B repairLiveHeaderBank S.R (repairLiveHeaderRaw (repairDescriptorSource key)) = []
      rw [repairLiveHeaderPair_descriptors]; exact hdesc key)
    l hl hlen
    (by
      change repairHeaderPairBank (T := repairLiveHeaderT) (A := prime + K) p₀ X rb R B repairLiveHeaderBank S.R (repairLiveHeaderRaw repairHost.src) = l.flatten
      rw [repairLiveHeaderPair_src]; exact hsrc)
  change (m₂ : ℝ) ≤ liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C at hm₂
  exact ⟨v₂, m₂, hu₂, hm₂, he₂⟩

end
end IntegerMultBounds.MathlibTM2.Routing
