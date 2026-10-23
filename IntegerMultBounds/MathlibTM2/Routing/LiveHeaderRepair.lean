module

public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderRepairGenerated
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

theorem liveHeaderRepair_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (hsrc : S.R (repairLiveHeaderRaw repairHost.src) = l.flatten) :
    ∃ (v' : HS repairLiveHeaderT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ liveHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lrow Lwidth w S ∧
      Exec headerBody (liveHeaderRepairProgram hQ hA) (mk v S) steps
        (mk v' { S with R := Function.update S.R (repairLiveHeaderRaw repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let G : Stacks repairLiveHeaderT (prime + K) := { S with R := repairHeaderPairBank (T := repairLiveHeaderT) (A := prime + K) p₀ X rb R B repairLiveHeaderBank S.R }
  let C := embStk sharedHeaderCore G
  have hheaders (c : Fin 2) (k : Fin 5) : S.R (repairLiveHeaderBank c (.exchange (.base (.header k)))) = [] := by
    simpa only [repairLiveHeaderBank_header, List.map_nil] using data.headers c k
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := embeddedRepairHeaders_exec liveDescriptorCore liveDescriptorCore_injective
    headerBody p₀ X rb R B wb Lrow Lwidth hRfit hR hwidthFit data.block_lt (by omega) v S
    data.widths hrowInput hwidthInput data.block hheaders hwork
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := liveHeaderRepairGenerated_exec ρ n m X rb scale active s
    body liveBody hlive w hQ hA hscale hn hR hB hrb hs (embDn sharedHeaderCore v₁) S
    data hready hempty hL hblank hdesc l hl hlen hsrc
  obtain ⟨v₃, hu₃, he₃⟩ := exec_emb_stream sharedHeaderCore sharedHeaderCore_injective id liveBody headerBody hheader
    (liveRepairProgram hQ hA) v₁ G v₂ m₂ (liveDescriptorCore repairHost.src)
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten he₂
  obtain ⟨v₄, hu₄, he₄⟩ := embeddedRepairHeadersClean_exec liveDescriptorCore liveDescriptorCore_injective
    headerBody p₀ X rb R B v₃ S (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten
    (by
      intro c k
      change S.R (repairLiveHeaderRaw (repairRoutingConfig (.header c k))) = []
      simpa only [List.map_nil] using data.headers c k)
  rw [embDn_user] at hu₂
  refine ⟨v₄, m₁ + (m₂ + repairHeaderErasePrice p₀ X rb R B), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_⟩
  · have hc₁ : (m₁ : ℝ) ≤ (2 * (14 * ((p₀).wc + (p₀).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) :=
      Nat.cast_le.mpr hm₁
    unfold liveHeaderRepairPrice
    change _ ≤ _ + liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C + _
    simp only [Nat.cast_add]
    simpa only [add_assoc] using add_le_add hc₁ (add_le_add hm₂ (le_refl (repairHeaderErasePrice p₀ X rb R B : ℝ)))
  · dsimp only [G] at he₃
    exact Exec.seq he₁ (Exec.seq he₃ he₄)

end
end IntegerMultBounds.MathlibTM2.Routing
