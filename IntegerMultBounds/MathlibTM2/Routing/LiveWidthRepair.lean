module

public import IntegerMultBounds.MathlibTM2.Routing.LiveWidthRepairGenerated
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Generate row/key-mask fields, execute generated-header live repair and erase
the generated fields. Every phase is charged and only the stream changes. -/

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

theorem liveWidthRepair_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (headerBody : P → Pr P repairLiveHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (liveBody f))
    (outerBody : P → Pr P liveHeaderConfigurationT Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg (fieldCore (N := repairLiveHeaderT)) id (headerBody f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (w : LiveDescriptorWidths)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS liveHeaderConfigurationT Q (prime + K) U) (S : Stacks liveHeaderConfigurationT (prime + K))
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
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm (p₀).wy)
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R (fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R (fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .keyMask)))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (fieldCore (repairLiveHeaderRaw repairHost.src)) = l.flatten) :
    let W : Stacks liveHeaderConfigurationT (prime + K) := { S with R := liveHeaderWidthBank rb (p₀).wy S.R }
    let C := embStk (fieldCore (N := repairLiveHeaderT)) W
    ∃ (v' : HS liveHeaderConfigurationT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (((Lr * (4 * rb + 11) + 8 * rb + 12) +
        (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) : ℝ) +
        liveHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lrow Lwidth w C +
        (2 * rb + 2 * (p₀).wy + 5 : ℕ) ∧
      Exec outerBody (.seq (binaryFieldBatch (liveHeaderWidthJobs Lr Lm rb (p₀).wy))
        (.seq (embProg (fieldCore (N := repairLiveHeaderT)) id (liveHeaderRepairProgram hQ hA))
          (metadataClean [fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .row))),
            fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .keyMask)))])))
        (mk v S) steps
        (mk v' { S with R := Function.update S.R (fieldCore (repairLiveHeaderRaw repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let W : Stacks liveHeaderConfigurationT (prime + K) := { S with R := liveHeaderWidthBank rb (p₀).wy S.R }
  let C := embStk (fieldCore (N := repairLiveHeaderT)) W
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := liveHeaderWidths_exec outerBody Lr Lm rb (p₀).wy
    hr hm v S hrowWidth hmaskWidth hwidthScratch hrow hmask
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := liveWidthRepairGenerated_exec ρ n m X rb scale active s
    body liveBody hlive headerBody hheader w hQ hA hscale hn hR hB hrb hs
    (embDn (fieldCore (N := repairLiveHeaderT)) v₁) S data hready hempty hL hblank hdesc
    Lrow Lwidth hRfit hwidthFit hrowInput hwidthInput hwork l hl hlen hsrc
  obtain ⟨v₃, hu₃, hx₃⟩ := exec_emb_stream (fieldCore (N := repairLiveHeaderT)) fieldCore_injective
    id headerBody outerBody houter (liveHeaderRepairProgram hQ hA) v₁ W v₂ m₂
    (repairLiveHeaderRaw repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hx₂
  obtain ⟨v₄, hu₄, hx₄⟩ := fieldPairClean_exec outerBody
    (repairLiveHeaderRaw (repairSetupSource (.inr .row)))
    (repairLiveHeaderRaw (repairSetupSource (.inr .keyMask))) (repairLiveHeaderRaw repairHost.src)
    (repairLiveHeaderRaw_injective.ne (by simp [repairSetupSource]))
    (repairLiveHeaderRaw_injective.ne (repairSetup_source_src (.inr .row)))
    (repairLiveHeaderRaw_injective.ne (repairSetup_source_src (.inr .keyMask)))
    rb (p₀).wy v₃ S (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hrow hmask
  rw [embDn_user] at hu₂
  refine ⟨v₄, m₁ + (m₂ + (2 * rb + 2 * (p₀).wy + 5)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_⟩
  · have hc₁ : (m₁ : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) +
        (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) := Nat.cast_le.mpr hm₁
    simp only [Nat.cast_add]
    simpa only [Nat.cast_add, add_assoc] using add_le_add hc₁
      (add_le_add hm₂ (le_refl ((2 * rb + 2 * (p₀).wy + 5 : ℕ) : ℝ)))
  · exact Exec.seq hx₁ (Exec.seq hx₃ hx₄)

end
end IntegerMultBounds.MathlibTM2.Routing
