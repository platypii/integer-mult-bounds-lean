module

public import IntegerMultBounds.MathlibTM2.Routing.AllSourceProfilesWidthGenerated

/-! Generate row/key-mask fields, headers and eleven profiles, execute exact
repair and clean all generated inputs. Only the repaired stream changes. -/

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

theorem allSourceProfilesWidthRepair_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (keySrc activity : Fin repairT) (hsa : keySrc ≠ activity)
    (hkeyHeader : ∀ c k, keySrc ≠ repairRoutingConfig (.header c k))
    (hactivityHeader : ∀ c k, activity ≠ repairRoutingConfig (.header c k))
    (hkeyRow : keySrc ≠ repairSetupSource (.inr .row))
    (hkeyMask : keySrc ≠ repairSetupSource (.inr .keyMask))
    (hactivityRow : activity ≠ repairSetupSource (.inr .row))
    (hactivityMask : activity ≠ repairSetupSource (.inr .keyMask))
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hselectorWidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hkfit : (p₀).K < 2 ^ w.strideBits) (hnfit : n < 2 ^ w.indexBits)
    (hwfit : (p₀).wy + 2 * (p₀).wc + X < 2 ^ w.coordinateBits)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS inactiveProfileConfigurationT Q (prime + K) U) (S : Stacks T₀ (prime + K))
    (data : RepairPendingConfigurationData p₀ X rb wb wm wp wk R B
      (fun _ _ => []) (fun i => S.R (e₀ (liveDescriptorCore i))))
    (hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = [])
    (hfit : ∀ j, LiveDescriptorBounds p₀ X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p₀ X hG₀ hK₀ active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (hinput : ∀ j, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hkey : S.R (liveZSourceActivity keySrc) = gatedSelectedSourceWords w.indexBits w.strideBits
      (List.ofFn (fun c => (s c).gatedChoice (active c))))
    (hactivity : S.R (liveZSourceActivity activity) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten)
    (D : Stacks inactiveProfileHeaderT (prime + K)) (hproject : embStk sharedHeaderCore D = S)
    (headerBody : P → Pr P inactiveProfileHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (outerBody f))
    (Lrow Lwidth : ℕ) (hRfit : R < 2 ^ Lrow) (hwidthFit : (p₀).wc < 2 ^ Lwidth)
    (hrowInput : D.R (sharedHeaderBinary 0) = binSyms Lrow R)
    (hwidthInput : D.R (sharedHeaderBinary 1) = binSyms Lwidth (p₀).wc)
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → D.R (sharedHeaderWork r) = [])
    (E : Stacks inactiveProfileConfigurationT (prime + K)) (hE : embStk (fieldCore (N := inactiveProfileHeaderT)) E = D)
    (widthBody : P → Pr P inactiveProfileConfigurationT Q (prime + K) U)
    (hwidthBody : ∀ f, widthBody f = embProg (fieldCore (N := inactiveProfileHeaderT)) id (headerBody f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (hrowWidth : E.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : E.R (fieldAux 1) = binSyms Lm (p₀).wy)
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → E.R (fieldAux i) = [])
    (hrow : E.R (fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .row)))) = [])
    (hmask : E.R (fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))) = []) :
    let W : Stacks inactiveProfileConfigurationT (prime + K) := { E with R := inactiveProfileWidthBank rb (p₀).wy E.R }
    let D₁ := embStk (fieldCore (N := inactiveProfileHeaderT)) W
    let H : Stacks inactiveProfileHeaderT (prime + K) := { D₁ with R := repairHeaderPairBank p₀ X rb R B inactiveProfileHeaderBank D₁.R }
    let C₀ := embStk sharedHeaderCore H
    let G : Stacks T₀ (prime + K) := { C₀ with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w C₀.R repairAllSourceProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS inactiveProfileConfigurationT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) +
        ((2 * (14 * ((p₀).wc + (p₀).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
        (((liveSelectedProfilesCost p₀ w + repairControlProfilesCost p₀ w w.indexBits + (n * (6 * w.indexBits + 6 * w.coordinateBits + 19) + 2 * (n * (w.indexBits + w.coordinateBits + 5)) + 4 * n + 8)) : ℕ) +
        liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C +
        (9 * (2 * (n * (w.selectorBits + 3)) + 2) + 2 * (2 * ((p₀).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ)) + (repairHeaderErasePrice p₀ X rb R B : ℕ)) + (2 * rb + 2 * (p₀).wy + 5 : ℕ) ∧
      Exec widthBody (.seq (binaryFieldBatch (fieldPairJobs (inactiveProfileHeaderRaw (repairSetupSource (.inr .row)))
          (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask))) Lr Lm rb (p₀).wy))
        (.seq (embProg (fieldCore (N := inactiveProfileHeaderT)) id (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq (repairSourceRecordProfilesProgram keySrc activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw)))))
          (metadataClean [fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .row))),
            fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))])))
        (mk v E) steps
        (mk v' { E with R := Function.update E.R (fieldCore (inactiveProfileHeaderRaw repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let W : Stacks inactiveProfileConfigurationT (prime + K) := { E with R := inactiveProfileWidthBank rb (p₀).wy E.R }
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := embeddedRepairWidths_exec inactiveProfileHeaderRaw inactiveProfileHeaderRaw_injective
    widthBody Lr Lm rb (p₀).wy hr hm v E hrowWidth hmaskWidth hwidthScratch hrow hmask
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := allSourceProfilesWidthGenerated_exec ρ n m X rb scale active s
    body liveBody hlive outerBody houter keySrc activity hsa hkeyHeader hactivityHeader hkeyRow hkeyMask hactivityRow hactivityMask w hwidth hselectorWidthFit hkfit hnfit hwfit hQ hA hscale hn hR hB hrb hs
    (embDn (fieldCore (N := inactiveProfileHeaderT)) v₁) S data hempty hL hblank hfit hbank hdesc hinput hkey hactivity hcount hscratch
    l hl hlen hsrc D hproject headerBody hheader Lrow Lwidth hRfit hwidthFit hrowInput hwidthInput hwork E hE
  obtain ⟨v₃, hu₃, hx₃⟩ := exec_emb_stream (fieldCore (N := inactiveProfileHeaderT)) fieldCore_injective id headerBody widthBody hwidthBody
    _ v₁ W v₂ m₂ (inactiveProfileHeaderRaw repairHost.src)
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hx₂
  obtain ⟨v₄, hu₄, hx₄⟩ := fieldPairClean_exec widthBody
    (inactiveProfileHeaderRaw (repairSetupSource (.inr .row))) (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))
    (inactiveProfileHeaderRaw repairHost.src)
    (inactiveProfileHeaderRaw_injective.ne (by simp [repairSetupSource]))
    (inactiveProfileHeaderRaw_injective.ne (repairSetup_source_src (.inr .row)))
    (inactiveProfileHeaderRaw_injective.ne (repairSetup_source_src (.inr .keyMask)))
    rb (p₀).wy v₃ E (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hrow hmask
  rw [embDn_user] at hu₂
  refine ⟨v₄, m₁ + (m₂ + (2 * rb + 2 * (p₀).wy + 5)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_⟩
  · have hc₁ : (m₁ : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) +
        (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) := Nat.cast_le.mpr hm₁
    simpa only [Nat.cast_add, add_assoc] using add_le_add hc₁
      (add_le_add hm₂ (le_refl ((2 * rb + 2 * (p₀).wy + 5 : ℕ) : ℝ)))
  · dsimp only [W] at hx₃
    exact Exec.seq hx₁ (Exec.seq hx₃ hx₄)

end
end IntegerMultBounds.MathlibTM2.Routing
