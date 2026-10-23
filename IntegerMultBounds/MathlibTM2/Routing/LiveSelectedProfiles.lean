module

public import IntegerMultBounds.MathlibTM2.Routing.LivePreparedKeySourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LivePreparedXSourceGenerate

/-! Generate both selected-source profiles from raw local-coordinate records.
Each phase includes region-base setup and cleanup; all non-output tapes restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveSelectedProfilesProgram (keySrc xSrc : Fin repairT) : Pr P T₀ Q A U :=
  .seq (livePreparedKeySourceProgram keySrc) (livePreparedXSourceProgram xSrc)

def liveSelectedProfilesCost (p : Par) (w : LiveDescriptorWidths) :=
  (p.n * gatedSelectedSourceIterationCost w.widthBits w.indexBits w.strideBits +
    2 * (p.n * (w.indexBits + w.coordinateBits + 5)) + 2 * (p.n * (w.coordinateBits + 3)) + 6 +
    (w.indexBits * (12 * w.coordinateBits + 20) + 48 * w.coordinateBits + 56)) +
  (p.n * selectedSourceIterationCost w.indexBits w.strideBits +
    2 * (p.n * (w.indexBits + w.coordinateBits + 4)) + 2 * (p.n * (w.coordinateBits + 3)) + 6 +
    (w.indexBits * (12 * w.coordinateBits + 20) + 48 * w.coordinateBits + 56))

theorem liveSelectedProfiles_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (keySrc xSrc : Fin repairT) (hwidth : w.selectorBits = w.coordinateBits)
    (hwidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hk : p.K < 2 ^ w.strideBits) (hn : p.n < 2 ^ w.indexBits)
    (hw : p.wy + 2 * p.wc + X < 2 ^ w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hkey : S.R (liveZSourceActivity keySrc) = gatedSelectedSourceWords w.indexBits w.strideBits
      (List.ofFn (fun c => (s c).gatedChoice (active c))))
    (hxraw : S.R (liveZSourceActivity xSrc) = selectedSourceWords w.indexBits w.strideBits
      (List.ofFn (fun c => (s c).choice)))
    (hkeyOutput : S.R (e₀ (liveDescriptorAux (.input 0))) = [])
    (hxOutput : S.R (e₀ (liveDescriptorAux (.input 9))) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ liveSelectedProfilesCost p w ∧
      Exec body (liveSelectedProfilesProgram keySrc xSrc) (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R [0, 9] }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := livePreparedKeySourceGenerate_exec body p X hG hK active s w
    keySrc hwidth hwidthFit hk hn hw v S hbank hkey hkeyOutput hcount hscratch
  let G : Stacks T₀ A := { S with R := Function.update S.R (e₀ (liveDescriptorAux (.input 0))) ((repairLiveMode 0).profileFrames p X hG hK active s w.selectorBits) }
  have hkeep (i : Fin T₀) (hi : i ≠ e₀ (liveDescriptorAux (.input 0))) : G.R i = S.R i := by
    simp [G, hi]
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := livePreparedXSourceGenerate_exec body p X hG hK active s w
    xSrc hwidth hk hn hw v₁ G
    (by
      intro r hr
      rw [hkeep _ (liveInactiveProfileCore_injective.ne (liveDescriptorAux_injective.ne (hr 0)))]
      exact hbank r hr)
    ((hkeep _ (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux xSrc (.input 0)))).trans hxraw)
    ((hkeep _ (liveInactiveProfileCore_injective.ne (liveDescriptorAux_injective.ne (by decide)))).trans hxOutput)
    ((hkeep _ (liveInactiveProfileAux_core _ _)).trans hcount)
    (fun i hi => (hkeep _ (liveInactiveProfileAux_core _ _)).trans (hscratch i hi))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, Nat.add_le_add hm₁ hm₂, ?_⟩
  simp only [liveInactiveProfileBatchBank, liveInactiveProfileBank]
  exact Exec.seq hx₁ hx₂

theorem liveSelectedProfiles_ready
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (R : Fin T₀ → List (Fin (A + 4)))
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ ([0, 9] : List (Fin 11)), r ≠ .input j) →
      R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R [0, 9] (e₀ i)) :=
  liveInactiveProfileBatch_ready p X hG hK active s repairLiveMode w R [0, 9]
    (by decide) hfit hbank

end
end IntegerMultBounds.MathlibTM2.Routing
