module

public import IntegerMultBounds.MathlibTM2.Routing.LiveSourceBases
public import IntegerMultBounds.MathlibTM2.Routing.LiveSelectedKeySourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairXSourceGenerate

/-! Generate the key profile in the existing shared bank. Region bases are
generated from live dimensions and cleared; all borrowed tapes are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def livePreparedKeySourceProgram (src : Fin repairT) : Pr P T₀ Q A U :=
  .seq liveSourceBasesProgram (.seq (liveSelectedKeySourceProgram src) liveSourceBasesCleanProgram)

theorem livePreparedKeySourceGenerate_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (src : Fin repairT) (hwidth : w.selectorBits = w.coordinateBits)
    (hwidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hk : p.K < 2 ^ w.strideBits) (hn : p.n < 2 ^ w.indexBits)
    (hw : p.wy + 2 * p.wc + X < 2 ^ w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hraw : S.R (liveZSourceActivity src) = gatedSelectedSourceWords w.indexBits w.strideBits
      (List.ofFn (fun c => (s c).gatedChoice (active c))))
    (hinput : S.R (e₀ (liveDescriptorAux (.input 0))) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ p.n * gatedSelectedSourceIterationCost w.widthBits w.indexBits w.strideBits +
        2 * (p.n * (w.indexBits + w.coordinateBits + 5)) + 2 * (p.n * (w.coordinateBits + 3)) + 6 +
        (w.indexBits * (12 * w.coordinateBits + 20) + 48 * w.coordinateBits + 56) ∧
      Exec body (livePreparedKeySourceProgram src) (mk v S) steps
        (mk v' { S with R := Function.update S.R (e₀ (liveDescriptorAux (.input 0))) ((repairLiveMode 0).profileFrames p X hG hK active s w.selectorBits) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := liveSourceBases_exec body p X hG hK active s w hn hk
    (by omega) v S hbank hcount (hscratch 5 (by decide)) (hscratch 6 (by decide))
  let G : Stacks T₀ A := { S with R := liveSourceBasesBank S.R p w }
  have hcore (i : Fin (liveDescriptorT repairT 11)) : G.R (e₀ i) = S.R (e₀ i) :=
    liveSourceBasesBank_core S.R p w i
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := liveSelectedKeySourceGenerate_exec body p X hG hK active s w src
    hwidth hwidthFit hk hn.le hw v₁ G
    (fun r hr => (hcore _).trans (hbank r hr))
    (by simpa only [liveZSourceActivity] using (hcore (liveDescriptorCore src)).trans hraw)
    ((hcore _).trans hinput)
    (by
      intro i hi h5 h6
      simpa [G, liveSourceBasesBank, liveInactiveProfileAux_injective.eq_iff, hi, h5, h6] using hscratch i hi)
    (by simp [G, liveSourceBasesBank, liveInactiveProfileAux_injective.eq_iff])
    (by simp [G, liveSourceBasesBank])
  let word := (repairLiveMode 0).profileFrames (A := A) p X hG hK active s w.selectorBits
  let R := Function.update S.R (e₀ (liveDescriptorAux (.input 0))) word
  let H : Stacks T₀ A := { S with R := Function.update G.R (e₀ (liveDescriptorAux (.input 0))) word }
  have hH : H.R = liveSourceBasesBank R p w :=
    liveSourceBasesBank_update S.R p w (liveDescriptorAux (.input 0)) word
  obtain ⟨v₃, hu₃, hx₃⟩ := liveSourceBasesClean_exec body R p w
    (by simp [R, liveInactiveProfileAux_core, hscratch 5 (by decide)])
    (by simp [R, liveInactiveProfileAux_core, hscratch 6 (by decide)]) v₂ H hH
  exact ⟨v₃, m₁ + (m₂ + (4 * w.coordinateBits + 4)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end
end IntegerMultBounds.MathlibTM2.Routing
