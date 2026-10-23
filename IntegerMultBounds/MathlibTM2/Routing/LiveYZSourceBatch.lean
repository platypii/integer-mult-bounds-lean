module

public import IntegerMultBounds.MathlibTM2.Routing.LiveYZTargetSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LiveYZControlSourceCompile
public import IntegerMultBounds.MathlibTM2.Routing.LiveProfileBatchFrame

/-! Generate both YZ profiles in the shared live bank. The activity word,
binary count and all arithmetic/offset workspace are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section
variable {Q A : ℕ} {P U : Type}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveYZSourceBatchProgram (activity : Fin repairT) : Pr P T₀ Q A U :=
  .seq liveYZTargetSourceProgram (liveYZControlSourceCompileProgram activity)

def liveYZSourceBatchCost (Lc : ℕ) :=
  binaryAffineSourceGenerateCost Lc w.indexBits w.strideBits p.n +
    ((8 * w.coordinateBits + 8) +
      (p.n * optionalAffineSourceIterationCost w.widthBits w.indexBits w.strideBits + 2 * p.n +
        2 * (p.n * (w.indexBits + w.strideBits + 3)) + 16 * w.indexBits + 22) +
      (2 * w.coordinateBits + 2))

theorem liveYZSourceBatch_exec (body : P → Pr P T₀ Q A U) (activity : Fin repairT)
    (Lc : ℕ) (hn : p.n < 2 ^ Lc) (hwidth : w.selectorBits = w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (htarget : S.R liveYZTargetSourceDst = []) (hcontrol : S.R liveYZControlSourceDst = [])
    (hactivity : S.R (liveZSourceActivity activity) = (List.ofFn active).map bitSymbol)
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ liveYZSourceBatchCost p w Lc ∧
      Exec body (liveYZSourceBatchProgram activity) (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R [7, 8] }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := liveYZTargetSourceGenerate_exec p X hG hK active s w body Lc hn
    hwidth v S hfit hbank htarget hcount hscratch
  let G : Stacks T₀ A := { S with R := Function.update S.R liveYZTargetSourceDst ((repairLiveMode 7).profileFrames p X hG hK active s w.selectorBits) }
  have hkeep (r : LiveDescriptorRole 11) (hr : r ≠ .input 7) :
      G.R (e₀ (liveDescriptorAux r)) = S.R (e₀ (liveDescriptorAux r)) := by
    dsimp only [G]
    exact Function.update_of_ne (liveInactiveProfileCore_injective.ne (liveDescriptorAux_injective.ne hr)) _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := liveYZControlSourceCompile_exec body p X hG hK active s w activity
    hwidth v₁ G hfit (fun r hr => (hkeep r (hr 7)).trans (hbank r hr))
    ((hkeep (.input 8) (by simp)).trans hcontrol)
    (by
      dsimp only [G, liveZSourceActivity, liveYZTargetSourceDst]
      rw [Function.update_of_ne (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux activity _))]
      exact hactivity)
    (by
      intro i hi
      dsimp only [G, liveYZTargetSourceDst]
      rw [Function.update_of_ne (liveInactiveProfileAux_core _ _)]
      exact hscratch i hi)
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, Nat.add_le_add hm₁ hm₂, ?_⟩
  dsimp only [G] at hx₂
  exact Exec.seq hx₁ hx₂

end
end IntegerMultBounds.MathlibTM2.Routing
