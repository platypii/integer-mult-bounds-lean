module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedInputSemantics
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! The coordinate-source tape in the complete placed core is exactly the tape
filled by matching-table production. All intervening embeddings preserve its word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K : ℕ} {P P' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "ep₀" => inactiveClassifierPlacementEmbed (t₀ := t₀)

theorem GeneratedPlacedInput.rawWord (input : GeneratedPlacedInput t₀ Q K P P' U) (j : Fin repairT) :
    input.M.R (ep₀ (classifierCore (inactiveConfigurationCore j))) = input.S.R (inactiveProfileRaw j) := by
  have h₁ := congrArg (fun S => S.R (classifierCore (inactiveConfigurationCore j))) input.houterProject
  have h₂ := congrArg (fun S => S.R (inactiveConfigurationCore j)) input.hF
  have h₃ := congrArg (fun S => S.R (inactiveProfileHeaderRaw j)) input.hE
  have h₄ := congrArg (fun S => S.R (inactiveProfileRaw j)) input.hproject
  exact h₁.trans (h₂.trans (h₃.trans h₄))

def GeneratedPlacedInput.coordinateRegister (input : GeneratedPlacedInput t₀ Q K P P' U) : Fin TP₀ :=
  ep₀ (classifierCore (inactiveConfigurationCore input.keySrc))

def GeneratedPlacedInput.coordinateWords (input : GeneratedPlacedInput t₀ Q K P P' U) :=
  sourceCoordinateInputWords (A := prime + K) input.w.indexBits input.w.strideBits
    (profileCoordinateInputs input.p input.hK input.targets input.source)

theorem GeneratedPlacedInput.coordinateWord (input : GeneratedPlacedInput t₀ Q K P P' U) :
    input.M.R input.coordinateRegister = input.coordinateWords :=
  (input.rawWord input.keySrc).trans input.hkey

theorem GeneratedPlacedInput.coordinateRegister_ne_stream (input : GeneratedPlacedInput t₀ Q K P P' U) :
    input.coordinateRegister ≠ ep₀ (classifierCore (inactiveConfigurationCore repairHost.src)) := by
  exact inactiveClassifierPlacementEmbed_injective.ne
    (classifierCore_injective.ne (inactiveConfigurationCore_injective.ne input.hkeySrc))

theorem GeneratedPlacedInput.streamWord (input : GeneratedPlacedInput t₀ Q K P P' U) :
    input.M.R (ep₀ (classifierCore (inactiveConfigurationCore repairHost.src))) = input.l.flatten :=
  (input.rawWord repairHost.src).trans input.hsrc

/-- Installing only the produced coordinate stream completes the declared core bank. -/
theorem GeneratedPlacedInput.installCoordinate_bank (input : GeneratedPlacedInput t₀ Q K P P' U)
    {T : ℕ} (e : Fin TP₀ → Fin T) (he : Function.Injective e)
    (S : Stacks T (prime + K))
    (hbank : (embStk e S).R = Function.update input.M.R input.coordinateRegister []) :
    (embStk e { S with R := Function.update S.R (e input.coordinateRegister) input.coordinateWords }).R = input.M.R := by
  rw [embStk_update_stream e he]
  dsimp only
  rw [hbank, Function.update_idem, ← input.coordinateWord, Function.update_eq_self]

end
end IntegerMultBounds.MathlibTM2.Routing
