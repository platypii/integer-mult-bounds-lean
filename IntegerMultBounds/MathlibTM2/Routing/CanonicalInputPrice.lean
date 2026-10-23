module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalInputStream
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedInputSemantics

/-! Canonical generated repair prices depend on dimensions and metadata,
not the values or order of live records. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

theorem canonicalGeneratedInput_price_records_independent {Q K : ℕ} (p : Par) (a : CanonicalStageArithmetic p)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (hsource : ∀ q ∈ targets, source q ∉ targets)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p 0)) (hw : p.wc ≤ H) (reservoir : Fin 3)
    (l l' : List (List (Fin (prime + K + 4))))
    (hl : l.length = a.R * 2 ^ fieldsLen (selectiveLen p 0))
    (hl' : l'.length = a.R * 2 ^ fieldsLen (selectiveLen p 0))
    (hlen : ∀ r ∈ l, r.length = a.B ∧ ∀ x ∈ r, x.val < 8)
    (hlen' : ∀ r ∈ l', r.length = a.B ∧ ∀ x ∈ r, x.val < 8) :
    (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l' hl' hlen').price = (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen).price := by
  have hblank : ∀ j, RepairBlank j → (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen).E.R (inactiveConfigurationCore j) = [] := by
    intro j hj
    have h := congrArg (fun S => S.R (inactiveProfileRaw j)) (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen).hproject
    have h' := congrArg (fun S => S.R (inactiveProfileHeaderRaw j)) (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen).hE
    dsimp only [embStk, inactiveConfigurationCore, inactiveProfileHeaderRaw, embeddedRepairHeaderRaw] at h h' ⊢
    exact h'.trans (h.trans ((canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen).hblank j hj))
  dsimp only [GeneratedPlacedInput.price]
  rw [canonicalGeneratedInput_stack_updateStream p a targets source hsource hQ hA H hplacementFit hw reservoir l l' hl hl' hlen hlen',
    canonicalGeneratedInput_configuration_updateStream p a targets source hsource hQ hA H hplacementFit hw reservoir l l' hl hl' hlen hlen']
  dsimp only [canonicalGeneratedInput, GeneratedPlacedInput.calls] at hblank ⊢
  apply allSourcePlacedRepairPrice_updateStream
  exact hblank

end
end IntegerMultBounds.MathlibTM2.Routing
