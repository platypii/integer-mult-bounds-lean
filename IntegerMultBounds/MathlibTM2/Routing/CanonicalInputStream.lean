module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalGeneratedInput

/-! Canonical bank extensions transport a change of live records without
changing any scalar operands or profile metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

theorem finAddCases_update {N M : ℕ} {α : Type*} (core : Fin N → α) (aux : Fin M → α)
    (str : Fin N) (replacement : α) :
    Fin.addCases (motive := fun _ => α) (Function.update core str replacement) aux =
      Function.update (Fin.addCases (motive := fun _ => α) core aux) (Fin.castAdd M str) replacement := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.addCases_left]
    by_cases hi : i = str
    · subst i; simp only [Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne ((Fin.castAdd_injective N M).ne hi), Fin.addCases_left]
  · rw [Fin.addCases_right, Function.update_of_ne, Fin.addCases_right]
    intro he
    have hv := congrArg (fun q : Fin (N + M) => q.val) he
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    have := str.isLt
    omega

variable {A : ℕ}

theorem canonicalRepairInput_updateStream (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records replacement : List (Fin (A + 4))) :
    canonicalRepairInput p X rb wb wm wp wk R B replacement =
      Function.update (canonicalRepairInput p X rb wb wm wp wk R B records) repairHost.src replacement := by
  funext j
  by_cases hj : j = repairHost.src
  · subst j
    rw [canonicalRepairInput_stream, Function.update_self]
  · rw [Function.update_of_ne hj]
    by_cases hs : ∃ key, repairSetupSource key = j
    · obtain ⟨key, rfl⟩ := hs
      rw [canonicalRepairInput_source, canonicalRepairInput_source]
    · have hoff : ∀ key, repairSetupSource key ≠ j := fun key he => hs ⟨key, he⟩
      rw [canonicalRepairInput_off _ _ _ _ _ _ _ _ _ _ _ hoff,
        canonicalRepairInput_off _ _ _ _ _ _ _ _ _ _ _ hoff]
      simp only [ite_eq_right hj]

theorem canonicalProfileCoreBank_updateStream (p : Par) (X rb wb wm wp wk R B : ℕ)
    (records replacement coordinates : List (Fin (A + 4))) :
    canonicalProfileCoreBank p X rb wb wm wp wk R B replacement coordinates =
      Function.update (canonicalProfileCoreBank p X rb wb wm wp wk R B records coordinates) repairHost.src replacement := by
  unfold canonicalProfileCoreBank
  rw [canonicalRepairInput_updateStream p X rb wb wm wp wk R B records replacement]
  have hne : repairHost.src ≠ canonicalProfileKey := by
    simp [canonicalProfileKey, repairKey, repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole]
  exact Function.update_comm (β := fun _ : Fin repairT => List (Fin (A + 4))) hne replacement coordinates _

theorem canonicalHeaderInputBank_updateStream {N : ℕ} (core : Fin N → List (Fin (A + 4)))
    (Lrow Lwidth R wc : ℕ) (str : Fin N) (replacement : List (Fin (A + 4))) :
    canonicalHeaderInputBank (Function.update core str replacement) Lrow Lwidth R wc =
      Function.update (canonicalHeaderInputBank core Lrow Lwidth R wc) (sharedHeaderCore str) replacement :=
  finAddCases_update core (fun i => canonicalHeaderOperands Lrow Lwidth R wc ((Fintype.equivFin HeaderWorkRole).symm i)) str replacement

theorem canonicalWidthInputBank_updateStream {N : ℕ} (core : Fin N → List (Fin (A + 4)))
    (Lr Lm rb wy : ℕ) (str : Fin N) (replacement : List (Fin (A + 4))) :
    canonicalWidthInputBank (Function.update core str replacement) Lr Lm rb wy =
      Function.update (canonicalWidthInputBank core Lr Lm rb wy) (fieldCore str) replacement :=
  finAddCases_update core (fun i : Fin 6 => if i = 0 then binSyms Lr rb else if i = 1 then binSyms Lm wy else []) str replacement

theorem canonicalClassifierInputBank_updateStream {N : ℕ} (core : Fin N → List (Fin (A + 4)))
    (p : Par) (LK Ln Lo Lt : ℕ) (str : Fin N) (replacement : List (Fin (A + 4))) :
    canonicalClassifierInputBank (Function.update core str replacement) p LK Ln Lo Lt =
      Function.update (canonicalClassifierInputBank core p LK Ln Lo Lt) (classifierCore str) replacement :=
  finAddCases_update _ _ _ _

theorem canonicalLiveInputBank_updateStream (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (source : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (core : Fin repairT → List (Fin (A + 4))) (str : Fin repairT) (replacement : List (Fin (A + 4))) :
    canonicalLiveInputBank p X hG hK active source w (Function.update core str replacement) =
      Function.update (canonicalLiveInputBank p X hG hK active source w core)
        (liveInactiveProfileCore (liveDescriptorCore str)) replacement := by
  unfold canonicalLiveInputBank liveDescriptorBank
  rw [finAddCases_update, finAddCases_update]
  rfl

theorem canonicalGeneratedInput_bank_updateStream {Q K : ℕ} (p : Par) (a : CanonicalStageArithmetic p)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (hsource : ∀ q ∈ targets, source q ∉ targets)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p 0)) (hw : p.wc ≤ H) (reservoir : Fin 3)
    (l l' : List (List (Fin (prime + K + 4))))
    (hl : l.length = a.R * 2 ^ fieldsLen (selectiveLen p 0))
    (hl' : l'.length = a.R * 2 ^ fieldsLen (selectiveLen p 0))
    (hlen : ∀ r ∈ l, r.length = a.B ∧ ∀ x ∈ r, x.val < 8)
    (hlen' : ∀ r ∈ l', r.length = a.B ∧ ∀ x ∈ r, x.val < 8) :
    (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l' hl' hlen').M.R =
      Function.update (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen).M.R
        (inactiveClassifierPlacementEmbed (t₀ := 6) (classifierCore (inactiveConfigurationCore repairHost.src))) l'.flatten := by
  dsimp only [canonicalGeneratedInput, canonicalPlacementInputStack, canonicalClassifierInputStack,
    canonicalWidthInputStack, canonicalHeaderInputStack]
  rw [canonicalProfileCoreBank_updateStream p 0 a.rb a.wb a.wm a.wp a.wk a.R a.B l.flatten l'.flatten,
    canonicalLiveInputBank_updateStream, canonicalHeaderInputBank_updateStream,
    canonicalWidthInputBank_updateStream, canonicalClassifierInputBank_updateStream]
  dsimp only [inactiveConfigurationCore, inactiveProfileHeaderRaw, embeddedRepairHeaderRaw, inactiveProfileRaw]
  rw [sharedScheduleInputBank_updateStream]
  rfl

theorem canonicalGeneratedInput_stack_updateStream {Q K : ℕ} (p : Par) (a : CanonicalStageArithmetic p)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (hsource : ∀ q ∈ targets, source q ∉ targets)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p 0)) (hw : p.wc ≤ H) (reservoir : Fin 3)
    (l l' : List (List (Fin (prime + K + 4))))
    (hl : l.length = a.R * 2 ^ fieldsLen (selectiveLen p 0))
    (hl' : l'.length = a.R * 2 ^ fieldsLen (selectiveLen p 0))
    (hlen : ∀ r ∈ l, r.length = a.B ∧ ∀ x ∈ r, x.val < 8)
    (hlen' : ∀ r ∈ l', r.length = a.B ∧ ∀ x ∈ r, x.val < 8) :
    (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l' hl' hlen').M =
      { (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen).M with R := Function.update (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen).M.R (inactiveClassifierPlacementEmbed (t₀ := 6) (classifierCore (inactiveConfigurationCore repairHost.src))) l'.flatten } := by
  apply Stacks.ext
  · dsimp only [canonicalGeneratedInput, canonicalPlacementInputStack, canonicalClassifierInputStack, canonicalWidthInputStack, canonicalHeaderInputStack]
  · dsimp only [canonicalGeneratedInput, canonicalPlacementInputStack, canonicalClassifierInputStack, canonicalWidthInputStack, canonicalHeaderInputStack]
  · dsimp only [canonicalGeneratedInput, canonicalPlacementInputStack, canonicalClassifierInputStack, canonicalWidthInputStack, canonicalHeaderInputStack]
  · exact canonicalGeneratedInput_bank_updateStream p a targets source hsource hQ hA H hplacementFit hw reservoir l l' hl hl' hlen hlen'

theorem canonicalGeneratedInput_configuration_updateStream {Q K : ℕ} (p : Par) (a : CanonicalStageArithmetic p)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (hsource : ∀ q ∈ targets, source q ∉ targets)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p 0)) (hw : p.wc ≤ H) (reservoir : Fin 3)
    (l l' : List (List (Fin (prime + K + 4))))
    (hl : l.length = a.R * 2 ^ fieldsLen (selectiveLen p 0))
    (hl' : l'.length = a.R * 2 ^ fieldsLen (selectiveLen p 0))
    (hlen : ∀ r ∈ l, r.length = a.B ∧ ∀ x ∈ r, x.val < 8)
    (hlen' : ∀ r ∈ l', r.length = a.B ∧ ∀ x ∈ r, x.val < 8) :
    (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l' hl' hlen').E =
      { (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen).E with R := Function.update (canonicalGeneratedInput p a targets source hsource hQ hA H hplacementFit hw reservoir l hl hlen).E.R (inactiveConfigurationCore repairHost.src) l'.flatten } := by
  dsimp only [canonicalGeneratedInput, canonicalWidthInputStack, canonicalHeaderInputStack]
  rw [canonicalProfileCoreBank_updateStream p 0 a.rb a.wb a.wm a.wp a.wk a.R a.B l.flatten l'.flatten,
    canonicalLiveInputBank_updateStream, canonicalHeaderInputBank_updateStream, canonicalWidthInputBank_updateStream]
  rfl

end
end IntegerMultBounds.MathlibTM2.Routing
