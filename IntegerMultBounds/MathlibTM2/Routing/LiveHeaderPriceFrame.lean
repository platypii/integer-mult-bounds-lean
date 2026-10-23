module

public import IntegerMultBounds.MathlibTM2.Routing.LiveRepairPriceFrame

/-! Header generation and live-profile repair retain their price when the record
stream is permuted. All numerical generation terms are independent of tape data. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T A K : ℕ}

theorem elementaryHeaderBank_update (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryHeaderReg → Fin T) (words : Fin 5 → List Bool)
    (str : Fin T) (out : List (Fin (A + 4))) (hstr : ∀ k, str ≠ rg (.header k)) :
    elementaryHeaderBank (Function.update R str out) rg words =
      Function.update (elementaryHeaderBank R rg words) str out := by
  funext j
  by_cases hj : j = str
  · subst j
    simp [elementaryHeaderBank, hstr]
  · simp [elementaryHeaderBank, Function.update_apply, hj]

theorem repairHeaderPairBank_update (p : Par) (X rb R B : ℕ)
    (bank : Fin 2 → RepairHeaderReg → Fin T) (tapes : Fin T → List (Fin (A + 4)))
    (str : Fin T) (out : List (Fin (A + 4)))
    (hstr : ∀ c k, str ≠ bank c (.exchange (.base (.header k)))) :
    repairHeaderPairBank p X rb R B bank (Function.update tapes str out) =
      Function.update (repairHeaderPairBank p X rb R B bank tapes) str out := by
  unfold repairHeaderPairBank
  rw [elementaryHeaderBank_update _ _ _ str out (hstr 0),
    elementaryHeaderBank_update _ _ _ str out (hstr 1)]

noncomputable section
variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem liveHeaderRepairPrice_updateStream (scale wb wm wp wk R B Lrow Lwidth : ℕ)
    (w : LiveDescriptorWidths) (S : Stacks repairLiveHeaderT (prime + K))
    (out : List (Fin (prime + K + 4)))
    (hblank : ∀ j, RepairBlank j → S.R (repairLiveHeaderRaw j) = []) :
    liveHeaderRepairPrice p X rb hG hK active s scale wb wm wp wk R B Lrow Lwidth w
        { S with R := Function.update S.R (repairLiveHeaderRaw repairHost.src) out } =
      liveHeaderRepairPrice p X rb hG hK active s scale wb wm wp wk R B Lrow Lwidth w S := by
  have hstr : ∀ c k, repairLiveHeaderRaw repairHost.src ≠
      repairLiveHeaderBank c (.exchange (.base (.header k))) := by
    intro c k
    rw [repairLiveHeaderBank_header]
    apply sharedHeaderCore_injective.ne
    apply liveDescriptorCore_injective.ne
    exact (repairSetup_source_src (.inl (.header c k))).symm
  have hgen := repairHeaderPairBank_update p X rb R B repairLiveHeaderBank S.R
    (repairLiveHeaderRaw repairHost.src) out hstr
  let G : Stacks repairLiveHeaderT (prime + K) := { S with R := repairHeaderPairBank p X rb R B repairLiveHeaderBank S.R }
  have hb : ∀ j, RepairBlank j → (embStk sharedHeaderCore G).R (liveDescriptorCore j) = [] := by
    intro j hj
    exact (repairLiveHeaderPair_blank p X rb R B S.R j hj).trans (hblank j hj)
  rw [liveHeaderRepairPrice, liveHeaderRepairPrice]
  dsimp only
  rw [hgen]
  change (_ : ℝ) + liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w
    (embStk sharedHeaderCore { G with R := Function.update G.R (sharedHeaderCore (liveDescriptorCore repairHost.src)) out }) + _ = _
  rw [embStk_update_stream sharedHeaderCore sharedHeaderCore_injective,
    liveRepairPrice_updateStream p X rb hG hK active s scale wb wm wp wk R B w _ out hb]

end
end IntegerMultBounds.MathlibTM2.Routing
