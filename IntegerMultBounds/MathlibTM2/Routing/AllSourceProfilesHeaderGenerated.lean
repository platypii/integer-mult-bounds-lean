module

public import IntegerMultBounds.MathlibTM2.Routing.InactiveProfileHeaderFrame
public import IntegerMultBounds.MathlibTM2.Routing.SourceRecordProfilesRepair

/-! Execute eleven-profile generation and repair on an actually generated
header bank. All input contracts follow from the original header-free bank. -/

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

theorem allSourceProfilesHeaderGenerated_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (keySrc activity : Fin repairT) (hsa : keySrc ≠ activity)
    (hkeyHeader : ∀ c k, keySrc ≠ repairRoutingConfig (.header c k))
    (hactivityHeader : ∀ c k, activity ≠ repairRoutingConfig (.header c k))
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hwidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hkfit : (p₀).K < 2 ^ w.strideBits) (hnfit : n < 2 ^ w.indexBits)
    (hwfit : (p₀).wy + 2 * (p₀).wc + X < 2 ^ w.coordinateBits)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T₀ Q (prime + K) U) (S : Stacks T₀ (prime + K))
    (data : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B
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
    (D : Stacks inactiveProfileHeaderT (prime + K)) (hproject : embStk sharedHeaderCore D = S) :
    let H : Stacks inactiveProfileHeaderT (prime + K) := { D with R := repairHeaderPairBank p₀ X rb R B inactiveProfileHeaderBank D.R }
    let C₀ := embStk sharedHeaderCore H
    let G : Stacks T₀ (prime + K) := { C₀ with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w C₀.R repairAllSourceProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS T₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ ((liveSelectedProfilesCost p₀ w + repairControlProfilesCost p₀ w w.indexBits + (n * (6 * w.indexBits + 6 * w.coordinateBits + 19) + 2 * (n * (w.indexBits + w.coordinateBits + 5)) + 4 * n + 8)) : ℕ) +
        liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C +
        (9 * (2 * (n * (w.selectorBits + 3)) + 2) + 2 * (2 * ((p₀).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ) ∧
      Exec outerBody (.seq (repairSourceRecordProfilesProgram keySrc activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs))))
        (mk v C₀) steps
        (mk v' { C₀ with R := Function.update C₀.R (e₀ (liveDescriptorCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let H : Stacks inactiveProfileHeaderT (prime + K) := { D with R := repairHeaderPairBank p₀ X rb R B inactiveProfileHeaderBank D.R }
  let C₀ := embStk sharedHeaderCore H
  have hread (i : Fin T₀) : D.R (sharedHeaderCore i) = S.R i := congrArg (fun C => C.R i) hproject
  have hraw (i : Fin repairT) (hi : ∀ c k, i ≠ repairRoutingConfig (.header c k)) :
      C₀.R (e₀ (liveDescriptorCore i)) = S.R (e₀ (liveDescriptorCore i)) :=
    (inactiveProfileHeaderPair_raw_keep p₀ X rb R B D.R i hi).trans (hread _)
  have haux (r : LiveDescriptorRole 11) : C₀.R (e₀ (liveDescriptorAux r)) = S.R (e₀ (liveDescriptorAux r)) := by
    dsimp only [C₀, H, embStk, Function.comp_apply]
    exact (inactiveProfileHeaderPair_liveAux p₀ X rb R B D.R r).trans (hread _)
  have houterAux (i : Fin 7) : C₀.R (liveInactiveProfileAux i) = S.R (liveInactiveProfileAux i) := by
    dsimp only [C₀, H, embStk, Function.comp_apply]
    exact (inactiveProfileHeaderPair_outerAux p₀ X rb R B D.R i).trans (hread _)
  have hd : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B (fun _ _ => [])
      (fun i => D.R (inactiveProfileHeaderRaw i)) := by
    apply data.congr p₀ X rb
    intro key
    exact hread _
  apply sourceRecordProfilesRepair_exec ρ n m X rb scale active s body liveBody hlive outerBody houter keySrc activity hsa w hwidth hwidthFit hkfit hnfit hwfit
    hQ hA hscale hn hR hB hrb hs v C₀
  · exact hd.embeddedHeaders inactiveProfileRaw inactiveProfileRaw_injective p₀ X rb R B
  · intro key
    exact (hraw _ (fun c k => (repairSetup_sources (.inl (.header c k)) key).symm)).trans (hempty key)
  · intro j
    have hp := congrArg (fun C => C.L (e₀ (liveDescriptorCore j))) hproject
    exact hp.trans (hL j)
  · intro j hj
    exact (hraw j (repairBlank_headerSource j hj)).trans (hblank j hj)
  · exact hfit
  · intro r hr
    exact (haux r).trans (hbank r hr)
  · intro d
    exact (hraw _ (fun c k => (repairNonDescriptor_source (.inl (.header c k)) trivial d).symm)).trans (hdesc d)
  · intro j
    exact (haux (.input j)).trans (hinput j)
  · exact (hraw keySrc hkeyHeader).trans hkey
  · exact (hraw activity hactivityHeader).trans hactivity
  · exact (houterAux 0).trans hcount
  · intro i hi
    exact (houterAux i).trans (hscratch i hi)
  · exact hl
  · exact hlen
  · exact (hraw repairHost.src (fun c k => (repairSetup_source_src (.inl (.header c k))).symm)).trans hsrc

end
end IntegerMultBounds.MathlibTM2.Routing
