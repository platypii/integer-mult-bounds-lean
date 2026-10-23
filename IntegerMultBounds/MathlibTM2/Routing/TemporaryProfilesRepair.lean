module

public import IntegerMultBounds.MathlibTM2.Routing.TemporaryProfilesRepairGenerated

/-! Generate eight profile inputs, execute live exact repair, then erase
the profiles. Every phase is charged; only the repaired stream changes. -/

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

theorem temporaryProfilesRepair_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (activity : Fin repairT) (Lc : ℕ) (hnfit : n < 2 ^ Lc)
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T₀ Q (prime + K) U) (S : Stacks T₀ (prime + K))
    (data : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (fun i => S.R (e₀ (liveDescriptorCore i))))
    (hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = [])
    (hfit : ∀ j, LiveDescriptorBounds p₀ X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairTemporaryProfileJobs, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p₀ X hG₀ hK₀ active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (hinput : ∀ j ∈ repairTemporaryProfileJobs, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hactivity : S.R (liveZSourceActivity activity) = (List.ofFn active).map bitSymbol)
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten) :
    let G : Stacks T₀ (prime + K) := { S with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w S.R repairTemporaryProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS T₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (repairTemporaryProfilesCost p₀ w Lc : ℕ) +
        liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C +
        (7 * (2 * (n * (w.selectorBits + 3)) + 2) + (2 * ((p₀).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ) ∧
      Exec outerBody (.seq (repairTemporaryProfilesProgram activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairTemporaryProfileJobs))))
        (mk v S) steps
        (mk v' { S with R := Function.update S.R (e₀ (liveDescriptorCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let G : Stacks T₀ (prime + K) := { S with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w S.R repairTemporaryProfileJobs }
  let C := embStk e₀ G
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := repairLiveTemporaryProfiles_exec p₀ X hG₀ hK₀ active s w
    outerBody activity Lc hnfit hwidth v S hfit hbank hinput hactivity hcount hscratch
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := temporaryProfilesRepairGenerated_exec ρ n m X rb scale active s
    body liveBody hlive w hQ hA hscale hn hR hB hrb hs (embDn e₀ v₁) S
    data hempty hL hblank hfit hbank hdesc l hl hlen hsrc
  obtain ⟨v₃, hu₃, hx₃⟩ := exec_emb_stream e₀ liveInactiveProfileCore_injective id liveBody outerBody houter
    (liveRepairProgram hQ hA) v₁ G v₂ m₂ (liveDescriptorCore repairHost.src)
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hx₂
  have hstr : e₀ (liveDescriptorCore repairHost.src) ∉ liveInactiveProfileTargets repairTemporaryProfileJobs := by
    intro h
    obtain ⟨j, _, he⟩ := List.mem_map.mp h
    exact (liveDescriptorCore_aux repairHost.src (.input j)) (liveInactiveProfileCore_injective he.symm)
  obtain ⟨v₄, hu₄, hx₄⟩ := repairTemporaryProfileClean_exec p₀ X hG₀ hK₀ active s w outerBody
    v₃ S hinput _ hstr (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten
  rw [embDn_user] at hu₂
  refine ⟨v₄, m₁ + (m₂ + (7 * (2 * (n * (w.selectorBits + 3)) + 2) + (2 * ((p₀).wc * (w.selectorBits + 3)) + 2) + 1)),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, Exec.seq hx₁ (Exec.seq hx₃ hx₄)⟩
  have hc₁ : (m₁ : ℝ) ≤ (repairTemporaryProfilesCost p₀ w Lc : ℕ) := Nat.cast_le.mpr hm₁
  simpa only [Nat.cast_add, add_assoc] using add_le_add hc₁ (add_le_add hm₂
    (le_refl ((7 * (2 * (n * (w.selectorBits + 3)) + 2) + (2 * ((p₀).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ) : ℝ)))

end
end IntegerMultBounds.MathlibTM2.Routing
