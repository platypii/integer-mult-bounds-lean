module

public import IntegerMultBounds.MathlibTM2.Routing.AllSourceProfilesRepairGenerated
public import IntegerMultBounds.MathlibTM2.Routing.RepairAllSourceProfileClean
public import IntegerMultBounds.MathlibTM2.Routing.LiveCoordinateProfiles

/-! Generate all eleven profile inputs, execute live exact repair, then erase
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

theorem coordinateProfilesRepairOfGeometry_exec
    (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (hguard : p.G + 1 < p.K) (scale : ℕ)
    (hscale : (0 : ℝ) < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G))
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (targets : Finset (Fin (p).wy)) (source : Fin (p).wy → Fin (p).wy)
    (hactive : active = profileActive p hK targets)
    (hsources : s = profileSources p hK targets source) (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (src raw activity : Fin repairT) (hreg : [src, raw, activity].Nodup)
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hwidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hkfit : (p).K < 2 ^ w.strideBits) (hnfit : p.n < 2 ^ w.indexBits)
    (hwfit : (p).wy + 2 * (p).wc + X < 2 ^ w.coordinateBits)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T₀ Q (prime + K) U) (S : Stacks T₀ (prime + K))
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) (fun i => S.R (e₀ (liveDescriptorCore i))))
    (hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = [])
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (hinput : ∀ j, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hraw : S.R (liveZSourceActivity src) = sourceCoordinateInputWords w.indexBits w.strideBits
      (profileCoordinateInputs p hK targets source))
    (hrawBlank : S.R (liveZSourceActivity raw) = [])
    (hactivityBlank : S.R (liveZSourceActivity activity) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten) :
    let G : Stacks T₀ (prime + K) := { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairAllSourceProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS T₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (liveCoordinateProfilesCost p w : ℕ) +
        liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w C +
        (9 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 2 * (2 * ((p).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ) ∧
      Exec outerBody (.seq (liveCoordinateProfilesProgram src raw activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs))))
        (mk v S) steps
        (mk v' { S with R := Function.update S.R (e₀ (liveDescriptorCore repairHost.src)) (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten }) := by
  let G : Stacks T₀ (prime + K) := { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairAllSourceProfileJobs }
  let C := embStk e₀ G
  have hgen := liveCoordinateProfiles_exec outerBody p X hG hK targets source w src raw activity hreg
    hwidth hwidthFit hwfit hkfit hnfit v S hfit (by simpa only [hactive, hsources] using hbank)
    hraw hrawBlank hactivityBlank hinput hcount hscratch
  simp only [← hactive, ← hsources] at hgen
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := hgen
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := allSourceProfilesRepairGeneratedOfGeometry_exec p X rb hG hK hguard scale hscale hn hradix hgap active s
    body liveBody hlive w hQ hA hR hB hrb hs (embDn e₀ v₁) S
    data hempty hL hblank hfit hbank hdesc l hl hlen hsrc
  obtain ⟨v₃, hu₃, hx₃⟩ := exec_emb_stream e₀ liveInactiveProfileCore_injective id liveBody outerBody houter
    (liveRepairProgram hQ hA) v₁ G v₂ m₂ (liveDescriptorCore repairHost.src)
    (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten hx₂
  have hstr : e₀ (liveDescriptorCore repairHost.src) ∉ liveInactiveProfileTargets repairAllSourceProfileJobs := by
    intro h
    obtain ⟨j, _, he⟩ := List.mem_map.mp h
    exact (liveDescriptorCore_aux repairHost.src (.input j)) (liveInactiveProfileCore_injective he.symm)
  obtain ⟨v₄, hu₄, hx₄⟩ := repairAllSourceProfileClean_exec p X hG hK active s w outerBody
    v₃ S (fun j _ => hinput j) _ hstr (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten
  rw [embDn_user] at hu₂
  refine ⟨v₄, m₁ + (m₂ + (9 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 2 * (2 * ((p).wc * (w.selectorBits + 3)) + 2) + 1)),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, Exec.seq hx₁ (Exec.seq hx₃ hx₄)⟩
  have hc₁ : (m₁ : ℝ) ≤ (liveCoordinateProfilesCost p w : ℕ) := Nat.cast_le.mpr hm₁
  simpa only [Nat.cast_add, add_assoc] using add_le_add hc₁ (add_le_add hm₂
    (le_refl ((9 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 2 * (2 * ((p).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ) : ℝ)))


theorem coordinateProfilesRepair_exec
    (targets : Finset (Fin (p₀).wy)) (source : Fin (p₀).wy → Fin (p₀).wy)
    (hactive : active = profileActive p₀ hK₀ targets)
    (hsources : s = profileSources p₀ hK₀ targets source) (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (src raw activity : Fin repairT) (hreg : [src, raw, activity].Nodup)
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
      (repairCanonicalHeaders p₀ X rb R B) (fun i => S.R (e₀ (liveDescriptorCore i))))
    (hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = [])
    (hfit : ∀ j, LiveDescriptorBounds p₀ X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p₀ X hG₀ hK₀ active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (hinput : ∀ j, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hraw : S.R (liveZSourceActivity src) = sourceCoordinateInputWords w.indexBits w.strideBits
      (profileCoordinateInputs p₀ hK₀ targets source))
    (hrawBlank : S.R (liveZSourceActivity raw) = [])
    (hactivityBlank : S.R (liveZSourceActivity activity) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten) :
    let G : Stacks T₀ (prime + K) := { S with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w S.R repairAllSourceProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS T₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (liveCoordinateProfilesCost p₀ w : ℕ) +
        liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C +
        (9 * (2 * (n * (w.selectorBits + 3)) + 2) + 2 * (2 * ((p₀).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ) ∧
      Exec outerBody (.seq (liveCoordinateProfilesProgram src raw activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs))))
        (mk v S) steps
        (mk v' { S with R := Function.update S.R (e₀ (liveDescriptorCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  have hg := routingParameters_guards ρ n m (Nat.clog 2 scale)
  have hp : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hnp : (n : ℝ) ≤ scale := by exact_mod_cast hn
  have hlog : (scale : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 scale := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) scale
  have hx := routingParameters_radices ρ n m (Nat.clog 2 scale) scale hp.le hlog
  exact coordinateProfilesRepairOfGeometry_exec p₀ X rb hg.1 hg.2.1 hg.2.2
    scale hp hnp hx.1 hx.2 active s targets source hactive hsources body liveBody hlive outerBody houter
    src raw activity hreg w hwidth hwidthFit hkfit hnfit hwfit hQ hA hR hB hrb hs v S
    data hempty hL hblank hfit hbank hdesc hinput hraw hrawBlank hactivityBlank hcount hscratch
    l hl hlen hsrc

end
end IntegerMultBounds.MathlibTM2.Routing
