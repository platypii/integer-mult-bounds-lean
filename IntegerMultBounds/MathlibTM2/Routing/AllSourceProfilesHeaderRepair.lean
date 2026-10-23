module

public import IntegerMultBounds.MathlibTM2.Routing.AllSourceProfilesHeaderGenerated

/-! Generate headers and eleven profiles, execute exact live repair, and erase
all generated inputs. Only the stream changes; every phase is charged. -/

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

private theorem headerRepairCost_add {a b c : ℕ} {x y : ℝ}
    (ha : (a : ℝ) ≤ x) (hb : (b : ℝ) ≤ y) :
    ((a + (b + c) : ℕ) : ℝ) ≤ x + y + (c : ℝ) := by
  simp only [Nat.cast_add]
  exact (add_le_add ha (add_le_add hb (le_refl (c : ℝ)))).trans_eq (add_assoc x y (c : ℝ)).symm

theorem allSourceProfilesHeaderRepairOfGeometry_exec
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
    (keySrc raw activity : Fin repairT) (hreg : [keySrc, raw, activity].Nodup)
    (hkeyHeader : ∀ c k, keySrc ≠ repairRoutingConfig (.header c k))
    (hrawHeader : ∀ c k, raw ≠ repairRoutingConfig (.header c k))
    (hactivityHeader : ∀ c k, activity ≠ repairRoutingConfig (.header c k))
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hselectorWidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hkfit : (p).K < 2 ^ w.strideBits) (hnfit : p.n < 2 ^ w.indexBits)
    (hwfit : (p).wy + 2 * (p).wc + X < 2 ^ w.coordinateBits)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS inactiveProfileHeaderT Q (prime + K) U) (S : Stacks T₀ (prime + K))
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B
      (fun _ _ => []) (fun i => S.R (e₀ (liveDescriptorCore i))))
    (hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = [])
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (hinput : ∀ j, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hkey : S.R (liveZSourceActivity keySrc) = sourceCoordinateInputWords w.indexBits w.strideBits
      (profileCoordinateInputs p hK targets source))
    (hrawBlank : S.R (liveZSourceActivity raw) = [])
    (hactivity : S.R (liveZSourceActivity activity) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten)
    (D : Stacks inactiveProfileHeaderT (prime + K)) (hproject : embStk sharedHeaderCore D = S)
    (headerBody : P → Pr P inactiveProfileHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (outerBody f))
    (Lrow Lwidth : ℕ) (hRfit : R < 2 ^ Lrow) (hwidthFit : (p).wc < 2 ^ Lwidth)
    (hrowInput : D.R (sharedHeaderBinary 0) = binSyms Lrow R)
    (hwidthInput : D.R (sharedHeaderBinary 1) = binSyms Lwidth (p).wc)
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → D.R (sharedHeaderWork r) = []) :
    let H : Stacks inactiveProfileHeaderT (prime + K) := { D with R := repairHeaderPairBank p X rb R B inactiveProfileHeaderBank D.R }
    let C₀ := embStk sharedHeaderCore H
    let G : Stacks T₀ (prime + K) := { C₀ with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w C₀.R repairAllSourceProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS inactiveProfileHeaderT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (2 * (14 * ((p).wc + (p).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
        ((liveCoordinateProfilesCost p w : ℕ) +
        liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w C +
        (9 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 2 * (2 * ((p).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ)) + (repairHeaderErasePrice p X rb R B : ℕ) ∧
      Exec headerBody (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq (liveCoordinateProfilesProgram keySrc raw activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw))))
        (mk v D) steps
        (mk v' { D with R := Function.update D.R (inactiveProfileHeaderRaw repairHost.src) (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten }) := by
  let H : Stacks inactiveProfileHeaderT (prime + K) := { D with R := repairHeaderPairBank p X rb R B inactiveProfileHeaderBank D.R }
  have hd : RepairPendingDescriptorData p X rb wb wm wp wk R B (fun _ _ => [])
      (fun i => D.R (inactiveProfileHeaderRaw i)) := by
    apply data.congr p X rb
    intro key
    exact congrArg (fun C => C.R (inactiveProfileRaw (repairSetupSource key))) hproject
  have hheaders (c : Fin 2) (k : Fin 5) : D.R (inactiveProfileHeaderBank c (.exchange (.base (.header k)))) = [] := by
    simpa only [inactiveProfileHeaderBank_header, inactiveProfileHeaderRaw_eq, List.map_nil] using hd.headers c k
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := embeddedRepairHeaders_exec inactiveProfileRaw inactiveProfileRaw_injective
    headerBody p X rb R B wb Lrow Lwidth hRfit hR hwidthFit hd.block_lt (by omega) v D
    hd.widths hrowInput hwidthInput hd.block hheaders hwork
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := allSourceProfilesHeaderGeneratedOfGeometry_exec p X rb hG hK hguard scale hscale hn hradix hgap active s targets source hactive hsources
    body liveBody hlive outerBody houter keySrc raw activity hreg hkeyHeader hrawHeader hactivityHeader w hwidth hselectorWidthFit hkfit hnfit hwfit hQ hA hR hB hrb hs
    (embDn sharedHeaderCore v₁) S data hempty hL hblank hfit hbank hdesc hinput hkey hrawBlank hactivity hcount hscratch
    l hl hlen hsrc D hproject
  obtain ⟨v₃, hu₃, hx₃⟩ := exec_emb_stream sharedHeaderCore sharedHeaderCore_injective id outerBody headerBody hheader
    _ v₁ H v₂ m₂ (inactiveProfileRaw repairHost.src)
    (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten hx₂
  obtain ⟨v₄, hu₄, hx₄⟩ := embeddedRepairHeadersClean_exec inactiveProfileRaw inactiveProfileRaw_injective
    headerBody p X rb R B v₃ D (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten
    (by intro c k; simpa only [inactiveProfileHeaderBank_header, inactiveProfileHeaderRaw_eq, List.map_nil] using hd.headers c k)
  rw [embDn_user] at hu₂
  refine ⟨v₄, m₁ + (m₂ + repairHeaderErasePrice p X rb R B), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_⟩
  · have hc₁ : (m₁ : ℝ) ≤ (2 * (14 * ((p).wc + (p).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) := Nat.cast_le.mpr hm₁
    exact headerRepairCost_add hc₁ hm₂
  · dsimp only [H] at hx₃
    exact Exec.seq hx₁ (Exec.seq hx₃ hx₄)


theorem allSourceProfilesHeaderRepair_exec
    (targets : Finset (Fin (p₀).wy)) (source : Fin (p₀).wy → Fin (p₀).wy)
    (hactive : active = profileActive p₀ hK₀ targets)
    (hsources : s = profileSources p₀ hK₀ targets source) (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (keySrc raw activity : Fin repairT) (hreg : [keySrc, raw, activity].Nodup)
    (hkeyHeader : ∀ c k, keySrc ≠ repairRoutingConfig (.header c k))
    (hrawHeader : ∀ c k, raw ≠ repairRoutingConfig (.header c k))
    (hactivityHeader : ∀ c k, activity ≠ repairRoutingConfig (.header c k))
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hselectorWidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hkfit : (p₀).K < 2 ^ w.strideBits) (hnfit : n < 2 ^ w.indexBits)
    (hwfit : (p₀).wy + 2 * (p₀).wc + X < 2 ^ w.coordinateBits)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS inactiveProfileHeaderT Q (prime + K) U) (S : Stacks T₀ (prime + K))
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
    (hkey : S.R (liveZSourceActivity keySrc) = sourceCoordinateInputWords w.indexBits w.strideBits
      (profileCoordinateInputs p₀ hK₀ targets source))
    (hrawBlank : S.R (liveZSourceActivity raw) = [])
    (hactivity : S.R (liveZSourceActivity activity) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten)
    (D : Stacks inactiveProfileHeaderT (prime + K)) (hproject : embStk sharedHeaderCore D = S)
    (headerBody : P → Pr P inactiveProfileHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (outerBody f))
    (Lrow Lwidth : ℕ) (hRfit : R < 2 ^ Lrow) (hwidthFit : (p₀).wc < 2 ^ Lwidth)
    (hrowInput : D.R (sharedHeaderBinary 0) = binSyms Lrow R)
    (hwidthInput : D.R (sharedHeaderBinary 1) = binSyms Lwidth (p₀).wc)
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → D.R (sharedHeaderWork r) = []) :
    let H : Stacks inactiveProfileHeaderT (prime + K) := { D with R := repairHeaderPairBank p₀ X rb R B inactiveProfileHeaderBank D.R }
    let C₀ := embStk sharedHeaderCore H
    let G : Stacks T₀ (prime + K) := { C₀ with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w C₀.R repairAllSourceProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS inactiveProfileHeaderT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (2 * (14 * ((p₀).wc + (p₀).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
        ((liveCoordinateProfilesCost p₀ w : ℕ) +
        liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C +
        (9 * (2 * (n * (w.selectorBits + 3)) + 2) + 2 * (2 * ((p₀).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ)) + (repairHeaderErasePrice p₀ X rb R B : ℕ) ∧
      Exec headerBody (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq (liveCoordinateProfilesProgram keySrc raw activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw))))
        (mk v D) steps
        (mk v' { D with R := Function.update D.R (inactiveProfileHeaderRaw repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  have hg := routingParameters_guards ρ n m (Nat.clog 2 scale)
  have hp : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hnp : (n : ℝ) ≤ scale := by exact_mod_cast hn
  have hlog : (scale : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 scale := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) scale
  have hx := routingParameters_radices ρ n m (Nat.clog 2 scale) scale hp.le hlog
  exact allSourceProfilesHeaderRepairOfGeometry_exec p₀ X rb hg.1 hg.2.1 hg.2.2
    scale hp hnp hx.1 hx.2 active s
    targets source hactive hsources body liveBody hlive outerBody houter keySrc raw activity
    hreg hkeyHeader hrawHeader hactivityHeader w hwidth hselectorWidthFit hkfit hnfit hwfit hQ hA
    hR hB hrb hs v S data hempty hL hblank hfit hbank
    hdesc hinput hkey hrawBlank hactivity hcount hscratch l hl hlen hsrc D
    hproject headerBody hheader Lrow Lwidth hRfit hwidthFit hrowInput hwidthInput hwork

end
end IntegerMultBounds.MathlibTM2.Routing
