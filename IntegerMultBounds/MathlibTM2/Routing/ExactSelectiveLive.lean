module

public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveDescriptorScratch
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Compile eleven descriptors from live profiles, execute exact R2 and erase
the generated tables. Only the record stream changes; every phase is charged. -/

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

theorem exactSelectiveLive_exec (body : P → Pr P repairT Q (prime + K) U)
    (body' : P → Pr P repairLiveT Q (prime + K) U)
    (hbody : ∀ f, body' f = embProg liveDescriptorCore id (body f))
    (w : LiveDescriptorWidths)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS repairLiveT Q (prime + K) U) (S : Stacks repairLiveT (prime + K))
    (data : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk liveDescriptorCore S).R)
    (hempty : ∀ key, S.R (liveDescriptorCore (repairSetupTarget key)) = [])
    (hL : ∀ j, S.L (liveDescriptorCore j) = []) (hblank : ∀ j, RepairBlank j → S.R (liveDescriptorCore j) = [])
    (hfit : ∀ j, LiveDescriptorBounds p₀ X w (repairLiveMode j))
    (hbank : ∀ r, S.R (liveDescriptorAux r) = liveDescriptorData p₀ X hG₀ hK₀ active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (liveDescriptorCore (repairDescriptorSource d)) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R (liveDescriptorCore repairHost.src) = l.flatten) :
    let S₁ : Stacks repairLiveT (prime + K) := { S with R := liveDescriptorBankGenerated p₀ X hG₀ hK₀ active s repairLiveMode S.R repairLiveJobs }
    let jobs := repairJobs p₀ X rb wb wm wp wk R B
    let installed := metadataInstalled (embStk liveDescriptorCore S₁).R jobs
    ∃ (v' : HS repairLiveT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ liveDescriptorBatchCost p₀ X hG₀ hK₀ active s repairLiveMode w repairLiveJobs +
        metadataInstallCost (embStk liveDescriptorCore S₁).R jobs +
        repairDensityCoreCost p₀ X rb R B scale { embStk liveDescriptorCore S₁ with R := installed } +
        metadataCleanCost installed repairTargets + liveDescriptorEraseCost p₀ X repairLiveMode repairLiveJobs ∧
      Exec body' (.seq (liveDescriptorBatch repairLiveMode repairLiveJobs)
        (.seq (embProg liveDescriptorCore id (repairProgram hQ hA)) (metadataClean (repairLiveJobs.map LiveDescriptorJob.target))))
        (mk v S) steps
        (mk v' { S with R := Function.update S.R (liveDescriptorCore repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  dsimp only
  let cfg := repairLiveJobs
  let S₁ : Stacks repairLiveT (prime + K) := { S with R := liveDescriptorBankGenerated p₀ X hG₀ hK₀ active s repairLiveMode S.R cfg }
  have hGK₀ : (p₀).G < (p₀).K := by
    have hgk := (routingParameters_guards ρ n m (Nat.clog 2 scale)).2.2
    omega
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := repairLiveBank_exec p₀ X hG₀ hK₀ active s body' hGK₀ w v S hfit hbank
  have hd : RepairSetupData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk liveDescriptorCore S₁).R :=
    data.liveGenerated p₀ X rb hG₀ hK₀ active s hdesc
  have hs₁ : S₁.R (liveDescriptorCore repairHost.src) = l.flatten := by
    change liveDescriptorBankGenerated p₀ X hG₀ hK₀ active s repairLiveMode S.R cfg (liveDescriptorCore repairHost.src) = l.flatten
    rw [repairLiveBank_core_keep p₀ X hG₀ hK₀ active s S.R repairHost.src (fun d => ?_)]
    · exact hsrc
    · rw [repairDescriptorSource_eq]
      exact (repairSetup_source_src _).symm
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := exactSelectiveEmbedded_exec ρ n m X rb scale active s body
    liveDescriptorCore liveDescriptorCore_injective id body' hbody hQ hA hscale hn hR hB hrb hs v₁ S₁ hd
    (repairLiveBank_targets p₀ X hG₀ hK₀ active s S.R hempty) hL
    (repairLiveBank_blank p₀ X hG₀ hK₀ active s S.R hblank) l hl hlen hs₁
  obtain ⟨v₃, hu₃, he₃⟩ := repairLiveClean_exec p₀ X hG₀ hK₀ active s body' v₂ S
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hdesc
  change v₂.user = v₁.user at hu₂
  have hu : v₃.user = v.user := hu₃.trans (hu₂.trans hu₁)
  refine ⟨v₃, m₁ + (m₂ + liveDescriptorEraseCost p₀ X repairLiveMode cfg), hu, ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hc₁ : (m₁ : ℝ) ≤ liveDescriptorBatchCost p₀ X hG₀ hK₀ active s repairLiveMode w cfg := by exact_mod_cast hm₁
  push_cast
  linarith

end
end IntegerMultBounds.MathlibTM2.Routing
