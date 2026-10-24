module

public import IntegerMultBounds.MathlibTM2.Routing.RepairSetup

/-!
# Exact selective update with executed installation and cleanup

Raw configuration tapes enter the fixed 34-word installer; the actual shared
key/route/repair core runs; all installed metadata is cleared. The final register
file differs from the original only at the stream, and every phase is charged.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {Q K : ℕ} {P U : Type}

def repairTargets : List (Fin repairT) := repairSetupKeys.map repairSetupTarget

theorem repairJobs_targets (p : Par) (X rb wb wm wp wk R B : ℕ) :
    (repairJobs p X rb wb wm wp wk R B).map MetadataJob.dst = repairTargets := by
  simp only [repairJobs, repairSetupJobs, List.map_map, Function.comp_def, repairSetupJob_dst, repairTargets]

theorem repairTargets_src : repairHost.src ∉ repairTargets := by
  intro hm
  obtain ⟨key, _, he⟩ := List.mem_map.mp hm
  exact repairSetup_target_src key he

def repairProgram (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) : Pr P repairT Q (prime + K) U :=
  .seq repairSetup (.seq (repairCore hQ hA) (metadataClean repairTargets))

variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem repairMetadataCleanCost_le (wb wm wp wk R B L : ℕ)
    (headers : Fin 2 → Fin 5 → List Bool)
    (bank : Fin repairT → List (Fin (prime + K + 4)))
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers bank)
    (hpayload : ∀ key, (repairSetupPayload (A := prime + K) p X rb hG hK active s R B headers key).length ≤ L) :
    metadataCleanCost (metadataInstalled bank (repairJobs p X rb wb wm wp wk R B)) repairTargets ≤
      34 * (2 * L + 2) + 1 := by
  have hc := metadataCleanCost_le (metadataInstalled bank (repairJobs p X rb wb wm wp wk R B))
    repairTargets L (by
      intro j hj
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
      rw [repairSetup_at p X rb hG hK active s data key]
      exact hpayload key)
  have hlen : repairTargets.length = 34 := by decide +kernel
  simpa only [hlen] using hc

/-- Exact all-address execution from raw input configuration, with no prepared
key, classifier, counter, placement or per-phase execution assumptions. -/
theorem repairProgram_exec (hGK : p.G + 1 < p.K)
    (body : P → Pr P repairT Q (prime + K) U)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active) (headers : Fin 2 → Fin 5 → List Bool)
    (hv : ∀ c j, Counter.value (headers c j) =
      selectiveSwapValues p X R (fieldsLen (selectiveKeyLen p X rb) + B) c j)
    (hc : ∀ c j, GrowingCounterData.Canonical (headers c j))
    (v : HS repairT Q (prime + K) U) (S : Stacks repairT (prime + K))
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers S.R)
    (hempty : ∀ key, S.R (repairSetupTarget key) = [])
    (hL : ∀ j, S.L j = []) (hblank : ∀ j, RepairBlank j → S.R j = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R repairHost.src = l.flatten) :
    let jobs := repairJobs p X rb wb wm wp wk R B
    let installed := metadataInstalled S.R jobs
    ∃ (v' : HS repairT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ metadataInstallCost S.R jobs +
        repairCoreCost p X rb R B { S with R := installed } + metadataCleanCost installed repairTargets ∧
      Exec body (repairProgram hQ hA) (mk v S) steps
        (mk v' { S with R := Function.update S.R repairHost.src (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten }) := by
  dsimp only
  let jobs := repairJobs p X rb wb wm wp wk R B
  let installed := metadataInstalled S.R jobs
  have htargets : jobs.map MetadataJob.dst = repairTargets := repairJobs_targets _ _ _ _ _ _ _ _ _
  have hn : repairTargets.Nodup := htargets ▸ repairJobs_nodup p X rb wb wm wp wk R B
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, hp⟩ := repairSetup_exec p X rb hG hK active s body v S data hempty hL hblank
  have hstream : installed repairHost.src = l.flatten := by
    exact (metadataInstalled_keep S.R jobs repairHost.src (by rw [htargets]; exact repairTargets_src)).trans hsrc
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := repairCore_exec p X rb hG hK active s hGK body hQ hA
    hR hB hrb hs headers hv hc v₁ { S with R := installed } hp l hl hlen hstream
  let routed := (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body repairTargets hn v₂
    { S with R := Function.update installed repairHost.src routed }
  have hrestore : metadataCleared installed repairTargets = S.R := by
    rw [← htargets]
    apply metadataClean_restore
    intro job hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    simpa only [repairSetupJob_dst] using hempty key
  have hfinal : metadataCleared (Function.update installed repairHost.src routed) repairTargets =
      Function.update S.R repairHost.src routed := by
    rw [metadataCleared_update _ _ _ _ repairTargets_src, hrestore]
  have hcost : metadataCleanCost (Function.update installed repairHost.src routed) repairTargets =
      metadataCleanCost installed repairTargets := by
    apply metadataCleanCost_congr
    intro j hj
    have hne : j ≠ repairHost.src := by
      intro he
      exact repairTargets_src (he ▸ hj)
    exact Function.update_of_ne hne _ _
  rw [hfinal, hcost] at he₃
  refine ⟨v₃, m₁ + (m₂ + metadataCleanCost installed repairTargets),
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hm₁' : (m₁ : ℝ) ≤ metadataInstallCost S.R jobs := by exact_mod_cast hm₁
  push_cast
  linarith

end
end IntegerMultBounds.MathlibTM2.Routing
