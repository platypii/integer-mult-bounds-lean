module

public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigLoaderLayout
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankCall
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelective

/-! Execute actual exact repair from framed raw configuration, then erase the
loaded raw bank. No per-call readiness or execution callback is assumed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} {P U : Type}

theorem framedExactSelective_exec (p : Par) (X rb : ℕ)
    (hG : 0 < p.G) (hK : 0 < p.K) (hguard : p.G + 1 < p.K)
    (scale : ℝ) (hscale : 0 < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * scale ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * scale ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G))
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (body : P → Pr P repairT Q (prime + K) U)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (words : Fin repairT → List (Fin (prime + K + 4)))
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) words)
    (delimiter : Fin (prime + K + 4)) (scan : Fin (prime + K + 4) → Bool)
    (hstop : scan delimiter = false)
    (hword : ∀ key, ∀ x ∈ words (repairSetupSource key), scan x = true)
    (rest : List (Fin (prime + K + 4))) (v : HS repairT Q (prime + K) U)
    (S : Stacks repairT (prime + K))
    (hinput : S.R repairConfigInput = delimitedBankFrames delimiter (repairConfigLoadJobs words) ++ rest)
    (htmp : S.R repairConfigTmp = []) (hraw : ∀ key, S.R (repairSetupSource key) = [])
    (hempty : ∀ key, S.R (repairSetupTarget key) = [])
    (hL : ∀ j, S.L j = []) (hblank : ∀ j, RepairBlank j → S.R j = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R repairHost.src = l.flatten) :
    let G : Stacks repairT (prime + K) := { S with R := delimitedBankLoaded repairConfigInput repairConfigTmp repairConfigArchive delimiter rest (repairConfigLoadJobs words) S.R }
    let installed := metadataInstalled G.R (repairJobs p X rb wb wm wp wk R B)
    ∃ (v' : HS repairT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ metadataInstallCost G.R (repairJobs p X rb wb wm wp wk R B) +
        repairDensityCoreCost p X rb R B scale { G with R := installed } +
        metadataCleanCost installed repairTargets +
        (6 * (delimitedBankFrames delimiter (repairConfigLoadJobs words)).length +
          2 * (repairConfigLoadJobs words).length + 2 : ℕ) ∧
      Exec body (delimitedBankCall repairConfigInput repairConfigTmp repairConfigArchive delimiter scan
        repairConfigDestinations (repairProgram hQ hA)) (mk v S) steps
        (mk v' { S with R := Function.update (Function.update (Function.update S.R repairConfigInput rest) repairConfigArchive ((delimitedBankFrames delimiter (repairConfigLoadJobs words)).reverse ++ S.R repairConfigArchive)) repairHost.src (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten }) := by
  dsimp only
  let G : Stacks repairT (prime + K) := { S with R := delimitedBankLoaded repairConfigInput repairConfigTmp repairConfigArchive delimiter rest (repairConfigLoadJobs words) S.R }
  have hd : RepairSetupData p X rb hG hK active s wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) G.R :=
    data.framedLoaded p X rb hG hK active s repairConfigInput repairConfigTmp repairConfigArchive
      delimiter rest S.R (fun key => (repairRawSource_setupSource 0 key).symm)
      (fun key => (repairRawSource_setupSource 1 key).symm)
      (fun key => (repairRawSource_setupSource 2 key).symm)
  have hsep : ∀ j ∈ repairConfigLoadJobs words,
      j.1 ≠ repairConfigInput ∧ j.1 ≠ repairConfigTmp ∧ j.1 ≠ repairConfigArchive := by
    intro j hj
    apply repairConfigLoader_separate j.1
    rw [← repairConfigLoadJobs_destinations words]
    exact List.mem_map.mpr ⟨j, hj, rfl⟩
  have hx := delimitedBankCall_exec body repairConfigInput repairConfigTmp repairConfigArchive repairHost.src
    repairConfigLoader_nodup delimiter scan hstop (repairConfigLoadJobs words)
    (by rw [repairConfigLoadJobs_destinations]; exact repairConfigDestinations_nodup) hsep
    (by rw [repairConfigLoadJobs_destinations]; exact repairConfigDestinations_stream)
    (by intro j hj; obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj; exact hword key)
    rest (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten v S hinput htmp
    (by intro j hj; obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj; exact hraw key)
    (repairProgram hQ hA)
    (metadataInstallCost G.R (repairJobs p X rb wb wm wp wk R B) +
      repairDensityCoreCost p X rb R B scale { G with R := metadataInstalled G.R (repairJobs p X rb wb wm wp wk R B) } +
      metadataCleanCost (metadataInstalled G.R (repairJobs p X rb wb wm wp wk R B)) repairTargets) ?_
  · simpa only [repairConfigLoadJobs_destinations] using hx
  · intro u
    exact exactSelectiveOfGeometry_exec p X rb hG hK hguard scale hscale hn hradix hgap active s body hQ hA
      hR hB hrb hs u G hd
      (fun key => (repairConfigLoader_targets delimiter rest words S.R key).trans (hempty key)) hL
      (fun j hj => (repairConfigLoader_blank delimiter rest words S.R j hj).trans (hblank j hj))
      l hl hlen ((repairConfigLoader_stream delimiter rest words S.R).trans hsrc)

end
end IntegerMultBounds.MathlibTM2.Routing
