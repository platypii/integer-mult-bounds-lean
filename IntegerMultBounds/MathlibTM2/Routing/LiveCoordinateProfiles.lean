module

public import IntegerMultBounds.MathlibTM2.Routing.LivePreparedCoordinateSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairSourceRecordProfiles

/-! Generate every repair source profile from framed physical coordinates and
activity. The intermediate canonical source stream is generated and erased;
all non-profile tapes, including the physical input, restore exactly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveCoordinateProfilesProgram (src raw activity : Fin repairT) : Pr P T₀ Q A U :=
  .seq (livePreparedCoordinateSourceProgram src raw)
    (.seq (repairSourceRecordProfilesProgram raw activity) (bclear (liveZSourceActivity raw)))

def liveCoordinateProfilesCost (p : Par) (w : LiveDescriptorWidths) :=
  livePreparedCoordinateSourceCost p w +
  (liveSelectedProfilesCost p w + repairControlProfilesCost p w w.indexBits +
    (p.n * (6 * w.indexBits + 6 * w.coordinateBits + 19) +
      2 * (p.n * (w.indexBits + w.coordinateBits + 5)) + 4 * p.n + 8)) +
  (2 * (p.n * (w.indexBits + w.coordinateBits + 5)) + 2)

theorem liveCoordinateProfilesCost_mono (p q : Par) (w : LiveDescriptorWidths)
    (hn : p.n ≤ q.n) (hg : p.G ≤ q.G) (hc : p.wc ≤ q.wc) :
    liveCoordinateProfilesCost p w ≤ liveCoordinateProfilesCost q w := by
  unfold liveCoordinateProfilesCost livePreparedCoordinateSourceCost liveSelectedProfilesCost
    repairControlProfilesCost repairTemporaryProfilesCost repairYZProfilesCost liveYZSourceBatchCost
    binaryCounterSourceGenerateCost binaryAffineSourceGenerateCost binaryInactiveProfileCost
    optionalAffineSourceGroupIterationCost binaryWordRepeatCost
  gcongr

theorem liveCoordinateProfilesCost_widths_mono (p : Par) (w w' : LiveDescriptorWidths)
    (hi : w.indexBits ≤ w'.indexBits) (hg : w.groupBits ≤ w'.groupBits)
    (hk : w.strideBits ≤ w'.strideBits) (hs : w.selectorBits ≤ w'.selectorBits)
    (hw : w.widthBits ≤ w'.widthBits) :
    liveCoordinateProfilesCost p w ≤ liveCoordinateProfilesCost p w' := by
  have hc : w.coordinateBits ≤ w'.coordinateBits := Nat.add_le_add hi hk
  unfold liveCoordinateProfilesCost livePreparedCoordinateSourceCost liveSelectedProfilesCost
    repairControlProfilesCost repairTemporaryProfilesCost repairYZProfilesCost liveYZSourceBatchCost
    binaryCounterSourceGenerateCost binaryAffineSourceGenerateCost binaryInactiveProfileCost
    optionalAffineSourceGroupIterationCost binaryWordRepeatCost
    sourceCoordinateIterationCost sourceCoordinateRecordCost gatedSelectedSourceIterationCost
    sharedSelectedSourceIterationCost gatedSelectedSourceFrameCost selectedSourceFrameCost
    optionalAffineSourceIterationCost optionalAffineSourceFrameCost optionalBinaryProfileFrameCost
    affineSourceIterationCost affineSourceFrameCost counterSourceIterationCost
  gcongr

theorem liveCoordinateProfiles_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy) (w : LiveDescriptorWidths)
    (src raw activity : Fin repairT) (hreg : [src, raw, activity].Nodup)
    (hwidth : w.selectorBits = w.coordinateBits) (hwidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hw : p.wy + 2 * p.wc + X < 2 ^ w.coordinateBits) (hk : p.K < 2 ^ w.strideBits)
    (hn : p.n < 2 ^ w.indexBits) (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK (profileActive p hK targets)
        (profileSources p hK targets source) repairLiveMode w r)
    (hraw : S.R (liveZSourceActivity src) = sourceCoordinateInputWords w.indexBits w.strideBits
      (profileCoordinateInputs p hK targets source))
    (hrawBlank : S.R (liveZSourceActivity raw) = []) (hactivityBlank : S.R (liveZSourceActivity activity) = [])
    (hinput : ∀ j, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ liveCoordinateProfilesCost p w ∧
      Exec body (liveCoordinateProfilesProgram src raw activity) (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBatchBank p X hG hK (profileActive p hK targets) (profileSources p hK targets source) repairLiveMode w S.R repairAllSourceProfileJobs }) := by
  have hnreg := hreg
  regs_ne hnreg
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := livePreparedCoordinateSourceGenerate_exec body p X hG hK targets source w
    src raw ‹src ≠ raw› (by omega) hk hn v S hbank hraw hcount hscratch
  rw [hrawBlank, List.append_nil] at hx₁
  let word := profileSourceRecords (A := A) p hK X targets source w.indexBits w.strideBits
  let G : Stacks T₀ A := { S with R := Function.update S.R (liveZSourceActivity raw) word }
  have hkeep (i : Fin T₀) (hi : i ≠ liveZSourceActivity raw) : G.R i = S.R i := by simp [G, hi]
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := repairSourceRecordProfiles_exec body p X hG hK (profileActive p hK targets)
    (profileSources p hK targets source) w raw activity ‹raw ≠ activity› hwidth hwidthFit hk hn hw v₁ G hfit
    (by
      intro r hr
      exact (hkeep _ (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux raw r).symm)).trans (hbank r hr))
    (by simp [G, word, profileSourceRecords])
    (by simpa [G, liveZSourceActivity, liveInactiveProfileCore_injective.eq_iff,
      liveDescriptorCore_injective.eq_iff, ‹raw ≠ activity›.symm] using hactivityBlank)
    (fun j => (hkeep _ (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux raw (.input j)).symm)).trans (hinput j))
    ((hkeep _ (liveInactiveProfileAux_core _ _)).trans hcount)
    (fun i hi => (hkeep _ (liveInactiveProfileAux_core _ _)).trans (hscratch i hi))
  let R := liveInactiveProfileBatchBank p X hG hK (profileActive p hK targets)
    (profileSources p hK targets source) repairLiveMode w S.R repairAllSourceProfileJobs
  let H : Stacks T₀ A := { S with R := liveInactiveProfileBatchBank p X hG hK (profileActive p hK targets) (profileSources p hK targets source) repairLiveMode w G.R repairAllSourceProfileJobs }
  have hH : H.R = Function.update R (liveZSourceActivity raw) word :=
    liveProfileBatchBank_update_raw p X hG hK (profileActive p hK targets) (profileSources p hK targets source)
      w S.R repairAllSourceProfileJobs raw word
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (liveZSourceActivity raw) v₂ H
  have hlen : (H.R (liveZSourceActivity raw)).length = p.n * (w.indexBits + w.coordinateBits + 5) := by
    simp [hH, word, profileSourceRecords_length, LiveDescriptorWidths.coordinateBits]
  have hf : Function.update H.R (liveZSourceActivity raw) [] = R := by
    rw [hH, Function.update_idem]
    have hz : R (liveZSourceActivity raw) = [] :=
      (liveInactiveProfileBatch_keep p X hG hK (profileActive p hK targets) (profileSources p hK targets source)
        repairLiveMode w S.R repairAllSourceProfileJobs _
        (fun j _ => liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux raw (.input j)))).trans hrawBlank
    funext j
    by_cases hj : j = liveZSourceActivity raw
    · subst j; simp [hz]
    · simp [hj]
  rw [hlen, hf] at hx₃
  exact ⟨v₃, m₁ + (m₂ + (2 * (p.n * (w.indexBits + w.coordinateBits + 5)) + 2)),
    hu₃.trans (hu₂.trans hu₁), by unfold liveCoordinateProfilesCost; omega, Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end
end IntegerMultBounds.MathlibTM2.Routing
