module

public import IntegerMultBounds.MathlibTM2.Routing.LiveSourceActivityGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LiveProfileRawFrame

/-! Generate all eleven profiles from one canonical source stream, including
activity extraction and cleanup. No separate activity stream is supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def repairSourceRecordProfilesProgram (src activity : Fin repairT) : Pr P T₀ Q A U :=
  .seq (liveSourceActivityProgram src activity)
    (.seq (repairAllSourceProfilesProgram src src activity) (bclear (liveZSourceActivity activity)))

theorem repairSourceRecordProfiles_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (src activity : Fin repairT) (hsa : src ≠ activity) (hwidth : w.selectorBits = w.coordinateBits)
    (hwidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hk : p.K < 2 ^ w.strideBits) (hn : p.n < 2 ^ w.indexBits)
    (hw : p.wy + 2 * p.wc + X < 2 ^ w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hraw : S.R (liveZSourceActivity src) = gatedSelectedSourceWords w.indexBits w.strideBits
      (List.ofFn (fun c => (s c).gatedChoice (active c))))
    (hactivityBlank : S.R (liveZSourceActivity activity) = [])
    (hinput : ∀ j, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ liveSelectedProfilesCost p w + repairControlProfilesCost p w w.indexBits +
        (p.n * (6 * w.indexBits + 6 * w.coordinateBits + 19) +
          2 * (p.n * (w.indexBits + w.coordinateBits + 5)) + 4 * p.n + 8) ∧
      Exec body (repairSourceRecordProfilesProgram src activity) (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairAllSourceProfileJobs }) := by
  obtain ⟨v₁, hu₁, hx₁⟩ := liveSourceActivityGenerate_exec body p X hG hK active s w src activity hsa
    v S hbank hraw hscratch
  rw [hactivityBlank, List.append_nil] at hx₁
  let word : List (Fin (A + 4)) := (List.ofFn active).map bitSymbol
  let G : Stacks T₀ A := { S with R := Function.update S.R (liveZSourceActivity activity) word }
  have hkeep (i : Fin T₀) (hi : i ≠ liveZSourceActivity activity) : G.R i = S.R i := by simp [G, hi]
  have hrawG : G.R (liveZSourceActivity src) = gatedSelectedSourceWords w.indexBits w.strideBits
      (List.ofFn (fun c => (s c).gatedChoice (active c))) := by
    rw [hkeep _ (by simpa [liveZSourceActivity, liveInactiveProfileCore_injective.eq_iff,
      liveDescriptorCore_injective.eq_iff] using hsa)]
    exact hraw
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := repairAllSourceProfiles_exec body p X hG hK active s w
    src src activity hwidth hwidthFit hk hn hw v₁ G hfit
    (by
      intro r hr
      exact (hkeep _ (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux activity r).symm)).trans (hbank r hr))
    hrawG hrawG (by simp [G, word])
    (fun j => (hkeep _ (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux activity (.input j)).symm)).trans (hinput j))
    ((hkeep _ (liveInactiveProfileAux_core _ _)).trans hcount)
    (fun i hi => (hkeep _ (liveInactiveProfileAux_core _ _)).trans (hscratch i hi))
  let H : Stacks T₀ A := { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w G.R repairAllSourceProfileJobs }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (liveZSourceActivity activity) v₂ H
  have hH : H.R = Function.update
      (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairAllSourceProfileJobs)
      (liveZSourceActivity activity) word :=
    liveProfileBatchBank_update_raw p X hG hK active s w S.R repairAllSourceProfileJobs activity word
  have hlen : (H.R (liveZSourceActivity activity)).length = p.n := by simp [hH, word]
  have hf : Function.update H.R (liveZSourceActivity activity) [] =
      liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairAllSourceProfileJobs := by
    rw [hH, Function.update_idem]
    have hz := (liveInactiveProfileBatch_keep p X hG hK active s repairLiveMode w S.R repairAllSourceProfileJobs _
      (fun j _ => liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux activity (.input j)))).trans hactivityBlank
    funext j
    by_cases hj : j = liveZSourceActivity activity
    · subst j; simp [liveZSourceActivity, hz]
    · simp [hj]
  rw [hlen, hf] at hx₃
  refine ⟨v₃, (p.n * (6 * w.indexBits + 6 * w.coordinateBits + 19) +
    2 * (p.n * (w.indexBits + w.coordinateBits + 5)) + 2 * p.n + 6) + (m₂ + (2 * p.n + 2)),
    hu₃.trans (hu₂.trans hu₁), by omega, Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end
end IntegerMultBounds.MathlibTM2.Routing
