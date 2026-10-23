module

public import IntegerMultBounds.MathlibTM2.Routing.LiveYSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LiveProfileBatchFrame

/-! Generate the three inactive profiles and first Y profile in one shared
workspace. All four inputs start blank; no prepared profile is supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

def repairGeneratedProfileJobs : List (Fin 11) := repairInactiveProfileJobs ++ [5]

theorem repairGeneratedProfileJobs_nodup : repairGeneratedProfileJobs.Nodup := by decide

variable {Q A : ℕ} {P U : Type}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)

local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def repairGeneratedProfilesProgram : Pr P T₀ Q A U :=
  .seq (liveInactiveProfileBatch repairInactiveProfileJobs) liveYSourceProgram

theorem repairLiveGeneratedProfiles_ready (R : Fin T₀ → List (Fin (A + 4)))
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairGeneratedProfileJobs, r ≠ .input j) →
      R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairGeneratedProfileJobs (e₀ i)) :=
  liveInactiveProfileBatch_ready p X hG hK active s repairLiveMode w R repairGeneratedProfileJobs
    repairGeneratedProfileJobs_nodup hfit hbank

theorem repairLiveGeneratedProfiles_exec (body : P → Pr P T₀ Q A U) (Lc : ℕ) (hn : p.n < 2 ^ Lc)
    (hwidth : w.selectorBits = w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairGeneratedProfileJobs, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hinput : ∀ j ∈ repairGeneratedProfileJobs, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (3 * binaryInactiveProfileCost w.widthBits Lc w.selectorBits p.n + 1) +
        binaryAffineSourceGenerateCost Lc w.indexBits w.strideBits p.n ∧
      Exec body repairGeneratedProfilesProgram (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairGeneratedProfileJobs }) := by
  have hwidthInput : S.R (e₀ (liveDescriptorAux .selectorBits)) = binSyms w.widthBits w.selectorBits :=
    hbank .selectorBits (by intro j hj; simp)
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := repairLiveInactiveProfiles_exec p X hG hK active s w body Lc hn
    (hfit 0).selector_fits v S hwidthInput
    (fun j hj => hinput j (List.mem_append_left _ hj)) hcount hscratch
  let G : Stacks T₀ A := { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairInactiveProfileJobs }
  have hpending := liveProfileBatch_pending p X hG hK active s repairLiveMode w S.R repairInactiveProfileJobs [5]
    repairInactiveProfileJobs_nodup hbank
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := liveYSourceGenerate_exec p X hG hK active s w body Lc hn hwidth v₁ G hfit
    (by
      intro r hr
      dsimp only [G]
      exact hpending r (by simpa using hr))
    (by
      rw [show G.R liveYSourceDst = S.R liveYSourceDst from ?_]
      · exact hinput 5 (by simp [repairGeneratedProfileJobs])
      · apply liveInactiveProfileBatch_keep
        intro j hj
        apply liveInactiveProfileCore_injective.ne
        apply liveDescriptorAux_injective.ne
        simp only [repairInactiveProfileJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl <;> simp)
    (by
      dsimp only [G]
      exact (repairLiveInactiveProfiles_aux p X hG hK active s w S.R 0).trans hcount)
    (by
      intro i hi
      dsimp only [G]
      exact (repairLiveInactiveProfiles_aux p X hG hK active s w S.R i).trans (hscratch i hi))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, Nat.add_le_add hm₁ hm₂, ?_⟩
  have hf : liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairGeneratedProfileJobs =
      Function.update G.R liveYSourceDst ((repairLiveMode 5).profileFrames p X hG hK active s w.selectorBits) := by
    rw [repairGeneratedProfileJobs, liveProfileBatchBank_append]
    rfl
  rw [hf]
  exact Exec.seq hx₁ hx₂

theorem repairLiveGeneratedProfiles_core (R : Fin T₀ → List (Fin (A + 4))) (i : Fin repairT) :
    liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairGeneratedProfileJobs
      (e₀ (liveDescriptorCore i)) = R (e₀ (liveDescriptorCore i)) := by
  apply liveInactiveProfileBatch_keep
  intro j _
  exact liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux i (.input j))

end
end IntegerMultBounds.MathlibTM2.Routing
