module

public import IntegerMultBounds.MathlibTM2.Routing.LiveZSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveGeneratedProfiles

/-! Generate five repair profiles in the same bank: first Z from raw activity,
then the three inactive profiles and first Y. Every source tape is restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

def repairActivityProfileJobs : List (Fin 11) := [3] ++ repairGeneratedProfileJobs

theorem repairActivityProfileJobs_nodup : repairActivityProfileJobs.Nodup := by decide

variable {Q A : ℕ} {P U : Type}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)

local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def repairActivityProfilesProgram (activity : Fin repairT) : Pr P T₀ Q A U :=
  .seq (liveZSourceProgram activity) repairGeneratedProfilesProgram

theorem repairLiveActivityProfiles_ready (R : Fin T₀ → List (Fin (A + 4)))
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairActivityProfileJobs, r ≠ .input j) →
      R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairActivityProfileJobs (e₀ i)) :=
  liveInactiveProfileBatch_ready p X hG hK active s repairLiveMode w R repairActivityProfileJobs
    repairActivityProfileJobs_nodup hfit hbank

theorem repairLiveActivityProfiles_exec (body : P → Pr P T₀ Q A U)
    (activity : Fin repairT) (Lc : ℕ) (hn : p.n < 2 ^ Lc)
    (hwidth : w.selectorBits = w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairActivityProfileJobs, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hinput : ∀ j ∈ repairActivityProfileJobs, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hactivity : S.R (liveZSourceActivity activity) = (List.ofFn active).map bitSymbol)
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (p.n * optionalAffineSourceIterationCost w.widthBits w.indexBits w.strideBits + 2 * p.n +
        2 * (p.n * (w.indexBits + w.strideBits + 3)) + 16 * w.indexBits + 22) +
        ((3 * binaryInactiveProfileCost w.widthBits Lc w.selectorBits p.n + 1) +
          binaryAffineSourceGenerateCost Lc w.indexBits w.strideBits p.n) ∧
      Exec body (repairActivityProfilesProgram activity) (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairActivityProfileJobs }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := liveZSourceGenerate_exec p X hG hK active s w body activity
    hwidth v S hfit (fun r hr => hbank r (fun j _ => hr j))
    (hinput 3 (by simp [repairActivityProfileJobs])) hactivity hscratch
  let G : Stacks T₀ A := { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R [3] }
  have hpending := liveProfileBatch_pending p X hG hK active s repairLiveMode w S.R [3]
    repairGeneratedProfileJobs (by simp) hbank
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := repairLiveGeneratedProfiles_exec p X hG hK active s w body Lc hn
    hwidth v₁ G hfit (by
      intro r hr
      dsimp only [G]
      exact hpending r hr)
    (by
      intro j hj
      have hj3 : j ≠ 3 := by
        simp only [repairGeneratedProfileJobs, repairInactiveProfileJobs, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with (rfl | rfl | rfl) | rfl <;> decide
      dsimp only [G]
      rw [liveInactiveProfileBatch_keep p X hG hK active s repairLiveMode w S.R [3] _ (by
        intro k hk
        simp only [List.mem_singleton] at hk
        subst k
        exact liveInactiveProfileCore_injective.ne (liveDescriptorAux_injective.ne (by simpa using hj3)))]
      exact hinput j (List.mem_append_right _ hj))
    (by
      dsimp only [G]
      exact (liveInactiveProfileBatch_keep p X hG hK active s repairLiveMode w S.R [3] _
        (fun _ _ => liveInactiveProfileAux_core _ _)).trans hcount)
    (by
      intro i hi
      dsimp only [G]
      exact (liveInactiveProfileBatch_keep p X hG hK active s repairLiveMode w S.R [3] _
        (fun _ _ => liveInactiveProfileAux_core _ _)).trans (hscratch i hi))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, Nat.add_le_add hm₁ hm₂, ?_⟩
  rw [repairActivityProfileJobs, liveProfileBatchBank_append]
  dsimp only [G] at hx₂
  simp only [liveInactiveProfileBatchBank] at hx₂ ⊢
  exact Exec.seq hx₁ hx₂

theorem repairLiveActivityProfiles_core (R : Fin T₀ → List (Fin (A + 4))) (i : Fin repairT) :
    liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairActivityProfileJobs
      (e₀ (liveDescriptorCore i)) = R (e₀ (liveDescriptorCore i)) := by
  apply liveInactiveProfileBatch_keep
  intro j _
  exact liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux i (.input j))

end
end IntegerMultBounds.MathlibTM2.Routing
