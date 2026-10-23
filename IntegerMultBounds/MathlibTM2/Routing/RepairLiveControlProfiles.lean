module

public import IntegerMultBounds.MathlibTM2.Routing.LiveAControlSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveTemporaryProfiles

/-! Nine actual repair source profiles are generated in one shared workspace.
Raw activity and binary dimensions remain inputs; every borrowed tape is restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

def repairControlProfileJobs : List (Fin 11) := [1] ++ repairTemporaryProfileJobs

theorem repairControlProfileJobs_nodup : repairControlProfileJobs.Nodup := by decide

variable {Q A : ℕ} {P U : Type}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def repairControlProfilesProgram (activity : Fin repairT) : Pr P T₀ Q A U :=
  .seq (liveAControlSourceProgram activity) (repairTemporaryProfilesProgram activity)

def repairControlProfilesCost (Lc : ℕ) :=
  (p.n * optionalAffineSourceGroupIterationCost w.groupBits p.G w.widthBits w.indexBits w.strideBits + 2 * p.n +
    2 * (p.n * (p.G * (w.indexBits + w.strideBits + 3))) + 16 * w.indexBits + 22) +
    repairTemporaryProfilesCost p w Lc

theorem repairLiveControlProfiles_ready (R : Fin T₀ → List (Fin (A + 4)))
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairControlProfileJobs, r ≠ .input j) →
      R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairControlProfileJobs (e₀ i)) :=
  liveInactiveProfileBatch_ready p X hG hK active s repairLiveMode w R repairControlProfileJobs
    repairControlProfileJobs_nodup hfit hbank

theorem repairLiveControlProfiles_exec (body : P → Pr P T₀ Q A U) (activity : Fin repairT)
    (Lc : ℕ) (hn : p.n < 2 ^ Lc) (hwidth : w.selectorBits = w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairControlProfileJobs, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hinput : ∀ j ∈ repairControlProfileJobs, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hactivity : S.R (liveZSourceActivity activity) = (List.ofFn active).map bitSymbol)
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ repairControlProfilesCost p w Lc ∧
      Exec body (repairControlProfilesProgram activity) (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairControlProfileJobs }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := liveAControlSourceGenerate_exec p X hG hK active s w body activity
    hwidth v S hfit (fun r hr => hbank r (fun j _ => hr j))
    (hinput 1 (by simp [repairControlProfileJobs])) hactivity hscratch
  let G : Stacks T₀ A := { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R [1] }
  have hpending := liveProfileBatch_pending p X hG hK active s repairLiveMode w S.R [1]
    repairTemporaryProfileJobs (by decide) hbank
  have haux (i : Fin 7) : G.R (liveInactiveProfileAux i) = S.R (liveInactiveProfileAux i) := by
    dsimp only [G]
    exact liveInactiveProfileBatch_keep p X hG hK active s repairLiveMode w S.R [1] _
      (fun _ _ => liveInactiveProfileAux_core _ _)
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := repairLiveTemporaryProfiles_exec p X hG hK active s w body activity Lc hn
    hwidth v₁ G hfit (by intro r hr; dsimp only [G]; exact hpending r hr)
    (by
      intro j hj
      have hdis : ∀ j ∈ repairTemporaryProfileJobs, j ∉ ([1] : List (Fin 11)) := by decide
      dsimp only [G]
      rw [liveInactiveProfileBatch_keep p X hG hK active s repairLiveMode w S.R [1] _ (by
        intro k hk
        apply liveInactiveProfileCore_injective.ne
        apply liveDescriptorAux_injective.ne
        intro he
        cases he
        exact hdis j hj hk)]
      exact hinput j (List.mem_append_right _ hj))
    (by
      dsimp only [G]
      exact (liveInactiveProfileBatch_keep p X hG hK active s repairLiveMode w S.R [1] _
        (fun j _ => liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux activity (.input j)))).trans hactivity)
    ((haux 0).trans hcount) (fun i hi => (haux i).trans (hscratch i hi))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, Nat.add_le_add hm₁ hm₂, ?_⟩
  rw [repairControlProfileJobs, liveProfileBatchBank_append]
  dsimp only [G] at hx₂
  simp only [liveInactiveProfileBatchBank] at hx₂ ⊢
  exact Exec.seq hx₁ hx₂

theorem repairLiveControlProfiles_core (R : Fin T₀ → List (Fin (A + 4))) (i : Fin repairT) :
    liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairControlProfileJobs
      (e₀ (liveDescriptorCore i)) = R (e₀ (liveDescriptorCore i)) := by
  apply liveInactiveProfileBatch_keep
  intro j _
  exact liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux i (.input j))

end
end IntegerMultBounds.MathlibTM2.Routing
