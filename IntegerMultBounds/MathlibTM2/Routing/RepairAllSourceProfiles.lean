module

public import IntegerMultBounds.MathlibTM2.Routing.LiveSelectedProfiles
public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveControlProfiles

/-! All eleven source-profile jobs, in generation order. Readiness requires
only the non-profile descriptor bank; no completed profile is supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

def repairAllSourceProfileJobs : List (Fin 11) := [0, 9] ++ repairControlProfileJobs

theorem repairAllSourceProfileJobs_nodup : repairAllSourceProfileJobs.Nodup := by decide

theorem repairAllSourceProfileJobs_complete (j : Fin 11) : j ∈ repairAllSourceProfileJobs := by
  fin_cases j <;> decide

theorem repairAllSourceProfiles_ready {A : ℕ}
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (R : Fin (liveInactiveProfileT repairT 11) → List (Fin (A + 4)))
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      R (liveInactiveProfileCore (liveDescriptorAux r)) =
        liveDescriptorData p X hG hK active s repairLiveMode w r) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R
        repairAllSourceProfileJobs (liveInactiveProfileCore i)) := by
  apply liveInactiveProfileBatch_ready p X hG hK active s repairLiveMode w R
    repairAllSourceProfileJobs repairAllSourceProfileJobs_nodup hfit
  intro r hr
  exact hbank r (fun j => hr j (repairAllSourceProfileJobs_complete j))

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
variable {Q A : ℕ} {P U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def repairAllSourceProfilesProgram (keySrc xSrc activity : Fin repairT) : Pr P T₀ Q A U :=
  .seq (liveSelectedProfilesProgram keySrc xSrc) (repairControlProfilesProgram activity)

theorem repairAllSourceProfiles_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (keySrc xSrc activity : Fin repairT) (hwidth : w.selectorBits = w.coordinateBits)
    (hwidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hk : p.K < 2 ^ w.strideBits) (hn : p.n < 2 ^ w.indexBits)
    (hw : p.wy + 2 * p.wc + X < 2 ^ w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hkey : S.R (liveZSourceActivity keySrc) = gatedSelectedSourceWords w.indexBits w.strideBits
      (List.ofFn (fun c => (s c).gatedChoice (active c))))
    (hxraw : S.R (liveZSourceActivity xSrc) = selectedSourceWords w.indexBits w.strideBits
      (List.ofFn (fun c => (s c).choice)))
    (hactivity : S.R (liveZSourceActivity activity) = (List.ofFn active).map bitSymbol)
    (hinput : ∀ j, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ liveSelectedProfilesCost p w + repairControlProfilesCost p w w.indexBits ∧
      Exec body (repairAllSourceProfilesProgram keySrc xSrc activity) (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairAllSourceProfileJobs }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := liveSelectedProfiles_exec body p X hG hK active s w
    keySrc xSrc hwidth hwidthFit hk hn hw v S hbank hkey hxraw (hinput 0) (hinput 9) hcount hscratch
  let G : Stacks T₀ A := { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R [0, 9] }
  have hpending := liveProfileBatch_pending p X hG hK active s repairLiveMode w S.R [0, 9]
    repairControlProfileJobs (by decide) (by
      intro r hr
      exact hbank r (fun j => hr j (repairAllSourceProfileJobs_complete j)))
  have haux (i : Fin 7) : G.R (liveInactiveProfileAux i) = S.R (liveInactiveProfileAux i) := by
    dsimp only [G]
    exact liveInactiveProfileBatch_keep p X hG hK active s repairLiveMode w S.R [0, 9] _
      (fun _ _ => liveInactiveProfileAux_core _ _)
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := repairLiveControlProfiles_exec p X hG hK active s w body activity
    w.indexBits hn hwidth v₁ G hfit (by intro r hr; dsimp only [G]; exact hpending r hr)
    (by
      intro j hj
      have hdis : ∀ j ∈ repairControlProfileJobs, j ∉ ([0, 9] : List (Fin 11)) := by decide
      dsimp only [G]
      rw [liveInactiveProfileBatch_keep p X hG hK active s repairLiveMode w S.R [0, 9] _ (by
        intro k hk
        apply liveInactiveProfileCore_injective.ne
        apply liveDescriptorAux_injective.ne
        intro he
        cases he
        exact hdis j hj hk)]
      exact hinput j)
    (by
      dsimp only [G]
      exact (liveInactiveProfileBatch_keep p X hG hK active s repairLiveMode w S.R [0, 9] _
        (fun j _ => liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux activity (.input j)))).trans hactivity)
    ((haux 0).trans hcount) (fun i hi => (haux i).trans (hscratch i hi))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, Nat.add_le_add hm₁ hm₂, ?_⟩
  rw [repairAllSourceProfileJobs, liveProfileBatchBank_append]
  dsimp only [G] at hx₂
  simp only [liveInactiveProfileBatchBank] at hx₂ ⊢
  exact Exec.seq hx₁ hx₂

end
end IntegerMultBounds.MathlibTM2.Routing
