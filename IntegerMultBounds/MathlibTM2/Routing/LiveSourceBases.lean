module

public import IntegerMultBounds.MathlibTM2.Routing.LiveHighSourceBase
public import IntegerMultBounds.MathlibTM2.Routing.LiveSpectatorBase

/-! Generate both selected-source region bases in the shared outer workspace.
The original count and every live descriptor operand are preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveSourceBasesProgram : Pr P T₀ Q A U :=
  .seq liveHighSourceBaseProgram liveSpectatorBaseProgram

def liveSourceBasesBank (R : Fin T₀ → List (Fin (A + 4))) (p : Par) (w : LiveDescriptorWidths) :=
  Function.update (Function.update R (liveInactiveProfileAux 5)
    (binSyms w.coordinateBits (p.ρ + p.n * p.K))) (liveInactiveProfileAux 6)
    (binSyms w.coordinateBits (p.wy + 2 * p.wc))

theorem liveSourceBases_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (hn : p.n < 2 ^ w.indexBits) (hk : p.K < 2 ^ w.strideBits)
    (hfit : p.wy + 2 * p.wc < 2 ^ w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (hhigh : S.R (liveInactiveProfileAux 5) = [])
    (hspectator : S.R (liveInactiveProfileAux 6) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ w.indexBits * (12 * w.coordinateBits + 20) + 44 * w.coordinateBits + 52 ∧
      Exec body liveSourceBasesProgram (mk v S) steps
        (mk v' { S with R := liveSourceBasesBank S.R p w }) := by
  have hhfit : p.ρ + p.n * p.K < 2 ^ w.coordinateBits := by
    have hy : p.wy = p.ρ + p.n * p.K + p.m := rfl
    omega
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := liveHighSourceBase_exec body p X hG hK active s w
    hn hk hhfit v S hbank hcount hhigh
  let G : Stacks T₀ A := { S with R := Function.update S.R (liveInactiveProfileAux 5) (binSyms w.coordinateBits (p.ρ + p.n * p.K)) }
  obtain ⟨v₂, hu₂, hx₂⟩ := liveSpectatorBase_exec body p X hG hK active s w hfit v₁ G
    (by intro r hr; simpa [G, liveInactiveProfileCore_aux] using hbank r hr)
    (by simpa [G, liveInactiveProfileAux_injective.eq_iff] using hspectator)
  exact ⟨v₂, m₁ + (18 * w.coordinateBits + 18), hu₂.trans hu₁, by omega, Exec.seq hx₁ hx₂⟩

theorem liveSourceBasesBank_core (R : Fin T₀ → List (Fin (A + 4)))
    (p : Par) (w : LiveDescriptorWidths) (i : Fin (liveDescriptorT repairT 11)) :
    liveSourceBasesBank R p w (e₀ i) = R (e₀ i) := by
  simp [liveSourceBasesBank, liveInactiveProfileCore_aux]

theorem liveSourceBasesBank_update (R : Fin T₀ → List (Fin (A + 4)))
    (p : Par) (w : LiveDescriptorWidths) (i : Fin (liveDescriptorT repairT 11))
    (word : List (Fin (A + 4))) :
    Function.update (liveSourceBasesBank R p w) (e₀ i) word =
      liveSourceBasesBank (Function.update R (e₀ i) word) p w := by
  funext j
  by_cases h : j = e₀ i
  · subst j; simp [liveSourceBasesBank, liveInactiveProfileCore_aux]
  · simp [liveSourceBasesBank, Function.update_apply, h]

def liveSourceBasesCleanProgram : Pr P T₀ Q A U :=
  .seq (bclear (liveInactiveProfileAux 5)) (bclear (liveInactiveProfileAux 6))

theorem liveSourceBasesClean_bank (R : Fin T₀ → List (Fin (A + 4)))
    (p : Par) (w : LiveDescriptorWidths)
    (hhigh : R (liveInactiveProfileAux 5) = []) (hspectator : R (liveInactiveProfileAux 6) = []) :
    Function.update (Function.update (liveSourceBasesBank R p w) (liveInactiveProfileAux 5) [])
      (liveInactiveProfileAux 6) [] = R := by
  funext j
  by_cases h5 : j = liveInactiveProfileAux 5
  · subst j; simp [liveSourceBasesBank, liveInactiveProfileAux_injective.eq_iff, hhigh]
  · by_cases h6 : j = liveInactiveProfileAux 6
    · subst j; simp [hspectator]
    · simp [liveSourceBasesBank, h5, h6]

theorem liveSourceBasesClean_exec (body : P → Pr P T₀ Q A U)
    (R : Fin T₀ → List (Fin (A + 4))) (p : Par) (w : LiveDescriptorWidths)
    (hhigh : R (liveInactiveProfileAux 5) = []) (hspectator : R (liveInactiveProfileAux 6) = [])
    (v : HS T₀ Q A U) (S : Stacks T₀ A) (hbank : S.R = liveSourceBasesBank R p w) :
    ∃ (v' : HS T₀ Q A U), v'.user = v.user ∧
      Exec body liveSourceBasesCleanProgram (mk v S) (4 * w.coordinateBits + 4)
        (mk v' { S with R := R }) := by
  obtain ⟨v₁, hu₁, _, hx₁⟩ := bclear_exec body (liveInactiveProfileAux 5) v S
  let G : Stacks T₀ A := { S with R := Function.update S.R (liveInactiveProfileAux 5) [] }
  obtain ⟨v₂, hu₂, _, hx₂⟩ := bclear_exec body (liveInactiveProfileAux 6) v₁ G
  have h5 : (S.R (liveInactiveProfileAux 5)).length = w.coordinateBits := by
    simp [hbank, liveSourceBasesBank, liveInactiveProfileAux_injective.eq_iff]
  have h6 : (G.R (liveInactiveProfileAux 6)).length = w.coordinateBits := by
    simp [G, hbank, liveSourceBasesBank, liveInactiveProfileAux_injective.eq_iff]
  have hf : Function.update G.R (liveInactiveProfileAux 6) [] = R := by
    dsimp only [G]
    rw [hbank]
    exact liveSourceBasesClean_bank R p w hhigh hspectator
  rw [h5] at hx₁
  rw [h6, hf] at hx₂
  exact ⟨v₂, hu₂.trans hu₁, Exec.cast (Exec.seq hx₁ hx₂) (by omega) rfl⟩

end
end IntegerMultBounds.MathlibTM2.Routing
