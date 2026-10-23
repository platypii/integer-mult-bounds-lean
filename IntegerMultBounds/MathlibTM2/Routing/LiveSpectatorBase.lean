module

public import IntegerMultBounds.MathlibTM2.Routing.BinarySpectatorBase
public import IntegerMultBounds.MathlibTM2.Routing.LiveSelectedSourceLayout

/-! Generate the spectator base in outer tape 6 from the existing live Y and
control row counts. No additional scalar input is required. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveSpectatorBaseRole : Fin 8 → LiveDescriptorRole 11 :=
  ![.rows 0, .rows 5, .coordinate .target, .archive,
    .profile (.coordinate (.arithmetic .tx)), .profile (.coordinate (.arithmetic .ty)),
    .profile (.coordinate (.arithmetic .tz)), .profile .loadTmp]

def liveSpectatorBaseReg (r : Fin 8) : Fin T₀ :=
  if r = 3 then liveInactiveProfileAux 6 else e₀ (liveDescriptorAux (liveSpectatorBaseRole r))

theorem liveSpectatorBaseReg_injective : Function.Injective liveSpectatorBaseReg := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [liveSpectatorBaseReg, liveSpectatorBaseRole, liveInactiveProfileAux_core,
      liveInactiveProfileCore_aux, liveInactiveProfileCore_injective.eq_iff,
      liveDescriptorAux_injective.eq_iff]

variable {Q A : ℕ} {P U : Type}

def liveSpectatorBaseProgram : Pr P T₀ Q A U := binarySpectatorBaseProgram liveSpectatorBaseReg

theorem liveSpectatorBase_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (hfit : p.wy + 2 * p.wc < 2 ^ w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (houtput : S.R (liveInactiveProfileAux 6) = []) :
    ∃ (v' : HS T₀ Q A U), v'.user = v.user ∧
      Exec body liveSpectatorBaseProgram (mk v S) (18 * w.coordinateBits + 18)
        (mk v' { S with R := Function.update S.R (liveInactiveProfileAux 6) (binSyms w.coordinateBits (p.wy + 2 * p.wc)) }) := by
  have hr (r : Fin 8) : S.R (e₀ (liveDescriptorAux (liveSpectatorBaseRole r))) =
      liveDescriptorData p X hG hK active s repairLiveMode w (liveSpectatorBaseRole r) :=
    hbank _ (by intro j; fin_cases r <;> simp [liveSpectatorBaseRole])
  have hy : repairCompactRows p (repairLiveMode 0).key = p.wy := rfl
  have hc : repairCompactRows p (repairLiveMode 5).key = p.wc := rfl
  obtain ⟨v', hu, hx⟩ := binarySpectatorBase_exec body liveSpectatorBaseReg liveSpectatorBaseReg_injective
    w.coordinateBits p.wy p.wc hfit v S
    (by simpa [liveSpectatorBaseReg, liveSpectatorBaseRole, liveDescriptorData, hy] using hr 0)
    (by simpa [liveSpectatorBaseReg, liveSpectatorBaseRole, liveDescriptorData, hc] using hr 1)
    (by
      intro r h0 h1 h7
      fin_cases r <;>
        simp_all [liveSpectatorBaseReg, liveSpectatorBaseRole, liveDescriptorData])
  have hd : liveSpectatorBaseReg 3 = liveInactiveProfileAux 6 := by simp [liveSpectatorBaseReg]
  rw [hd] at hx
  exact ⟨v', hu, hx⟩

end
end IntegerMultBounds.MathlibTM2.Routing
