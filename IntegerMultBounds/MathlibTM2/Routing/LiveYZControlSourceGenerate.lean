module

public import IntegerMultBounds.MathlibTM2.Routing.LiveYZControlSourceLayout
public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorArithmeticWidths

/-! Generate the YZ control profile directly in its live input tape, borrowing
existing arithmetic scratch and the same seven outer tapes as inactive jobs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {Q A : ℕ} {P U : Type}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)

local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveYZControlSourceProgram (activity : Fin repairT) : Pr P T₀ Q A U :=
  optionalAffineSourceGenerateProgram liveYZControlSourceReg liveZSourceZeroReg (liveZSourceActivity activity)
    (liveInactiveProfileAux 3) (liveInactiveProfileAux 1) liveYZControlSourceDst (liveInactiveProfileAux 4)

theorem liveYZControlSource_ready (R : Fin T₀ → List (Fin (A + 4)))
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, r ≠ .input 8 → R (e₀ (liveDescriptorAux r)) =
      liveDescriptorData p X hG hK active s repairLiveMode w r) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => Function.update R liveYZControlSourceDst
        ((repairLiveMode 8).profileFrames p X hG hK active s w.selectorBits) (e₀ i)) :=
  liveInactiveProfile_ready p X hG hK active s repairLiveMode w R 8 hfit hbank

theorem liveYZControlSourceGenerate_exec (body : P → Pr P T₀ Q A U) (activity : Fin repairT) (hwidth : w.selectorBits = w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) → S.R (e₀ (liveDescriptorAux r)) =
      liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hinput : S.R liveYZControlSourceDst = [])
    (hactivity : S.R (liveZSourceActivity activity) = (List.ofFn active).map bitSymbol)
    (hbase : S.R (liveInactiveProfileAux 6) = binSyms w.coordinateBits (p.wy + p.wc))
    (hscratch : ∀ i : Fin 7, i ≠ 0 → i ≠ 6 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ p.n * optionalAffineSourceIterationCost w.widthBits w.indexBits w.strideBits + 2 * p.n +
        2 * (p.n * (w.indexBits + w.strideBits + 3)) + 16 * w.indexBits + 22 ∧
      Exec body (liveYZControlSourceProgram activity) (mk v S) steps
        (mk v' { S with R := Function.update S.R liveYZControlSourceDst ((repairLiveMode 8).profileFrames p X hG hK active s w.selectorBits) }) := by
  have hrdata (r : Fin 12) (hr : r ≠ 2) : S.R (liveYZControlSourceReg r) =
      liveDescriptorData p X hG hK active s repairLiveMode w (liveZSourceRole r) := by
    rw [liveYZControlSourceReg, Function.update_of_ne hr]
    dsimp only [liveZSourceReg]
    exact hbank _ (by intro j; fin_cases r <;> simp [liveZSourceRole])
  have hzdata (r : BinaryZeroReg) : S.R (liveZSourceZeroReg r) =
      liveDescriptorData p X hG hK active s repairLiveMode w (liveZSourceZeroRole r) :=
    hbank _ (by intro j; cases r <;> simp [liveZSourceZeroRole])
  have hk : p.G < 2 ^ w.strideBits := (hfit 5).stride_fits
  have hi : p.n ≤ 2 ^ w.indexBits := (hfit 8).slots_fit
  have hcontrol : p.wy + 2 * p.wc ≤ 2 ^ (w.indexBits + w.strideBits) := by
    have h := (hfit 8).source_fits
    rw [hwidth] at h
    change p.wy + 2 * p.wc + X + 1 < 2 ^ (w.indexBits + w.strideBits) at h
    omega
  obtain ⟨v', steps, hu, ht, hx⟩ := repairYZControlSourceGenerate_exec body p X hG hK active s
    liveYZControlSourceReg liveYZControlSourceReg_injective liveZSourceZeroReg liveZSourceZeroReg_injective
    (by simpa only [liveYZControlSourceReg, Function.update_of_ne (by decide : (5 : Fin 12) ≠ 2)] using liveZSourceZeroReg_dst) (liveZSourceActivity activity) (liveInactiveProfileAux 3)
    (liveInactiveProfileAux 1) liveYZControlSourceDst (liveInactiveProfileAux 4)
    (by simp [List.nodup_cons, liveInactiveProfileAux_injective.eq_iff, liveYZControlSourceDst,
      liveInactiveProfileAux_core, liveInactiveProfileCore_aux, liveZSourceActivity, liveInactiveProfileCore_injective.eq_iff,
      liveDescriptorCore_aux])
    (liveYZControlSourceActivity_reg activity) (liveYZControlSourceAux_separate 3 (by decide)) (liveYZControlSourceAux_separate 1 (by decide))
    liveYZControlSourceDst_separate (liveYZControlSourceAux_separate 4 (by decide))
    (liveZSourceActivity_zero activity) (liveZSourceAux_zero 3) (liveZSourceAux_zero 1)
    (liveZSourceAux_zero 4) (by simpa only [liveYZControlSourceReg, Function.update_of_ne (by decide : (0 : Fin 12) ≠ 2)] using liveZSourceZeroReg_index)
    w.widthBits w.indexBits w.strideBits
    (by
      have h := (hfit 8).selector_fits
      rw [hwidth] at h
      exact h)
    hk hi hcontrol v S hactivity (hrdata 0 (by decide)) (hrdata 1 (by decide)) hbase
    (hscratch 3 (by decide) (by decide)) (hscratch 1 (by decide) (by decide)) (hscratch 4 (by decide) (by decide))
    (by
      intro r h0 h1 h2
      rw [hrdata r h2]
      fin_cases r <;> simp_all [liveZSourceRole, liveDescriptorData])
    (by simpa only [liveZSourceZeroRole, liveDescriptorData, hwidth,
      LiveDescriptorWidths.coordinateBits] using hzdata .width)
    (hzdata .unary) (fun r => hzdata (.scratch r))
  refine ⟨v', steps, hu, ht, ?_⟩
  have hmode : repairLiveMode 8 = LiveDescriptorMode.ofKey (some (.YZ, 1)) := rfl
  simpa only [liveYZControlSourceProgram, hmode, hinput, List.append_nil, hwidth,
    LiveDescriptorWidths.coordinateBits] using hx

end
end IntegerMultBounds.MathlibTM2.Routing
