module

public import IntegerMultBounds.MathlibTM2.Routing.LiveYSourceLayout
public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorArithmeticWidths

/-! Generate the first Y profile directly in its live input tape, borrowing
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

def liveYSourceProgram : Pr P T₀ Q A U :=
  binaryAffineSourceGenerateProgram liveYSourceReg (liveInactiveProfileAux 0) (liveInactiveProfileAux 2)
    (liveInactiveProfileAux 3) (liveInactiveProfileAux 1) liveYSourceDst (liveInactiveProfileAux 4)

theorem liveYSource_ready (R : Fin T₀ → List (Fin (A + 4)))
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, r ≠ .input 5 → R (e₀ (liveDescriptorAux r)) =
      liveDescriptorData p X hG hK active s repairLiveMode w r) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => Function.update R liveYSourceDst
        ((repairLiveMode 5).profileFrames p X hG hK active s w.selectorBits) (e₀ i)) :=
  liveInactiveProfile_ready p X hG hK active s repairLiveMode w R 5 hfit hbank

theorem liveYSourceGenerate_exec (body : P → Pr P T₀ Q A U) (Lc : ℕ) (hn : p.n < 2 ^ Lc)
    (hwidth : w.selectorBits = w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, r ≠ .input 5 → S.R (e₀ (liveDescriptorAux r)) =
      liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hinput : S.R liveYSourceDst = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ binaryAffineSourceGenerateCost Lc w.indexBits w.strideBits p.n ∧
      Exec body liveYSourceProgram (mk v S) steps
        (mk v' { S with R := Function.update S.R liveYSourceDst ((repairLiveMode 5).profileFrames p X hG hK active s w.selectorBits) }) := by
  have hrdata (r : Fin 12) : S.R (liveYSourceReg r) =
      liveDescriptorData p X hG hK active s repairLiveMode w (liveYSourceRole r) :=
    hbank _ (by fin_cases r <;> simp [liveYSourceRole])
  have hk : p.K < 2 ^ w.strideBits := (hfit 0).stride_fits
  have hi : p.n ≤ 2 ^ w.indexBits := (hfit 5).slots_fit
  have hwy : p.wy < 2 ^ (w.indexBits + w.strideBits) := by
    have h := (hfit 5).source_fits
    rw [hwidth] at h
    change p.wy + 2 * p.wc + X + 1 < 2 ^ (w.indexBits + w.strideBits) at h
    omega
  obtain ⟨v', steps, hu, ht, hx⟩ := repairYSourceGenerate_exec body p X hG hK active s liveYSourceReg
    liveYSourceReg_injective (liveInactiveProfileAux 0) (liveInactiveProfileAux 2) (liveInactiveProfileAux 3)
    (liveInactiveProfileAux 1) liveYSourceDst (liveInactiveProfileAux 4)
    (by simp [List.nodup_cons, liveInactiveProfileAux_injective.eq_iff, liveYSourceDst,
      liveInactiveProfileAux_core, liveInactiveProfileCore_aux])
    (liveYSourceAux_separate 0) (liveYSourceAux_separate 2) (liveYSourceAux_separate 3)
    (liveYSourceAux_separate 1) liveYSourceDst_separate (liveYSourceAux_separate 4)
    Lc w.indexBits w.strideBits hn hk hi hwy v S hcount
    (hrdata 0) (hrdata 1) (hrdata 2)
    (hscratch 2 (by decide)) (hscratch 3 (by decide)) (hscratch 1 (by decide)) (hscratch 4 (by decide))
    (by
      intro r h0 h1 h2
      rw [hrdata]
      fin_cases r <;> simp_all [liveYSourceRole, liveDescriptorData])
  refine ⟨v', steps, hu, ht, ?_⟩
  have hmode : repairLiveMode 5 = LiveDescriptorMode.ofKey (some (.Y, 0)) := rfl
  simpa only [liveYSourceProgram, hmode, hinput, List.append_nil, hwidth, LiveDescriptorWidths.coordinateBits] using hx

end
end IntegerMultBounds.MathlibTM2.Routing
