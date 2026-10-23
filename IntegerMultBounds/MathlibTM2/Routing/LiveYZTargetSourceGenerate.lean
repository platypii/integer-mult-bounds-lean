module

public import IntegerMultBounds.MathlibTM2.Routing.LiveYSourceLayout
public import IntegerMultBounds.MathlibTM2.Routing.RepairYZTargetSourceGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorArithmeticWidths

/-! Generate the first YZ profile directly in its live input tape, borrowing
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

def liveYZTargetSourceDst : Fin T₀ := e₀ (liveDescriptorAux (.input 7))

theorem liveYZTargetSourceDst_separate (r : Fin 12) : liveYZTargetSourceDst ≠ liveYSourceReg r := by
  apply liveInactiveProfileCore_injective.ne
  apply liveDescriptorAux_injective.ne
  fin_cases r <;> simp [liveYSourceRole]

def liveYZTargetSourceProgram : Pr P T₀ Q A U :=
  binaryAffineSourceGenerateProgram liveYSourceReg (liveInactiveProfileAux 0) (liveInactiveProfileAux 2)
    (liveInactiveProfileAux 3) (liveInactiveProfileAux 1) liveYZTargetSourceDst (liveInactiveProfileAux 4)

theorem liveYZTargetSource_ready (R : Fin T₀ → List (Fin (A + 4)))
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, r ≠ .input 7 → R (e₀ (liveDescriptorAux r)) =
      liveDescriptorData p X hG hK active s repairLiveMode w r) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => Function.update R liveYZTargetSourceDst
        ((repairLiveMode 7).profileFrames p X hG hK active s w.selectorBits) (e₀ i)) :=
  liveInactiveProfile_ready p X hG hK active s repairLiveMode w R 7 hfit hbank

theorem liveYZTargetSourceGenerate_exec (body : P → Pr P T₀ Q A U) (Lc : ℕ) (hn : p.n < 2 ^ Lc)
    (hwidth : w.selectorBits = w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) → S.R (e₀ (liveDescriptorAux r)) =
      liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hinput : S.R liveYZTargetSourceDst = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ binaryAffineSourceGenerateCost Lc w.indexBits w.strideBits p.n ∧
      Exec body liveYZTargetSourceProgram (mk v S) steps
        (mk v' { S with R := Function.update S.R liveYZTargetSourceDst ((repairLiveMode 7).profileFrames p X hG hK active s w.selectorBits) }) := by
  have hrdata (r : Fin 12) : S.R (liveYSourceReg r) =
      liveDescriptorData p X hG hK active s repairLiveMode w (liveYSourceRole r) :=
    hbank _ (by intro j; fin_cases r <;> simp [liveYSourceRole])
  have hk : p.K < 2 ^ w.strideBits := (hfit 0).stride_fits
  have hi : p.n ≤ 2 ^ w.indexBits := (hfit 7).slots_fit
  have hwy : p.wy < 2 ^ (w.indexBits + w.strideBits) := by
    have h := (hfit 7).source_fits
    rw [hwidth] at h
    change p.wy + 2 * p.wc + X + 1 < 2 ^ (w.indexBits + w.strideBits) at h
    omega
  obtain ⟨v', steps, hu, ht, hx⟩ := repairYZTargetSourceGenerate_exec body p X hG hK active s liveYSourceReg
    liveYSourceReg_injective (liveInactiveProfileAux 0) (liveInactiveProfileAux 2) (liveInactiveProfileAux 3)
    (liveInactiveProfileAux 1) liveYZTargetSourceDst (liveInactiveProfileAux 4)
    (by simp [List.nodup_cons, liveInactiveProfileAux_injective.eq_iff, liveYZTargetSourceDst,
      liveInactiveProfileAux_core, liveInactiveProfileCore_aux])
    (liveYSourceAux_separate 0) (liveYSourceAux_separate 2) (liveYSourceAux_separate 3)
    (liveYSourceAux_separate 1) liveYZTargetSourceDst_separate (liveYSourceAux_separate 4)
    Lc w.indexBits w.strideBits hn hk hi hwy v S hcount
    (hrdata 0) (hrdata 1) (hrdata 2)
    (hscratch 2 (by decide)) (hscratch 3 (by decide)) (hscratch 1 (by decide)) (hscratch 4 (by decide))
    (by
      intro r h0 h1 h2
      rw [hrdata]
      fin_cases r <;> simp_all [liveYSourceRole, liveDescriptorData])
  refine ⟨v', steps, hu, ht, ?_⟩
  have hmode : repairLiveMode 7 = LiveDescriptorMode.ofKey (some (.YZ, 0)) := rfl
  simpa only [liveYZTargetSourceProgram, hmode, hinput, List.append_nil, hwidth, LiveDescriptorWidths.coordinateBits] using hx

end
end IntegerMultBounds.MathlibTM2.Routing
