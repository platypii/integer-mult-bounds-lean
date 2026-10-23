module

public import IntegerMultBounds.MathlibTM2.Routing.LiveATemporarySourceLayout
public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorArithmeticWidths

/-! Directly generate the second A profile from the live control-row count.
No added scalar operand or precomputed source profile is supplied. -/

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

def liveATemporarySourceProgram : Pr P T₀ Q A U :=
  binaryCounterSourceGenerateProgram liveATemporarySourceReg liveATemporarySourceCount
    (liveInactiveProfileAux 2) (liveInactiveProfileAux 3) (liveInactiveProfileAux 1)
    liveATemporarySourceDst (liveInactiveProfileAux 4)

theorem liveATemporarySourceGenerate_exec (body : P → Pr P T₀ Q A U)
    (hwidth : w.selectorBits = w.coordinateBits) (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hinput : S.R liveATemporarySourceDst = [])
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ binaryCounterSourceGenerateCost w.coordinateBits w.coordinateBits p.wc ∧
      Exec body liveATemporarySourceProgram (mk v S) steps
        (mk v' { S with R := Function.update S.R liveATemporarySourceDst ((repairLiveMode 2).profileFrames p X hG hK active s w.selectorBits) }) := by
  have hrdata (r : Fin 5) : S.R (liveATemporarySourceReg r) =
      liveDescriptorData p X hG hK active s repairLiveMode w (liveATemporarySourceRole r) :=
    hbank _ (by intro j; fin_cases r <;> simp [liveATemporarySourceRole])
  have hc : S.R liveATemporarySourceCount = binSyms w.coordinateBits p.wc :=
    hbank (.rows 5) (by intro j; simp)
  obtain ⟨v', steps, hu, ht, hx⟩ := repairATemporarySourceGenerate_exec body p X hG hK active s
    liveATemporarySourceReg liveATemporarySourceReg_injective liveATemporarySourceCount
    (liveInactiveProfileAux 2) (liveInactiveProfileAux 3) (liveInactiveProfileAux 1)
    liveATemporarySourceDst (liveInactiveProfileAux 4)
    (by simp [List.nodup_cons, liveATemporarySourceCount, liveATemporarySourceDst,
      liveInactiveProfileAux_injective.eq_iff, liveInactiveProfileCore_aux,
      liveInactiveProfileAux_core, liveInactiveProfileCore_injective.eq_iff,
      liveDescriptorAux_injective.eq_iff])
    liveATemporarySourceCount_separate
    (fun _ => liveInactiveProfileAux_core _ _) (fun _ => liveInactiveProfileAux_core _ _)
    (fun _ => liveInactiveProfileAux_core _ _) liveATemporarySourceDst_separate
    (fun _ => liveInactiveProfileAux_core _ _) w.coordinateBits w.coordinateBits
    (hfit 5).coordinate_fits v S hc (hrdata 0)
    (hscratch 2 (by decide)) (hscratch 3 (by decide)) (hscratch 1 (by decide)) (hscratch 4 (by decide))
    (by
      intro r hr
      rw [hrdata]
      fin_cases r <;> simp_all [liveATemporarySourceRole, liveDescriptorData])
  refine ⟨v', steps, hu, ht, ?_⟩
  have hmode : repairLiveMode 2 = LiveDescriptorMode.ofKey (some (.A, 1)) := rfl
  simpa only [liveATemporarySourceProgram, hmode, hwidth, hinput, List.append_nil] using hx

end
end IntegerMultBounds.MathlibTM2.Routing
