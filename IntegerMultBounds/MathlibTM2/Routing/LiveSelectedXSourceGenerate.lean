module

public import IntegerMultBounds.MathlibTM2.Routing.LiveSelectedSourceLayout
public import IntegerMultBounds.MathlibTM2.Routing.RepairSharedXSourceGenerate

/-! Generate the first X profile in the existing shared bank. The two remaining
region bases are explicit setup operands; all borrowed tapes are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveSelectedXSourceProgram (src : Fin repairT) : Pr P T₀ Q A U :=
  sharedSelectedSourceGenerateProgram liveSelectedSourceReg (liveZSourceActivity src)
    (liveInactiveProfileAux 2) (liveSelectedSourceReg 0 0) (liveSelectedSourceReg 0 3)
    (liveInactiveProfileAux 3) (liveInactiveProfileAux 1) (liveInactiveProfileAux 4)
    (e₀ (liveDescriptorAux (.input 9)))

theorem liveSelectedXSourceGenerate_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (src : Fin repairT) (hwidth : w.selectorBits = w.coordinateBits)
    (hk : p.K < 2 ^ w.strideBits) (hn : p.n ≤ 2 ^ w.indexBits)
    (hw : p.wy + 2 * p.wc + X < 2 ^ w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hraw : S.R (liveZSourceActivity src) = gatedSelectedSourceWords w.indexBits w.strideBits
      (List.ofFn (fun c => (s c).gatedChoice (active c))))
    (hinput : S.R (e₀ (liveDescriptorAux (.input 9))) = [])
    (hscratch : ∀ i : Fin 7, i ≠ 0 → i ≠ 5 → i ≠ 6 → S.R (liveInactiveProfileAux i) = [])
    (hhigh : S.R (liveInactiveProfileAux 5) = binSyms w.coordinateBits (p.ρ + p.n * p.K))
    (hspectator : S.R (liveInactiveProfileAux 6) = binSyms w.coordinateBits (p.wy + 2 * p.wc)) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ p.n * sharedSelectedSourceIterationCost w.indexBits w.strideBits +
        2 * (p.n * (w.indexBits + w.coordinateBits + 5)) + 2 * (p.n * (w.coordinateBits + 3)) + 6 ∧
      Exec body (liveSelectedXSourceProgram src) (mk v S) steps
        (mk v' { S with R := Function.update S.R (e₀ (liveDescriptorAux (.input 9))) ((repairLiveMode 9).profileFrames p X hG hK active s w.selectorBits) }) := by
  have hrdata (r : Fin 13) : S.R (e₀ (liveDescriptorAux (selectedScratchRole r))) =
      liveDescriptorData p X hG hK active s repairLiveMode w (selectedScratchRole r) :=
    hbank _ (by intro j; fin_cases r <;> simp [selectedScratchRole])
  have hb (tag : Fin 4) (r : Fin 13) (h1 : r ≠ 1) (h2 : r ≠ 2) :
      S.R (liveSelectedSourceReg tag r) = [] := by
    simp only [liveSelectedSourceReg, ite_eq_right h2]
    rw [hrdata, selectedScratchRole_data p X hG hK active s w r h1 h2]
  obtain ⟨v', steps, hu, ht, hx⟩ := repairSharedXSourceGenerate_exec body p X hG hK active s
    liveSelectedSourceReg liveSelectedSourceReg_injective (liveZSourceActivity src)
    (liveInactiveProfileAux 2) (liveSelectedSourceReg 0 0) (liveSelectedSourceReg 0 3)
    (liveInactiveProfileAux 3) (liveInactiveProfileAux 1) (liveInactiveProfileAux 4)
    (e₀ (liveDescriptorAux (.input 9)))
    (by simp [List.nodup_cons, liveSelectedSourceReg, selectedScratchRole, liveZSourceActivity,
      liveInactiveProfileAux_injective.eq_iff, liveInactiveProfileAux_core, liveInactiveProfileCore_aux,
      liveInactiveProfileCore_injective.eq_iff, liveDescriptorAux_injective.eq_iff, liveDescriptorCore_aux])
    (liveSelectedSourceRaw_reg src)
    (fun tag r => liveSelectedSourceAux_separate 2 (by decide) (by decide) tag r)
    (fun tag => by simp [liveSelectedSourceReg, selectedScratchRole])
    (fun tag => by simp [liveSelectedSourceReg, selectedScratchRole])
    (fun tag r => liveSelectedSourceAux_separate 1 (by decide) (by decide) tag r)
    (fun tag r => liveSelectedSourceAux_separate 4 (by decide) (by decide) tag r)
    w.indexBits w.strideBits hk hn hw v S hraw
    (hb 0 0 (by decide) (by decide)) (hb 0 3 (by decide) (by decide))
    (hscratch 3 (by decide) (by decide) (by decide))
    (hscratch 1 (by decide) (by decide) (by decide))
    (by intro tag; simpa [liveSelectedSourceReg, selectedScratchRole] using
      (hrdata 1).trans (selectedSourceStride p X hG hK active s w))
    (by
      intro tag
      fin_cases tag
      · simpa [liveSelectedSourceReg, SlotSource.regionBase, LiveDescriptorWidths.coordinateBits] using
          (hbank (.base 9) (by simp)).trans (selectedSourceBase_zero p X hG hK active s w)
      · simpa [liveSelectedSourceReg, SlotSource.regionBase, LiveDescriptorWidths.coordinateBits] using
          (hbank (.base 0) (by simp)).trans (selectedSourceBase_rho p X hG hK active s w)
      · simpa [liveSelectedSourceReg, SlotSource.regionBase, LiveDescriptorWidths.coordinateBits] using hhigh
      · simpa [liveSelectedSourceReg, SlotSource.regionBase, LiveDescriptorWidths.coordinateBits] using hspectator)
    (fun tag r _ h1 h2 _ => hb tag r h1 h2)
    (hscratch 2 (by decide) (by decide) (by decide))
    (hscratch 4 (by decide) (by decide) (by decide))
  refine ⟨v', steps, hu, ht, ?_⟩
  have hmode : repairLiveMode 9 = LiveDescriptorMode.ofKey (some (.X, 0)) := rfl
  simpa only [liveSelectedXSourceProgram, hinput, List.append_nil, hwidth,
    LiveDescriptorWidths.coordinateBits, hmode] using hx

end
end IntegerMultBounds.MathlibTM2.Routing
