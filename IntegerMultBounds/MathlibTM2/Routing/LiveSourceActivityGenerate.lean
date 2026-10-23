module

public import IntegerMultBounds.MathlibTM2.Routing.SourceActivityGenerate
public import IntegerMultBounds.MathlibTM2.Routing.LiveSelectedSourceLayout

/-! Derive the live activity stream from canonical source records, restoring
raw input and every borrowed workspace tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveSourceActivityProgram (src activity : Fin repairT) : Pr P T₀ Q A U :=
  sourceActivityGenerateProgram (liveZSourceActivity src) (liveInactiveProfileAux 2)
    (liveSelectedSourceReg 0 0) (liveSelectedSourceReg 0 3) (liveInactiveProfileAux 3)
    (liveInactiveProfileAux 4) (liveZSourceActivity activity)

theorem sourceActivityWord_encoded (p : Par) (X : ℕ) (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) :
    sourceActivityWord (A := A) (List.ofFn (fun c => (s c).gatedChoice (active c))) =
      (List.ofFn active).map bitSymbol := by
  simp only [sourceActivityWord, List.map_ofFn]
  rfl

theorem liveSourceActivityGenerate_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (src activity : Fin repairT) (hsa : src ≠ activity)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hraw : S.R (liveZSourceActivity src) = gatedSelectedSourceWords w.indexBits w.strideBits
      (List.ofFn (fun c => (s c).gatedChoice (active c))))
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U), v'.user = v.user ∧
      Exec body (liveSourceActivityProgram src activity) (mk v S)
        (p.n * (6 * w.indexBits + 6 * w.coordinateBits + 19) +
          2 * (p.n * (w.indexBits + w.coordinateBits + 5)) + 2 * p.n + 6)
        (mk v' { S with R := Function.update S.R (liveZSourceActivity activity) ((List.ofFn active).map bitSymbol ++ S.R (liveZSourceActivity activity)) }) := by
  have hr (r : Fin 13) : S.R (e₀ (liveDescriptorAux (selectedScratchRole r))) =
      liveDescriptorData p X hG hK active s repairLiveMode w (selectedScratchRole r) :=
    hbank _ (by intro j; fin_cases r <;> simp [selectedScratchRole])
  have hb (r : Fin 13) (h1 : r ≠ 1) (h2 : r ≠ 2) : S.R (liveSelectedSourceReg 0 r) = [] := by
    simp only [liveSelectedSourceReg, ite_eq_right h2]
    rw [hr, selectedScratchRole_data p X hG hK active s w r h1 h2]
  obtain ⟨v', hu, hx⟩ := sourceActivityGenerate_exec body (liveZSourceActivity src)
    (liveInactiveProfileAux 2) (liveSelectedSourceReg 0 0) (liveSelectedSourceReg 0 3)
    (liveInactiveProfileAux 3) (liveInactiveProfileAux 4) (liveZSourceActivity activity)
    (by simp [List.nodup_cons, liveZSourceActivity, liveSelectedSourceReg, selectedScratchRole,
      liveInactiveProfileAux_injective.eq_iff, liveInactiveProfileAux_core,
      liveInactiveProfileCore_injective.eq_iff, liveDescriptorCore_injective.eq_iff,
      liveDescriptorAux_injective.eq_iff, liveDescriptorCore_aux, hsa, eq_comm])
    w.indexBits w.strideBits (List.ofFn (fun c => (s c).gatedChoice (active c))) v S hraw
    (hb 0 (by decide) (by decide)) (hb 3 (by decide) (by decide))
    (hscratch 3 (by decide)) (hscratch 2 (by decide)) (hscratch 4 (by decide))
  rw [sourceActivityWord_encoded p X active s] at hx
  refine ⟨v', hu, ?_⟩
  simpa only [liveSourceActivityProgram, List.length_ofFn, LiveDescriptorWidths.coordinateBits] using hx

end
end IntegerMultBounds.MathlibTM2.Routing
