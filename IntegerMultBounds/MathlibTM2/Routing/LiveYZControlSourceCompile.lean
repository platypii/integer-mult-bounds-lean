module

public import IntegerMultBounds.MathlibTM2.Routing.LiveYZControlSourceGenerate

/-! Compute the YZ control base, generate its full activity-dependent profile,
and erase the temporary base. Only the actual profile input changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section
variable {Q A : ℕ} {P U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveYZControlSourceCompileProgram (activity : Fin repairT) : Pr P T₀ Q A U :=
  .seq liveYZControlOffsetProgram
    (.seq (liveYZControlSourceProgram activity) (bclear (liveInactiveProfileAux 6)))

theorem liveYZControlSourceCompile_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (activity : Fin repairT) (hwidth : w.selectorBits = w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hinput : S.R liveYZControlSourceDst = [])
    (hactivity : S.R (liveZSourceActivity activity) = (List.ofFn active).map bitSymbol)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (8 * w.coordinateBits + 8) +
        (p.n * optionalAffineSourceIterationCost w.widthBits w.indexBits w.strideBits + 2 * p.n +
          2 * (p.n * (w.indexBits + w.strideBits + 3)) + 16 * w.indexBits + 22) +
        (2 * w.coordinateBits + 2) ∧
      Exec body (liveYZControlSourceCompileProgram activity) (mk v S) steps
        (mk v' { S with R := Function.update S.R liveYZControlSourceDst ((repairLiveMode 8).profileFrames p X hG hK active s w.selectorBits) }) := by
  obtain ⟨v₁, hu₁, hx₁⟩ := liveYZControlOffset_exec body p X hG hK active s w v S hfit hwidth hbank
    (hscratch 6 (by decide))
  let G : Stacks T₀ A := { S with R := Function.update S.R (liveInactiveProfileAux 6) (binSyms w.coordinateBits (p.wy + p.wc)) }
  have hkeep (r : LiveDescriptorRole 11) : G.R (e₀ (liveDescriptorAux r)) = S.R (e₀ (liveDescriptorAux r)) := by
    dsimp only [G]
    exact Function.update_of_ne (liveInactiveProfileCore_aux _ _) _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := liveYZControlSourceGenerate_exec p X hG hK active s w body activity
    hwidth v₁ G hfit (fun r hr => (hkeep r).trans (hbank r hr))
    ((hkeep (.input 8)).trans hinput)
    (by
      dsimp only [G]
      rw [Function.update_of_ne (liveZSourceActivity_aux activity 6)]
      exact hactivity)
    (by simp [G])
    (by
      intro i hi hi6
      dsimp only [G]
      rw [Function.update_of_ne (liveInactiveProfileAux_injective.ne hi6)]
      exact hscratch i hi)
  let out := (repairLiveMode 8).profileFrames (A := A) p X hG hK active s w.selectorBits
  let H : Stacks T₀ A := { G with R := Function.update G.R liveYZControlSourceDst out }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (liveInactiveProfileAux 6) v₂ H
  have hd : liveYZControlSourceDst ≠ liveInactiveProfileAux 6 := liveInactiveProfileCore_aux _ _
  have hbase : H.R (liveInactiveProfileAux 6) = binSyms w.coordinateBits (p.wy + p.wc) := by
    simp [H, G, hd.symm]
  have hf : Function.update H.R (liveInactiveProfileAux 6) [] = Function.update S.R liveYZControlSourceDst out := by
    funext j
    by_cases hj : j = liveInactiveProfileAux 6
    · subst j
      simp [hd.symm, hscratch 6 (by decide)]
    · by_cases hjd : j = liveYZControlSourceDst
      · subst j
        simp [H, G, hd]
      · simp [H, G, hj, hjd]
  rw [hf, hbase, length_binSyms] at hx₃
  refine ⟨v₃, (8 * w.coordinateBits + 8) + (m₂ + (2 * w.coordinateBits + 2)),
    hu₃.trans (hu₂.trans hu₁), by omega, ?_⟩
  exact Exec.seq hx₁ (Exec.seq hx₂ hx₃)

end
end IntegerMultBounds.MathlibTM2.Routing
