module

public import IntegerMultBounds.MathlibTM2.Routing.LiveCoordinateSourceGenerate

/-! Coordinate-stream compilation includes executed region-base setup and
cleanup. All raw inputs and non-output tapes are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def livePreparedCoordinateSourceProgram (src out : Fin repairT) : Pr P T₀ Q A U :=
  .seq liveSourceBasesProgram (.seq (liveCoordinateSourceProgram src out) liveSourceBasesCleanProgram)

def livePreparedCoordinateSourceCost (p : Par) (w : LiveDescriptorWidths) :=
  (p.n * sourceCoordinateIterationCost w.indexBits w.strideBits +
    2 * (p.n * (w.coordinateBits + 3)) + 2 * (p.n * (w.indexBits + w.coordinateBits + 5)) + 6) +
    (w.indexBits * (12 * w.coordinateBits + 20) + 48 * w.coordinateBits + 56)

theorem livePreparedCoordinateSourceGenerate_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy) (w : LiveDescriptorWidths)
    (src out : Fin repairT) (hso : src ≠ out)
    (hw : p.wy + 2 * p.wc < 2 ^ w.coordinateBits) (hk : p.K < 2 ^ w.strideBits)
    (hn : p.n < 2 ^ w.indexBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK (profileActive p hK targets)
        (profileSources p hK targets source) repairLiveMode w r)
    (hraw : S.R (liveZSourceActivity src) = sourceCoordinateInputWords w.indexBits w.strideBits
      (profileCoordinateInputs p hK targets source))
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ livePreparedCoordinateSourceCost p w ∧
      Exec body (livePreparedCoordinateSourceProgram src out) (mk v S) steps
        (mk v' { S with R := Function.update S.R (liveZSourceActivity out) (profileSourceRecords p hK X targets source w.indexBits w.strideBits ++ S.R (liveZSourceActivity out)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := liveSourceBases_exec body p X hG hK (profileActive p hK targets)
    (profileSources p hK targets source) w hn hk hw v S hbank hcount
    (hscratch 5 (by decide)) (hscratch 6 (by decide))
  let G : Stacks T₀ A := { S with R := liveSourceBasesBank S.R p w }
  have hcore (i : Fin (liveDescriptorT repairT 11)) : G.R (e₀ i) = S.R (e₀ i) :=
    liveSourceBasesBank_core S.R p w i
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := liveCoordinateSourceGenerate_exec body p X hG hK targets source w src out hso
    (by omega) hk v₁ G (fun r hr => (hcore _).trans (hbank r hr))
    (by simp [G, liveSourceBasesBank, liveInactiveProfileAux_injective.eq_iff])
    (by simpa only [liveZSourceActivity] using (hcore (liveDescriptorCore src)).trans hraw)
    (by
      intro i hi h5 h6
      simpa [G, liveSourceBasesBank, liveInactiveProfileAux_injective.eq_iff, hi, h5, h6] using hscratch i hi)
  let word := profileSourceRecords (A := A) p hK X targets source w.indexBits w.strideBits ++ S.R (liveZSourceActivity out)
  let R := Function.update S.R (liveZSourceActivity out) word
  let H : Stacks T₀ A := { S with R := Function.update G.R (liveZSourceActivity out) word }
  have hH : H.R = liveSourceBasesBank R p w := by
    dsimp only [H, R, liveZSourceActivity]
    exact liveSourceBasesBank_update S.R p w (liveDescriptorCore out) word
  have ho : G.R (liveZSourceActivity out) = S.R (liveZSourceActivity out) := hcore _
  rw [ho] at hx₂
  obtain ⟨v₃, hu₃, hx₃⟩ := liveSourceBasesClean_exec body R p w
    (by simp [R, liveZSourceActivity, liveInactiveProfileAux_core, hscratch 5 (by decide)])
    (by simp [R, liveZSourceActivity, liveInactiveProfileAux_core, hscratch 6 (by decide)]) v₂ H hH
  exact ⟨v₃, m₁ + (m₂ + (4 * w.coordinateBits + 4)), hu₃.trans (hu₂.trans hu₁),
    by unfold livePreparedCoordinateSourceCost; omega, Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end
end IntegerMultBounds.MathlibTM2.Routing
