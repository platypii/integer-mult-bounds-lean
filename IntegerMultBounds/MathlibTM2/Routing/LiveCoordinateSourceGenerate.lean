module

public import IntegerMultBounds.MathlibTM2.Routing.LiveCoordinateSourceLayout

/-! Compile logical bulk-profile coordinates on the actual live repair bank.
All input and workspace tapes restore; only the canonical source stream grows. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveCoordinateSourceProgram (src out : Fin repairT) : Pr P T₀ Q A U :=
  sourceCoordinateGenerateProgram liveCoordinateSourceReg (liveZSourceActivity src)
    (liveInactiveProfileAux 2) (liveInactiveProfileAux 3) (liveInactiveProfileAux 4) (liveZSourceActivity out)

theorem liveCoordinateSourceGenerate_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy) (w : LiveDescriptorWidths)
    (src out : Fin repairT) (hso : src ≠ out)
    (hw : p.wy < 2 ^ w.coordinateBits) (hk : p.K < 2 ^ w.strideBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK (profileActive p hK targets)
        (profileSources p hK targets source) repairLiveMode w r)
    (hhigh : S.R (liveInactiveProfileAux 5) = binSyms w.coordinateBits (p.ρ + p.n * p.K))
    (hraw : S.R (liveZSourceActivity src) = sourceCoordinateInputWords w.indexBits w.strideBits
      (profileCoordinateInputs p hK targets source))
    (hscratch : ∀ i : Fin 7, i ≠ 0 → i ≠ 5 → i ≠ 6 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ p.n * sourceCoordinateIterationCost w.indexBits w.strideBits +
        2 * (p.n * (w.coordinateBits + 3)) + 2 * (p.n * (w.indexBits + w.coordinateBits + 5)) + 6 ∧
      Exec body (liveCoordinateSourceProgram src out) (mk v S) steps
        (mk v' { S with R := Function.update S.R (liveZSourceActivity out) (profileSourceRecords p hK X targets source w.indexBits w.strideBits ++ S.R (liveZSourceActivity out)) }) := by
  have hsetup := liveCoordinateSourceSetup p X hG hK (profileActive p hK targets)
    (profileSources p hK targets source) w S hbank hhigh
  obtain ⟨v', steps, hu, ht, hx⟩ := profileCoordinateGenerate_exec body liveCoordinateSourceReg
    liveCoordinateSourceReg_injective (liveZSourceActivity src) (liveInactiveProfileAux 2)
    (liveInactiveProfileAux 3) (liveInactiveProfileAux 4) (liveZSourceActivity out)
    (by simp [List.nodup_cons, liveZSourceActivity, liveInactiveProfileCore_aux, liveInactiveProfileAux_core,
      liveInactiveProfileAux_injective.eq_iff, liveInactiveProfileCore_injective.eq_iff,
      liveDescriptorCore_injective.eq_iff, hso])
    (liveCoordinateSourceRaw_separate src)
    (liveCoordinateSourceAux_separate 2 (by decide)) (liveCoordinateSourceAux_separate 3 (by decide))
    (liveCoordinateSourceAux_separate 4 (by decide))
    p hK X w.indexBits w.strideBits targets source hw hk v S hsetup hraw
    (hscratch 3 (by decide) (by decide) (by decide))
    (by
      simpa [liveCoordinateSourceReg, liveCoordinateSourceRole, liveDescriptorData] using
        hbank (.coordinate .dst) (by simp))
    (hscratch 2 (by decide) (by decide) (by decide)) (hscratch 4 (by decide) (by decide) (by decide))
  exact ⟨v', steps, hu, ht, hx⟩

end
end IntegerMultBounds.MathlibTM2.Routing
