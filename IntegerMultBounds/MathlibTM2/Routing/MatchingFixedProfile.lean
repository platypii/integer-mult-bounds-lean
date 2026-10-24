module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingFixedCount
public import IntegerMultBounds.MathlibTM2.Routing.MatchingProfileCompactControls

/-! Executed profile compilation on the fixed production bank. Count and resized
controls are generated from compact core tapes and erased after compilation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {N Q A : ℕ} {P U : Type}

def matchingFixedProfileProgram (control count : Fin 3 → Fin N) (reverse : Bool)
    (dst : Fin N) : Pr P (N + 36) Q A U :=
  matchingControlScope (matchingFixedControlSlot control)
    (matchingPrefixCountScope (matchingFixedCountSlot count)
      (matchingFullProfileProductionProgram (matchingExtractSlot N) (matchingGatherSlot N)
        (matchingGenerateSlot N) reverse (matchingCoreEmbed N dst)))

theorem matchingFixedProfile_exec (body : P → Pr P (N + 36) Q A U)
    (p : Par) (mate : Fin p.wy → Fin p.wy)
    (hK : 0 < p.K) (hρ : p.ρ < p.K) (hinv : Function.Involutive mate) (reverse : Bool)
    (Li Lk Ln Le M Ls : ℕ) (hwidth : p.wy < 2 ^ (Li + Lk)) (hk : p.K < 2 ^ Lk)
    (hn : p.n < 2 ^ Ln) (he : 2 * (Li + Lk) + 2 < 2 ^ Le)
    (hwidthFit : Lk < 2 ^ M) (hstrideFit : p.K < 2 ^ Ls)
    (control count : Fin 3 → Fin N)
    (hcontrol : Function.Injective control) (hcount : Function.Injective count)
    (coreWords : Fin N → List (Fin (A + 4)))
    (hstride : coreWords (control 0) = binSyms Ls p.K)
    (hresidue : coreWords (control 1) = binSyms Ls p.ρ)
    (hcontrolWidth : coreWords (control 2) = binSyms M Lk)
    (hrows : coreWords (count 0) = binSyms Ln p.n)
    (hcountStride : coreWords (count 1) = binSyms Ls p.K)
    (hcountWidth : coreWords (count 2) = binSyms Le (Li + Lk))
    (dst : Fin N) (v : HS (N + 36) Q A U) (S : Stacks (N + 36) A)
    (hR : S.R = matchingProductionBank coreWords []
      (matchingEntryWords (Li + Lk) (matchingTableEntries p.wy (matchingMateCoordinate mate))) [] []) :
    ∃ (v' : HS (N + 36) Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ matchingPrefixCountCost Ln Ls Le + 24 * Le + 29 +
        matchingFullProfileProductionCost p (Li + Lk) Lk (Ln + Ls + Le) +
        2 * (Ln + Ls + Le) + 2 + 4 * M * (4 * Lk + 11) + 24 * Ls + 56 * Lk + 90 ∧
      Exec body (matchingFixedProfileProgram control count reverse dst) (mk v S) m
        (mk v' { S with R := (Function.update S.R (matchingCoreEmbed N dst)
          (sourceCoordinateInputWords Li Lk
            (profileCoordinateInputs p hK (matchingDirectionTargets mate reverse) mate) ++ S.R (matchingCoreEmbed N dst))) }) := by
  let C : Stacks (N + 36) A :=
    { S with R := matchingControlBank S.R (matchingFixedControlSlot control) Lk p.K p.ρ }
  have hC : C.R = matchingControlBank
      (matchingProductionBank coreWords []
        (matchingEntryWords (Li + Lk) (matchingTableEntries p.wy (matchingMateCoordinate mate))) [] [])
      (matchingFixedControlSlot control) Lk p.K p.ρ := by
    dsimp only [C]
    rw [hR]
  let frame := matchingFixedControlFrame control p mate hK hρ hinv reverse Li Lk
    (Ln + Ls + Le) hwidth hk coreWords dst C hC
  have core (j : Fin N) : S.R (matchingCoreEmbed N j) = coreWords j := by
    rw [hR, matchingProductionBank_core]
  apply matchingProfileCompactControls_exec body p mate Li Lk Ln Le M Ls v S
    (matchingCoreEmbed N dst) (matchingFixedControlSlot control)
    (matchingFixedControlSlot_injective control hcontrol)
    ((core _).trans hstride) ((core _).trans hresidue) ((core _).trans hcontrolWidth)
    hwidthFit hstrideFit
    (by intro j h0 h1 h7; rw [hR]; exact matchingFixedControlBlank control _ _ _ j h0 h1 h7)
    ⟨matchingCoreEmbed_gather N dst 1, matchingCoreEmbed_gather N dst 11⟩ frame
    rfl rfl (matchingFixedCountSlot count) (matchingFixedCountSlot_injective count hcount)
    (matchingFixedCountSlot_controls count) rfl (matchingCoreEmbed_extract N dst 0)
    matchingFixedCount_gather matchingFixedCount_generate hn he
    ((core _).trans hrows) ((core _).trans hcountStride) ((core _).trans hcountWidth)
    (by intro j h0 h1 h10 h11; rw [hR]; exact matchingFixedCountBlank count _ _ j h0 h1 h10 h11)

end
end IntegerMultBounds.MathlibTM2.Routing
