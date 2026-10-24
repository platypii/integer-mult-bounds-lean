module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingFixedTableResize
public import IntegerMultBounds.MathlibTM2.Routing.MatchingFixedProfile

/-! Compile profiles from a scalar-width matching table in the core. Actual
re-encoding installs the compiler table and erases it after the call. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {N Q A : ℕ} {P U : Type}

def matchingResizedProfileProgram (resize : Fin 2 → Fin N) (control count : Fin 3 → Fin N)
    (reverse : Bool) (dst : Fin N) : Pr P (N + 36) Q A U :=
  matchingTableResizeScope (matchingFixedTableResizeSlot resize) (matchingExtractSlot N 5)
    (matchingFixedProfileProgram control count reverse dst)

theorem matchingResizedProfile_exec (body : P → Pr P (N + 36) Q A U)
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
    (resize : Fin 2 → Fin N) (hresize : Function.Injective resize) (Mr Lin : ℕ)
    (hrawFit : p.wy < 2 ^ Lin) (htargetFit : Li + Lk < 2 ^ Mr)
    (htarget : coreWords (resize 0) = binSyms Mr (Li + Lk))
    (hraw : coreWords (resize 1) = matchingEntryWords Lin
      (matchingTableEntries p.wy (matchingMateCoordinate mate)))
    (dst : Fin N) (v : HS (N + 36) Q A U) (S : Stacks (N + 36) A)
    (hR : S.R = matchingProductionBank coreWords [] [] [] []) :
    ∃ (v' : HS (N + 36) Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ matchingPrefixCountCost Ln Ls Le + 24 * Le + 29 +
        matchingFullProfileProductionCost p (Li + Lk) Lk (Ln + Ls + Le) +
        2 * (Ln + Ls + Le) + 2 + 4 * M * (4 * Lk + 11) + 24 * Ls + 56 * Lk + 90 +
        p.wy * (4 * Mr * (4 * (Li + Lk) + 11) + 40 * Lin + 64 * (Li + Lk) + 122) + 8 ∧
      Exec body (matchingResizedProfileProgram resize control count reverse dst) (mk v S) m
        (mk v' { S with R := (Function.update S.R (matchingCoreEmbed N dst)
          (sourceCoordinateInputWords Li Lk
            (profileCoordinateInputs p hK (matchingDirectionTargets mate reverse) mate) ++ S.R (matchingCoreEmbed N dst))) }) := by
  let xs := matchingTableEntries p.wy (matchingMateCoordinate mate)
  let price := matchingPrefixCountCost Ln Ls Le + 24 * Le + 29 +
    matchingFullProfileProductionCost p (Li + Lk) Lk (Ln + Ls + Le) +
    2 * (Ln + Ls + Le) + 2 + 4 * M * (4 * Lk + 11) + 24 * Ls + 56 * Lk + 90
  let output := sourceCoordinateInputWords Li Lk
    (profileCoordinateInputs p hK (matchingDirectionTargets mate reverse) mate) ++ S.R (matchingCoreEmbed N dst)
  have core (j : Fin N) : S.R (matchingCoreEmbed N j) = coreWords j := by
    rw [hR, matchingProductionBank_core]
  have hfit : ∀ x ∈ xs, x.1 < 2 ^ Lin ∧ x.2 < 2 ^ Lin := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    have hq := List.mem_range.mp hq
    refine ⟨hq.trans hrawFit, ?_⟩
    change matchingMateCoordinate mate q < 2 ^ Lin
    simp only [matchingMateCoordinate, dite_eq_left hq]
    exact (mate ⟨q, hq⟩).isLt.trans hrawFit
  have hcall (u : HS (N + 36) Q A U) :
      let C : Stacks (N + 36) A := { S with R := Function.update S.R (matchingExtractSlot N 5) (matchingEntryWords (Li + Lk) xs) }
      ∃ (u' : HS (N + 36) Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body (matchingFixedProfileProgram control count reverse dst) (mk u C) m
          (mk u' { C with R := Function.update C.R (matchingCoreEmbed N dst) output }) := by
    dsimp only
    let C : Stacks (N + 36) A := { S with R := Function.update S.R (matchingExtractSlot N 5) (matchingEntryWords (Li + Lk) xs) }
    have hC : C.R = matchingProductionBank coreWords [] (matchingEntryWords (Li + Lk) xs) [] [] := by
      dsimp only [C]
      rw [hR, matchingProductionBank_update_table]
    obtain ⟨u', m, hu, hm, hex⟩ := matchingFixedProfile_exec body p mate hK hρ hinv reverse
      Li Lk Ln Le M Ls hwidth hk hn he hwidthFit hstrideFit control count hcontrol hcount coreWords
      hstride hresidue hcontrolWidth hrows hcountStride hcountWidth dst u C hC
    have keep : C.R (matchingCoreEmbed N dst) = S.R (matchingCoreEmbed N dst) :=
      Function.update_of_ne (matchingCoreEmbed_extract N dst 5) _ _
    rw [keep] at hex
    exact ⟨u', m, hu, hm, hex⟩
  obtain ⟨v', m, hu, hm, hex⟩ := matchingTableResizeScope_exec body
    (matchingFixedTableResizeSlot resize) (matchingFixedTableResizeSlot_injective resize hresize)
    (matchingExtractSlot N 5) (matchingFixedTableResizeSlot_table resize) Mr Lin (Li + Lk) htargetFit
    xs hfit v S ((core _).trans htarget) ((core _).trans hraw)
    (by intro j h0 h10; rw [hR]; exact matchingFixedTableResizeBlank resize _ _ _ _ _ j h0 h10)
    (by rw [hR]; simp [matchingProductionBank_extract, matchingWorkspaceWords])
    (matchingCoreEmbed N dst) (matchingCoreEmbed_extract N dst 5) output
    (matchingFixedProfileProgram control count reverse dst) price hcall
  refine ⟨v', m, hu, ?_, hex⟩
  simpa only [price, xs, matchingTableEntries, List.length_map, List.length_range] using hm

end
end IntegerMultBounds.MathlibTM2.Routing
