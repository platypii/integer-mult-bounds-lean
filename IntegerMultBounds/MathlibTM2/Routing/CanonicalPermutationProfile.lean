module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPermutationCompile

/-! From original dimension, residue and permutation table to a compiled profile.
Canonical geometry, matching tables and compiler controls are generated and erased;
every register except the profile output restores. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}

def canonicalPermutationProfileProgram (second : Bool) (k : Fin 3) (reverse : Bool)
    (dst : Fin 126) : Pr P 162 Q A U :=
  canonicalProfileScope (matchingCoreEmbed 126 ∘ canonicalPermutationGeometrySlot)
    (canonicalPermutationCompileProgram second k reverse dst)

theorem canonicalPermutationProfile_exec (body : P → Pr P 162 Q A U)
    (L n : ℕ) (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (p : Par)
    (hp : p = routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
    (second : Bool) (k : Fin 3) (reverse : Bool) (f : Equiv.Perm (Fin n))
    (R : Fin 126 → List (Fin (A + 4))) (hdimension : R 57 = binSyms L n)
    (hresidue : R 116 = binSyms L r.val)
    (htable : R 85 = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate f)))
    (hblank : ∀ j : Fin 126, j.val < 98 → j ≠ 57 → j ≠ 70 → j ≠ 84 → j ≠ 85 → R j = [])
    (hgeometry : ∀ j : Fin 28, j ≠ 0 → j ≠ 9 → j ≠ 18 → R (canonicalPermutationGeometrySlot j) = [])
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (dst : Fin 126) (hdst : dst ≠ 34) (hoff : dst ∉ canonicalProfileTargets canonicalPermutationGeometrySlot) (v : HS 162 Q A U) (S : Stacks 162 A)
    (hR : S.R = matchingProductionBank R [] [] [] []) :
    let H := routingReservoirWidth n (canonicalRouterGap n)
    let hfit := routingReservoir_fit n (canonicalRouterGap n) hlarge
    let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
    let hw := routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)
    let hsize : p.wy = n - 3 * w := by subst p; exact routerProfileParameters_width n _ _ hlarge r
    let mate := permutationReservoirSource n H hfit w hw k second f p hsize
    let widths := canonicalStageWidths p
    ∃ (v' : HS 162 Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ permutationMatchingTableBinaryCost n L + reservoirClassLocalTableCost n w L +
        682 * L + 765 + 2 * (n * (2 * L + 2)) + 2 + canonicalPreparedProfileCost L p +
        2 * ((n - 3 * w) * (2 * L + 2)) + 2 + 96 * L * L + 584 * L + 549 ∧
      Exec body (canonicalPermutationProfileProgram second k reverse dst) (mk v S) m
        (mk v' { S with R := (Function.update S.R (matchingCoreEmbed 126 dst)
          (sourceCoordinateInputWords widths.indexBits widths.strideBits
            (profileCoordinateInputs p (by subst p; exact (canonicalProfileFits L n hn hlarge r).1)
              (matchingDirectionTargets mate reverse) mate) ++ S.R (matchingCoreEmbed 126 dst))) }) := by
  dsimp only
  have core (j : Fin 126) : S.R (matchingCoreEmbed 126 j) = R j := by
    rw [hR, matchingProductionBank_core]
  have hoff' : matchingCoreEmbed 126 dst ∉
      canonicalProfileTargets (matchingCoreEmbed 126 ∘ canonicalPermutationGeometrySlot) := by
    simpa [canonicalProfileTargets, (matchingCoreEmbed_injective 126).eq_iff] using hoff
  apply canonicalProfileScope_exec body (matchingCoreEmbed 126 ∘ canonicalPermutationGeometrySlot)
    ((matchingCoreEmbed_injective 126).comp canonicalPermutationGeometrySlot_injective)
    L n r.val hn hlarge hdivisor r.isLt v S ((core 57).trans hdimension) ((core 116).trans hresidue)
    (fun j h0 h9 h18 => (core _).trans (hgeometry j h0 h9 h18))
    (matchingCoreEmbed 126 dst) hoff' _ _ _ _
  intro u
  let C : Stacks 162 A := { S with R := (canonicalProfileSetupBank S.R
    (matchingCoreEmbed 126 ∘ canonicalPermutationGeometrySlot) L n r.val) }
  have hC : C.R = matchingProductionBank
      (canonicalProfileSetupBank R canonicalPermutationGeometrySlot L n r.val) [] [] [] [] := by
    dsimp only [C]
    rw [hR, canonicalProfileSetupBank_production]
  obtain ⟨u', m, hu, hm, hex⟩ := canonicalPermutationCompile_exec body L n hn hlarge r p hp second k reverse
    f R hdimension hresidue htable hblank dst hdst u C hC
  have keep : C.R (matchingCoreEmbed 126 dst) = S.R (matchingCoreEmbed 126 dst) :=
    canonicalProfileSetupBank_keep S.R (matchingCoreEmbed 126 ∘ canonicalPermutationGeometrySlot)
      L n r.val _ hoff'
  rw [keep] at hex
  exact ⟨u', m, hu, hm, hex⟩

end
end IntegerMultBounds.MathlibTM2.Routing
