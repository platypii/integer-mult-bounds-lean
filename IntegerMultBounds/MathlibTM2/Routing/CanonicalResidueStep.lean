module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPermutationProfile
public import IntegerMultBounds.MathlibTM2.Routing.IndexedCountStep

/-! One actual residue round compiles its permutation profile, advances the
binary residue and archives one count symbol. The extra archive is outside the
compiler bank; count and output occupy unused core registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}

def canonicalResidueCoreSlot : Fin 162 → Fin 163 := Fin.castLE (by decide)
theorem canonicalResidueCoreSlot_injective : Function.Injective canonicalResidueCoreSlot := by decide +kernel

def canonicalResidueStepProgram (second : Bool) (k : Fin 3) (reverse : Bool) : Pr P 163 Q A U :=
  indexedCountStepProgram 107 162 116 126 70
    (embProg canonicalResidueCoreSlot Empty.elim
      (canonicalPermutationProfileProgram (P := Empty) second k reverse 98))

theorem canonicalResidueStep_exec (body : P → Pr P 163 Q A U)
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
    (c : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (v : HS 163 Q A U) (S : Stacks 163 A) (hcount : S.R 107 = c :: rest)
    (hR : (embStk canonicalResidueCoreSlot S).R = matchingProductionBank R [] [] [] []) :
    let H := routingReservoirWidth n (canonicalRouterGap n)
    let hfit := routingReservoir_fit n (canonicalRouterGap n) hlarge
    let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
    let hw := routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)
    let hsize : p.wy = n - 3 * w := by subst p; exact routerProfileParameters_width n _ _ hlarge r
    let mate := permutationReservoirSource n H hfit w hw k second f p hsize
    let widths := canonicalStageWidths p
    let output := sourceCoordinateInputWords widths.indexBits widths.strideBits
      (profileCoordinateInputs p (by subst p; exact (canonicalProfileFits L n hn hlarge r).1)
        (matchingDirectionTargets mate reverse) mate) ++ S.R 98
    ∃ (v' : HS 163 Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalPermutationProfileCost L n p + 4 * L + 6 ∧
      Exec body (canonicalResidueStepProgram second k reverse) (mk v S) m
        (mk v' { S with R := indexedCountStepBank S.R 107 162 116 98 L r.val c rest output }) := by
  dsimp only
  have core (j : Fin 126) : S.R (canonicalResidueCoreSlot (matchingCoreEmbed 126 j)) = R j := by
    change (embStk canonicalResidueCoreSlot S).R (matchingCoreEmbed 126 j) = _
    rw [hR, matchingProductionBank_core]
  have htmp : S.R 126 = [] := by
    change (embStk canonicalResidueCoreSlot S).R (matchingExtractSlot 126 0) = _
    rw [hR]
    simp [matchingProductionBank_extract, matchingWorkspaceWords]
  apply indexedCountStep_exec body 107 162 116 98 126 70 (by decide +kernel) L r.val c rest _ _
    (canonicalPermutationProfileCost L n p) v S hcount ((core 116).trans hresidue) htmp
  intro u
  let smallBody : Empty → Pr Empty 162 Q A U := Empty.elim
  obtain ⟨u₁, m, hu₁, hm, hex⟩ := canonicalPermutationProfile_exec smallBody L n hn hlarge r p hp second k reverse
    f R hdimension hresidue htable hblank hgeometry hdivisor 98 (by decide) (by decide +kernel)
    (embDn canonicalResidueCoreSlot u) (embStk canonicalResidueCoreSlot S) hR
  obtain ⟨u₂, hu₂, hex₂⟩ := exec_emb_stream canonicalResidueCoreSlot canonicalResidueCoreSlot_injective
    Empty.elim smallBody body (by intro q; exact q.elim) (canonicalPermutationProfileProgram second k reverse 98)
    u S u₁ m (matchingCoreEmbed 126 98) _ hex
  exact ⟨u₂, m, hu₂.trans hu₁, hm, hex₂⟩

end
end IntegerMultBounds.MathlibTM2.Routing
