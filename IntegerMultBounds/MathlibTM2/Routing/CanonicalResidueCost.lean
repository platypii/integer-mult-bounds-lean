module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalResidueGenerated

/-! A residue-independent arithmetic ledger for actual profile generation.
Every row/slot/coordinate count is bounded by dimension and every descriptor
operand width by the canonical gap. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def canonicalPreparedProfileBound (L n G : ℕ) : ℕ :=
  matchingPrefixCountCost L L L + 24 * L + 29 +
    matchingFullProfileProductionBound n G G (L + L + L) +
    2 * (L + L + L) + 2 + 4 * L * (4 * G + 11) + 24 * L + 56 * G + 90 +
    n * (4 * L * (4 * G + 11) + 40 * L + 64 * G + 122) + 8

theorem canonicalPreparedProfileCost_le (L n : ℕ) (hlarge : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    canonicalPreparedProfileCost L p ≤ canonicalPreparedProfileBound L n (canonicalRouterGap n) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  have hrows : p.n ≤ n := by
    change (n - canonicalRouterStride n) / (canonicalRouterStride n + 3 * canonicalRouterGap n) ≤ n
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hslots : p.n * p.K ≤ n := by
    have h := routerGeometry_decomposition n (canonicalRouterStride n) (canonicalRouterGap n) hlarge
    change routerDigits n (canonicalRouterStride n) (canonicalRouterGap n) * canonicalRouterStride n ≤ n
    omega
  have hsource : p.wy ≤ n := by
    dsimp only [p]
    rw [routerProfileParameters_width n _ _ hlarge r]
    exact Nat.sub_le _ _
  obtain ⟨hi, hg, hs, hsel, hw⟩ := canonicalStageWidths_router n hlarge r
  have hcoord : (canonicalStageWidths p).indexBits + (canonicalStageWidths p).strideBits ≤ canonicalRouterGap n := by
    dsimp only [p]
    rw [hi, hs]
    have h := canonicalDescriptorCoordinateWidth_le_gap n
    omega
  have hstride : (canonicalStageWidths p).strideBits ≤ canonicalRouterGap n := by omega
  have hfull := matchingFullProfileProductionCost_le_bound p n
    ((canonicalStageWidths p).indexBits + (canonicalStageWidths p).strideBits)
    (canonicalStageWidths p).strideBits (L + L + L)
    (canonicalRouterGap n) (canonicalRouterGap n) (L + L + L)
    hrows hslots hcoord hstride le_rfl
  change canonicalPreparedProfileCost L p ≤ _
  unfold canonicalPreparedProfileCost canonicalPreparedProfileBound
  dsimp only
  gcongr

def canonicalResidueRoundBound (L n : ℕ) : ℕ :=
  permutationMatchingTableBinaryCost n L + reservoirClassLocalTableCost n 0 L +
    682 * L + 765 + 2 * (n * (2 * L + 2)) + 2 +
    canonicalPreparedProfileBound L n (canonicalRouterGap n) +
    2 * (n * (2 * L + 2)) + 2 + 96 * L * L + 584 * L + 549 + 4 * L + 6

theorem canonicalResidueRoundCost_le (L n : ℕ) (hlarge : canonicalRouterStride n ≤ n)
    (i : ℕ) (hi : i < canonicalRouterStride n) :
    canonicalResidueRoundCost L n i ≤ canonicalResidueRoundBound L n := by
  have hp := canonicalPreparedProfileCost_le L n hlarge ⟨i,hi⟩
  have ht := reservoirClassLocalTableCost_le n
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) L L le_rfl
  have hn : n - 3 * routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) ≤ n := Nat.sub_le _ _
  unfold canonicalResidueRoundCost canonicalPermutationProfileCost canonicalResidueRoundBound
  dsimp only at hp ⊢
  gcongr

def canonicalResidueTotalBound (L n : ℕ) : ℕ :=
  canonicalRouterStride n * (canonicalResidueRoundBound L n + 12) + 4 * L * L + 129 * L + 192

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {Q A : ℕ} {P U : Type}
noncomputable section

theorem canonicalResidueUniform_exec (body : P → Pr P 163 Q A U)
    (L n : ℕ) (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (second : Bool) (k : Fin 3) (reverse : Bool) (f : Equiv.Perm (Fin n))
    (core : Fin 126 → List (Fin (A + 4))) (hdimension : core 57 = binSyms L n)
    (htable : core 85 = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate f)))
    (hblank : ∀ j : Fin 126, j.val < 98 → j ≠ 57 → j ≠ 70 → j ≠ 84 → j ≠ 85 → core j = [])
    (hgeometry : ∀ j : Fin 28, j ≠ 0 → j ≠ 9 → j ≠ 18 → core (canonicalPermutationGeometrySlot j) = [])
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (v : HS 163 Q A U) (S : Stacks 163 A)
    (hR : (embStk canonicalResidueCoreSlot S).R = matchingProductionBank core [] [] [] [])
    (hcount : S.R 107 = []) (hsaved : S.R 162 = []) (hindex : S.R 116 = []) :
    let profile := canonicalResidueWords n hlarge second k reverse f
    ∃ (v' : HS 163 Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalResidueTotalBound L n ∧
      Exec body (canonicalResidueGeneratedProgram second k reverse) (mk v S) m
        (mk v' { S with R := (Function.update S.R 98
          (indexedCountOutput profile (canonicalRouterStride n) ++ S.R 98)) }) := by
  exact canonicalResidueGenerated_exec body L n hn hlarge second k reverse f core hdimension htable
    hblank hgeometry hdivisor (canonicalResidueRoundBound L n) (canonicalResidueRoundCost_le L n hlarge)
    v S hR hcount hsaved hindex

end

end IntegerMultBounds.MathlibTM2.Routing
