module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalResidueStep

/-! Exact profile words produced in each residue round. The total family is empty
outside the residue range; this convention occurs only in the proof ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {A : ℕ}
noncomputable section

def canonicalResidueWord (n : ℕ) (hlarge : canonicalRouterStride n ≤ n)
    (second : Bool) (k : Fin 3) (reverse : Bool) (f : Equiv.Perm (Fin n))
    (r : Fin (canonicalRouterStride n)) : List (Fin (A + 4)) :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let H := routingReservoirWidth n (canonicalRouterGap n)
  let hfit := routingReservoir_fit n (canonicalRouterGap n) hlarge
  let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
  let hw := routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)
  let hsize : p.wy = n - 3 * w := routerProfileParameters_width n _ _ hlarge r
  let mate := permutationReservoirSource n H hfit w hw k second f p hsize
  let widths := canonicalStageWidths p
  sourceCoordinateInputWords widths.indexBits widths.strideBits
    (profileCoordinateInputs p (by
      change 0 < canonicalRouterStride n
      have hg := canonicalRouterGap_pos n
      change 0 < 64 * canonicalRouterGap n
      omega) (matchingDirectionTargets mate reverse) mate)

def canonicalResidueWords (n : ℕ) (hlarge : canonicalRouterStride n ≤ n)
    (second : Bool) (k : Fin 3) (reverse : Bool) (f : Equiv.Perm (Fin n)) (i : ℕ) : List (Fin (A + 4)) :=
  if h : i < canonicalRouterStride n then canonicalResidueWord n hlarge second k reverse f ⟨i,h⟩ else []

def canonicalResidueRoundCost (L n i : ℕ) : ℕ :=
  canonicalPermutationProfileCost L n (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) i) + 4 * L + 6

end
end IntegerMultBounds.MathlibTM2.Routing
