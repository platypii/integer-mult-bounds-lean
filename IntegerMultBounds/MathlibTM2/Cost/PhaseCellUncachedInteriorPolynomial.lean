module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellUncachedInteriorComparison

/-! The constructor's extra weight generation is linear in axis volume and
quartic in a common numerical width; cached arithmetic is kept separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloInteriorCostBound_weights_poly {s t : ℕ} [NeZero s]
    (p l u target rhsExp a b Z : ℕ) (hst : s < t) (hZ : 1 ≤ Z)
    (hP : 2^15*p ≤ Z) (hN : executionStagePrecision p l target rhsExp+1 ≤ Z)
    (hq : executionPrecision p l target rhsExp ≤ Z) (hl : l ≤ Z) (hu : u ≤ Z)
    (hw : executionWidth p l target rhsExp ≤ Z)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ Z)
    (hkeys : ∀ L ∈ haloLengthCandidates s t (PhaseCellBand.width p u) a b, L ≤ Z) :
    haloInteriorCostBound p l s t u target rhsExp a b ≤
      familyHaloInteriorGeometryCost p l s t u target rhsExp a b+10000000*t*Z^4 := by
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth P q w t u
  let keys := haloLengthCandidates s t band a b
  let extra := fun L => sharedBatchWeightSetupCost P s t u q L w 0+1000*(P+N+q+l+w+1)
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hlen : keys.length = 6 := by simp [keys,haloLengthCandidates,naturalLengthCandidates]
  have hsmall : 1000*(P+N+q+l+w+1) ≤ 6000*Z := by
    dsimp only [P,N,q,w]; omega
  have hweight : ∀ L ∈ keys, extra L ≤ 1000000*t*Z^4+6000*Z := by
    intro L hL
    have hc := sharedBatchWeightSetupCost_poly hZ ht hst.le (Nat.zero_le t) hP hu hq (hkeys L hL) hw hV
    exact Nat.add_le_add hc hsmall
  have hsum := List.sum_le_length_nsmul (keys.map extra) (1000000*t*Z^4+6000*Z) (by
    intro x hx
    obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hx
    exact hweight L hL)
  have hsum' : (keys.map extra).sum ≤ 6*(1000000*t*Z^4+6000*Z) := by
    simpa only [List.length_map,hlen,nsmul_eq_mul,Nat.cast_ofNat] using hsum
  have hp2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have hp3 : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  have hp4 : Z^3 ≤ Z^4 := by nlinarith only [Nat.mul_le_mul_left (Z^3) hZ]
  have htable : tblC V w ≤ 808*Z^2 := by
    have hsquare := Nat.pow_le_pow_left (show V+4 ≤ 5*Z by dsimp only [V,P,q,w]; omega) 2
    unfold tblC
    nlinarith only [hsquare,hw,hp2]
  have hcoord : (310*P+124)*tblC V w+92*w+45 ≤ 400000*Z^3 := by
    have hc : (310*P+124)*tblC V w+92*w+45 ≤ (310*Z+124)*(808*Z^2)+92*Z+45 := by gcongr
    nlinarith only [hc,hZ,hp2,hp3]
  have hcell : 3*tblC V w+8*V+200 ≤ 3000*Z^2 := by
    nlinarith only [htable,hV,hZ,hp2]
  have hcoords := Nat.mul_le_mul hst.le hcoord
  have hphases : t-s+1 ≤ t := by have := NeZero.pos s; omega
  have hcells := Nat.mul_le_mul hphases hcell
  have htZ := Nat.mul_le_mul_left t hp2
  have htZ2 := Nat.mul_le_mul_left t hp3
  have htZ3 := Nat.mul_le_mul_left t hp4
  have hZt := Nat.mul_le_mul_left (Z^4) ht
  have hc := haloInteriorCostBound_cached_le (s := s) (t := t) p l u target rhsExp a b
  dsimp only at hc
  dsimp only [keys,extra,P,N,q,w,band,V] at hsum' hcoords hcells
  nlinarith only [hc,hsum',hcoords,hcells,hZ,ht,hp2,hp3,hp4,htZ,htZ2,htZ3,hZt]

end IntegerMultBounds.MathlibTM2.Cost
