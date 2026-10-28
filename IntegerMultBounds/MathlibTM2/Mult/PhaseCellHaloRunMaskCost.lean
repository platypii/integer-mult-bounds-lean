module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedHaloRunMask

/-! A coarse compatibility bound; the actual ledger retains the phase/output split. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem closedHaloRunMaskCost_le (s t band a b : ℕ) :
    closedHaloRunMaskCost s t band a b ≤
      4000*(s+t+band+a+b+1)*(publicationGeometryWidth t band+4)^2 := by
  let W := publicationGeometryWidth t band
  let H := s+t+band+a+b+1
  let N := t-s+1
  let R := 2*(haloRunIntervals s t band a b).length+1
  let D := (W+4)^2
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hN : N ≤ H := by dsimp [N,H]; omega
  have hR : R ≤ 3*H := by
    have := haloRunIntervals_length_le s t band a b
    dsimp [R,N,H] at *
    omega
  have hsum : s+t+band+a+b ≤ H := by dsimp [H]; omega
  have hs : s ≤ H := by dsimp [H]; omega
  have htband : t+band ≤ H := by dsimp [H]; omega
  have hD : 16 ≤ D := by dsimp [D]; nlinarith only [Nat.zero_le (W^2),Nat.zero_le W]
  have h8 : 8*W+8 ≤ D := by dsimp [D]; nlinarith only [Nat.zero_le (W^2),Nat.zero_le W]
  have h4 : 4*W+10 ≤ D := by dsimp [D]; nlinarith only [Nat.zero_le (W^2),Nat.zero_le W]
  have h2 : 2*W+4 ≤ D := by dsimp [D]; nlinarith only [Nat.zero_le (W^2),Nat.zero_le W]
  have h19 : 19*W+22 ≤ 3*D := by dsimp [D]; nlinarith only [Nat.zero_le (W^2),Nat.zero_le W]
  have hlinear : 396*W+554 ≤ 100*H*D := by
    have h : 396*W+554 ≤ 100*D := by dsimp [D]; nlinarith only [Nat.zero_le (W^2),Nat.zero_le W]
    exact h.trans (by nlinarith only [Nat.mul_le_mul_left (100*D) hH])
  have htable : (40*N+13)*(64*D+8*W+8) ≤ 3445*H*D := by
    calc
      _ ≤ (53*H)*(65*D) := by gcongr <;> omega
      _ = _ := by ring
  have hload : 2*(s+t+band+a+b)*(4*W+10) ≤ 2*H*D := by gcongr
  have hpairs : R*(2*W+4) ≤ 3*H*D := by gcongr
  have houtput : 10*s ≤ H*D := by
    nlinarith only [hs,Nat.mul_le_mul_left H hD]
  have hscan : (19*W+22)*(2*N+1) ≤ 9*H*D := by
    calc
      _ ≤ (3*D)*(3*H) := by gcongr <;> omega
      _ = _ := by ring
  have hgeometry : 38*(t+band) ≤ 3*H*D := by
    nlinarith only [htband,Nat.mul_le_mul_left H hD]
  have heq : closedHaloRunMaskCost s t band a b =
      (396*W+554)+38*(t+band)+2*(s+t+band+a+b)*(4*W+10)+
        (40*N+13)*(64*D+8*W+8)+R*(2*W+4)+10*s+(19*W+22)*(2*N+1) := by
    simp [closedHaloRunMaskCost,haloRunMaskFromHeadersCost,haloRunsFromHeadersCost,
      haloRunEmissionWidth,setHaloRunEmissionWidthCost,generatePublicationWidthCost,tblC,W,N,R,D]
    ring
  rw [heq]
  change _ ≤ 4000*H*D
  nlinarith only [hlinear,htable,hload,hpairs,houtput,hscan,hgeometry]

theorem closedHaloRunMaskCost_halo_le {s t band a b : ℕ}
    (hst : s ≤ t) (hband : band ≤ s) (ha : a ≤ s) (hb : b ≤ s) :
    closedHaloRunMaskCost s t band a b ≤ 4000*(5*t+1)*(4*Nat.size t+11)^2 := by
  have hsize : Nat.size band ≤ Nat.size t := Nat.size_le_size (hband.trans hst)
  have hwidth : publicationGeometryWidth t band+4 ≤ 4*Nat.size t+11 := by
    dsimp [publicationGeometryWidth]; omega
  have hcount : s+t+band+a+b+1 ≤ 5*t+1 := by omega
  exact (closedHaloRunMaskCost_le s t band a b).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 4000 hcount) (Nat.pow_le_pow_left hwidth 2))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
