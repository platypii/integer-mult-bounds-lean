module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellLengthKeySetup

/-! Shared origin classification and advance setup retain only sparse quadratic geometry work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem sharedHaloControls_le (P q s t u band a b L : ℕ) :
    let w := 2*q+8
    let G := haloGeometryWidth t w
    let V := weightWorkspaceWidth P q w t u
    let H := P+q+u+s+t+band+a+b+L+1
    haloOriginControlsSharedCost P q s t u band a b L+advanceControlsSharedCost G s w ≤
      (36*(t-s+1)+9)*tblC G G+2000*H*(G+w+V+1) := by
  let w := 2*q+8
  let G := haloGeometryWidth t w
  let V := weightWorkspaceWidth P q w t u
  let H := P+q+u+s+t+band+a+b+L+1
  let R := G+w+V+1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hinputs : s+t+band+a+b+L+w ≤ 9*H := by dsimp [H,w]; omega
  have hgeometry : 4*G+10 ≤ 10*R := by dsimp [R]; omega
  have hheaders := Nat.mul_le_mul hinputs hgeometry
  have hflat : 25*w+8*q+4*P+95*t+19*u+463 ≤ 800*H := by dsimp [H,w]; omega
  have hGV : 284*G+4*V ≤ 284*R := by dsimp [R]; omega
  have hHp : H ≤ H*R := Nat.le_mul_of_pos_right _ hR
  have hRp : R ≤ H*R := Nat.le_mul_of_pos_left _ hH
  have hlinear : 284*G+25*w+8*q+4*P+95*t+19*u+4*V+463 ≤ 1200*H*R := by
    nlinarith only [hflat,hGV,hHp,hRp]
  have hs : s ≤ H := by dsimp [H]; omega
  have hw : w ≤ R := by dsimp [R]; omega
  have hroute := Nat.mul_le_mul hs hw
  have heq : haloOriginControlsSharedCost P q s t u band a b L+advanceControlsSharedCost G s w =
      (36*(t-s+1)+9)*tblC G G+(s+t+band+a+b+L+w)*(4*G+10)+
        (284*G+25*w+8*q+4*P+95*t+19*u+4*V+463)+8*s*w := by
    simp [haloOriginControlsSharedCost,advanceControlsSharedCost,generateHaloGeometryWidthCost,
      haloClassHeadersCost,weightWidthCost,w,G,V]
    ring
  change haloOriginControlsSharedCost P q s t u band a b L+advanceControlsSharedCost G s w ≤
    (36*(t-s+1)+9)*tblC G G+2000*H*R
  rw [heq]
  nlinarith only [hheaders,hlinear,hroute]

theorem selectedSharedHaloControls_fast_le (cq : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (q u band a b L : ℕ),
      q ≤ cq*Sizes.p n → u ≤ Sizes.p n → band ≤ Sizes.s n i → a ≤ Sizes.s n i →
      b ≤ Sizes.s n i → L ≤ Sizes.t n i →
      haloOriginControlsSharedCost (2^15*Sizes.p n) q (Sizes.s n i) (Sizes.t n i) u band a b L+
        advanceControlsSharedCost (haloGeometryWidth (Sizes.t n i) (2*q+8)) (Sizes.s n i) (2*q+8) ≤
          C*Sizes.t n i*Sizes.p n := by
  let cw := 2*cq+8
  let cV := 2*cw+426009
  let cH := 2^15+cq+8
  let cR := 2*cw+cV+4
  obtain ⟨K,hK⟩ := selectedHaloPhaseTables_fast_le cw
  refine ⟨K+2000*cH*cR,?_⟩
  intro n h i q u band a b L hq hu hband ha hb hL
  let w := 2*q+8
  let G := haloGeometryWidth (Sizes.t n i) w
  let V := weightWorkspaceWidth (2^15*Sizes.p n) q w (Sizes.t n i) u
  let H := 2^15*Sizes.p n+q+u+Sizes.s n i+Sizes.t n i+band+a+b+L+1
  let R := G+w+V+1
  have hp := h.thirteen_le_p
  have hpt := selectedPrecision_le_axis h i
  have hst := h.good.lt i
  have ht : 1 ≤ Sizes.t n i := by omega
  have hw : w ≤ cw*Sizes.p n := by dsimp [w,cw]; nlinarith only [hq,hp]
  have hv := selectedWeightWorkspaceWidth_le cw h i q w u hw (by dsimp [w]; omega) hu
  change V ≤ cV*Sizes.p n at hv
  have hbits : Nat.size w ≤ w := Nat.size_le.mpr Nat.lt_two_pow_self
  have htbits := selectedAxisBits_le n i
  have hell := selectedAxisLog_le_precision h
  have hg : G ≤ (cw+3)*Sizes.p n := by
    dsimp only [G,haloGeometryWidth]
    nlinarith only [hbits,htbits,hell,hw,hp]
  have hRbound : R ≤ cR*Sizes.p n := by
    dsimp only [R,cR]
    nlinarith only [hg,hw,hv,hp]
  have hHbound : H ≤ cH*Sizes.t n i := by
    have hq' := hq.trans (Nat.mul_le_mul_left cq hpt)
    have hP := Nat.mul_le_mul_left (2^15) hpt
    dsimp only [H,cH]
    nlinarith only [hq',hP,hu,hpt,hst,hband,ha,hb,hL,ht]
  have hlinear := Nat.mul_le_mul hHbound hRbound
  have htables := hK n h i w hw
  have hcoefficient : 36*(Sizes.t n i-Sizes.s n i+1)+9 ≤
      6*(36*(Sizes.t n i-Sizes.s n i+1)+9)+3*(Sizes.t n i-Sizes.s n i+1) := by omega
  have htable := (Nat.mul_le_mul_right (tblC G G) hcoefficient).trans htables
  have hcost := sharedHaloControls_le (2^15*Sizes.p n) q (Sizes.s n i) (Sizes.t n i) u band a b L
  change haloOriginControlsSharedCost (2^15*Sizes.p n) q (Sizes.s n i) (Sizes.t n i) u band a b L+
    advanceControlsSharedCost G (Sizes.s n i) w ≤
      (36*(Sizes.t n i-Sizes.s n i+1)+9)*tblC G G+2000*H*R at hcost
  nlinarith only [hcost,htable,hlinear]

theorem selectedSharedHaloControlCandidates_fast_le (cq : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (q u band a b : ℕ),
      q ≤ cq*Sizes.p n → u ≤ Sizes.p n → band ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      ((haloLengthCandidates (Sizes.s n i) (Sizes.t n i) band a b).map (fun L =>
        haloOriginControlsSharedCost (2^15*Sizes.p n) q (Sizes.s n i) (Sizes.t n i) u band a b L+
          advanceControlsSharedCost (haloGeometryWidth (Sizes.t n i) (2*q+8)) (Sizes.s n i) (2*q+8))).sum ≤
            C*Sizes.t n i*Sizes.p n := by
  obtain ⟨K,hK⟩ := selectedSharedHaloControls_fast_le cq
  refine ⟨6*K,?_⟩
  intro n h i q u band a b hq hu hband ha hb
  let F := fun L => haloOriginControlsSharedCost (2^15*Sizes.p n) q (Sizes.s n i) (Sizes.t n i) u band a b L+
    advanceControlsSharedCost (haloGeometryWidth (Sizes.t n i) (2*q+8)) (Sizes.s n i) (2*q+8)
  have hcost : ∀ L ∈ haloLengthCandidates (Sizes.s n i) (Sizes.t n i) band a b,
      F L ≤ K*Sizes.t n i*Sizes.p n := by
    intro L hL
    have hlen := haloLengthCandidates_uniform (h.good.lt i) band a b hL
    have hdiv := Nat.div_le_self (Sizes.s n i) (Sizes.t n i-Sizes.s n i)
    have hst := h.good.lt i
    exact hK n h i q u band a b L hq hu hband ha hb (by omega)
  have hsum := List.sum_le_length_nsmul
    ((haloLengthCandidates (Sizes.s n i) (Sizes.t n i) band a b).map F) (K*Sizes.t n i*Sizes.p n) (by
      intro x hx
      obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hx
      exact hcost L hL)
  simpa [F,haloLengthCandidates,naturalLengthCandidates,nsmul_eq_mul,Nat.mul_assoc] using hsum

end IntegerMultBounds.MathlibTM2.Cost
