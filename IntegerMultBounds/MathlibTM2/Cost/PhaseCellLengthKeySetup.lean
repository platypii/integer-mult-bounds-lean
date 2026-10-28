module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeometryControlSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloInteriorCost

/-! The actual length-key initializer has linear selected-axis cost, including its numerical table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement IntegerMultBounds.NLogN

/-- The already selected axis room absorbs a constant quadratic precision setup. -/
theorem selectedPrecision_le_axis {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n)) :
    Sizes.p n ≤ Sizes.t n i := by
  have hr := h.eight_p_le_r
  rw [Sizes.t_eq i]
  split_ifs <;> omega

theorem selectedAxisLog_le_precision {n : ℕ} (h : Sizes.Big n) : Sizes.ℓ n ≤ Sizes.p n := by
  have hl := h.ℓ_bounds.2
  have hd : Sizes.ℓ n ≤ Sizes.d n*Sizes.ℓ n := Nat.le_mul_of_pos_left _ h.one_le_d
  nlinarith only [hl,hd,Nat.zero_le (Sizes.d n*Sizes.ℓ n)]

theorem initializeHaloLengthKeysBound_le (P N q l s t u band a b : ℕ) :
    let V := weightWorkspaceWidth P q (2*q+8) t u
    let H := P+N+q+l+u+s+t+band+a+b+1
    initializeHaloLengthKeysBound P N q l s t u band a b ≤
      10000*(H*(V+4)+(V+4)^2) := by
  let V := weightWorkspaceWidth P q (2*q+8) t u
  let H := P+N+q+l+u+s+t+band+a+b+1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hheaders : s+t+band+a+b ≤ H := by dsimp [H]; omega
  have hsmall : 10*P+6*N+34*q+6*l+25*u+6*s+63*t+6*band+6*a+6*b+781 ≤ 800*H := by
    dsimp [H]; omega
  have hv : 1956*V ≤ 2000*H*(V+4) := by
    have hh : 1956*V ≤ 2000*(V+4) := by omega
    exact hh.trans (by nlinarith only [Nat.mul_le_mul_left (2000*(V+4)) hH])
  have hh : (s+t+band+a+b)*(4*V+10) ≤ 4*H*(V+4) := by
    calc
      _ ≤ H*(4*(V+4)) := by gcongr; omega
      _ = _ := by ring
  have hs : 800*H ≤ 200*H*(V+4) := by nlinarith only [Nat.zero_le V]
  have heq : initializeHaloLengthKeysBound P N q l s t u band a b =
      5824*(V+4)^2+(s+t+band+a+b)*(4*V+10)+1956*V+
        10*P+6*N+34*q+6*l+25*u+6*s+63*t+6*band+6*a+6*b+781 := by
    simp [initializeHaloLengthKeysBound,installHaloGroupHeadersCost,installGroupHeadersCost,
      prepareHaloLengthKeysCost,weightWidthCost,preparedHaloLengthCandidatesCost,haloHeadersCost,tblC,V]
    ring
  rw [heq]
  change _ ≤ 10000*(H*(V+4)+(V+4)^2)
  nlinarith only [hsmall,hv,hh,hs,Nat.zero_le ((V+4)^2)]

theorem selectedLengthKeyInitialization_fast_le (cN cq cl : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (N q l u band a b : ℕ),
      N ≤ cN*Sizes.p n → q ≤ cq*Sizes.p n → l ≤ cl*Sizes.p n → u ≤ Sizes.p n →
      band ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      initializeHaloLengthKeysBound (2^15*Sizes.p n) N q l (Sizes.s n i) (Sizes.t n i) u band a b ≤
        C*Sizes.t n i*Sizes.p n := by
  let cV := 4*cq+426029
  let cH := 2^15+cN+cq+cl+7
  refine ⟨10000*(cH*cV+cV*cV),?_⟩
  intro n h i N q l u band a b hN hq hl hu hband ha hb
  let V := weightWorkspaceWidth (2^15*Sizes.p n) q (2*q+8) (Sizes.t n i) u
  let H := 2^15*Sizes.p n+N+q+l+u+Sizes.s n i+Sizes.t n i+band+a+b+1
  have hp := h.thirteen_le_p
  have hpt := selectedPrecision_le_axis h i
  have hst := h.good.lt i
  have ht : 1 ≤ Sizes.t n i := by omega
  have hw : 2*q+8 ≤ (2*cq+8)*Sizes.p n := by nlinarith only [hq,hp]
  have hv := selectedWeightWorkspaceWidth_le (2*cq+8) h i q (2*q+8) u hw (by omega) hu
  have hV : V+4 ≤ cV*Sizes.p n := by
    change V ≤ (2*(2*cq+8)+426009)*Sizes.p n at hv
    dsimp only [cV]
    nlinarith only [hv,hp]
  have hVt : V+4 ≤ cV*Sizes.t n i := hV.trans (Nat.mul_le_mul_left cV hpt)
  have hH : H ≤ cH*Sizes.t n i := by
    have hN' := hN.trans (Nat.mul_le_mul_left cN hpt)
    have hq' := hq.trans (Nat.mul_le_mul_left cq hpt)
    have hl' := hl.trans (Nat.mul_le_mul_left cl hpt)
    have hP := Nat.mul_le_mul_left (2^15) hpt
    dsimp only [H,cH]
    nlinarith only [hN',hq',hl',hP,hu,hpt,hst,hband,ha,hb,ht]
  have hlinear := Nat.mul_le_mul hH hV
  have hquadratic := Nat.mul_le_mul hVt hV
  have hcost := initializeHaloLengthKeysBound_le (2^15*Sizes.p n) N q l (Sizes.s n i) (Sizes.t n i) u band a b
  change initializeHaloLengthKeysBound (2^15*Sizes.p n) N q l (Sizes.s n i) (Sizes.t n i) u band a b ≤
    10000*(H*(V+4)+(V+4)^2) at hcost
  nlinarith only [hcost,hlinear,hquadratic]

/-- Actual runtime precision headers are paid from their working-width bound. -/
theorem selectedExecutionLengthKeyInitialization_fast_le (cw cl : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (l u target rhsExp a b : ℕ),
      executionWidth (Sizes.p n) l target rhsExp ≤ cw*Sizes.p n → l ≤ cl*Sizes.p n →
      u ≤ Sizes.p n → PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      initializeHaloLengthKeysBound (2^15*Sizes.p n) (executionStagePrecision (Sizes.p n) l target rhsExp+1)
        (executionPrecision (Sizes.p n) l target rhsExp) l (Sizes.s n i) (Sizes.t n i) u
          (PhaseCellBand.width (Sizes.p n) u) a b ≤ C*Sizes.t n i*Sizes.p n := by
  obtain ⟨C,hC⟩ := selectedLengthKeyInitialization_fast_le cw cw cl
  refine ⟨C,?_⟩
  intro n h i l u target rhsExp a b hw hl hu hband ha hb
  have hN : executionStagePrecision (Sizes.p n) l target rhsExp+1 ≤ executionWidth (Sizes.p n) l target rhsExp := by
    dsimp [executionStagePrecision,executionWidth]; omega
  have hq : executionPrecision (Sizes.p n) l target rhsExp ≤ executionWidth (Sizes.p n) l target rhsExp := by
    dsimp [executionPrecision,executionWidth]; omega
  exact hC n h i _ _ _ _ _ _ _ (hN.trans hw) (hq.trans hw) hl hu hband ha hb

end IntegerMultBounds.MathlibTM2.Cost
