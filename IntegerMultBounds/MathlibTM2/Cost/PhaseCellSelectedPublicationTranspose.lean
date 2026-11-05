module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPublicationTransposeBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Shared transpose setup fits in tensor volume; only the sharp routing term
and source-linear traffic remain in the selected publication budget. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open FixedStreamedBank

theorem selectedPublicationCounterFits (cV : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ V L W a b : ℕ,
      V ≤ cV*Sizes.p n → (Sizes.p n)^2 ≤ L → 1 ≤ W →
      V ≤ 2^a*2^b*(L*W) := by
  filter_upwards [tendsto_atTop.1 Sizes.tendsto_b cV] with n hn
  intro V L W a b hV hL hW
  have hp : cV ≤ Sizes.p n := by unfold Sizes.p; omega
  have hv : V ≤ L := hV.trans ((by nlinarith only [hp] : cV*Sizes.p n ≤ (Sizes.p n)^2).trans hL)
  exact hv.trans ((Nat.le_mul_of_pos_right L hW).trans
    (Nat.le_mul_of_pos_left (L*W) (Nat.mul_pos (Nat.two_pow_pos a) (Nat.two_pow_pos b))))

private theorem selectedPublicationKernelSetup_le (cV : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (V : ℕ),
      V ≤ cV*Sizes.p n →
      100*V+500+2*(116*V+143+32921*(V+1)^5)+4 ≤ Sizes.T n ∧
      200*V+800+(342*V+423+98763*(V+1)^5)+38 ≤ Sizes.T n := by
  let coefficient := 874*cV+2051+164605*(cV+1)^5
  filter_upwards [selectedAxisPolynomial_le_volume coefficient 0 5] with n hn
  intro h i V hV
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpt := selectedPrecision_le_axis h i
  have ht := hp.trans hpt
  have ht5 : Sizes.t n i ≤ (Sizes.t n i)^5 := Nat.le_self_pow (by decide) _
  have hunit := ht.trans ht5
  have hVt := hV.trans (Nat.mul_le_mul_left cV hpt)
  have hV5 := hVt.trans (Nat.mul_le_mul_left cV ht5)
  have hbase : V+1 ≤ (cV+1)*Sizes.t n i := by nlinarith only [hVt,ht]
  have hpow := Nat.pow_le_pow_left hbase 5
  rw [Nat.mul_pow] at hpow
  have hsum : (100*V+500+2*(116*V+143+32921*(V+1)^5)+4)+
      (200*V+800+(342*V+423+98763*(V+1)^5)+38) ≤ coefficient*(Sizes.t n i)^5 := by
    dsimp only [coefficient]
    nlinarith only [hV5,hpow,hunit]
  have hbound : coefficient*(Sizes.t n i)^5 ≤ Sizes.T n := by
    simpa only [pow_zero,mul_one] using hn i
  have hh := hsum.trans hbound
  exact ⟨(Nat.le_add_right _ _).trans hh,(Nat.le_add_left _ _).trans hh⟩

theorem selectedPublicationTransposeCosts_le {Q : ℕ}
    (hstates : FixedStreamedBank.stateCount ≤ Q) (cV : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (L b W V : ℕ)
      (windows : PublicationWindows (Sizes.s n i) L),
      L ≤ Sizes.s n i → 0 < L*W → V ≤ cV*Sizes.p n →
      V ≤ 2^Nat.clog 2 windows.origins.length*2^b*(L*W) →
      let a := Nat.clog 2 windows.origins.length
      (1700*(2^b*(Sizes.s n i*W) : ℕ)+100*V+500+Sizes.T n+
          2*restoringTimeCost hstates a b (L*W) V : ℝ) ≤
        2*Sizes.T n+1700*(2^b*(Sizes.s n i*W) : ℕ)+
          6*(generatedDyadicStageCoeff tapeCount 6 1+300)*
            (2^b*(Sizes.s n i*W) : ℕ)*dyadicRouteCharge b a ∧
      3200*(2^b*(Sizes.s n i*W))+200*V+800+Sizes.T n+
          restoringStockAllowance hstates a b (L*W) V ≤
        2*Sizes.T n+(3200+3*(streamedDyadicStockCoeff tapeCount+40))*(2^b*(Sizes.s n i*W)) := by
  filter_upwards [selectedPublicationKernelSetup_le cV] with n hsetup
  intro h i L b W V windows hL hpacket hV hfit
  dsimp only
  obtain ⟨ht,hs⟩ := publicationTransposeCosts_le hstates windows hL b W V hpacket hfit
  obtain ⟨htSetup,hsSetup⟩ := hsetup h i V hV
  have htR := (Nat.cast_le (α := ℝ)).mpr htSetup
  constructor
  · push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at ht htR ⊢
    linarith only [ht,htR]
  · nlinarith only [hs,hsSetup]

end IntegerMultBounds.MathlibTM2.Cost
