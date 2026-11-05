module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCallerFormat
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInitializedPublishedClassRun

/-! Scalar accounting for the complete raw caller. Numerical work and the
shared routing charge stay separate from source-linear control traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.NLogN

def rawCallerTrafficFactor (ct cV cD : ℕ) : ℕ :=
  let cW := 1032+8*ct
  let cFormat := callerFormatFactor ct cV cD+1
  (60*cW+4*cFormat+14)+
    (coreExposureTrafficFactor cV cW+40*cV+48*cD+6185+1700)*cW+
    291*cFormat+1375*cW+4396+2*CallerLayout.headerCount

noncomputable def rawCallerTimeBudget (F G : ℝ)
    (n ct cV cD p u s t N : ℕ) : ℝ :=
  2624033*Sizes.T n+rawCallerTrafficFactor ct cV cD*(N*s*p : ℕ)+
    540*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*(1032+8*ct)*
      (N*s*p : ℕ)*Sizes.d n*((Sizes.ℓ n : ℝ)^Parameters.tau+1)+
    (F+G)*N*t*(1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d n)*(p : ℝ)^(129/128 : ℝ)

/-- All scalar fields are bounded once, before multiplying by replicas. -/
theorem rawCallerScalarTraffic_le (ct cV cD p s D B W N : ℕ)
    (hN : 1 ≤ N) (hs : 1 ≤ s) (hp : 1 ≤ p)
    (hD : D ≤ (callerFormatFactor ct cV cD+1)*p)
    (hB : B ≤ (1032+8*ct)*p) (hW : W ≤ (1032+8*ct)*p) :
    let cW := 1032+8*ct
    let cPrep := 60*cW+4*(callerFormatFactor ct cV cD+1)+14
    let cGather := coreExposureTrafficFactor cV cW+40*cV+48*cD+6185
    291*D+38*B+4*p+45*N+242*(N*s*(2*p+13))+717+
      (cPrep+1337*cW+2*CallerLayout.headerCount)*(N*s*p)+(cGather+1700)*(N*s*W) ≤
      rawCallerTrafficFactor ct cV cD*(N*s*p) := by
  dsimp only
  have hNs : 1 ≤ N*s := Nat.mul_pos hN hs
  have hpSource : p ≤ N*s*p := Nat.le_mul_of_pos_left p hNs
  have hNSource : N ≤ N*s*p :=
    (Nat.le_mul_of_pos_right N hs).trans (Nat.le_mul_of_pos_right (N*s) hp)
  have hone : 1 ≤ N*s*p := Nat.mul_pos hNs hp
  have hDSource := hD.trans (Nat.mul_le_mul_left (callerFormatFactor ct cV cD+1) hpSource)
  have hBSource := hB.trans (Nat.mul_le_mul_left (1032+8*ct) hpSource)
  have hvolume : N*s*(2*p+13) ≤ 15*(N*s*p) := by
    have hh := Nat.mul_le_mul_left (N*s) (show 2*p+13 ≤ 15*p by omega)
    nlinarith only [hh]
  have hwords : N*s*W ≤ (1032+8*ct)*(N*s*p) := by
    have hh := Nat.mul_le_mul_left (N*s) hW
    nlinarith only [hh]
  have htraffic := Nat.mul_le_mul_left
    (coreExposureTrafficFactor cV (1032+8*ct)+40*cV+48*cD+6185+1700) hwords
  unfold rawCallerTrafficFactor
  dsimp only
  nlinarith only [hDSource,hBSource,hpSource,hNSource,hone,hvolume,htraffic]

/-- Compress the exact component ledger; the two numerical solves share one
fast-work term, and gather/publication share one dyadic routing term. -/
theorem rawCallerTime_le (F G : ℝ) (n ct cV cD p u s t D B W N : ℕ)
    (hN : 1 ≤ N) (hs : 1 ≤ s) (hp : 1 ≤ p)
    (hD : D ≤ (callerFormatFactor ct cV cD+1)*p)
    (hB : B ≤ (1032+8*ct)*p) (hW : W ≤ (1032+8*ct)*p) :
    let cW := 1032+8*ct
    let prepBudget := 2*Sizes.T n+(60*cW+4*(callerFormatFactor ct cV cD+1)+14)*(N*s*p)
    let runTime := initializedPublishedRunTime F n ct cV cD p u s t D B W N
    let retainedTime : ℝ := 2*Sizes.T n+1700*(N*(s*W) : ℕ)+
      108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
        (N*(s*W) : ℕ)*Sizes.d n*((Sizes.ℓ n : ℝ)^Parameters.tau+1)
    let properTime := (Sizes.T n : ℝ)+(runTime+(14*Sizes.T n+37*N+82+retainedTime))+Sizes.T n
    let solveTime := 2624001*(Sizes.T n : ℝ)+(N : ℝ)*G*t*
      (1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d n)*(p : ℝ)^(129/128 : ℝ)+410
    let prepareTime := (((4*p+5)+Sizes.T n+(4*B+5)+(242*(N*s*(2*p+13))+45)+(2*B+3) : ℕ) : ℝ)+solveTime
    let publicationTime := Sizes.T n+1335*cW*(N*s*p)
    let retireSetupCost := Sizes.T n+(2*CallerLayout.headerCount+2*cW)*(N*s*p)
    (prepBudget : ℝ)+(properTime+(prepareTime+(publicationTime : ℝ)))+(retireSetupCost : ℝ) ≤
      rawCallerTimeBudget F G n ct cV cD p u s t N := by
  dsimp only
  have hscalar := rawCallerScalarTraffic_le ct cV cD p s D B W N hN hs hp hD hB hW
  dsimp only at hscalar
  have hscalarR := (Nat.cast_le (α := ℝ)).mpr hscalar
  have hwords : N*s*W ≤ (1032+8*ct)*(N*s*p) := by
    have hh := Nat.mul_le_mul_left (N*s) hW
    nlinarith only [hh]
  have hwordsR := (Nat.cast_le (α := ℝ)).mpr hwords
  have hc : 0 ≤ generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300 := by
    unfold generatedDyadicStageCoeff
    exact add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) Node.swapConst_pos.le)
      (Nat.cast_nonneg _)) (by norm_num)
  have hcharge : 0 ≤ 540*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
      Sizes.d n*((Sizes.ℓ n : ℝ)^Parameters.tau+1) := by positivity
  have hrouting := mul_le_mul_of_nonneg_left hwordsR hcharge
  unfold initializedPublishedRunTime rawCallerTimeBudget
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hscalarR hrouting ⊢
  nlinarith only [hscalarR,hrouting]

noncomputable def rawCallerStockFactor (ct cV cD Cstock : ℕ) : ℕ :=
  let cW := 1032+8*ct
  let cFormat := callerFormatFactor ct cV cD+1
  let cPrep := 60*cW+4*cFormat+14
  let cGather := 3*coreExposureTrafficFactor cV cW+60*cV+72*cD+268+
    12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700)
  let cSolve := (1312000+756)*cW+504
  100+795*cFormat+56*cW+7986+8*cPrep+5597*cW+
    (cGather+3200+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*cW+cSolve+Cstock

noncomputable def rawCallerStockBudget (ct cV cD Cstock Cprog n s t p N : ℕ) : ℕ :=
  rawCallerStockFactor ct cV cD Cstock*(Cprog+1)*(Sizes.T n+N*t*p)

theorem rawCallerStock_le (ct cV cD Cstock Cprog n p s t D B W N : ℕ)
    (hN : 1 ≤ N) (hs : 1 ≤ s) (hp : 1 ≤ p) (hst : s ≤ t)
    (hD : D ≤ (callerFormatFactor ct cV cD+1)*p)
    (hB : B ≤ (1032+8*ct)*p) (hW : W ≤ (1032+8*ct)*p) :
    let cW := 1032+8*ct
    let prepBudget := 2*Sizes.T n+(60*cW+4*(callerFormatFactor ct cV cD+1)+14)*(N*s*p)
    let runStock := initializedPublishedRunStock Cstock Cprog n ct cV cD p s t D B W N
    let retainedStock := 2*Sizes.T n+(3200+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(N*(s*W))
    let properStock := Sizes.T n+(runStock+(20*Sizes.T n+62*N+122+retainedStock))
    let solveStock := (Cprog+1)*(((1312000+756)*cW+504)*(N*s*p)+2*Sizes.T n)
    let prepareStock := 13*(4*p+5)+(Sizes.T n+(2*(4*B+5)+(solveStock+(480*(N*s*(2*p+13))+86))))
    let publicationStock := Sizes.T n+5597*cW*(N*s*p)
    8*prepBudget+max properStock (prepareStock+publicationStock) ≤
      rawCallerStockBudget ct cV cD Cstock Cprog n s t p N := by
  dsimp only
  let cW := 1032+8*ct
  let cFormat := callerFormatFactor ct cV cD+1
  let cPrep := 60*cW+4*cFormat+14
  let cGather := 3*coreExposureTrafficFactor cV cW+60*cV+72*cD+268+
    12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700)
  let cSolve := (1312000+756)*cW+504
  let C := 795*cFormat+56*cW+7986+8*cPrep+5597*cW+
    (cGather+3200+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*cW
  have hNs : 1 ≤ N*s := Nat.mul_pos hN hs
  have hpSource : p ≤ N*s*p := Nat.le_mul_of_pos_left p hNs
  have hNSource : N ≤ N*s*p :=
    (Nat.le_mul_of_pos_right N hs).trans (Nat.le_mul_of_pos_right (N*s) hp)
  have hone : 1 ≤ N*s*p := Nat.mul_pos hNs hp
  have hDSource := hD.trans (Nat.mul_le_mul_left cFormat hpSource)
  have hBSource := hB.trans (Nat.mul_le_mul_left cW hpSource)
  have hvolume : N*s*(2*p+13) ≤ 15*(N*s*p) := by
    have hh := Nat.mul_le_mul_left (N*s) (show 2*p+13 ≤ 15*p by omega)
    nlinarith only [hh]
  have hwords : N*s*W ≤ cW*(N*s*p) := by
    have hh := Nat.mul_le_mul_left (N*s) hW
    change N*s*W ≤ (1032+8*ct)*(N*s*p)
    nlinarith only [hh]
  have htraffic := Nat.mul_le_mul_left
    (cGather+3200+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40)) hwords
  have hscalar : 795*D+56*B+52*p+86*N+648+480*(N*s*(2*p+13))+
      (8*cPrep+5597*cW)*(N*s*p)+
      (cGather+3200+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(N*s*W) ≤ C*(N*s*p) := by
    dsimp only [C]
    nlinarith only [hDSource,hBSource,hpSource,hNSource,hone,hvolume,htraffic]
  have hsource : N*s*p ≤ N*t*p := Nat.mul_le_mul_right p (Nat.mul_le_mul_left N hst)
  have hbase := Nat.mul_le_mul_left C hsource
  have hbaseScale : C*(N*t*p) ≤ C*(Cprog+1)*(N*t*p) := by
    nlinarith only [Nat.zero_le (C*Cprog*(N*t*p))]
  have hsolve := Nat.mul_le_mul_left (cSolve*(Cprog+1)) hsource
  have hmax (x y : ℕ) : max x y ≤ x+y := by omega
  have hh := hmax
    (Sizes.T n+(initializedPublishedRunStock Cstock Cprog n ct cV cD p s t D B W N+
      (20*Sizes.T n+62*N+122+(2*Sizes.T n+(3200+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(N*(s*W))))))
    ((13*(4*p+5)+(Sizes.T n+(2*(4*B+5)+((Cprog+1)*(((1312000+756)*cW+504)*(N*s*p)+2*Sizes.T n)+(480*(N*s*(2*p+13))+86)))))+
      (Sizes.T n+5597*cW*(N*s*p)))
  unfold initializedPublishedRunStock at hh ⊢
  have hfactor : rawCallerStockFactor ct cV cD Cstock = 100+C+cSolve+Cstock := by
    dsimp only [rawCallerStockFactor,C,cSolve,cPrep,cFormat,cGather,cW]
    omega
  unfold rawCallerStockBudget
  rw [hfactor]
  dsimp only [cW] at hh
  dsimp only [cPrep,cFormat,cGather,cW] at hscalar
  have hpositive := Nat.zero_le ((C+cSolve+Cstock)*(Cprog+1)*Sizes.T n)
  dsimp only [cSolve,cW] at hsolve hpositive ⊢
  nlinarith only [hh,hscalar,hbase,hbaseScale,hsolve,hpositive,
    Nat.zero_le ((Cprog+1)*(N*t*p)),Nat.zero_le (Sizes.T n),
    Nat.zero_le (C*(Cprog+1)*Sizes.T n),Nat.zero_le (cSolve*(Cprog+1)*Sizes.T n),
    Nat.zero_le (Cstock*(Cprog+1)*Sizes.T n),Nat.zero_le (Cprog*Sizes.T n)]

end IntegerMultBounds.MathlibTM2.Cost
