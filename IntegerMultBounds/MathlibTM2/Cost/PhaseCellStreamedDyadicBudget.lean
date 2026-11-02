module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCanonicalDyadicTraffic
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStreamedScheduleData

/-! Complete streamed-stage budgets, including binary row reading, unary
master retirement and consuming-loop overhead. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

private theorem equalField_masters_le (P B k volume : ℕ) (hP : 0 < P) (hB : 0 < B)
    (hvolume : volume = P*2^k*2^k*B) : P ≤ volume ∧ B ≤ volume ∧ k ≤ volume ∧ 1 ≤ volume := by
  have hpos : 0 < volume := by rw [hvolume]; positivity
  have hPV : P ≤ volume := Nat.le_of_dvd hpos ⟨2^k*2^k*B,by rw [hvolume]; ring⟩
  have hBV : B ≤ volume := Nat.le_of_dvd hpos ⟨P*2^k*2^k,by rw [hvolume]; ring⟩
  have hpow : 2^k ≤ volume := Nat.le_of_dvd hpos ⟨P*2^k*B,by rw [hvolume]; ring⟩
  exact ⟨hPV,hBV,Nat.lt_two_pow_self.le.trans hpow,by omega⟩

private theorem streamedDyadicLifecycle_le {T : ℕ} (dims : Fin 5 → Fin T)
    (wordWidth P B k volume : ℕ) (hP : 0 < P) (hB : 0 < B)
    (hvolume : volume = P*2^k*2^k*B) (hwidth : wordWidth ≤ volume) :
    let row := interchangeDimensionRow dims P B k k
    readDimensionRowCost wordWidth row+(2*(row.map Prod.fst).sum+2*row.length+1)+3 ≤ 300*volume := by
  obtain ⟨hPV,hBV,hkV,hV⟩ := equalField_masters_le P B k volume hP hB hvolume
  have hh := interchangeDimensionRow_lifecycleCost dims wordWidth P B k k
  dsimp only at hh ⊢
  rw [hh]
  omega

theorem streamedDyadicStageTime_le {t₀ T Q : ℕ} (bank : StreamedChunkBank t₀ T Q)
    (wordWidth D P B k stock volume : ℕ) (hP : 0 < P) (hB : 0 < B) (hk : 0 < k)
    (hvolume : volume = P*2^k*2^k*B) (hstock : stock ≤ D*volume) (hwidth : wordWidth ≤ volume) :
    (bank.stageTimeCost wordWidth stock ⟨bank.dims,P,B,k,k⟩+3 : ℝ) ≤
      (generatedDyadicStageCoeff T t₀ D+300)*volume*((k : ℝ)^Parameters.tau+1) := by
  have hg := generatedDyadicStageCost_le T t₀ D P B k stock volume hP hB hk hvolume hstock
  have hl := streamedDyadicLifecycle_le bank.dims wordWidth P B k volume hP hB hvolume hwidth
  have hlR : (readDimensionRowCost wordWidth (interchangeDimensionRow bank.dims P B k k)+
      (2*((interchangeDimensionRow bank.dims P B k k).map Prod.fst).sum+
        2*(interchangeDimensionRow bank.dims P B k k).length+1)+3 : ℕ) ≤ (300 : ℝ)*volume := by
    exact_mod_cast hl
  have hpay : (300 : ℝ)*volume ≤ 300*volume*((k : ℝ)^Parameters.tau+1) := by
    have hh := mul_nonneg (by positivity : (0 : ℝ) ≤ 300*volume)
      (Real.rpow_nonneg (Nat.cast_nonneg k) Parameters.tau)
    nlinarith only [hh]
  simp only [StreamedChunkBank.stageTimeCost]
  push_cast at hlR ⊢
  nlinarith only [hg,hlR,hpay]

noncomputable def streamedDyadicStockCoeff (T : ℕ) : ℕ :=
  2*T*M8.Machine.BinaryInterchangeRunWithin.coefficient+5*T+1242

theorem streamedDyadicStageStock_le {t₀ T Q : ℕ} (bank : StreamedChunkBank t₀ T Q)
    (wordWidth P B k volume : ℕ) (hP : 0 < P) (hB : 0 < B)
    (hvolume : volume = P*2^k*2^k*B) (hwidth : wordWidth ≤ volume) :
    bank.stageStockAllowance wordWidth ⟨bank.dims,P,B,k,k⟩ ≤ streamedDyadicStockCoeff T*volume := by
  obtain ⟨hPV,hBV,hkV,hV⟩ := equalField_masters_le P B k volume hP hB hvolume
  have hl := streamedDyadicLifecycle_le bank.dims wordWidth P B k volume hP hB hvolume hwidth
  have hr : readDimensionRowCost wordWidth (interchangeDimensionRow bank.dims P B k k) ≤ 300*volume := by omega
  have hs : 21*(P+1+B+k+k)+56 ≤ 161*volume := by omega
  have hc := Nat.mul_le_mul_left (5*T+20) hV
  unfold StreamedChunkBank.stageStockAllowance generatedChunkStockAllowance
    SwapMachineStock.reserve BinaryAdjacentWidthInterchange.volume streamedDyadicStockCoeff
  dsimp only
  simp only [Nat.mul_one]
  rw [←hvolume]
  nlinarith only [hr,hs,hc]

end IntegerMultBounds.MathlibTM2.Cost
