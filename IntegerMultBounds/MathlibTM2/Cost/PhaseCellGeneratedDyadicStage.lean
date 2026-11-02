module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedChunkInterchange
public import IntegerMultBounds.MathlibTM2.Cost.MatchBase

/-! Pay the complete generated equal-field stage, including native metadata
and retirement, against its full payload volume and actual bit width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

noncomputable def generatedDyadicStageCoeff (T t₀ D : ℕ) : ℝ :=
  (T+12*swapT t₀+5 : ℕ)*swapConst+
    (6*D+267+2*T+6*swapT t₀+(T+12*swapT t₀+5) : ℕ)

theorem generatedDyadicStageCost_le (T t₀ D P B k stock V : ℕ)
    (hP : 0 < P) (hB : 0 < B) (hk : 0 < k)
    (hvolume : V = P*2^k*2^k*B) (hstock : stock ≤ D*V) :
    (generatedBalancedChunkInterchangeCost T t₀ P B k k stock : ℝ) ≤
      generatedDyadicStageCoeff T t₀ D*V*((k : ℝ)^Parameters.tau+1) := by
  have hp : 1 ≤ 2^k := Nat.one_le_pow _ _ (by decide : 1 ≤ 2)
  have h₁ : P ≤ P*2^k := by simpa using Nat.mul_le_mul_left P hp
  have h₂ : P*2^k ≤ P*2^k*2^k := by simpa using Nat.mul_le_mul_left (P*2^k) hp
  have h₃ : P*2^k*2^k ≤ V := by
    rw [hvolume]
    simpa using Nat.mul_le_mul_left (P*2^k*2^k) (show 1 ≤ B by omega)
  have hPV : P ≤ V := h₁.trans (h₂.trans h₃)
  have hprod : 1 ≤ P*2^k*2^k := (show 1 ≤ P by omega).trans (h₁.trans h₂)
  have hBV : B ≤ V := by
    rw [hvolume]
    simpa using Nat.mul_le_mul_right B hprod
  have hpow : 2^k ≤ P*2^k := by
    simpa using Nat.mul_le_mul_right (2^k) (show 1 ≤ P by omega)
  have hkV : k ≤ V := (Nat.lt_two_pow_self (n := k)).le.trans (hpow.trans (h₂.trans h₃))
  have hV : 1 ≤ V := (show 1 ≤ P by omega).trans hPV
  have hheader : interchangeHeaderVolume P 1 B k k ≤ 10*V := by
    have hh := interchangeHeaderVolume_le P 1 B k k
    omega
  have hsetup : 21*(P+1+B+k+k)+56 ≤ 161*V := by omega
  let M := T+12*swapT t₀+5
  let F := 6*D+267+2*T+6*swapT t₀+M
  have hoverhead : 21*(P+1+B+k+k)+56+
      (6*(stock+interchangeHeaderVolume P 1 B k k)+2*T+6*swapT t₀+15)+
      (2*interchangeHeaderVolume P 1 B k k+11)+M ≤ F*V := by
    have hh := Nat.mul_le_mul_left (2*T+6*swapT t₀+26+M) hV
    dsimp only [F]
    nlinarith only [hstock,hheader,hsetup,hh]
  have hswap := mt_swap_le (P := P) (G := 1) (E := B) (h := k) (w := k) (L := k) (interchangeHeaderBits P 1 B k k) hP (by decide) hB
    (by omega) (by omega) (fun i => Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self _))
    (fun i => binBits_size_canonical _) (le_refl k) (le_refl k) hk
  simp only [Nat.mul_one] at hswap
  rw [←hvolume] at hswap
  have hswapM := mul_le_mul_of_nonneg_left hswap (Nat.cast_nonneg M)
  have hoverheadR : (21*(P+1+B+k+k)+56+
      (6*(stock+interchangeHeaderVolume P 1 B k k)+2*T+6*swapT t₀+15)+
      (2*interchangeHeaderVolume P 1 B k k+11)+M : ℕ) ≤ (F : ℝ)*V := by
    exact_mod_cast hoverhead
  have hτ : 0 ≤ (k : ℝ)^Parameters.tau := Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hmain : 0 ≤ (M : ℝ)*swapConst*V := by
    have := swapConst_pos
    positivity
  have hlin : 0 ≤ (F : ℝ)*V*(k : ℝ)^Parameters.tau := by positivity
  unfold generatedBalancedChunkInterchangeCost generatedDyadicStageCoeff
  dsimp only [M,F] at *
  push_cast at hoverheadR hswapM hmain hlin ⊢
  nlinarith only [hswapM,hoverheadR,hmain,hlin]

end IntegerMultBounds.MathlibTM2.Cost
