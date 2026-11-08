module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundedDiagonalExec

/-! The actual owned reference family supplies every diagonal numerical bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s t α p u l T Q A : ℕ} [NeZero s] [NeZero t] {gap : ℝ}
  {P U : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem rsb_ownedDiagonal_runs_within
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {x y o : RsbR} (hfree : RsbFree x y o)
    (axis : RecoveryAxisBounds s t p u l (α : ℝ) gap) (target L k : ℕ)
    (hnear : t ≤ 2*s) (hL : 2 ≤ L)
    (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
    (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)
    (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α^2 ≤ p)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1)
    (z : ZMod s → ℂ) (hz : z ∈ axis.ownedTargets target L k hnear hL ha hb hfit Fs) :
    let q := packedHaloPrecision p l s t u (target+1) 2
      (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
      (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)
    let W := packedHaloCommonWidth p l s u (target+1) 2
    let c := cut s t L k
    let n := rows s t L k
    let active := haloVertices s c (cut s t L (k+1))
    ∀ (ρ : RsbR → List (Fin (A+4))) (_ : RsbReady ρ W p) (D : ZMod s → GaussianInt)
    (oldTail : List (Fin (A+4)))
    (_ : PhaseCellInterface.ErrorOn active
      (packedIntervalRead q (2*q+8) c (cstream A (2*q+8) (packedInterval c n D)++oldTail)) z (1/(2 : ℝ)^target))
    (_ : ρ x = cstream A W (packedInterval c n
      (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))))
    (_ : ρ y = cstream A W (packedInterval c n (diagonalField s t α p)))
    (C : ℕ) (_ : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg x y o)) ≤ C),
    let G := fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)
    RsbRunsWithin (body := body) (rg := rg) (ι := ι)
      (cmulStream (rsbCr rg x y o) (rmulOne ι hι hT hQ (rsbCr rg x y o))) ρ
      (Function.update ρ o (cstream A W (packedInterval c n (diagonalProduct s t α p G))++ρ o))
      (n*(rmulCost W+6*W+2)+8) (realWeightWorkspace C W n) ∧
    PhaseCellInterface.ErrorOn active
      (packedIntervalRead p W c (cstream A W (packedInterval c n (diagonalProduct s t α p G))++ρ o))
      (fun i => (dPrime s t (α : ℝ) i : ℂ)*(((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i))
      (8/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)) := by
  dsimp only
  intro ρ hr D oldTail herror hx hy C hpush
  have hmono := cut_mono s t L (show k ≤ k+1 by omega)
  have hend : cut s t L k+rows s t L k = cut s t L (k+1) := by dsimp only [rows]; omega
  have hinterval : cut s t L k+rows s t L k ≤ s := by rw [hend]; omega
  have hactive : ∀ i ∈ haloVertices s (cut s t L k) (cut s t L (k+1)),
      cut s t L k ≤ i.val ∧ i.val < cut s t L k+rows s t L k := by
    intro i hi; rw [hend]; exact (mem_haloVertices _ _ i).mp hi
  have hcover : ∀ i : ZMod s, cut s t L k ≤ i.val →
      i.val < cut s t L k+rows s t L k → i ∈ haloVertices s (cut s t L k) (cut s t L (k+1)) := by
    intro i hi hj; apply (mem_haloVertices _ _ i).mpr; rw [hend] at hj; exact ⟨hi,hj⟩
  have hmag := axis.ownedTargets_round_magnitude target L k hnear hL ha hb hfit Fs hF z (List.mem_reverse.mpr hz)
  have hscale : ∀ i ∈ haloVertices s (cut s t L k) (cut s t L (k+1)),
      ‖((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i‖ ≤ (3/2 : ℝ) := by
    intro i hi
    apply axis.ownedTargets_normalized_norm_le target L k hnear hL ha hb hfit Fs hF z hz i
    obtain ⟨hl,hr⟩ := (mem_haloVertices _ _ i).mp hi
    apply (mem_haloVertices _ _ i).mpr
    constructor <;> omega
  have hpq : p ≤ packedHaloPrecision p l s t u (target+1) 2
      (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
      (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u) := by
    dsimp [packedHaloPrecision,executionPrecision,executionExponent,inputExponent,sourceExponent]
    omega
  exact rsb_roundedDiagonal_runs_within (body := body) hrg hdisj hι hT hQ hA hfree ρ hr hp hpq
    (RecoveryAxisBounds.owned_normalization_width (s := s) (p := p) (u := u) (l := l) target) hα hαp
    _ hinterval hactive hcover D z hmag hscale oldTail herror hx hy C hpush

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
