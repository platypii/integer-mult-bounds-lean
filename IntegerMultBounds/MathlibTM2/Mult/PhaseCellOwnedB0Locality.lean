module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedGlobalTargets
public import IntegerMultBounds.NLogN.ResamplingNumeric

/-! The owned principal target approaches the normalized ambient D-prime target. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RecoveryAxisBounds
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
variable {s t p u l : ℕ} [NeZero s] {alpha gap : ℝ}

theorem ownedTargets_diagonal_global_error (h : RecoveryAxisBounds s t p u l alpha gap) (target L k j : ℕ)
    (hnear : t ≤ 2*s) (hL : 2 ≤ L)
    (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
    (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    List.Forall₂ (fun F z => ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1)))
      (fun i => (dPrime s t alpha i : ℂ)*(((2 : ℂ)^j)⁻¹*z i))
      (fun i => (dPrime s t alpha i : ℂ)*(((2 : ℂ)^j)⁻¹*h.globalHalfGridTarget F i))
      ((2/(2 : ℝ)^target)/(2 : ℝ)^j)) Fs (h.ownedTargets target L k hnear hL ha hb hfit Fs) := by
  let : NeZero t := ⟨Nat.ne_of_gt ((NeZero.pos s).trans h.hst)⟩
  apply List.Forall₂.imp _ (h.ownedTargets_global_error target L k hnear hL ha hb hfit Fs hF)
  intro F z herr i hi
  have hD : ‖(dPrime s t alpha i : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (dPrime_nonneg i)]
    exact dPrime_le_one i
  have heq : (dPrime s t alpha i : ℂ)*(((2 : ℂ)^j)⁻¹*z i)-
      (dPrime s t alpha i : ℂ)*(((2 : ℂ)^j)⁻¹*h.globalHalfGridTarget F i) =
      (dPrime s t alpha i : ℂ)*((2 : ℂ)^j)⁻¹*(z i-h.globalHalfGridTarget F i) := by ring
  rw [heq,norm_mul,norm_mul,norm_inv,norm_pow,Complex.norm_ofNat]
  calc
    _ ≤ 1*((2 : ℝ)^j)⁻¹*(2/(2 : ℝ)^target) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hD (by positivity)) (herr i hi) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem ownedDiagonal_global_accuracy (h : RecoveryAxisBounds s t p u l alpha gap) (target L k j : ℕ)
    (hnear : t ≤ 2*s) (hL : 2 ≤ L)
    (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
    (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod t → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    {A : ℕ} (w : ℕ) (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4))) (arithmetic : ℝ)
    (hgood : List.Forall₂ (fun z D => ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1)))
      (packedIntervalRead p w (cut s t L k) (cstream A w (packedInterval (cut s t L k) (rows s t L k) D)++tail)) z arithmetic)
      ((h.ownedTargets target L k hnear hL ha hb hfit Fs).map
        (fun z i => (dPrime s t alpha i : ℂ)*(((2 : ℂ)^j)⁻¹*z i))) Ds) :
    List.Forall₂ (fun F D => ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1)))
      (packedIntervalRead p w (cut s t L k) (cstream A w (packedInterval (cut s t L k) (rows s t L k) D)++tail))
      (fun i => (dPrime s t alpha i : ℂ)*(((2 : ℂ)^j)⁻¹*h.globalHalfGridTarget F i))
      (arithmetic+(2/(2 : ℝ)^target)/(2 : ℝ)^j)) Fs Ds := by
  rw [List.forall₂_map_left_iff] at hgood
  have hlocal := h.ownedTargets_diagonal_global_error target L k j hnear hL ha hb hfit Fs hF
  generalize hz : h.ownedTargets target L k hnear hL ha hb hfit Fs = Zs at hlocal hgood
  clear hF hz
  induction hlocal generalizing Ds with
  | nil => cases hgood; exact .nil
  | cons herr hrest ih =>
    cases hgood with
    | cons herror hgood => exact .cons (herror.trans herr) (ih _ hgood)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RecoveryAxisBounds
