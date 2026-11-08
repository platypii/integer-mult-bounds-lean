module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedDiagonalProduct
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRoundAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedRadius

/-! Derive real-factor input fits and accuracy from the actual recovery packet. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
variable {s t A p q α W c n target : ℕ} [NeZero s] [NeZero t]

omit [NeZero s] in
theorem packedInterval_fits_of_active (D : ZMod s → GaussianInt)
    (active : Finset (ZMod s)) (hfit : c+n ≤ s)
    (hcover : ∀ i : ZMod s, c ≤ i.val → i.val < c+n → i ∈ active)
    (hfits : ∀ i ∈ active, Fits W (D i)) :
    ∀ x ∈ packedInterval c n D, Fits W x := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hx
  have hjn : j < n := by simpa only [packedInterval_length D hfit] using hj
  rw [packedInterval_get D hfit hjn]
  have hval : (((c+j : ℕ) : ZMod s)).val = c+j := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (show c+j < s by omega)]
  exact hfits _ (hcover _ (by omega) (by omega))

theorem roundedDiagonal_accuracy (hA : 4 ≤ A) (hp : 13 ≤ p) (hpq : p ≤ q)
    (hW : 2*p+13 ≤ W) (hα : 1 ≤ α) (hαp : α^2 ≤ p)
    (active : Finset (ZMod s)) (hfit : c+n ≤ s)
    (hactive : ∀ i ∈ active, c ≤ i.val ∧ i.val < c+n)
    (D : ZMod s → GaussianInt) (z : ZMod s → ℂ)
    (hmag : ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^(p+8))
    (hscale : ∀ i ∈ active, ‖((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i‖ ≤ (3/2 : ℝ))
    (oldTail tail : List (Fin (A+4)))
    (herror : PhaseCellInterface.ErrorOn active
      (packedIntervalRead q (2*q+8) c (cstream A (2*q+8) (packedInterval c n D)++oldTail)) z (1/(2 : ℝ)^target)) :
    let G := fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)
    (∀ i ∈ active, Fits W (G i)) ∧
    (∀ i ∈ active, ‖value p (G i)‖ ≤ 2) ∧
    PhaseCellInterface.ErrorOn active
      (packedIntervalRead p W c (cstream A W (packedInterval c n (diagonalProduct s t α p G))++tail))
      (fun i => (dPrime s t (α : ℝ) i : ℂ)*(((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i))
      (8/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)) := by
  dsimp only
  let G := fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i)
  have he : 1/(2 : ℝ)^target ≤ 1 :=
    (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hfits : ∀ i ∈ active, Fits W (G i) := by
    intro i hi
    have hn := computed_solution_norm_of_error (p+8) _ (z i) (1/(2 : ℝ)^target) he (hmag i hi) (herror i hi)
    have hread := packedIntervalRead_decode q (2*q+8) c n D oldTail hfit i (hactive i hi).1 (hactive i hi).2
    rw [decodeWord_csyms_symZ hA (by omega)] at hread
    rw [hread] at hn
    exact finalRound_fits q p (inverseNormalizationShift p) (p+8) W hpq (by omega) _ hn
  have hdecode : ∀ i ∈ active, packedIntervalRead p W c (cstream A W (packedInterval c n G)++tail) i = value p (G i) := by
    intro i hi
    rw [packedIntervalRead_eq p W c n G tail [] hfit i (hactive i hi).1 (hactive i hi).2,
      pairedCellRead_encodedField hA (by omega) _ [] i (hfits i hi)]
  have hpublished := packedFinalRound_accuracy hA p q (inverseNormalizationShift p) (2*q+8) W (p+8) c n
    hpq (by omega) (by omega) D active hfit hactive z (1/(2 : ℝ)^target) he hmag oldTail tail herror
  have hvalue : PhaseCellInterface.ErrorOn active (fun i => value p (G i))
      (fun i => ((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i)
      (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p)) := by
    intro i hi
    have hh := hpublished i hi
    rw [hdecode i hi] at hh
    exact hh
  have hradius := published_norm_le_two p target (by omega) active _ _ hscale hvalue
  refine ⟨hfits,hradius,?_⟩
  have hd := diagonalPacket_accuracy (t := t) (w := W) (p := p) (α := α) hA (by omega) hp hα hαp hfit active hactive G
    (fun i => ((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i) _ tail hradius hvalue
  convert hd using 1
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
