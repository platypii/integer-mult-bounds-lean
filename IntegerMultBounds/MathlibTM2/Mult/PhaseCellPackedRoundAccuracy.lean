module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPairAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinalRoundList
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedError

/-! Normalize local decoded outputs, retaining ambient coordinates and suffixes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine

/-- The normalized local reader is exactly rounded scaling of the old physical
reader. Fixed-width reduction is handled before rounding, with no input Fits. -/
theorem packedIntervalRead_finalRound {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p q j w k E a L : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hk : p+E+5 ≤ k)
    (D : ZMod s → GaussianInt) (tail oldTail : List (Fin (A+4)))
    (hfit : a+L ≤ s) (i : ZMod s) (ha : a ≤ i.val) (hi : i.val < a+L)
    (hD : ‖packedIntervalRead q w a (cstream A w (packedInterval a L D)++oldTail) i‖ ≤ 8*(2 : ℝ)^E) :
    packedIntervalRead p k a
      (cstream A k (packedInterval a L (fun i => finalRoundWord w q p j (D i)))++tail) i =
        rhoC p (((2 : ℂ)^j)⁻¹*
          packedIntervalRead q w a (cstream A w (packedInterval a L D)++oldTail) i) := by
  have hread := packedIntervalRead_decode q w a L D oldTail hfit i ha hi
  rw [decodeWord_csyms_symZ hA hw] at hread
  have hnorm : ‖value q (symZ w (D i))‖ ≤ 8*(2 : ℝ)^E := by rwa [hread] at hD
  have hround := finalRound_fits q p j E k hp hk (symZ w (D i)) hnorm
  rw [packedIntervalRead_decode p k a L _ tail hfit i ha hi,
    decodeWord_of_fits hA (by omega) (finalRoundWord w q p j (D i)) hround,hread]
  exact value_finalRound q p j hp (symZ w (D i))

/-- Accuracy supplies the required output magnitude bound from the target's
bound. Normalization adds one rounding error and scales the solver error. -/
theorem packedFinalRound_accuracy {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p q j w k E a L : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hk : p+E+5 ≤ k)
    (D : ZMod s → GaussianInt) (active : Finset (ZMod s))
    (hfit : a+L ≤ s) (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (z : ZMod s → ℂ) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^E)
    (oldTail tail : List (Fin (A+4)))
    (herror : PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w a (cstream A w (packedInterval a L D)++oldTail)) z e) :
    PhaseCellInterface.ErrorOn active
      (packedIntervalRead p k a
        (cstream A k (packedInterval a L (fun i => finalRoundWord w q p j (D i)))++tail))
      (fun i => ((2 : ℂ)^j)⁻¹*z i) (2/(2 : ℝ)^p+e/(2 : ℝ)^j) := by
  intro i hi
  have hnorm := norm_le_norm_sub_add
    (packedIntervalRead q w a (cstream A w (packedInterval a L D)++oldTail) i) (z i)
  have hpow : (1 : ℝ) ≤ 2^E := one_le_pow₀ (by norm_num)
  have hD : ‖packedIntervalRead q w a (cstream A w (packedInterval a L D)++oldTail) i‖ ≤ 8*(2 : ℝ)^E := by
    have herr := herror i hi
    have htarget := hz i hi
    linarith
  rw [packedIntervalRead_finalRound hA p q j w k E a L hp hw hk D tail oldTail hfit i
    (hactive i hi).1 (hactive i hi).2 hD]
  exact scaleRound_error p j _ _ e (herror i hi)

/-- Normalize an ordered replica certificate with the same error for every
replica. There is no additional loss from flattening or the number of packets. -/
theorem packedFinalRoundBatch_accuracy {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p q j w k E a L : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hk : p+E+5 ≤ k)
    (active : Finset (ZMod s)) (hfit : a+L ≤ s)
    (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ z ∈ Zs, ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^E)
    (oldTail tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w a (cstream A w (packedInterval a L D)++oldTail)) z e) Zs Ds) :
    List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead p k a (cstream A k (packedInterval a L D)++tail)) z
        (2/(2 : ℝ)^p+e/(2 : ℝ)^j))
      (Zs.map (fun z i => ((2 : ℂ)^j)⁻¹*z i))
      (Ds.map (fun D i => finalRoundWord w q p j (D i))) := by
  induction hgood with
  | nil => exact .nil
  | @cons z D Zs Ds herror hgood ih =>
    exact .cons (packedFinalRound_accuracy hA p q j w k E a L hp hw hk D active hfit hactive
      z e he (hz z (by simp)) oldTail tail herror)
      (ih (by intro z hzmem; exact hz z (List.mem_cons_of_mem _ hzmem)))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
