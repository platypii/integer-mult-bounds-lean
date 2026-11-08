module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicIntervalRead
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRoundAccuracy

/-! Final rounding is independent of the seam and of the boundary setup geometry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

theorem cyclicIntervalRead_decode {A s : ℕ} [NeZero s] (q w a n : ℕ)
    (ha : a < s) (D : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (i : ZMod s) (hi : i ∈ cyclicPrincipalVertices s a n) :
    cyclicIntervalRead q w a (cstream A w (cyclicInterval a n D)++tail) i =
      value q (decodeWord (csyms A w (D i))) := by
  have hpos : (i-(a : ZMod s)).val < n := by
    rw [cyclicPrincipalVertices_eq a n ha] at hi
    simpa [mem_cyclicHaloLayer,haloLayer,mem_haloVertices] using hi
  have hindex : ((a+(i-(a : ZMod s)).val : ℕ) : ZMod s) = i := by
    rw [Nat.cast_add,ZMod.natCast_zmod_val,add_comm,sub_add_cancel]
  unfold cyclicIntervalRead packedIntervalRead
  rw [Nat.sub_zero,cstream_word w _ tail _ (by simpa only [cyclicInterval_length] using hpos),
    cyclicInterval_get D hpos,hindex]

theorem cyclicIntervalRead_finalRound {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p q j w k E a n : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hk : p+E+5 ≤ k)
    (ha : a < s) (D : ZMod s → GaussianInt) (tail oldTail : List (Fin (A+4)))
    (i : ZMod s) (hi : i ∈ cyclicPrincipalVertices s a n)
    (hD : ‖cyclicIntervalRead q w a (cstream A w (cyclicInterval a n D)++oldTail) i‖ ≤ 8*(2 : ℝ)^E) :
    cyclicIntervalRead p k a
      (cstream A k (cyclicInterval a n (fun i => finalRoundWord w q p j (D i)))++tail) i =
        rhoC p (((2 : ℂ)^j)⁻¹*
          cyclicIntervalRead q w a (cstream A w (cyclicInterval a n D)++oldTail) i) := by
  have hread := cyclicIntervalRead_decode q w a n ha D oldTail i hi
  rw [decodeWord_csyms_symZ hA hw] at hread
  have hnorm : ‖value q (symZ w (D i))‖ ≤ 8*(2 : ℝ)^E := by rwa [hread] at hD
  have hround := finalRound_fits q p j E k hp hk (symZ w (D i)) hnorm
  rw [cyclicIntervalRead_decode p k a n ha _ tail i hi,
    decodeWord_of_fits hA (by omega) (finalRoundWord w q p j (D i)) hround,hread]
  exact value_finalRound q p j hp (symZ w (D i))

theorem cyclicFinalRound_accuracy {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p q j w k E a n : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hk : p+E+5 ≤ k)
    (ha : a < s) (D : ZMod s → GaussianInt)
    (z : ZMod s → ℂ) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ i ∈ cyclicPrincipalVertices s a n, ‖z i‖ ≤ 4*(2 : ℝ)^E)
    (oldTail tail : List (Fin (A+4)))
    (herror : PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead q w a (cstream A w (cyclicInterval a n D)++oldTail)) z e) :
    PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead p k a
        (cstream A k (cyclicInterval a n (fun i => finalRoundWord w q p j (D i)))++tail))
      (fun i => ((2 : ℂ)^j)⁻¹*z i) (2/(2 : ℝ)^p+e/(2 : ℝ)^j) := by
  intro i hi
  have hD := computed_solution_norm_of_error E _ (z i) e he (hz i hi) (herror i hi)
  rw [cyclicIntervalRead_finalRound hA p q j w k E a n hp hw hk ha D tail oldTail i hi hD]
  exact scaleRound_error p j _ _ e (herror i hi)

/-- Real solver accuracy feeds the complex rounding language directly. -/
theorem cyclicRealFinalRound_accuracy {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p q j w k E a n : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hk : p+E+5 ≤ k)
    (ha : a < s) (D : ZMod s → GaussianInt)
    (hreal : ∀ i, (D i).im = 0) (hfits : ∀ i, Fits w (D i))
    (x : ZMod s → ℝ) (e : ℝ) (he : e ≤ 1)
    (hx : ∀ i ∈ cyclicPrincipalVertices s a n, ‖x i‖ ≤ 4*(2 : ℝ)^E)
    (tail : List (Fin (A+4)))
    (herror : PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (fun i => (value q (D i)).re) x e) :
    PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead p k a
        (cstream A k (cyclicInterval a n (fun i => finalRoundWord w q p j (D i)))++tail))
      (fun i => ((2 : ℂ)^j)⁻¹*(x i : ℂ)) (2/(2 : ℝ)^p+e/(2 : ℝ)^j) := by
  apply cyclicFinalRound_accuracy hA p q j w k E a n hp hw hk ha D
    (fun i => (x i : ℂ)) e he
    (by intro i hi; simpa only [Complex.norm_real] using hx i hi) [] tail
  intro i hi
  dsimp only
  rw [cyclicIntervalRead_eq q w a n hA (by omega) ha D hfits [] i hi]
  have hv : value q (D i) = ((value q (D i)).re : ℂ) := by
    apply Complex.ext <;> simp only [value,hreal i,Int.cast_zero,zero_div,Complex.ofReal_re,Complex.ofReal_im]
  rw [hv,←Complex.ofReal_sub,Complex.norm_real]
  exact herror i hi

/-- Every rounded word in the cyclic packet fits, including both sides of the seam. -/
theorem cyclicFinalRound_fits {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (p q j w k E a n : ℕ) (hp : p ≤ q) (hw : 1 ≤ w) (hk : p+E+5 ≤ k)
    (ha : a < s) (hn : n ≤ s) (D : ZMod s → GaussianInt)
    (z : ZMod s → ℂ) (e : ℝ) (he : e ≤ 1)
    (hz : ∀ i ∈ cyclicPrincipalVertices s a n, ‖z i‖ ≤ 4*(2 : ℝ)^E)
    (oldTail : List (Fin (A+4)))
    (herror : PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead q w a (cstream A w (cyclicInterval a n D)++oldTail)) z e) :
    ∀ x ∈ cyclicInterval a n (fun i => finalRoundWord w q p j (D i)), Fits k x := by
  intro x hx
  obtain ⟨r,hr,rfl⟩ := List.mem_iff_getElem.mp hx
  have hrn : r < n := by simpa only [cyclicInterval_length] using hr
  rw [cyclicInterval_get _ hrn]
  let i : ZMod s := ((a+r : ℕ) : ZMod s)
  have hi : i ∈ cyclicPrincipalVertices s a n := by
    rw [cyclicPrincipalVertices_eq a n ha]
    simp only [mem_cyclicHaloLayer,haloLayer,mem_haloVertices,Nat.mul_zero,Nat.add_zero,
      Nat.sub_zero,Nat.zero_le,true_and]
    simp only [i,Nat.cast_add,add_sub_cancel_left,ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hrn
  have hnorm := computed_solution_norm_of_error E _ (z i) e he (hz i hi) (herror i hi)
  have hread := cyclicIntervalRead_decode q w a n ha D oldTail i hi
  rw [decodeWord_csyms_symZ hA hw] at hread
  rw [hread] at hnorm
  exact finalRound_fits q p j E k hp hk (symZ w (D i)) hnorm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
