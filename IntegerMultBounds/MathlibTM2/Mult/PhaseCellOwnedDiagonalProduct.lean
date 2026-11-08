module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandProductRunsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream

/-! Apply the generated local D' page with the existing varying-real-factor
stream. Both the input and coefficient page restore for replica reuse. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.Resampling.WeightTable
variable {s t α p : ℕ} [NeZero s] [NeZero t]

theorem diagonalField_fits (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α^2 ≤ p)
    (w : ℕ) (hw : p+2 ≤ w) (i : ZMod s) : Fits w (diagonalField s t α p i) := by
  obtain ⟨_,hlo,hhi⟩ := tableD_spec s t α p hp hα hαp i
  change |tableD s t α p i| < (2 : ℤ)^(w-1) ∧ |(0 : ℤ)| < (2 : ℤ)^(w-1)
  constructor
  · rw [abs_of_nonneg hlo]
    apply hhi.trans_lt
    exact_mod_cast (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : p < w-1))
  · simp

omit [NeZero s] [NeZero t] in
theorem packedInterval_diagonalProduct (D : ZMod s → GaussianInt) (c n : ℕ) :
    List.zipWith (fun x y => tdivN p (x*y)) (packedInterval c n D)
      (packedInterval c n (diagonalField s t α p)) =
      packedInterval c n (diagonalProduct s t α p D) := by
  simp [packedInterval,chirpLine,←List.map_take,←List.map_drop,List.zipWith_map,List.zipWith_self,
    diagonalProduct]

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem rsb_diagonalInterval_runs_within
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {x y o : RsbR} (hfree : RsbFree x y o) {w c n : ℕ}
    (ρ : RsbR → List (Fin (A+4))) (hr : RsbReady ρ w p) (hw : p+2 ≤ w)
    (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α^2 ≤ p)
    (D : ZMod s → GaussianInt) (hfit : c+n ≤ s)
    (hD : ∀ z ∈ packedInterval c n D, Fits w z)
    (hx : ρ x = cstream A w (packedInterval c n D))
    (hy : ρ y = cstream A w (packedInterval c n (diagonalField s t α p)))
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg x y o)) ≤ C) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι)
      (cmulStream (rsbCr rg x y o) (rmulOne ι hι hT hQ (rsbCr rg x y o))) ρ
      (Function.update ρ o (cstream A w (packedInterval c n (diagonalProduct s t α p D))++ρ o))
      (n*(rmulCost w+6*w+2)+8) (realWeightWorkspace C w n) := by
  have htable : ∀ z ∈ packedInterval c n (diagonalField s t α p), Fits w z ∧ z.im = 0 := by
    intro z hz
    have hz' := List.mem_of_mem_drop (List.mem_of_mem_take hz)
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz'
    exact ⟨diagonalField_fits hp hα hαp w hw _,rfl⟩
  have he := rsb_rmulStream_runs_within (body := body) hrg hdisj hι hT hQ hA hfree ρ hr
    (by omega) (by omega) (packedInterval c n D) (packedInterval c n (diagonalField s t α p))
    (by rw [packedInterval_length _ hfit,packedInterval_length _ hfit]) hD htable hx hy C hpush
  simpa only [packedInterval_diagonalProduct,packedInterval_length D hfit] using he

theorem diagonalPacket_accuracy {w c n : ℕ} (hA : 4 ≤ A) (hw : p+3 ≤ w)
    (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α^2 ≤ p) (hfit : c+n ≤ s)
    (active : Finset (ZMod s)) (hactive : ∀ i ∈ active, c ≤ i.val ∧ i.val < c+n)
    (D : ZMod s → GaussianInt) (z : ZMod s → ℂ) (error : ℝ) (tail : List (Fin (A+4)))
    (hD : ∀ i ∈ active, ‖value p (D i)‖ ≤ 2)
    (herror : PhaseCellInterface.ErrorOn active (fun i => value p (D i)) z error) :
    PhaseCellInterface.ErrorOn active
      (packedIntervalRead p w c (cstream A w (packedInterval c n (diagonalProduct s t α p D))++tail))
      (fun i => (IntegerMultBounds.NLogN.dPrime s t (α : ℝ) i : ℂ)*z i) (6/(2 : ℝ)^p+error) := by
  have herr := diagonalProduct_accuracy (t := t) hp hα hαp active D z error hD herror
  intro i hi
  rw [packedIntervalRead_eq p w c n _ tail [] hfit i (hactive i hi).1 (hactive i hi).2,
    pairedCellRead_encodedField hA (by omega) _ [] i]
  · exact herr i hi
  · apply fits_of_value_power (e := 1) (by omega)
    simpa only [pow_one] using (diagonalProduct_norm_le (t := t) hp hα hαp D i).trans (hD i hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
