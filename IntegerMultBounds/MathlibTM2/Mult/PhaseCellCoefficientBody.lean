module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientExp
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWords

/-! # One off-diagonal Toeplitz distance coefficient on the table machine -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

def coefficientBody : TblCode 48 :=
  .ite 37 39 (.ins (.emit 41 41))
    (.ite 38 37 (.ins (.emit 41 41))
      (tblBlock 48 [.mul 37 37 20] (.mul 40 20 20) ;;
        coefficientExpCode.rename tblExpMap48))

/-- The body emits zero on the diagonal and outside the band, and otherwise
runs the corrected exponential on the unreduced Gaussian argument. -/
theorem coefficientBody_do {A V w P s t u band k : ℕ} (st : TblSt 48 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hs : st.val 21 = s)
    (hneg : st.val 22 = 1) (hk : st.val 37 = k) (hband : st.val 38 = band)
    (hone : st.val 39 = 1) (hbase : st.val 40 = u * t) (hz : st.val 41 = 0)
    (hP : 13 ≤ P) (hs0 : 0 < s) (hV : 13 * P + 8 ≤ V)
    (hkV : k * k < 2 ^ V) (haV : (u * t * k ^ 2) * 2 ^ (5 * P + 2) < 2 ^ V) :
    TblDo A V w coefficientBody st (fun st' =>
      st'.acc = (csyms A w (distanceFactorWord P s t u band k)).reverse ++ st.acc ∧
      st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧
      st'.val 21 = st.val 21 ∧ st'.val 22 = st.val 22 ∧
      ∀ x : Fin 48, 34 ≤ x.val → st'.val x = st.val x) (310 * P + 111) := by
  have hzero : TblDo A V w (.ins (.emit 41 41)) st
      (fun st' => st'.acc = (csyms A w 0).reverse ++ st.acc ∧
        st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧
      st'.val 21 = st.val 21 ∧ st'.val 22 = st.val 22 ∧
        ∀ x : Fin 48, 34 ≤ x.val → st'.val x = st.val x) 1 := by
    apply TblDo.insX (.emit 41 41) trivial
    simp [TblIns.exact, hz, csyms, coeffSyms, red, tblPairs]
  by_cases hk0 : k = 0
  · rcases hk0 with rfl
    exact (TblDo.iteT (by simp [hk, hone]) hzero).mono
      (fun st' h => by simpa [distanceFactorWord] using h) (by omega)
  by_cases hcut : band < k
  · exact (TblDo.iteF (by simp [hk, hone]; omega)
      (TblDo.iteT (by simpa [hband, hk] using hcut) hzero)).mono
      (fun st' h => by simpa [distanceFactorWord, hk0, coefficientNumerator, show ¬ k ≤ band by omega, show (⟨(0 : ℤ), 0⟩ : GaussianInt) = 0 from rfl] using h)
      (by omega)
  have hcoef : distanceFactorWord P s t u band k =
      (⟨(PhaseCellExpSample.numerator P (u * t * k ^ 2) s : ℤ), 0⟩ : GaussianInt) := by
    simp only [distanceFactorWord, hk0, ite_false, coefficientNumerator_gaussian (P := P) (s := s) (t := t) (u := u) (band := band) hk0 (by omega)]
  have ha0 : u * t * k ^ 2 < 2 ^ V := by
    have hp : 1 ≤ 2 ^ (5 * P + 2) := Nat.one_le_two_pow
    nlinarith
  have hkpow : k ^ 2 < 2 ^ V := by simpa only [pow_two] using hkV
  let S₁ : TblSt 48 A := ⟨Function.update (Function.update st.val 20 (k * k)) 20 (u * t * k ^ 2), st.acc⟩
  have hargs : TblDo A V w (tblBlock 48 [.mul 37 37 20] (.mul 40 20 20)) st
      (fun st' => st' = S₁) 2 := by
    apply TblDo.block
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hk, hbase, hkpow, ← pow_two, ha0]
    · simp [tblExactList, TblIns.exact, S₁, hk, hbase, pow_two]
  have hexp := (coefficientExpCode_do (A := A) (V := V) (w := w)
    (S₁.restrict tblExpMap48) (by simpa [S₁, TblSt.restrict, tblExpMap48] using hpi)
    (by simpa [S₁, TblSt.restrict, tblExpMap48] using hP')
    (by simp [S₁, TblSt.restrict, tblExpMap48])
    (by simpa [S₁, TblSt.restrict, tblExpMap48] using hs)
    (by simpa [S₁, TblSt.restrict, tblExpMap48] using hneg) hP hs0 hV haV).rename
      (show Function.Injective tblExpMap48 by intro i j h; exact Fin.ext (show i.val = j.val from congrArg (fun x : Fin 48 => x.val) h))
  have hbody : TblDo A V w
      (tblBlock 48 [.mul 37 37 20] (.mul 40 20 20) ;; coefficientExpCode.rename tblExpMap48) st
      (fun st' => st'.acc = (csyms A w (distanceFactorWord P s t u band k)).reverse ++ st.acc ∧
        st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧
      st'.val 21 = st.val 21 ∧ st'.val 22 = st.val 22 ∧
        ∀ x : Fin 48, 34 ≤ x.val → st'.val x = st.val x) (2 + (310 * P + 107)) := by
    refine hargs.seq (fun st' he => ?_)
    subst st'
    refine hexp.mono ?_ le_rfl
    intro st' ⟨⟨hout, hpi', hP'', hs', hneg'⟩, hframe⟩
    refine ⟨by simpa [S₁, TblSt.restrict, hcoef] using hout, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [S₁, TblSt.restrict, tblExpMap48] using hpi'
    · simpa [S₁, TblSt.restrict, tblExpMap48] using hP''
    · simpa [S₁, TblSt.restrict, tblExpMap48] using hs'
    · simpa [S₁, TblSt.restrict, tblExpMap48] using hneg'
    · intro x hx
      rw [hframe x (tbl_castLE_ne (by decide) x hx)]
      have hoff : x ≠ 20 := by intro he; have hv := congrArg Fin.val he; omega
      simp [S₁, hoff]
  exact (TblDo.iteF (by simp [hk, hone]; omega)
    (TblDo.iteF (by simpa [hband, hk] using hcut) hbody)).mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
