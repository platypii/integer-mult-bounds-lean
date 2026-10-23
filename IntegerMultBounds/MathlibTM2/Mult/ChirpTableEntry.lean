module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableBounds

/-! # Compute and emit all three chirp table entry types

The word-size envelope discharges all arithmetic overflow checks. Arguments are computed
on the table machine before calling its exponential evaluator. No coefficient value or
exponent argument is supplied as an execution hypothesis.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Resampling.WeightNat

def chirpNegativeNumerator (kernel : Bool) (s t α q offset k0 a : ℕ) : ℕ :=
  expPiNat true q (chirpArgumentN kernel s t offset k0 a) (chirpKD t α)

def tblChirpNegativeEntry (kernel : Bool) : TblCode 48 :=
  .seq (tblChirpArguments kernel) tblChirpExpEmit

theorem tblChirpNegativeEntry_do {A W w q B : ℕ} (st : TblSt 48 A)
    (size : ChirpTableSize W q B) (kernel : Bool) (s t α offset k0 a : ℕ)
    (hpi : st.val 18 = piN q) (hq : st.val 19 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (ho : st.val 37 = offset) (hk : st.val 38 = k0) (ha : st.val 39 = a)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B)
    (hoB : offset ≤ B) (hkB : k0 ≤ B) (haB : a ≤ B) :
    TblDo A W w (tblChirpNegativeEntry kernel) st
      (fun z => z.val 23 = chirpNegativeNumerator kernel s t α q offset k0 a ∧
        z.acc = (csyms A w (⟨(chirpNegativeNumerator kernel s t α q offset k0 a : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc ∧
        ChirpTableFrame st z) (310 * q + 119) := by
  have b := size.arguments kernel s t α offset k0 a hst hsB htB hαB hoB hkB haB
  have hargs := tblChirpArguments_do (w := w) st kernel s t α offset k0 a hs ht hα ho hk ha
    b.ordered b.dimT b.one b.originProduct b.shiftedIndex b.positiveDistance b.offsetProduct
    b.negativeDistance b.distanceSquare b.numerator b.tSquared b.tCubed b.alphaSquared b.denominator
  have htail : ∀ u : TblSt 48 A,
      u.val 20 = chirpArgumentN kernel s t offset k0 a ∧ u.val 21 = chirpKD t α ∧
        u.val 22 = 1 ∧ u.acc = st.acc ∧ ChirpTableFrame st u →
      TblDo A W w tblChirpExpEmit u
        (fun z => z.val 23 = chirpNegativeNumerator kernel s t α q offset k0 a ∧
          z.acc = (csyms A w (⟨(chirpNegativeNumerator kernel s t α q offset k0 a : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc ∧
          ChirpTableFrame st z) (310 * q + 102) := by
    intro u ⟨hn, hd, hneg, hacc, hf⟩
    have he := tblChirpExpEmit_do (w := w) u true q (chirpArgumentN kernel s t offset k0 a) (chirpKD t α)
      (hf.1.trans hpi) (hf.2.1.trans hq) hn hd hneg size.precision size.word
      (size.negativeNumerator kernel s t offset k0 a hsB htB hoB hkB haB) (by intro h; cases h)
    exact he.mono (fun z hz => ⟨hz.1, by simpa only [hacc, chirpNegativeNumerator] using hz.2.1,
      chirpTableFrame_trans hf hz.2.2⟩) le_rfl
  exact (hargs.seq htail).mono (fun z h => h) (by omega)

theorem chirpNegativeNumerator_input (s t α q m k0 a : ℕ) :
    chirpNegativeNumerator false s t α q m k0 a = chirpTableG s t α q m k0 a := by
  simp [chirpNegativeNumerator, chirpArgumentN_input, chirpTableG]

theorem chirpNegativeNumerator_kernel (s t α q m k0 j : ℕ) (hm : 1 ≤ m) :
    chirpNegativeNumerator true s t α q (2 * m - 1) k0 j =
      chirpTableK s t α q m k0 ((j : ℤ) - (m - 1 : ℕ)) := by
  simp [chirpNegativeNumerator, chirpArgumentN_kernel s t m k0 j hm, chirpTableK]

def tblChirpOutputEntry : TblCode 48 := .seq tblChirpOutputArguments tblChirpExpEmit

theorem tblChirpOutputEntry_do {A W w q B : ℕ} (st : TblSt 48 A)
    (size : ChirpTableSize W q B) (s t α b : ℕ)
    (hpi : st.val 18 = piN q) (hq : st.val 19 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α) (hb : st.val 39 = b)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hbB : b ≤ B)
    (ht0 : 0 < t) (hα0 : 0 < α) (hgate : 4 * chirpEN s t b ≤ (q - 1) * chirpED t α) :
    TblDo A W w tblChirpOutputEntry st
      (fun z => z.val 23 = chirpTableE s t α q b ∧
        z.acc = (csyms A w (⟨(chirpTableE s t α q b : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc ∧
        ChirpTableFrame st z) (310 * q + 110) := by
  have bounds := size.output s t α b hst hsB htB hαB hbB
  have hargs := tblChirpOutputArguments_do (w := w) st s t α b hs ht hα hb
    bounds.ordered bounds.dimT bounds.indexSquared bounds.difference bounds.numerator
    bounds.tSquared bounds.alphaSquared bounds.denominator
  have htail : ∀ u : TblSt 48 A,
      u.val 20 = chirpEN s t b ∧ u.val 21 = chirpED t α ∧ u.val 22 = 0 ∧
        u.acc = st.acc ∧ ChirpTableFrame st u →
      TblDo A W w tblChirpExpEmit u
        (fun z => z.val 23 = chirpTableE s t α q b ∧
          z.acc = (csyms A w (⟨(chirpTableE s t α q b : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc ∧
          ChirpTableFrame st z) (310 * q + 102) := by
    intro u ⟨hn, hd, hneg, hacc, hf⟩
    have he := tblChirpExpEmit_do (w := w) u false q (chirpEN s t b) (chirpED t α)
      (hf.1.trans hpi) (hf.2.1.trans hq) hn hd hneg size.precision size.word
      (size.outputNumerator s t b hsB htB hbB)
      (fun _ => chirp_positive_machine_gate q _ _ size.precision (by unfold chirpED; positivity) hgate)
    exact he.mono (fun z hz => ⟨hz.1, by simpa only [hacc, chirpTableE] using hz.2.1,
      chirpTableFrame_trans hf hz.2.2⟩) le_rfl
  exact (hargs.seq htail).mono (fun z h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
