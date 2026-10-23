module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableRows

/-! # Chirp table streams from dimension and precision words

Generate the Machin pi numerator once, then execute the row. The starting bank contains
only dimensions and counters; it supplies no pi approximation, exponent arguments or
coefficient numerators. The row output remains on the reversed-symbol accumulator used by
the standard table-host compiler.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Resampling.WeightNat

def tblChirpNegativeStream (kernel : Bool) : TblCode 48 :=
  .seq tblChirpPiSetup (tblChirpNegativeRow kernel)

theorem tblChirpNegativeStream_do {A W w q B : ℕ} (st : TblSt 48 A) (size : ChirpTableSize W q B)
    (kernel : Bool) (s t α offset k0 N : ℕ) (hq : st.val 19 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (ho : st.val 37 = offset) (hk : st.val 38 = k0) (hN : st.val 44 = N)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hoB : offset ≤ B)
    (hkB : k0 ≤ B) (hNB : N ≤ B) :
    TblDo A W w (tblChirpNegativeStream kernel) st
      (fun z => z.acc = (chirpEntryStream A w N (fun j => chirpNegativeNumerator kernel s t α q offset k0 j)).reverse ++ st.acc ∧
        z.val 18 = piN q ∧ z.val 19 = q ∧ z.val 39 = N ∧
        ∀ i : Fin 48, 34 ≤ i.val → i ≠ 39 → i ≠ 40 → i ≠ 41 → z.val i = st.val i)
      (N * (310 * q + 122) + 150 * q + 404) := by
  have hp := tblChirpPiSetup_do (W := W) (w := w) st q hq (by have := size.precision; omega)
    (by have := size.precision; have := size.word; omega)
  have hrun : TblDo A W w (tblChirpNegativeStream kernel) st
      (fun z => z.acc = (chirpEntryStream A w N (fun j => chirpNegativeNumerator kernel s t α q offset k0 j)).reverse ++ st.acc ∧
        z.val 18 = piN q ∧ z.val 19 = q ∧ z.val 39 = N ∧
        ∀ i : Fin 48, 34 ≤ i.val → i ≠ 39 → i ≠ 40 → i ≠ 41 → z.val i = st.val i)
      ((150 * q + 401) + (N * (310 * q + 122) + 3)) := hp.seq (fun u ⟨hpi, hacc, hhigh⟩ =>
    (tblChirpNegativeRow_do (w := w) u size kernel s t α offset k0 N hpi
      ((hhigh _ (by decide)).trans hq)
      ((hhigh _ (by decide)).trans hs) ((hhigh _ (by decide)).trans ht)
      ((hhigh _ (by decide)).trans hα) ((hhigh _ (by decide)).trans ho)
      ((hhigh _ (by decide)).trans hk) ((hhigh _ (by decide)).trans hN)
      hst hsB htB hαB hoB hkB hNB).mono
      (fun z ⟨hemit, hindex, hf⟩ =>
        ⟨by simpa only [hacc] using hemit, hf.1.trans hpi,
          hf.2.1.trans ((hhigh _ (by decide)).trans hq), hindex,
          fun i hi h39 h40 h41 => (hf.2.2 i hi h39 h40 h41).trans (hhigh i (by omega))⟩) le_rfl)
  exact hrun.mono (fun z h => h) (by omega)

def tblChirpOutputStream : TblCode 48 := .seq tblChirpPiSetup tblChirpOutputRow

theorem tblChirpOutputStream_do {A W w q B : ℕ} (st : TblSt 48 A) (size : ChirpTableSize W q B)
    (s t α N : ℕ) (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t)
    (hα : st.val 36 = α) (hN : st.val 44 = N) (hst : s ≤ t)
    (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hNB : N ≤ B) (ht0 : 0 < t) (hα0 : 0 < α)
    (hgate : ∀ b < N, 4 * chirpEN s t b ≤ (q - 1) * chirpED t α) :
    TblDo A W w tblChirpOutputStream st
      (fun z => z.acc = (chirpEntryStream A w N (fun b => chirpTableE s t α q b)).reverse ++ st.acc ∧
        z.val 18 = piN q ∧ z.val 19 = q ∧ z.val 39 = N ∧
        ∀ i : Fin 48, 34 ≤ i.val → i ≠ 39 → i ≠ 40 → i ≠ 41 → z.val i = st.val i)
      (N * (310 * q + 113) + 150 * q + 404) := by
  have hp := tblChirpPiSetup_do (W := W) (w := w) st q hq (by have := size.precision; omega)
    (by have := size.precision; have := size.word; omega)
  have hrun : TblDo A W w tblChirpOutputStream st
      (fun z => z.acc = (chirpEntryStream A w N (fun b => chirpTableE s t α q b)).reverse ++ st.acc ∧
        z.val 18 = piN q ∧ z.val 19 = q ∧ z.val 39 = N ∧
        ∀ i : Fin 48, 34 ≤ i.val → i ≠ 39 → i ≠ 40 → i ≠ 41 → z.val i = st.val i)
      ((150 * q + 401) + (N * (310 * q + 113) + 3)) := hp.seq (fun u ⟨hpi, hacc, hhigh⟩ =>
    (tblChirpOutputRow_do (w := w) u size s t α N hpi ((hhigh _ (by decide)).trans hq)
      ((hhigh _ (by decide)).trans hs) ((hhigh _ (by decide)).trans ht)
      ((hhigh _ (by decide)).trans hα) ((hhigh _ (by decide)).trans hN)
      hst hsB htB hαB hNB ht0 hα0 hgate).mono
      (fun z ⟨hemit, hindex, hf⟩ =>
        ⟨by simpa only [hacc] using hemit, hf.1.trans hpi,
          hf.2.1.trans ((hhigh _ (by decide)).trans hq), hindex,
          fun i hi h39 h40 h41 => (hf.2.2 i hi h39 h40 h41).trans (hhigh i (by omega))⟩) le_rfl)
  exact hrun.mono (fun z h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
