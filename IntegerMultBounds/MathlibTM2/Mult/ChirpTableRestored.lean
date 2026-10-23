module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableCleanup

/-! # Chirp table generation with complete working-bank restoration

The precision and dimension/control inputs are retained; every owned evaluator, row-index,
and distance word is cleared back to its initial zero. Only the emitted stream changes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

private theorem tblChirpClearStream_do {A W w : ℕ} (st : TblSt 48 A) (code : TblCode 48)
    (words : List (Fin (A + 4))) (K : ℕ)
    (run : TblDo A W w code st
      (fun z => z.acc = words.reverse ++ st.acc ∧ z.val 19 = st.val 19 ∧
        ∀ i : Fin 48, 34 ≤ i.val → i ≠ 39 → i ≠ 40 → i ≠ 41 → z.val i = st.val i) K)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0) :
    TblDo A W w (.seq code (tblChirpZeroWords chirpTableOwned)) st
      (fun z => z.val = st.val ∧ z.acc = words.reverse ++ st.acc) (K + 37) := by
  have hrun := run.seq (fun u ⟨ha, hq, hf⟩ =>
    (tblChirpZeroWords_do (W := W) (w := w) chirpTableOwned u).mono
      (P' := fun z => z.val = st.val ∧ z.acc = words.reverse ++ st.acc)
      (fun z ⟨hv, hacc⟩ =>
        ⟨hv.trans (chirpTableOwned_restore st u howned hq hf), hacc.trans ha⟩) le_rfl)
  exact hrun.mono (fun z h => h) (by simp only [chirpTableOwned_length]; omega)

def tblChirpNegativeTable (kernel : Bool) : TblCode 48 :=
  .seq (tblChirpNegativeStream kernel) (tblChirpZeroWords chirpTableOwned)

theorem tblChirpNegativeTable_do {A W w q B : ℕ} (st : TblSt 48 A) (size : ChirpTableSize W q B)
    (kernel : Bool) (s t α offset k0 N : ℕ) (hq : st.val 19 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (ho : st.val 37 = offset) (hk : st.val 38 = k0) (hN : st.val 44 = N)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hoB : offset ≤ B)
    (hkB : k0 ≤ B) (hNB : N ≤ B) (howned : ∀ i ∈ chirpTableOwned, st.val i = 0) :
    TblDo A W w (tblChirpNegativeTable kernel) st
      (fun z => z.val = st.val ∧
        z.acc = (chirpEntryStream A w N (fun j => chirpNegativeNumerator kernel s t α q offset k0 j)).reverse ++ st.acc)
      (N * (310 * q + 122) + 150 * q + 441) := by
  have h := tblChirpNegativeStream_do (w := w) st size kernel s t α offset k0 N hq hs ht hα ho hk hN
    hst hsB htB hαB hoB hkB hNB
  have hc := tblChirpClearStream_do st (tblChirpNegativeStream kernel) _ _
    (h.mono (P' := fun z => z.acc = (chirpEntryStream A w N
        (fun j => chirpNegativeNumerator kernel s t α q offset k0 j)).reverse ++ st.acc ∧
        z.val 19 = st.val 19 ∧
        ∀ i : Fin 48, 34 ≤ i.val → i ≠ 39 → i ≠ 40 → i ≠ 41 → z.val i = st.val i)
      (fun z hz => ⟨hz.1, hz.2.2.1.trans hq.symm, hz.2.2.2.2⟩) le_rfl) howned
  exact hc.mono (fun z h => h) (by omega)

def tblChirpOutputTable : TblCode 48 := .seq tblChirpOutputStream (tblChirpZeroWords chirpTableOwned)

theorem tblChirpOutputTable_do {A W w q B : ℕ} (st : TblSt 48 A) (size : ChirpTableSize W q B)
    (s t α N : ℕ) (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t)
    (hα : st.val 36 = α) (hN : st.val 44 = N) (hst : s ≤ t)
    (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hNB : N ≤ B) (ht0 : 0 < t) (hα0 : 0 < α)
    (hgate : ∀ b < N, 4 * chirpEN s t b ≤ (q - 1) * chirpED t α)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0) :
    TblDo A W w tblChirpOutputTable st
      (fun z => z.val = st.val ∧
        z.acc = (chirpEntryStream A w N (fun b => chirpTableE s t α q b)).reverse ++ st.acc)
      (N * (310 * q + 113) + 150 * q + 441) := by
  have h := tblChirpOutputStream_do (w := w) st size s t α N hq hs ht hα hN hst hsB htB hαB hNB
    ht0 hα0 hgate
  have hc := tblChirpClearStream_do st tblChirpOutputStream _ _
    (h.mono (P' := fun z => z.acc = (chirpEntryStream A w N (fun b => chirpTableE s t α q b)).reverse ++ st.acc ∧
        z.val 19 = st.val 19 ∧
        ∀ i : Fin 48, 34 ≤ i.val → i ≠ 39 → i ≠ 40 → i ≠ 41 → z.val i = st.val i)
      (fun z hz => ⟨hz.1, hz.2.2.1.trans hq.symm, hz.2.2.2.2⟩) le_rfl) howned
  exact hc.mono (fun z h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
