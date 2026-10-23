module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableRow

/-! # Executed rows of the chirp input, kernel, and output tables

Instantiate the structural row loop with the proved argument/evaluation/emission programs.
No row-entry execution assumption remains. All high controls except the row index are kept.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Resampling.WeightNat

def tblChirpNegativeRow (kernel : Bool) : TblCode 48 := tblFor 39 44 (tblChirpNegativeEntry kernel)

theorem tblChirpNegativeRow_do {A W w q B : ℕ} (st : TblSt 48 A) (size : ChirpTableSize W q B)
    (kernel : Bool) (s t α offset k0 N : ℕ)
    (hpi : st.val 18 = piN q) (hq : st.val 19 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (ho : st.val 37 = offset) (hk : st.val 38 = k0) (hN : st.val 44 = N)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hoB : offset ≤ B)
    (hkB : k0 ≤ B) (hNB : N ≤ B) :
    TblDo A W w (tblChirpNegativeRow kernel) st
      (fun z => z.acc = (chirpEntryStream A w N (fun j => chirpNegativeNumerator kernel s t α q offset k0 j)).reverse ++ st.acc ∧
        z.val 39 = N ∧ ChirpRowFrame st z) (N * (310 * q + 122) + 3) := by
  have hNW : N < 2 ^ W := hNB.trans_lt (by simpa using size.cap 1 1 (by decide) (by decide))
  have hrow := tblChirpRow_loop (w := w) st (tblChirpNegativeEntry kernel) N (310 * q + 119)
    (fun j => chirpNegativeNumerator kernel s t α q offset k0 j) hN hNW
    (fun j hj u hf hindex =>
      (tblChirpNegativeEntry_do (w := w) u size kernel s t α offset k0 j
        (hf.1.trans hpi) (hf.2.1.trans hq)
        ((hf.2.2 _ (by decide) (by decide) (by decide) (by decide)).trans hs)
        ((hf.2.2 _ (by decide) (by decide) (by decide) (by decide)).trans ht)
        ((hf.2.2 _ (by decide) (by decide) (by decide) (by decide)).trans hα)
        ((hf.2.2 _ (by decide) (by decide) (by decide) (by decide)).trans ho)
        ((hf.2.2 _ (by decide) (by decide) (by decide) (by decide)).trans hk)
        hindex hst hsB htB hαB hoB hkB (by omega)).mono
        (fun z h => ⟨h.2.1, h.2.2⟩) le_rfl)
  exact hrow.mono (fun z h => h) (by ring_nf; exact le_rfl)

def tblChirpOutputRow : TblCode 48 := tblFor 39 44 tblChirpOutputEntry

theorem tblChirpOutputRow_do {A W w q B : ℕ} (st : TblSt 48 A) (size : ChirpTableSize W q B)
    (s t α N : ℕ) (hpi : st.val 18 = piN q) (hq : st.val 19 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α) (hN : st.val 44 = N)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hNB : N ≤ B)
    (ht0 : 0 < t) (hα0 : 0 < α)
    (hgate : ∀ b < N, 4 * chirpEN s t b ≤ (q - 1) * chirpED t α) :
    TblDo A W w tblChirpOutputRow st
      (fun z => z.acc = (chirpEntryStream A w N (fun b => chirpTableE s t α q b)).reverse ++ st.acc ∧
        z.val 39 = N ∧ ChirpRowFrame st z) (N * (310 * q + 113) + 3) := by
  have hNW : N < 2 ^ W := hNB.trans_lt (by simpa using size.cap 1 1 (by decide) (by decide))
  have hrow := tblChirpRow_loop (w := w) st tblChirpOutputEntry N (310 * q + 110)
    (fun b => chirpTableE s t α q b) hN hNW
    (fun j hj u hf hindex =>
      (tblChirpOutputEntry_do (w := w) u size s t α j (hf.1.trans hpi) (hf.2.1.trans hq)
        ((hf.2.2 _ (by decide) (by decide) (by decide) (by decide)).trans hs)
        ((hf.2.2 _ (by decide) (by decide) (by decide) (by decide)).trans ht)
        ((hf.2.2 _ (by decide) (by decide) (by decide) (by decide)).trans hα)
        hindex hst hsB htB hαB (by omega) ht0 hα0 (hgate j hj)).mono
        (fun z h => ⟨h.2.1, h.2.2⟩) le_rfl)
  exact hrow.mono (fun z h => h) (by ring_nf; exact le_rfl)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
