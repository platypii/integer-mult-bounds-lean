module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableOutputArgs
public import IntegerMultBounds.MathlibTM2.Fast.TableExp

/-! # Evaluate and emit a chirp coefficient on the table machine

The existing exponential program operates on variables 0 through 33. Preserve the high
row-control bank and emit its natural result as one real pair-symbol word.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Resampling.WeightNat

def chirpExpMap : Fin 34 → Fin 48 := Fin.castLE (by decide)

theorem chirpExpMap_injective : Function.Injective chirpExpMap := Fin.castLE_injective _

theorem chirpExpMap_off (i : Fin 48) (hi : 34 ≤ i.val) : ∀ j, chirpExpMap j ≠ i := by
  intro j h
  have hv := congrArg Fin.val h
  change j.val = i.val at hv
  have := j.isLt
  omega

/-- The table-machine pair encoding agrees with the raw coefficient streams used by S1. -/
theorem chirpPairs_csyms (A w x : ℕ) :
    tblPairs A w x 0 = csyms A w (⟨(x : ℤ), 0⟩ : GaussianInt) := by
  simp [tblPairs, csyms, Layer.red]

def tblChirpExpEmit : TblCode 48 :=
  .seq (tblExpCode.rename chirpExpMap) (tblBlock 48 [.zero 24] (.emit 23 24))

/-- The exponential evaluator and one coefficient emission, with high controls preserved. -/
theorem tblChirpExpEmit_do {A W w : ℕ} (st : TblSt 48 A) (neg : Bool) (q a b : ℕ)
    (hpi : st.val 18 = piN q) (hqR : st.val 19 = q) (ha : st.val 20 = a) (hb : st.val 21 = b)
    (hneg : st.val 22 = if neg then 1 else 0) (hq : 13 ≤ q) (hW : 13 * q + 8 ≤ W)
    (haW : a * 2 ^ (5 * q + 2) < 2 ^ W)
    (hpos : neg = false → piN q * a / b < q * 2 ^ (5 * q)) :
    TblDo A W w tblChirpExpEmit st
      (fun z => z.val 23 = expPiNat neg q a b ∧
        z.acc = (csyms A w (⟨(expPiNat neg q a b : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc ∧
        ChirpTableFrame st z) (310 * q + 102) := by
  have hexp := (tblExp_do (w := w) (st.restrict chirpExpMap) neg hpi hqR ha hb hneg hq hW haW hpos).rename
    chirpExpMap_injective
  have htail : ∀ z : TblSt 48 A,
      z.val 23 = expPiNat neg q a b ∧ z.acc = st.acc ∧ ChirpTableFrame st z →
      TblDo A W w (tblBlock 48 [.zero 24] (.emit 23 24)) z
        (fun u => u.val 23 = expPiNat neg q a b ∧
          u.acc = (csyms A w (⟨(expPiNat neg q a b : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc ∧
          ChirpTableFrame st u) 2 := by
    intro z ⟨hres, hacc, hf⟩
    let u := tblExactList A w ([.zero 24] ++ [.emit 23 24]) z
    have hframe : ChirpTableFrame z u := by
      refine ⟨?_, ?_, ?_⟩
      · simp [u, tblExactList, TblIns.exact]
      · simp [u, tblExactList, TblIns.exact]
      · intro i hi _ _
        have h24 : i ≠ 24 := by intro h; subst i; norm_num at hi
        simp [u, tblExactList, TblIns.exact, h24]
    exact TblDo.block [.zero 24] (.emit 23 24) (by simp [tblFitsList, TblIns.fits])
      ⟨by simp [tblExactList, TblIns.exact, hres],
        by simp [tblExactList, TblIns.exact, hres, hacc, chirpPairs_csyms],
        chirpTableFrame_trans hf hframe⟩
  have hrun := hexp.seq (fun z ⟨⟨hres, h18, h19, _, _, _, hacc⟩, hhigh⟩ =>
    htail z ⟨hres, hacc, h18, h19,
      fun i hi _ _ => hhigh i (chirpExpMap_off i hi)⟩)
  exact hrun.mono (fun z h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
