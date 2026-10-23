module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableEntry
public import IntegerMultBounds.MathlibTM2.Fast.TablePi

/-! # Generate pi once for the chirp table streams

Compute the Machin numerator from the precision word. Every variable numbered 19 and above
is preserved, so dimensions and loop-control words are shared by all later entries.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Resampling.WeightNat

def chirpPiMap (i : Fin 18) : Fin 48 :=
  ⟨if i.val = 15 then 18 else i.val, by have := i.isLt; split_ifs <;> omega⟩

theorem chirpPiMap_injective : Function.Injective chirpPiMap := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (if i.val = 15 then 18 else i.val) = (if j.val = 15 then 18 else j.val) at hv
  have hi := i.isLt
  have hj := j.isLt
  split_ifs at hv <;> omega

theorem chirpPiMap_off (i : Fin 48) (hi : 19 ≤ i.val) : ∀ j, chirpPiMap j ≠ i := by
  intro j h
  have hv := congrArg Fin.val h
  change (if j.val = 15 then 18 else j.val) = i.val at hv
  have hj := j.isLt
  split_ifs at hv <;> omega

def tblChirpPiSetup : TblCode 48 :=
  .seq (tblBlock 48 [] (.copy 19 0)) (tblPiCode.rename chirpPiMap)

/-- Pi generation has a single setup cost for the entire table stream. -/
theorem tblChirpPiSetup_do {A W w : ℕ} (st : TblSt 48 A) (q : ℕ)
    (hqR : st.val 19 = q) (hq : 2 ≤ q) (hW : 5 * q + 16 ≤ W) :
    TblDo A W w tblChirpPiSetup st
      (fun z => z.val 18 = piN q ∧ z.acc = st.acc ∧
        ∀ i : Fin 48, 19 ≤ i.val → z.val i = st.val i) (150 * q + 401) := by
  let st₀ : TblSt 48 A := ⟨Function.update st.val 0 q, st.acc⟩
  have hcopy := TblDo.block (W := W) (w := w) [] (.copy 19 0) (st := st) (P := fun z => z = st₀)
    (by simp [tblFitsList, TblIns.fits]) (by simp [tblExactList, TblIns.exact, st₀, hqR])
  have hpi := (tblPi_do (w := w) (st₀.restrict chirpPiMap) hq
    (by simp [TblSt.restrict, chirpPiMap, tblPiIn, st₀]) hW).rename chirpPiMap_injective
  have hsetup := hcopy.seq (fun z hz => by cases hz; exact hpi)
  exact hsetup.mono (fun z ⟨⟨hres, hacc⟩, hframe⟩ =>
    ⟨hres, hacc, fun i hi => by
      rw [hframe i (chirpPiMap_off i hi)]
      simp [st₀, Function.update_of_ne (show i ≠ 0 by intro h; subst i; norm_num at hi)]⟩)
    (by simp only [List.length_nil]; omega)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
