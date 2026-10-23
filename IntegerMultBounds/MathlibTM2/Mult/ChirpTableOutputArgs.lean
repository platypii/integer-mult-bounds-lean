module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableMachineArgs

/-! # Compute the growing output-factor exponential arguments

The output factor uses numerator `s(t-s)b²` and denominator `t²α²`. All arguments and the
positive sign bit are generated from dimension words; high loop variables are preserved.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblChirpOutputPrefix : List (TblIns 48) :=
  [.sub 35 34 28, .mul 39 39 27, .mul 34 28 20, .mul 20 27 20,
    .mul 35 35 21, .mul 36 36 30, .mul 21 30 21]

def tblChirpOutputArguments : TblCode 48 := tblBlock 48 tblChirpOutputPrefix (.zero 22)

/-- Eight table-machine atoms produce the exact positive exponential arguments. -/
theorem tblChirpOutputArguments_do {A W w : ℕ} (st : TblSt 48 A) (s t α b : ℕ)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α) (hb : st.val 39 = b)
    (hst : s ≤ t) (htW : t < 2 ^ W) (hb2 : b * b < 2 ^ W)
    (hdiff : s * (t - s) < 2 ^ W) (hnum : s * (t - s) * (b * b) < 2 ^ W)
    (ht2 : t * t < 2 ^ W) (hα2 : α * α < 2 ^ W) (hden : t * t * (α * α) < 2 ^ W) :
    TblDo A W w tblChirpOutputArguments st
      (fun z => z.val 20 = chirpEN s t b ∧ z.val 21 = chirpED t α ∧ z.val 22 = 0 ∧
        z.acc = st.acc ∧ ChirpTableFrame st z) 8 := by
  let code := tblChirpOutputPrefix ++ [.zero 22]
  let z := tblExactList A w code st
  have hf : tblFitsList A W w code st := by
    simp [code, tblChirpOutputPrefix, tblFitsList, TblIns.fits, TblIns.exact,
      hs, ht, hα, hb, hst, htW, hb2, hdiff, hnum, ht2, hα2, hden]
  have hv : z.val 20 = chirpEN s t b ∧ z.val 21 = chirpED t α ∧ z.val 22 = 0 ∧ z.acc = st.acc := by
    simp [z, code, tblChirpOutputPrefix, tblExactList, TblIns.exact, hs, ht, hα, hb,
      chirpEN, chirpED, pow_two]
  have hframe : ChirpTableFrame st z := by
    refine ⟨?_, ?_, ?_⟩
    · simp [z, code, tblChirpOutputPrefix, tblExactList, TblIns.exact]
    · simp [z, code, tblChirpOutputPrefix, tblExactList, TblIns.exact]
    · intro i hi _ _
      have h20 : i ≠ 20 := by intro h; subst i; norm_num at hi
      have h21 : i ≠ 21 := by intro h; subst i; norm_num at hi
      have h22 : i ≠ 22 := by intro h; subst i; norm_num at hi
      have h27 : i ≠ 27 := by intro h; subst i; norm_num at hi
      have h28 : i ≠ 28 := by intro h; subst i; norm_num at hi
      have h30 : i ≠ 30 := by intro h; subst i; norm_num at hi
      simp [z, code, tblChirpOutputPrefix, tblExactList, TblIns.exact, h20, h21, h22, h27, h28, h30]
  exact (TblDo.block tblChirpOutputPrefix (.zero 22) hf
    ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hframe⟩).mono (fun z h => h)
    (by simp [tblChirpOutputPrefix])

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
