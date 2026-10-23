module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableDistance

/-! # Generate the negative chirp exponential arguments on the table machine

The input and kernel tables share a squared-distance routine and denominator `t³α²`.
Only the natural multiplier differs. Produce both evaluator arguments and its sign bit
from the actual dimension variables, preserving the high loop-control bank.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

def chirpArgumentN (kernel : Bool) (s t offset k0 a : ℕ) : ℕ :=
  (if kernel then s else t - s) * chirpDistanceSquare s t offset k0 a

def tblChirpFactor (kernel : Bool) : TblCode 48 :=
  if kernel then .ins (.copy 34 28) else .ins (.sub 35 34 28)

def tblChirpArgumentTail : List (TblIns 48) :=
  [.mul 28 27 20, .mul 35 35 21, .mul 21 35 21, .mul 36 36 30, .mul 21 30 21, .zero 22]

def tblChirpArguments (kernel : Bool) : TblCode 48 :=
  .seq tblChirpDistance (.seq (tblChirpFactor kernel) (tblBlock 48 tblChirpArgumentTail (.inc 22)))

/-- All exponent arguments are computed in seventeen atoms, with explicit overflow conditions. -/
theorem tblChirpArguments_do {A W w : ℕ} (st : TblSt 48 A)
    (kernel : Bool) (s t α offset k0 a : ℕ)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (ho : st.val 37 = offset) (hk : st.val 38 = k0) (ha : st.val 39 = a)
    (hst : s ≤ t) (htW : t < 2 ^ W) (h1 : 1 < 2 ^ W)
    (hsk : s * k0 < 2 ^ W) (hadd : s * k0 / t + a < 2 ^ W)
    (hP : t * (s * k0 / t + a) < 2 ^ W) (hto : t * offset < 2 ^ W)
    (hN : s * k0 + t * offset < 2 ^ W) (hsq : chirpDistanceSquare s t offset k0 a < 2 ^ W)
    (hnum : chirpArgumentN kernel s t offset k0 a < 2 ^ W)
    (ht2 : t * t < 2 ^ W) (ht3 : t * t * t < 2 ^ W) (hα2 : α * α < 2 ^ W)
    (hden : t * t * t * (α * α) < 2 ^ W) :
    TblDo A W w (tblChirpArguments kernel) st
      (fun z => z.val 20 = chirpArgumentN kernel s t offset k0 a ∧ z.val 21 = chirpKD t α ∧
        z.val 22 = 1 ∧ z.acc = st.acc ∧ ChirpTableFrame st z) 17 := by
  have hdist := tblChirpDistance_do (w := w) st s t offset k0 a hs ht ho hk ha hsk hadd hP hto hN hsq
  have hbody : ∀ z : TblSt 48 A,
      z.val 27 = chirpDistanceSquare s t offset k0 a ∧ z.acc = st.acc ∧ ChirpTableFrame st z →
      TblDo A W w (.seq (tblChirpFactor kernel) (tblBlock 48 tblChirpArgumentTail (.inc 22))) z
        (fun u => u.val 20 = chirpArgumentN kernel s t offset k0 a ∧ u.val 21 = chirpKD t α ∧
          u.val 22 = 1 ∧ u.acc = st.acc ∧ ChirpTableFrame st u) 8 := by
    intro z ⟨hd, hacc, hf⟩
    have hsz : z.val 34 = s := (hf.2.2 _ (by decide) (by decide) (by decide)).trans hs
    have htz : z.val 35 = t := (hf.2.2 _ (by decide) (by decide) (by decide)).trans ht
    have hαz : z.val 36 = α := (hf.2.2 _ (by decide) (by decide) (by decide)).trans hα
    let f := if kernel then s else t - s
    let z₁ : TblSt 48 A := ⟨Function.update z.val 28 f, z.acc⟩
    have hfactor : TblDo A W w (tblChirpFactor kernel) z (fun u => u = z₁) 1 := by
      cases kernel with
      | false =>
        refine TblDo.insX (.sub 35 34 28) ?_ ?_
        · simpa only [TblIns.fits, hsz, htz] using And.intro hst htW
        · simp [TblIns.exact, z₁, f, hsz, htz]
      | true =>
        refine TblDo.insX (.copy 34 28) (by trivial) ?_
        simp [TblIns.exact, z₁, f, hsz]
    let code := tblChirpArgumentTail ++ [.inc 22]
    let z₂ := tblExactList A w code z₁
    have hn : f * chirpDistanceSquare s t offset k0 a < 2 ^ W := hnum
    have hfits : tblFitsList A W w code z₁ := by
      simp [code, tblChirpArgumentTail, tblFitsList, TblIns.fits, TblIns.exact, z₁,
        htz, hαz, hd, hn, ht2, ht3, hα2, hden, h1]
    have hargs : z₂.val 20 = chirpArgumentN kernel s t offset k0 a ∧ z₂.val 21 = chirpKD t α ∧
        z₂.val 22 = 1 ∧ z₂.acc = st.acc := by
      simp [z₂, code, tblChirpArgumentTail, tblExactList, TblIns.exact, z₁, f,
        htz, hαz, hd, chirpArgumentN, chirpKD, hacc, pow_succ, Nat.mul_assoc]
    have hframe : ChirpTableFrame z z₂ := by
      refine ⟨?_, ?_, ?_⟩
      · simp [z₂, code, tblChirpArgumentTail, tblExactList, TblIns.exact, z₁]
      · simp [z₂, code, tblChirpArgumentTail, tblExactList, TblIns.exact, z₁]
      · intro i hi h40 h41
        have h20 : i ≠ 20 := by intro h; subst i; norm_num at hi
        have h21 : i ≠ 21 := by intro h; subst i; norm_num at hi
        have h22 : i ≠ 22 := by intro h; subst i; norm_num at hi
        have h28 : i ≠ 28 := by intro h; subst i; norm_num at hi
        have h30 : i ≠ 30 := by intro h; subst i; norm_num at hi
        simp [z₂, code, tblChirpArgumentTail, tblExactList, TblIns.exact, z₁, h20, h21, h22, h28, h30]
    have htail := TblDo.block tblChirpArgumentTail (.inc 22) hfits
      (P := fun u => u.val 20 = chirpArgumentN kernel s t offset k0 a ∧ u.val 21 = chirpKD t α ∧
        u.val 22 = 1 ∧ u.acc = st.acc ∧ ChirpTableFrame st u)
      ⟨hargs.1, hargs.2.1, hargs.2.2.1, hargs.2.2.2, chirpTableFrame_trans hf hframe⟩
    exact (hfactor.seq (fun u hu => by cases hu; exact htail)).mono (fun u h => h)
      (by simp [tblChirpArgumentTail])
  exact (hdist.seq hbody).mono (fun z h => h) (by decide)

/-- Input-table arguments coincide with the certified mathematical numerators. -/
theorem chirpArgumentN_input (s t m k0 a : ℕ) :
    chirpArgumentN false s t m k0 a = chirpGN s t m k0 a := by
  simp [chirpArgumentN, chirpGN, chirpDistanceSquare_eq]

/-- Kernel-table arguments include the required signed shift. -/
theorem chirpArgumentN_kernel (s t m k0 j : ℕ) (hm : 1 ≤ m) :
    chirpArgumentN true s t (2 * m - 1) k0 j = chirpKN s t m k0 ((j : ℤ) - (m - 1 : ℕ)) := by
  simp [chirpArgumentN, chirpKN, chirpDistanceSquare_kernel s t m k0 j hm]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
