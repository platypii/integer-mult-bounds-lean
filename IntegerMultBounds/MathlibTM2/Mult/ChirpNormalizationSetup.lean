module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputTables
public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableRestoredHost

/-! # Generate the output normalization word from q and α

Compute 2^q by the existing doubling loop, divide by 2α, emit one real word,
and erase every arithmetic temporary. No normalization numerator is supplied.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast

def tblChirpNormalization : TblCode 48 :=
  .seq (tblPow2 0 19 1)
    (tblBlock 48 [.add 36 36 2, .div 0 2 0, .zero 3, .emit 0 3,
      .zero 0, .zero 1, .zero 2] (.zero 3))

/-- The normalization computation retains the entire dimension/precision bank. -/
theorem tblChirpNormalization_do {A W w : ℕ} (st : TblSt 48 A) (q α : ℕ)
    (hq : st.val 19 = q) (hα : st.val 36 = α) (hqW : q < W)
    (hαW : 2 * α < 2 ^ W) (hzero : ∀ i : Fin 48, i.val < 4 → st.val i = 0) :
    TblDo A W w tblChirpNormalization st
      (fun z => z.val = st.val ∧
        z.acc = (csyms A w (⟨(chirpNormalization q α : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc)
      (4 * q + 13) := by
  have hp := tblPow2_do (W := W) (w := w) (by decide : (0 : Fin 48) ≠ 19)
    (by decide : (0 : Fin 48) ≠ 1) (by decide : (19 : Fin 48) ≠ 1) st (by rwa [hq])
  have hr : TblDo A W w tblChirpNormalization st
      (fun z => z.val = st.val ∧
        z.acc = (csyms A w (⟨(chirpNormalization q α : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc)
      ((4 * st.val 19 + 5) + 8) := hp.seq (fun u ⟨hpow, hindex, hframe, hacc⟩ => by
    have huα : u.val 36 = α := (hframe 36 (by decide) (by decide)).trans hα
    have hpow' : u.val 0 = 2 ^ q := by simpa only [hq] using hpow
    have hfits : tblFitsList A W w
        ([.add 36 36 2, .div 0 2 0, .zero 3, .emit 0 3, .zero 0, .zero 1, .zero 2] ++ [.zero 3]) u := by
      simpa [tblFitsList, TblIns.fits, TblIns.exact, huα, ← two_mul] using hαW
    have hvals : (tblExactList A w
        ([.add 36 36 2, .div 0 2 0, .zero 3, .emit 0 3, .zero 0, .zero 1, .zero 2] ++ [.zero 3]) u).val = st.val := by
      funext i
      by_cases hi0 : i = 0
      · subst i; simp [tblExactList, TblIns.exact, hzero]
      by_cases hi1 : i = 1
      · subst i; simp [tblExactList, TblIns.exact, hzero]
      by_cases hi2 : i = 2
      · subst i; simp [tblExactList, TblIns.exact, hzero]
      by_cases hi3 : i = 3
      · subst i; simp [tblExactList, TblIns.exact, hzero]
      · simp [tblExactList, TblIns.exact, hi0, hi1, hi2, hi3, hframe i hi0 hi1]
    exact TblDo.block _ _ hfits ⟨hvals, by
      simp [tblExactList, TblIns.exact, huα, hpow', hacc,
        ← two_mul, chirpNormalization, chirpPairs_csyms]⟩)
  exact hr.mono (fun _ h => h) (by simp only [hq]; omega)

/-- Execute normalization setup with only its destination stack changed. -/
theorem chirpNormalizationSetup_exec {T Q A : ℕ} {P U : Type}
    {body : P → Pr P T Q A U} {rg : TblR 48 → Fin T}
    (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 48 A) (q α : ℕ) (hq : st.val 19 = q) (hα : st.val 36 = α)
    (hqW : q < W) (hαW : 2 * α < 2 ^ W)
    (hzero : ∀ i : Fin 48, i.val < 4 → st.val i = 0)
    (hfit : ∀ i, st.val i < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (4 * q + 13) * tblC W w + 2 * w + 2 ∧
      Exec body (tblHost rg tblChirpNormalization out) (mk v S) n
        (mk v' { S with R := (Function.update S.R out
          (csyms A w (⟨(chirpNormalization q α : ℤ), 0⟩ : GaussianInt) ++ S.R out)) }) := by
  simpa only [csyms, Layer.length_coeffSyms] using tblChirpRestored_host (body := body) hrg hout
    wl nl hwl hnl hw tblChirpNormalization st _ _
    (tblChirpNormalization_do st q α hq hα hqW hαW hzero) hfit hacc v S hS

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
