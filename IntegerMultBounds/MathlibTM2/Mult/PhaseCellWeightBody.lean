module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightArgument
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightEmit

/-! One similarity weight pair: natural argument construction, one corrected
exponential, and both exact grid encoders. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def weightBody : TblCode 48 := weightArgument ;;
  (correctedExpCode.rename tblExpMap48 ;; weightEmit)

theorem weightBody_do {A V w q P s t u j : ℕ} (st : TblSt 48 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = j) (hdouble : st.val 38 = 2 * s)
    (hden : st.val 39 = similarityDenominator s t)
    (hq : st.val 42 = 2 ^ q) (hpowP : st.val 43 = 2 ^ P)
    (hqp : st.val 44 = 2 ^ (q + P))
    (hP : 13 ≤ P) (hs0 : 0 < s) (hst : s < t)
    (hindex : 2 * t * j + s < 2 ^ V) (hsV : 2 * s < 2 ^ V)
    (hsq : s ^ 2 < 2 ^ V) (huV : u * s ^ 2 < 2 ^ V)
    (hV : 13 * P + 8 ≤ V)
    (haV : similarityNumerator s t u j * 2 ^ (5 * P + 2) < 2 ^ V)
    (hqV : q + P + 2 ≤ V) :
    TblDo A V w weightBody st (fun st' =>
      st'.acc = (csyms A w (reciprocalWeightWord q
          (PhaseCellConcreteCoefficients.similarity P s t u j))).reverse ++
        (csyms A w (rationalWord q
          (PhaseCellConcreteCoefficients.similarity P s t u j))).reverse ++ st.acc ∧
      st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
      ∀ k : Fin 48, 34 ≤ k.val → k ≠ 40 → k ≠ 41 → st'.val k = st.val k)
      (310 * P + 119) := by
  have hnV := similarityGridNumerator_fits (q := q) (j := j) (u := u) hP hs0 hst hqV
  have hargs := weightArgument_do (A := A) (V := V) (w := w) st
    hs ht hu hj hdouble hden hs0 hindex hsV hsq huV
  have hcore : TblDo A V w weightBody st (fun st' =>
      st'.acc = (csyms A w (reciprocalWeightWord q
          (PhaseCellConcreteCoefficients.similarity P s t u j))).reverse ++
        (csyms A w (rationalWord q
          (PhaseCellConcreteCoefficients.similarity P s t u j))).reverse ++ st.acc ∧
      st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
      ∀ k : Fin 48, 34 ≤ k.val → k ≠ 40 → k ≠ 41 → st'.val k = st.val k) (8 + ((310 * P + 106) + 5)) := by
    unfold weightBody
    refine hargs.seq (K₂ := (310 * P + 106) + 5) (fun s₁ h₁ => ?_)
    have hpre (k : Fin 48) (hk : k ∉ [(20 : Fin 48), 21, 40, 41]) := h₁.2.2.2 k hk
    have hexp := (correctedExpCode_do (A := A) (V := V) (w := w)
      (s₁.restrict tblExpMap48)
      (by simpa [TblSt.restrict, tblExpMap48, hpre 18 (by simp)] using hpi)
      (by simpa [TblSt.restrict, tblExpMap48, hpre 19 (by simp)] using hP')
      (by simpa [TblSt.restrict, tblExpMap48] using h₁.1)
      (by simpa [TblSt.restrict, tblExpMap48] using h₁.2.1)
      (by simpa [TblSt.restrict, tblExpMap48, hpre 22 (by simp)] using hneg)
      hP (similarityDenominator_pos hs0 hst) hV haV).rename
        (show Function.Injective tblExpMap48 by
          intro i j h
          exact Fin.ext (congrArg (fun x : Fin 48 => x.val) h))
    refine hexp.seq (K₂ := 5) (fun s₂ h₂ => ?_)
    have hoff (k : Fin 48) (hk : 34 ≤ k.val) : s₂.val k = s₁.val k :=
      h₂.2 k (tbl_castLE_ne (by decide) k hk)
    have hem := weightEmit_do (A := A) (V := V) (w := w) (q := q) (P := P) s₂
      (by simpa [similarityGridNumerator, TblSt.restrict, tblExpMap48] using h₂.1.1)
      h₂.1.2.1
      (by rw [hoff 42 (by decide), hpre 42 (by simp)]; exact hq)
      (by rw [hoff 43 (by decide), hpre 43 (by simp)]; exact hpowP)
      (by rw [hoff 44 (by decide), hpre 44 (by simp)]; exact hqp) hnV
    refine hem.mono (fun s₃ h₃ => ?_) le_rfl
    have hf (k : Fin 48) (hk : k ≠ 40 ∧ k ≠ 41) := h₃.2 k (by simpa using hk)
    have hacc : s₂.acc = st.acc := h₂.1.2.2.1.trans h₁.2.2.1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [← similarity_grid P s t u j hs0 hst, hacc] using h₃.1
    · exact (hf 18 (by simp)).trans (h₂.1.2.2.2.1.trans (hpre 18 (by simp)))
    · exact (hf 19 (by simp)).trans (h₂.1.2.2.2.2.1.trans (hpre 19 (by simp)))
    · exact (hf 22 (by simp)).trans (h₂.1.2.2.2.2.2.2.trans (hpre 22 (by simp)))
    · intro k hk hk40 hk41
      rw [hf k ⟨hk40, hk41⟩, hoff k hk, hpre k]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by intro h; subst k; norm_num at hk, by intro h; subst k; norm_num at hk, hk40, hk41⟩
  exact hcore.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
