module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLatticeArgument
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientGridEmit

/-! Execute the direct cross-cell coefficient of the original rounded matrix.
The unreduced lattice argument and q-grid encoding are both constructed here. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
  IntegerMultBounds.Resampling.WeightNat

def directCoefficientBody : TblCode 48 :=
  latticeArgument ;; (correctedExpCode.rename tblExpMap48 ;; coefficientGridEmit)

theorem directCoefficientBody_do {A V w q P s t u j k : ℕ} (st : TblSt 48 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = j) (hk : st.val 38 = k) (hq : st.val 39 = 2^q) (hpowP : st.val 40 = 2^P)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P)
    (hjV : 2*t*j+s < 2^V) (hkV : 2*t*k+s < 2^V) (hsV : 2*s < 2^V)
    (hnjV : s*nearestNatural s t j < 2^V) (hnkV : s*nearestNatural s t k < 2^V)
    (hdjV : latticeDistance s t j k^2 < 2^V) (hdkV : latticeDistance s t k k^2 < 2^V)
    (hsqV : s^2 < 2^V) (hV : 13*P+8 ≤ V)
    (haV : latticeNumerator s t u j k*2^(5*P+2) < 2^V) (hqV : q+P+2 ≤ V) :
    TblDo A V w directCoefficientBody st (fun st' =>
      st'.acc = (csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u j k))).reverse++st.acc ∧
      st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
      ∀ r : Fin 48, 34 ≤ r.val → r.val ≤ 40 → st'.val r = st.val r) (310*P+129) := by
  have hb : 0 < s^2 := by positivity
  have hnumV : latticeNumerator s t u j k < 2^V := by
    have hh : 1 ≤ 2^(5*P+2) := Nat.one_le_two_pow
    nlinarith
  have hn : PhaseCellExpSample.numerator P (latticeNumerator s t u j k) (s^2) < 2^(P+2) :=
    (Nat.sub_le _ _).trans_lt (expPiNat_neg_lt_pow hP le_rfl _ _ hb)
  have hgrid : 2^q*PhaseCellExpSample.numerator P (latticeNumerator s t u j k) (s^2) < 2^V := by
    calc
      _ < 2^q*2^(P+2) := Nat.mul_lt_mul_of_pos_left hn (by positivity)
      _ = 2^(q+P+2) := by rw [← pow_add,Nat.add_assoc]
      _ ≤ 2^V := Nat.pow_le_pow_right (by decide) hqV
  have hargs := latticeArgument_do (A := A) (V := V) (w := w) st hs ht hu hj hk hs0 hst
    hjV hkV hsV hnjV hnkV hdjV hdkV hnumV hsqV
  have hcore : TblDo A V w directCoefficientBody st (fun st' =>
      st'.acc = (csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u j k))).reverse++st.acc ∧
      st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
      ∀ r : Fin 48, 34 ≤ r.val → r.val ≤ 40 → st'.val r = st.val r) (20+((310*P+106)+3)) := by
    unfold directCoefficientBody
    refine hargs.seq (K₂ := (310*P+106)+3) (fun s₁ h₁ => ?_)
    have hpre (r : Fin 48) (hr : r.val ≤ 40) (hr20 : r ≠ 20) (hr21 : r ≠ 21) :=
      h₁.2.2.2 r hr hr20 hr21
    have hexp := (correctedExpCode_do (A := A) (V := V) (w := w)
      (s₁.restrict tblExpMap48)
      (by simpa [TblSt.restrict,tblExpMap48,hpre 18 (by decide) (by decide) (by decide)] using hpi)
      (by simpa [TblSt.restrict,tblExpMap48,hpre 19 (by decide) (by decide) (by decide)] using hP')
      (by simpa [TblSt.restrict,tblExpMap48] using h₁.1)
      (by simpa [TblSt.restrict,tblExpMap48] using h₁.2.1)
      (by simpa [TblSt.restrict,tblExpMap48,hpre 22 (by decide) (by decide) (by decide)] using hneg)
      hP hb hV haV).rename
      (show Function.Injective tblExpMap48 by intro i j he; exact Fin.ext (show i.val = j.val from congrArg (fun x : Fin 48 => x.val) he))
    refine hexp.seq (K₂ := 3) (fun s₂ h₂ => ?_)
    have hoff (r : Fin 48) (hr : 34 ≤ r.val) : s₂.val r = s₁.val r :=
      h₂.2 r (tbl_castLE_ne (by decide) r hr)
    have hem := coefficientGridEmit_do (A := A) (V := V) (w := w) (q := q) (P := P) s₂
      (by simpa [TblSt.restrict,tblExpMap48] using h₂.1.1)
      (by simpa [TblSt.restrict,tblExpMap48] using h₂.1.2.1)
      (by rw [hoff 39 (by decide),hpre 39 (by decide) (by decide) (by decide)]; exact hq)
      (by rw [hoff 40 (by decide),hpre 40 (by decide) (by decide) (by decide)]; exact hpowP) hgrid
    refine hem.mono (fun s₃ h₃ => ?_) le_rfl
    have hf (r : Fin 48) (hr : r ≠ 41) := h₃.2 r hr
    have hacc : s₂.acc = st.acc := h₂.1.2.2.1.trans h₁.2.2.1
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [direct_sample P s t u j k hs0 hst]
      simpa only [PhaseCellExpSample.sample,hacc] using h₃.1
    · exact (hf 18 (by decide)).trans (h₂.1.2.2.2.1.trans (hpre 18 (by decide) (by decide) (by decide)))
    · exact (hf 19 (by decide)).trans (h₂.1.2.2.2.2.1.trans (hpre 19 (by decide) (by decide) (by decide)))
    · exact (hf 22 (by decide)).trans (h₂.1.2.2.2.2.2.2.trans (hpre 22 (by decide) (by decide) (by decide)))
    · intro r hrlo hrhi
      rw [hf r (by intro he; subst r; norm_num at hrhi),hoff r hrlo,
        hpre r hrhi (by intro he; subst r; norm_num at hrlo) (by intro he; subst r; norm_num at hrlo)]
  exact hcore.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
