module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellParameterArithmetic
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundDimensionSelection

/-! Compute the selected logarithmic shift and magnitude exponent inside inverse scalar scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def roundBitCountMap : Fin 4 → Fin 25 := ![9,10,12,14]
theorem roundBitCountMap_injective : Function.Injective roundBitCountMap := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [roundBitCountMap]

def tblRoundSelection : TblCode 25 :=
  .seq (tblBlock 25 [.copy 0 8,.inc 8,.inc 8,.inc 8,.inc 8,.inc 8,.inc 8,.inc 8,.inc 8,
    .copy 0 9,.add 9 9 9] (.add 9 9 9)) (tblBitCount.rename roundBitCountMap)

theorem tblRoundSelection_do {A W e p : ℕ} (st : TblSt 25 A) (hp : st.val 0 = p)
    (hroom : 8*(p+2) < 2^W) (hfit : ∀ i, st.val i < 2^W) :
    TblDo A W e tblRoundSelection st (fun z =>
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.val 8 = p+8 ∧ z.val 14 = inverseNormalizationShift p ∧
      z.acc = st.acc ∧ z.val 18 = st.val 18 ∧ z.val 20 = st.val 20 ∧ ∀ i, z.val i < 2^W) (4*Nat.size (4*p)+19) := by
  let st₁ : TblSt 25 A := ⟨Function.update (Function.update st.val 8 (p+8)) 9 (4*p),st.acc⟩
  have hinit : TblDo A W e
      (tblBlock 25 [.copy 0 8,.inc 8,.inc 8,.inc 8,.inc 8,.inc 8,.inc 8,.inc 8,.inc 8,
        .copy 0 9,.add 9 9 9] (.add 9 9 9)) st (fun z => z = st₁) 12 :=
    TblDo.block _ _
      (by simp [tblFitsList,TblIns.fits,TblIns.exact,hp]; omega)
      (by simp [tblExactList,TblIns.exact,st₁,hp,show p+p+(p+p) = 4*p by omega])
  have hinitFit := tblDo_with_fits hinit hfit
  unfold tblRoundSelection
  have h := hinitFit.seq (fun z ⟨he,hfit₁⟩ => by
    subst z
    have hc := ((tblBitCount_do (W := W) (e := e) (st₁.restrict roundBitCountMap) (4*p)
      (by simp [TblSt.restrict,roundBitCountMap,st₁]) (by omega)).rename roundBitCountMap_injective)
    exact (tblDo_with_fits hc hfit₁).mono
      (P' := fun z => (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
        z.val 8 = p+8 ∧ z.val 14 = inverseNormalizationShift p ∧ z.acc = st.acc ∧
        z.val 18 = st.val 18 ∧ z.val 20 = st.val 20 ∧ ∀ i, z.val i < 2^W)
      (K' := 4*Nat.size (4*p)+7) (fun z ⟨⟨⟨hv,ha,hf⟩,hoff⟩,hfitZ⟩ => by
      have hvalue (i : Fin 4) : z.val (roundBitCountMap i) = bitCountValues (4*p) i := congrFun hv i
      refine ⟨?_,?_,hvalue 3,ha,?_,?_,hfitZ⟩
      · intro i
        rw [hoff _ (by
          intro j he
          have hv := congrArg Fin.val he
          have hi := i.isLt
          fin_cases j <;> simp [roundBitCountMap] at hv <;> omega)]
        fin_cases i <;> simp [st₁]
      · rw [hoff 8 (by intro j; fin_cases j <;> decide)]
        simp [st₁]
      · rw [hoff 18 (by intro j; fin_cases j <;> decide)]
        simp [st₁]
      · rw [hoff 20 (by intro j; fin_cases j <;> decide)]
        simp [st₁]) (le_refl _))
  exact h.mono (fun _ hz => hz) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
