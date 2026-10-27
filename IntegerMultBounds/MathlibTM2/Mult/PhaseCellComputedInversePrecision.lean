module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInversePrecisionSetup

/-! One fixed scalar program computes all inverse precisions from p, l, target, row count and band. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM

namespace InversePrecision

def logP : Fin 4 → Fin 18 := ![5,11,12,6]
def logN : Fin 4 → Fin 18 := ![3,11,12,7]
def logBand : Fin 4 → Fin 18 := ![13,11,12,8]
def exponent : Fin 8 → Fin 18 := ![0,1,2,6,7,8,9,10]
def dimensions : Fin 6 → Fin 18 := ![0,9,14,15,16,17]

theorem logP_injective : Function.Injective logP := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [logP]
theorem logN_injective : Function.Injective logN := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [logN]
theorem logBand_injective : Function.Injective logBand := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [logBand]
theorem exponent_injective : Function.Injective exponent := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [exponent]
theorem dimensions_injective : Function.Injective dimensions := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [dimensions]

end InversePrecision

def tblComputedInversePrecision : TblCode 18 :=
  .seq (tblBlock 18 [.copy 0 5,.add 5 5 5,.add 5 5 5,.add 5 5 5,.add 4 4 13] (.inc 13))
    (.seq (tblBitCount.rename InversePrecision.logP)
      (.seq (tblBitCount.rename InversePrecision.logN)
        (.seq (tblBitCount.rename InversePrecision.logBand)
          (.seq (tblInverseExponent.rename InversePrecision.exponent)
            (tblInverseDimensionWords.rename InversePrecision.dimensions)))))

def inversePrecisionRoom (p l target N band : ℕ) : ℕ :=
  2^15*(p+1)+8*inverseExecutionExponent p l target N band+2*(N+1)+4*(band+1)+9

def inversePrecisionAtoms (p N band : ℕ) : ℕ :=
  4*(Nat.size (8*p)+Nat.size N+Nat.size (2*band+1))+100

private theorem tableFit_of_frame {m n A W : ℕ} (f : Fin m → Fin n)
    (σ τ : TblSt n A) (hσ : ∀ i, σ.val i < 2^W)
    (hτ : ∀ i, τ.val (f i) < 2^W)
    (hoff : ∀ i, (∀ j, f j ≠ i) → τ.val i = σ.val i) : ∀ i, τ.val i < 2^W := by
  intro i
  by_cases hi : ∃ j, f j = i
  · obtain ⟨j,rfl⟩ := hi
    exact hτ j
  · rw [hoff i (by intro j he; exact hi ⟨j,he⟩)]
    exact hσ i

theorem tblComputedInversePrecision_do {A W e : ℕ} (st : TblSt 18 A) (p l target N band : ℕ)
    (h0 : st.val 0 = p) (h1 : st.val 1 = l) (h2 : st.val 2 = target)
    (h3 : st.val 3 = N) (h4 : st.val 4 = band)
    (hroom : inversePrecisionRoom p l target N band < 2^W) (hfit : ∀ i, st.val i < 2^W) :
    let E := inverseExecutionExponent p l target N band
    TblDo A W e tblComputedInversePrecision st
      (fun z => z.val 0 = p ∧ z.val 1 = l ∧ z.val 2 = target ∧ z.val 3 = N ∧ z.val 4 = band ∧
        z.val 9 = E ∧ z.val 14 = 4*E ∧ z.val 15 = 2*E+1 ∧ z.val 16 = 8*E+8 ∧
        z.val 17 = 2^15*p ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2^W)
      (inversePrecisionAtoms p N band) := by
  dsimp only
  let E := inverseExecutionExponent p l target N band
  have hbound : 2^15*(p+1)+8*E+2*(N+1)+4*(band+1)+9 < 2^W := hroom
  have hlogP : 2*(8*p+1) < 2^W := by omega
  have hlogN : 2*(N+1) < 2^W := by omega
  have hlogBand : 2*((2*band+1)+1) < 2^W := by omega
  have hE : E < 2^W := by omega
  let st₁ : TblSt 18 A := ⟨Function.update (Function.update st.val 5 (8*p)) 13 (2*band+1),st.acc⟩
  have hinit : TblDo A W e
      (tblBlock 18 [.copy 0 5,.add 5 5 5,.add 5 5 5,.add 5 5 5,.add 4 4 13] (.inc 13)) st
      (fun z => z = st₁) 6 := TblDo.block _ _
    (by simp [tblFitsList,TblIns.fits,TblIns.exact,h0,h4]; omega)
    (by simp [tblExactList,TblIns.exact,st₁,h0,h4,← two_mul,← Nat.mul_assoc])
  have hf₁ : ∀ i, st₁.val i < 2^W := by
    intro i
    by_cases h13 : i = 13
    · subst i; simp [st₁]; omega
    by_cases h5 : i = 5
    · subst i; simp [st₁]; omega
    simpa [st₁,h13,h5] using hfit i
  have hP := tblBitCount_at (e := e) InversePrecision.logP InversePrecision.logP_injective st₁ (8*p)
    (by simp [st₁,InversePrecision.logP]) hlogP hf₁
  unfold tblComputedInversePrecision
  have hr := hinit.seq (fun z hz => by
    cases hz
    exact hP.seq (fun zP ⟨hP,haP,hfP,hfitP⟩ => by
      have hN := tblBitCount_at (e := e) InversePrecision.logN InversePrecision.logN_injective zP N
        ((hfP 3 (by decide) (by decide) (by decide)).trans (by simpa [st₁] using h3)) hlogN hfitP
      exact hN.seq (fun zN ⟨hN,haN,hfN,hfitN⟩ => by
        have hB := tblBitCount_at (e := e) InversePrecision.logBand InversePrecision.logBand_injective zN (2*band+1)
          ((hfN 13 (by decide) (by decide) (by decide)).trans
            ((hfP 13 (by decide) (by decide) (by decide)).trans (by simp [st₁]))) hlogBand hfitN
        exact hB.seq (fun zB ⟨hB,haB,hfB,hfitB⟩ => by
          have hkeep (i : Fin 18) (h6 : i ≠ 6) (h7 : i ≠ 7) (h8 : i ≠ 8)
              (h11 : i ≠ 11) (h12 : i ≠ 12) : zB.val i = st₁.val i :=
            (hfB i h11 h12 h8).trans ((hfN i h11 h12 h7).trans (hfP i h11 h12 h6))
          have hpB : zB.val 0 = p := (hkeep 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simpa [st₁] using h0)
          have hlB : zB.val 1 = l := (hkeep 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simpa [st₁] using h1)
          have htB : zB.val 2 = target := (hkeep 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simpa [st₁] using h2)
          have hNB : zB.val 3 = N := (hkeep 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simpa [st₁] using h3)
          have hbB : zB.val 4 = band := (hkeep 4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simpa [st₁] using h4)
          have hPB : zB.val 6 = Nat.size (8*p) := (hfB 6 (by decide) (by decide) (by decide)).trans
            ((hfN 6 (by decide) (by decide) (by decide)).trans hP)
          have hNlogB : zB.val 7 = Nat.size N := (hfB 7 (by decide) (by decide) (by decide)).trans hN
          have hexp := (tblInverseExponent_do (A := A) (W := W) (e := e)
            (zB.restrict InversePrecision.exponent) p l target (Nat.size (8*p)) (Nat.size N) (Nat.size (2*band+1))
            hpB hlB htB hPB hNlogB hB hE).rename InversePrecision.exponent_injective
          exact hexp.seq (fun zE ⟨⟨hvE,haE,hfitE⟩,hoffE⟩ => by
            have hv (i : Fin 8) : zE.val (InversePrecision.exponent i) =
                inverseExponentValues p l target (Nat.size (8*p)) (Nat.size N) (Nat.size (2*band+1)) i := congrFun hvE i
            have hpE : zE.val 0 = p := hv 0
            have hEE : zE.val 9 = E := hv 6
            have hfE : ∀ i, zE.val i < 2^W := tableFit_of_frame InversePrecision.exponent zB zE hfitB hfitE hoffE
            have hdim := (tblInverseDimensionWords_do (A := A) (W := W) (e := e)
              (zE.restrict InversePrecision.dimensions) p E hpE hEE (by omega)).rename InversePrecision.dimensions_injective
            exact hdim.mono (P' := fun z => z.val 0 = p ∧ z.val 1 = l ∧ z.val 2 = target ∧
              z.val 3 = N ∧ z.val 4 = band ∧ z.val 9 = E ∧ z.val 14 = 4*E ∧
              z.val 15 = 2*E+1 ∧ z.val 16 = 8*E+8 ∧ z.val 17 = 2^15*p ∧
              z.acc = st.acc ∧ ∀ i, z.val i < 2^W) (fun zD ⟨⟨hvD,haD,hfitD⟩,hoffD⟩ => by
              have hd (i : Fin 6) : zD.val (InversePrecision.dimensions i) = inverseDimensionValues p E i := congrFun hvD i
              refine ⟨hd 0,?_,?_,?_,?_,hd 1,hd 2,hd 3,hd 4,hd 5,
                haD.trans (haE.trans (haB.trans (haN.trans haP))),
                tableFit_of_frame InversePrecision.dimensions zE zD hfE hfitD hoffD⟩
              · exact (hoffD 1 (by intro i; fin_cases i <;> decide)).trans (hv 1)
              · exact (hoffD 2 (by intro i; fin_cases i <;> decide)).trans (hv 2)
              · exact (hoffD 3 (by intro i; fin_cases i <;> decide)).trans
                  ((hoffE 3 (by intro i; fin_cases i <;> decide)).trans hNB)
              · exact (hoffD 4 (by intro i; fin_cases i <;> decide)).trans
                  ((hoffE 4 (by intro i; fin_cases i <;> decide)).trans hbB)) (le_refl _))))))
  exact hr.mono (fun _ h => h) (by dsimp [inversePrecisionAtoms]; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
