module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryGuardCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginStreamHost

/-! Execute and release the geometry table, retaining one selection symbol per coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def recoveryGuardMaskSymbols (boundary : Bool) (A s t band a b : ℕ) : List (Fin (A+4)) :=
  (List.range s).map (fun k => pairSym A (recoveryGuardMaskAt boundary s t band a b k) (recoveryGuardMaskAt boundary s t band a b k))

@[simp] theorem recoveryGuardMaskSymbols_length (boundary : Bool) (A s t band a b : ℕ) :
    (recoveryGuardMaskSymbols boundary A s t band a b).length = s := by simp [recoveryGuardMaskSymbols]

theorem recoveryGuardMaskSymbols_getElem (boundary : Bool) (A s t band a b k : ℕ) (hk : k < s) :
    (recoveryGuardMaskSymbols boundary A s t band a b)[k]'(by simpa using hk) =
      pairSym A (recoveryGuardMaskAt boundary s t band a b k) (recoveryGuardMaskAt boundary s t band a b k) := by
  simp [recoveryGuardMaskSymbols]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def recoveryGuardMaskHost (boundary : Bool) : Pr P₀ 117 Q A U :=
  originStreamHost (recoveryGuardMaskCode boundary)

def recoveryGuardMaskHostCost (V s : ℕ) : ℕ := (46*s+3)*tblC V 1+64*V+2*s+68

theorem recoveryGuardMaskHost_exec (boundary : Bool) {V s t band a b : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hbound : ∀ r, st.val r < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ recoveryGuardMaskHostCost V s ∧
      Exec body (recoveryGuardMaskHost boundary) (mk v S) m
        (mk v' {S with R := fun r => if r.val < 31 then [] else if r = 109 then
          recoveryGuardMaskSymbols boundary A s t band a b++S.R r else S.R r}) := by
  have hV : 1 ≤ V := by
    by_contra h
    have : V = 0 := by omega
    subst V
    norm_num at hwide <;> omega
  have hc := recoveryGuardMaskCode_do boundary (A := A) (V := V) (w := 1) st hs ht hband ha hb
    hs0 hst haS hbS hwide
  have hmask : (List.range s).flatMap (fun k =>
      tblPairs A 1 (if recoveryGuardMaskAt boundary s t band a b k then 1 else 0)
        (if recoveryGuardMaskAt boundary s t band a b k then 1 else 0)) = recoveryGuardMaskSymbols boundary A s t band a b := by
    simp only [recoveryGuardMaskSymbols,publicationMaskSymbol]
    exact List.map_eq_flatMap.symm
  rw [hmask] at hc
  obtain ⟨v',m,hu,hm,he⟩ := originStreamHost_exec (body := body) hV (recoveryGuardMaskCode boundary) st
    (recoveryGuardMaskSymbols boundary A s t band a b) hacc hc hbound v S hS
  exact ⟨v',m,hu,by simpa [recoveryGuardMaskHostCost] using hm,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
