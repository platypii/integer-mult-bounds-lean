module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceMaskHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationMaskCode


/-! Execute and release the geometry table, retaining one selection symbol per coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def publicationMaskSymbols (A s t band a b : ℕ) : List (Fin (A+4)) :=
  couplingSourceMaskSymbols false A s t band a b

@[simp] theorem publicationMaskSymbols_length (A s t band a b : ℕ) :
    (publicationMaskSymbols A s t band a b).length = s := by
  simp [publicationMaskSymbols]

theorem publicationMaskSymbols_getElem (A s t band a b k : ℕ) (hk : k < s) :
    (publicationMaskSymbols A s t band a b)[k]'(by simpa using hk) =
      pairSym A (haloInteriorAt s t band a b k) (haloInteriorAt s t band a b k) := by
  simpa [publicationMaskSymbols,haloMaskAt] using
    couplingSourceMaskSymbols_getElem false A s t band a b k hk

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def publicationMaskHost : Pr P₀ 117 Q A U :=
  couplingSourceMaskHost false

def publicationMaskHostCost (V s : ℕ) : ℕ :=
  couplingSourceMaskHostCost V s

theorem publicationMaskHost_exec {V s t band a b : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hbound : ∀ r, st.val r < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ publicationMaskHostCost V s ∧
      Exec body publicationMaskHost (mk v S) m
        (mk v' {S with R := fun r => if r.val < 31 then [] else if r = 109 then
          publicationMaskSymbols A s t band a b++S.R r else S.R r}) := by
  simpa [publicationMaskHost,publicationMaskHostCost,publicationMaskSymbols] using
    couplingSourceMaskHost_exec false st hs ht hband ha hb hacc hs0 hst haS hbS hwide hbound v S hS

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
