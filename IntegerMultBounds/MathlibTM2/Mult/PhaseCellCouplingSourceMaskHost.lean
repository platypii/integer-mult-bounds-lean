module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceMaskCode
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

def couplingSourceMaskSymbols (boundary : Bool) (A s t band a b : ℕ) : List (Fin (A+4)) :=
  (List.range s).map (fun k => pairSym A (haloMaskAt boundary s t band a b k) (haloMaskAt boundary s t band a b k))

@[simp] theorem couplingSourceMaskSymbols_length (boundary : Bool) (A s t band a b : ℕ) :
    (couplingSourceMaskSymbols boundary A s t band a b).length = s := by simp [couplingSourceMaskSymbols]

theorem couplingSourceMaskSymbols_getElem (boundary : Bool) (A s t band a b k : ℕ) (hk : k < s) :
    (couplingSourceMaskSymbols boundary A s t band a b)[k]'(by simpa using hk) =
      pairSym A (haloMaskAt boundary s t band a b k) (haloMaskAt boundary s t band a b k) := by
  simp [couplingSourceMaskSymbols]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def couplingSourceMaskHost (boundary : Bool) : Pr P₀ 117 Q A U :=
  originStreamHost (couplingSourceMaskCode boundary)

def couplingSourceMaskHostCost (V s : ℕ) : ℕ := (29*s+3)*tblC V 1+64*V+2*s+68

theorem couplingSourceMaskHost_exec (boundary : Bool) {V s t band a b : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hbound : ∀ r, st.val r < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingSourceMaskHostCost V s ∧
      Exec body (couplingSourceMaskHost boundary) (mk v S) m
        (mk v' {S with R := fun r => if r.val < 31 then [] else if r = 109 then
          couplingSourceMaskSymbols boundary A s t band a b++S.R r else S.R r}) := by
  have hV : 1 ≤ V := by
    by_contra h
    have : V = 0 := by omega
    subst V
    norm_num at hwide <;> omega
  have hc := couplingSourceMaskCode_do boundary (A := A) (V := V) (w := 1) st hs ht hband ha hb
    hs0 hst haS hbS hwide
  have hmask : (List.range s).flatMap (fun k =>
      tblPairs A 1 (if haloMaskAt boundary s t band a b k then 1 else 0)
        (if haloMaskAt boundary s t band a b k then 1 else 0)) = couplingSourceMaskSymbols boundary A s t band a b := by
    simp only [couplingSourceMaskSymbols,publicationMaskSymbol]
    exact List.map_eq_flatMap.symm
  rw [hmask] at hc
  obtain ⟨v',m,hu,hm,he⟩ := originStreamHost_exec (body := body) hV (couplingSourceMaskCode boundary) st
    (couplingSourceMaskSymbols boundary A s t band a b) hacc hc hbound v S hS
  exact ⟨v',m,hu,by simpa [couplingSourceMaskHostCost] using hm,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
