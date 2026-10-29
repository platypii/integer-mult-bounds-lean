module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalGuardStreamHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceIntervalMaskCode

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Guards use ambient coordinates; storage contains only the requested interval. -/
def couplingSourceIntervalMaskSymbols (boundary : Bool) (A s t band a b origin N : ℕ) : List (Fin (A+4)) :=
  (List.range N).map (fun j => pairSym A (haloMaskAt boundary s t band a b (origin+j))
    (haloMaskAt boundary s t band a b (origin+j)))

@[simp] theorem couplingSourceIntervalMaskSymbols_length (boundary : Bool) (A s t band a b origin N : ℕ) :
    (couplingSourceIntervalMaskSymbols boundary A s t band a b origin N).length = N := by
  simp [couplingSourceIntervalMaskSymbols]

def couplingSourceIntervalMaskHost {P U : Type} {Q A : ℕ} (boundary : Bool) : Pr P 117 Q A U :=
  intervalGuardStreamHost (couplingSourceIntervalMaskCode boundary)

theorem couplingSourceIntervalMaskHost_exec {P U : Type} {Q A V s t band a b origin N : ℕ}
    {body : P → Pr P 117 Q A U} (boundary : Bool) (st : TblSt 17 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hindex : st.val 3 = origin)
    (hcount : st.val 16 = origin+N) (hfit : origin+N ≤ s) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hbound : ∀ r, st.val r < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds intervalGuardReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ (29*N+2)*tblC V 1+66*V+2*N+70 ∧
      Exec body (couplingSourceIntervalMaskHost boundary) (mk v S) m
        (mk v' {S with R := fun r => if r.val < 32 then [] else if r = 109 then
          couplingSourceIntervalMaskSymbols boundary A s t band a b origin N++S.R r else S.R r}) := by
  have hV : 1 ≤ V := by
    by_contra h
    have : V = 0 := by omega
    subst V
    norm_num at hwide <;> omega
  have hc := couplingSourceIntervalMaskCode_do (A := A) (V := V) (w := 1) boundary st
    hs ht hband ha hb hindex hcount hfit hs0 hst haS hbS hwide
  have hmask : (List.range N).flatMap (fun j =>
      tblPairs A 1 (if haloMaskAt boundary s t band a b (origin+j) then 1 else 0)
        (if haloMaskAt boundary s t band a b (origin+j) then 1 else 0)) =
      couplingSourceIntervalMaskSymbols boundary A s t band a b origin N := by
    simp only [couplingSourceIntervalMaskSymbols,publicationMaskSymbol]
    exact List.map_eq_flatMap.symm
  rw [hmask] at hc
  simpa only [couplingSourceIntervalMaskHost,couplingSourceIntervalMaskSymbols_length] using
    intervalGuardStreamHost_exec (body := body) hV (couplingSourceIntervalMaskCode boundary) st
      (couplingSourceIntervalMaskSymbols boundary A s t band a b origin N) hacc hc hbound v S hS

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
