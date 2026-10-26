module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClipCode

/-! Compute the original ambient phase of an endpoint, including endpoints
beyond the ambient interval. Only the phase register and one temporary change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def naturalPhaseCode : TblCode 16 :=
  tblBlock 16 [.mul 6 8 4, .add 4 0 4, .add 0 0 9] (.div 4 9 4)

theorem naturalPhaseCode_do {A W w s t band x : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hden : st.val 6 = 2*(t-s)) (hx : st.val 8 = x)
    (_hs : 0 < s) (hst : s < t) (hxs : x ≤ 2*s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w naturalPhaseCode st (fun st' =>
      st'.val 4 = naturalPhase s t x ∧ st'.acc = st.acc ∧
      ∀ k, k ∉ [(4 : Fin 16),9] → st'.val k = st.val k) 4 := by
  have hd := Nat.sub_le t s
  have hprod : 2*(t-s)*x ≤ 4*t*t := by
    calc
      _ ≤ 2*t*(2*t) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hd) (by omega)
      _ = _ := by ring
  have hfit : 2*(t-s)*x+s < 2^W := by nlinarith only [hprod,hwide,hst]
  have hsfit : 2*s < 2^W := by nlinarith only [hwide,hst]
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,hs',hden,hx]
    exact ⟨by omega,hfit,by omega⟩
  · constructor
    · simp [tblExactList,TblIns.exact,hs',hden,hx,naturalPhase,Function.update_idem,two_mul]
    constructor
    · rfl
    · intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
      simp [tblExactList,TblIns.exact,hk.1,hk.2]

theorem naturalPhase_le_double_gap {s t x : ℕ} (hs : 0 < s) (hx : x ≤ 2*s) :
    naturalPhase s t x ≤ 2*(t-s)+1 := by
  apply Nat.le_of_lt_succ
  rw [naturalPhase,Nat.div_lt_iff_lt_mul (by omega : 0 < 2*s)]
  have hm := Nat.mul_le_mul_left (2*(t-s)) hx
  nlinarith only [hm,hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
