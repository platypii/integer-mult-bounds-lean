module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloMembershipMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableBitHost

/-! Publish the executed geometry membership test and release its private table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloMembershipHost (boundary : Bool) : Pr P₀ 117 Q A U :=
  tableBitHost (haloMembershipMaskCode boundary)

theorem haloMembershipHost_exec {V s t band a b k : ℕ} (boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hbound : ∀ r, st.val r < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (h109 : S.R 109 = [])
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ v'.flag = haloMaskAt boundary s t band a b k ∧
      m ≤ 25*tblC V V+62*V+65 ∧
      Exec body (haloMembershipHost boundary) (mk v S) m
        (mk v' {S with R := fun r => if r.val < 31 then [] else if r = 109 then
          (if haloMaskAt boundary s t band a b k then [tick] else []) else S.R r}) := by
  have hc := haloMembershipMaskCode_do (w := V) boundary st hs ht hband hk ha hb
    hs0 hst haS hbS hwide
  have hV : 0 < V := by
    by_contra hn
    have hzero : V = 0 := by omega
    subst V
    norm_num at hwide
  exact tableBitHost_exec (body := body) (haloMembershipMaskCode boundary) st _
    (hc.mono (fun _ h => ⟨h.1,h.2.1.trans hacc⟩) le_rfl) hbound hV v S h109 hS

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
