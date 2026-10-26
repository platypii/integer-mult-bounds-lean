module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloMaskPhase

/-! Convert the computed endpoint-phase equality to a retained natural bit. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloPhaseBitCode : TblCode 16 := haloMaskPhaseCode ;;
  tableIfEq 11 12 (.ins (.inc 15)) (.ins (.zero 15))

theorem haloPhaseBitCode_do {A V w s t band k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hb : st.val 2 = band) (hk : st.val 3 = k)
    (hz : st.val 15 = 0) (hs0 : 0 < s) (hst : s ≤ t) (hband : band ≤ k)
    (hsV : 2*s < 2^V) (hgapV : 2*(t-s) < 2^V) (hksum : k+band < 2^V)
    (hleft : 2*(t-s)*(k-band)+s < 2^V) (hright : 2*(t-s)*(k+band)+s < 2^V) :
    TblDo A V w haloPhaseBitCode st (fun st' =>
      st'.val 15 = (if naturalPhase s t (k-band) = naturalPhase s t (k+band) then 1 else 0) ∧
      st'.acc = st.acc ∧ ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 14 := by
  have hphase := haloMaskPhaseCode_do (w := w) st hs ht hb hk hst hband hsV hgapV hksum hleft hright
  unfold haloPhaseBitCode
  refine hphase.seq (K₂ := 3) (fun s₁ h₁ => ?_)
  have hf (r : Fin 16) (hr : r ∉ [(6 : Fin 16),7,8,9,10,11,12]) := h₁.2.2.2 r hr
  have hzero : s₁.val 15 = 0 := (hf 15 (by simp)).trans hz
  have hlow (r : Fin 16) (hr : r.val < 6) : s₁.val r = st.val r := by
    apply hf
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    repeat' constructor
    all_goals intro he; subst r; norm_num at hr
  apply tableIfEq_do
  · intro he
    have heq : naturalPhase s t (k-band) = naturalPhase s t (k+band) := by simpa [h₁.1,h₁.2.1] using he
    apply TblDo.insX (.inc 15)
    · have hone : 1 < 2^V := by omega
      simpa only [TblIns.fits,hzero,Nat.zero_add] using hone
    · refine ⟨by simp [TblIns.exact,hzero,heq],h₁.2.2.1,?_⟩
      intro r hr
      have hr15 : r ≠ 15 := by intro he; subst r; norm_num at hr
      simpa [TblIns.exact,hr15] using hlow r hr
  · intro he
    have hne : naturalPhase s t (k-band) ≠ naturalPhase s t (k+band) := by simpa [h₁.1,h₁.2.1] using he
    apply TblDo.insX (.zero 15) (by simp [TblIns.fits])
    refine ⟨by simp [TblIns.exact,hne],h₁.2.2.1,?_⟩
    intro r hr
    have hr15 : r ≠ 15 := by intro he; subst r; norm_num at hr
    simpa [TblIns.exact,hr15] using hlow r hr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
