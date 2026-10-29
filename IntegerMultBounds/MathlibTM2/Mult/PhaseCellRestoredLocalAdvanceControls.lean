module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedAdvanceBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceSchedule

/-! The existing absolute-origin scanner generates a local sweep by retaining
its initial origin. Loading and releasing the scanner bank are paid here. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def restoredLocalAdvanceControls : Pr P 117 Q A U :=
  .seq (chirpBankLoad advanceReg packedAdvanceSource 115 115)
    (.seq originAdvanceControls releaseAdvanceBank)

theorem restoredLocalAdvanceControls_exec (V a N w : ℕ) (ha : a < 2^V) (hw : w < 2^V)
    (origins : List ℕ) (hsorted : (a::origins).Pairwise (· ≤ ·))
    (hcoords : ∀ j ∈ origins, j < 2^V) (hunits : ∀ j ∈ origins, j*w < 2^V)
    (hbound : ∀ j ∈ origins, j ≤ a+N)
    (cs suffix : List (Fin (A+4))) (hlen : cs.length = origins.length)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V)
    (hsrc : ∀ i, S.R (packedAdvanceSource i) = binSyms V (packedAdvanceValues a w (packedAdvanceSource i)))
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hc : S.R 116 = cs) (hpackets : S.R 109 = origins.flatMap (binSyms V)++suffix)
    (h88 : S.R 88 = []) (h89 : S.R 89 = []) (h90 : S.R 90 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ origins.length*(3*tblC V V+29*V+30)+8*N*w+78*V+91 ∧
      Exec body restoredLocalAdvanceControls (mk v S) m
        (mk v' {S with R := (Function.update S.R 91
          (gatherControls A (originAdvances w a origins++[0])++S.R 91))}) := by
  have hb : ∀ r, S.R (advanceReg r) = [] := fun r => hblank _ (advanceReg_range r)
  obtain ⟨v₁,hu₁,he₁,hh,hf⟩ := packedAdvanceBank_exec (body := body) V a w ha hw v S hV hsrc hb
  let B : Stacks 117 A := {S with R := chirpBankLoadR advanceReg packedAdvanceSource V V (packedAdvanceValues a w) S.R}
  let st : TblSt 4 A := ⟨fun i => packedAdvanceValues a w (packedAdvanceSource i),[]⟩
  have hst : ∀ i, st.val i < 2^V := packedAdvanceBank_bounded V a w ha hw
  obtain ⟨st',v₂,C,m₂,hw₂,ha₂,hb₂,hu₂,hm₂,he₂,hh₂,hout,hin,hout',hl,hframe⟩ :=
    originAdvanceControls_exec (body := body) le_rfl origins hsorted hcoords hunits st
      (by simp [st]) (by simp [st]) hst cs suffix hlen v₁ B hh
      (by simpa only [B,hf 116 (by decide)] using hc)
      (by simpa only [B,hf 109 (by decide)] using hpackets)
      (by simpa only [B,hf 88 (by decide)] using h88)
      (by simpa only [B,hf 89 (by decide)] using h89)
      (by simpa only [B,hf 90 (by decide)] using h90)
  have hoff (k : Fin 117) (hk : 19 ≤ k.val) : ∀ r, advanceReg r ≠ k := by
    intro r he
    have hr := advanceReg_range r
    rw [he] at hr
    omega
  change st'.acc = [] at ha₂
  have hst' : st' = ⟨st'.val,[]⟩ := by cases st'; cases ha₂; rfl
  have hrelease : tblHolds advanceReg C
      (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val,[]⟩) := by
    rw [← hst']; exact hh₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := releaseAdvanceBank_exec (body := body) V st'.val v₂ C hrelease
  have hvol : (originAdvances w a origins).sum ≤ N*w := by
    have hh := originAdvances_sum_le w a (a+N) origins hsorted (by omega) hbound
    nlinarith only [hh]
  refine ⟨v₃,40*V+41+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),by nlinarith only [hm₂,hm₃,hvol],
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext hin hout' hl ?_
  funext k
  by_cases hk : k.val < 19
  · have hn : k ≠ 91 := by intro he; subst k; norm_num at hk
    simp [hk,hn,hblank k hk]
  · have hge : 19 ≤ k.val := by omega
    by_cases h91 : k = 91
    · subst k
      simpa [B,hf 91 (by decide)] using hout
    · have hh := hframe k h91 (hoff k hge)
      simpa [hk,Function.update_of_ne h91,hh,B,hf k hge] using (rfl : S.R k = S.R k)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
