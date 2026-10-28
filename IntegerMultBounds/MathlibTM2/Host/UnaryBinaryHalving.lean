module

public import IntegerMultBounds.MathlibTM2.Fast.LoadRing
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Retained unary headers convert by halving, then pad once to the requested width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.Spec.SignedRingProduct

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem reverse_msbBits_symbols (L n : ℕ) :
    ((msbBits L n).map (bitSymbol (a := A))).reverse = binSyms L n := by
  induction L generalizing n with
  | zero => simp [msbBits,binSyms]
  | succ L ih =>
    rw [ldr_msbBits_succ,List.map_append,List.reverse_append]
    simp only [List.map_cons,List.map_nil,List.reverse_cons,List.reverse_nil,List.nil_append]
    rw [ih,binSyms_succ]
    simp [Nat.testBit_zero]

def unaryBinary (src dst a h par bits cnt saved : Fin T) : Pr P T Q A U :=
  .seq (ucopy src a saved)
    (.seq (ldrLoop a h par bits cnt) (.seq (moveR bits dst id) (uclear cnt)))

theorem unaryBinary_exec {src dst a h par bits cnt saved : Fin T}
    (hreg : [src,dst,a,h,par,bits,cnt,saved].Nodup)
    (n : ℕ) (v : HS T Q A U) (S : Stacks T A) (hn : (S.R src).length = n)
    (hfresh : ∀ k ∈ [dst,a,h,par,bits,cnt,saved], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 21*n+10 ∧
      Exec body (unaryBinary src dst a h par bits cnt saved) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (binSyms (Nat.size n) n)}) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) ‹src ≠ a› ‹src ≠ saved› ‹a ≠ saved› v S
    (hfresh saved (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R a (List.replicate n tick)}
  have he₁' : Exec body (ucopy src a saved) (mk v S) (4*n+4) (mk v₁ S₁) := by
    simpa [S₁,hn,hfresh a (by simp)] using he₁
  have hp := Exec.act (body := body) (peekR a) (mk v₁ S₁)
  rw [peekR_run] at hp
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := ldr_loop_aux (body := body)
    (show [a,h,par,bits,cnt].Nodup by simp_all [ne_comm]) n
    {v₁ with flag := (S₁.R a).head?.isSome} S₁ (by simp [S₁])
    (by simpa [S₁,‹a ≠ h›.symm] using hfresh h (by simp))
    (by simpa [S₁,‹a ≠ par›.symm] using hfresh par (by simp)) rfl
  let S₂ : Stacks T A := {S₁ with R := ldrLoopR a bits cnt S₁.R n}
  have hbits : S₂.R bits = (msbBits (Nat.size n) n).map bitSymbol := by
    simp [S₂,S₁,ldrLoopR,‹bits ≠ cnt›,‹a ≠ bits›.symm,hfresh bits (by simp)]
  have hdst : S₂.R dst = [] := by
    simp [S₂,S₁,ldrLoopR,‹dst ≠ cnt›,‹dst ≠ bits›,‹dst ≠ a›,hfresh dst (by simp)]
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (body := body) bits dst ‹dst ≠ bits›.symm id v₂ S₂
  let S₃ : Stacks T A := {S₂ with R := movedR S₂.R bits dst id (S₂.R bits)}
  have hcnt : S₃.R cnt = List.replicate (Nat.size n) tick := by
    simp [S₃,movedR,S₂,S₁,ldrLoopR,‹bits ≠ cnt›.symm,‹dst ≠ cnt›.symm,‹a ≠ cnt›.symm,hfresh cnt (by simp)]
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) cnt v₃ S₃
  refine ⟨v₄,(4*n+4)+(1+m₂)+ (2*Nat.size n+2)+(2*Nat.size n+2),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),by have := ldr_size_le n; omega,
    (Exec.seq he₁' (Exec.seq (Exec.seq hp he₂) (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · rw [hbits,List.length_map,length_msbBits,hcnt,List.length_replicate]
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = dst
    · subst k
      simp [S₃,movedR,hbits,hdst,reverse_msbBits_symbols,‹dst ≠ cnt›]
    by_cases hc : k = cnt
    · subst k; simp [hfresh cnt (by simp),hk]
    by_cases hb : k = bits
    · subst k; simp [S₃,movedR,‹bits ≠ cnt›,hfresh bits (by simp),hk]
    by_cases ha : k = a
    · subst k; simp [S₃,movedR,S₂,ldrLoopR,‹a ≠ cnt›,hk,hb,hc,hfresh a (by simp)]
    simp [S₃,movedR,S₂,ldrLoopR,S₁,hk,hc,hb,ha,Function.update_apply]

def unaryBinaryWidth (src width dst a h par bits cnt saved : Fin T) : Pr P T Q A U :=
  .seq (unaryBinary src dst a h par bits cnt saved) (bwiden dst width cnt a h)

theorem unaryBinaryWidth_exec {src width dst a h par bits cnt saved : Fin T}
    (hreg : [src,width,dst,a,h,par,bits,cnt,saved].Nodup)
    (n W : ℕ) (hfit : Nat.size n ≤ W) (v : HS T Q A U) (S : Stacks T A)
    (hn : (S.R src).length = n) (hW : (S.R width).length = W)
    (hfresh : ∀ k ∈ [dst,a,h,par,bits,cnt,saved], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 21*n+12*W+28 ∧
      Exec body (unaryBinaryWidth src width dst a h par bits cnt saved) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (binSyms W n)}) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryBinary_exec (body := body)
    (by simp_all) n v S hn hfresh
  let S₁ : Stacks T A := {S with R := Function.update S.R dst (binSyms (Nat.size n) n)}
  obtain ⟨v₂,hu₂,he₂⟩ := bwiden_exec (body := body)
    (show [dst,width,cnt,a,h].Nodup by simp_all [ne_comm]) hfit (Nat.lt_size_self n) v₁ S₁
    (by simp [S₁]) (by simpa [S₁,‹width ≠ dst›] using hW)
    (by simpa [S₁,‹dst ≠ cnt›.symm] using hfresh cnt (by simp))
    (by simpa [S₁,‹dst ≠ a›.symm] using hfresh a (by simp))
    (by simpa [S₁,‹dst ≠ h›.symm] using hfresh h (by simp))
  refine ⟨v₂,m₁+(12*W+18),hu₂.trans hu₁,by omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  simp [S₁]

end IntegerMultBounds.MathlibTM2.Host
