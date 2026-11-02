module

public import IntegerMultBounds.MathlibTM2.Host.UnaryBinaryHalving
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources
public import Mathlib.Data.Nat.Log

/-! Borrow a unary count and retain only its binary length. Optionally remove
one copied tick first, giving the exact dyadic ceiling exponent. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.Spec.SignedRingProduct
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def unaryBitLength (trim : Bool) (src dst a half par bits saved : Fin T) : Pr P T Q A U :=
  .seq (ucopy src a saved)
    (.seq (.act (if trim then dropTop a .done else .done))
      (.seq (ldrLoop a half par bits dst) (uclear bits)))

theorem unaryBitLength_native (trim : Bool) (src dst a half par bits saved : Fin T) :
    mnNativePushBound 2 (unaryBitLength (P := P) (Q := Q) (A := A) (U := U)
      trim src dst a half par bits saved) := by
  cases trim <;> simp [unaryBitLength,ucopy,umulSym,scanR,keepIn,pushN,
    ldrLoop,ldrStep,ldrHalfFx,ldrBitAct,uclear,drainR,popDo,dropTop,moveR,whileR,moveStep,peekR,
    mnNativePushBound,mnActPush]

theorem unaryBitLength_exec (trim : Bool) (src dst a half par bits saved : Fin T)
    (hreg : [src,dst,a,half,par,bits,saved].Nodup) (n : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hn : (S.R src).length = n)
    (hfresh : ∀ k ∈ [dst,a,half,par,bits,saved], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 19*n+9 ∧
      Exec body (unaryBitLength trim src dst a half par bits saved) (mk v S) m
        (mk v' {S with R := (Function.update S.R dst
          (List.replicate (Nat.size (n-if trim then 1 else 0)) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) ‹src ≠ a› ‹src ≠ saved› ‹a ≠ saved› v S
    (hfresh saved (by simp))
  let M : Stacks T A := {S with R := Function.update S.R a (List.replicate n tick)}
  have he₁' : Exec body (ucopy src a saved) (mk v S) (4*n+4) (mk v₁ M) := by
    simpa [M,hn,hfresh a (by simp)] using he₁
  let m := n-if trim then 1 else 0
  let F : Stacks T A := {S with R := Function.update S.R a (List.replicate m tick)}
  have hp : Exec body (.act (if trim then dropTop a .done else .done)) (mk v₁ M) 1 (mk v₁ F) := by
    have hh := Exec.act (body := body) (if trim then dropTop a .done else .done) (mk v₁ M)
    convert hh using 1 <;> cases trim <;>
      simp [M,F,m,Action.run,dropTop,update_rt,List.tail_replicate]
  have hpeek := Exec.act (body := body) (peekR a) (mk v₁ F)
  rw [peekR_run] at hpeek
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := ldr_loop_aux (body := body)
    (show [a,half,par,bits,dst].Nodup by regs_nodup) m
    {v₁ with flag := (F.R a).head?.isSome} F (by simp [F])
    (by simpa [F,‹a ≠ half›.symm] using hfresh half (by simp))
    (by simpa [F,‹a ≠ par›.symm] using hfresh par (by simp)) rfl
  let G : Stacks T A := {F with R := ldrLoopR a bits dst F.R m}
  have hbits : G.R bits = (msbBits (Nat.size m) m).map bitSymbol := by
    simp [G,F,ldrLoopR,‹dst ≠ bits›.symm,‹a ≠ bits›.symm,hfresh bits (by simp)]
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) bits v₂ G
  refine ⟨v₃,(4*n+4)+(1+((1+m₂)+(2*Nat.size m+2))),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · have hs : Nat.size m ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
    have hm : m ≤ n := Nat.sub_le _ _
    omega
  · refine (Exec.seq he₁' (Exec.seq hp (Exec.seq (Exec.seq hpeek he₂) he₃))).cast ?_ ?_
    · rw [hbits,List.length_map,length_msbBits]
    · apply congrArg (mk v₃)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hd : k = dst
      · subst k; simp [G,F,ldrLoopR,‹dst ≠ bits›,‹dst ≠ a›,hfresh dst (by simp),m]
      by_cases hb : k = bits
      · subst k; simp [hd,hfresh bits (by simp)]
      by_cases ha : k = a
      · subst k; simp [G,F,ldrLoopR,hd,hb,hfresh a (by simp)]
      simp [G,F,ldrLoopR,hd,hb,ha,Function.update_apply]

theorem size_pred_eq_clog (n : ℕ) : Nat.size (n-1) = Nat.clog 2 n := by
  apply Nat.le_antisymm
  · apply Nat.size_le.mpr
    have hp := Nat.le_pow_clog (by decide : 1 < 2) n
    have hz := Nat.two_pow_pos (Nat.clog 2 n)
    omega
  · apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    have hp := Nat.lt_size_self (n-1)
    omega

/-- Exact minimal dyadic capacity exponent, preserving the original count. -/
theorem unaryCeilLog_exec_within (src dst a half par bits saved : Fin T)
    (hreg : [src,dst,a,half,par,bits,saved].Nodup) (n : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hn : (S.R src).length = n)
    (hfresh : ∀ k ∈ [dst,a,half,par,bits,saved], S.R k = []) (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 19*n+9 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(19*n+9)) depth
        (unaryBitLength true src dst a half par bits saved) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (List.replicate (Nat.clog 2 n) tick)}) := by
  obtain ⟨v',m,hu,hm,he⟩ := unaryBitLength_exec (body := body) true src dst a half par bits saved hreg n v S hn hfresh
  simp only [ite_true,size_pred_eq_clog] at he
  exact ⟨v',m,hu,hm,mn_native_exec_within he 2 (unaryBitLength_native _ _ _ _ _ _ _ _) depth _ (by omega)⟩

def unaryPowerExponent (src dst a half par bits saved : Fin T) : Pr P T Q A U :=
  .seq (unaryBitLength false src dst a half par bits saved) (.act (dropTop dst .done))

/-- Extract the exponent of an actual power-of-two replica count. -/
theorem unaryPowerExponent_exec_within (src dst a half par bits saved : Fin T)
    (hreg : [src,dst,a,half,par,bits,saved].Nodup) (e : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hn : (S.R src).length = 2^e)
    (hfresh : ∀ k ∈ [dst,a,half,par,bits,saved], S.R k = []) (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 19*2^e+10 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(19*2^e+10)) depth
        (unaryPowerExponent src dst a half par bits saved) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (List.replicate e tick)}) := by
  obtain ⟨v',m,hu,hm,he⟩ := unaryBitLength_exec (body := body) false src dst a half par bits saved hreg (2^e) v S hn hfresh
  simp only [Bool.false_eq_true,ite_false,Nat.sub_zero,Nat.size_pow] at he
  let M : Stacks T A := {S with R := Function.update S.R dst (List.replicate (e+1) tick)}
  have hp := Exec.act (body := body) (dropTop dst .done) (mk v' M)
  have he' : Exec body (unaryPowerExponent src dst a half par bits saved) (mk v S) (m+1)
      (mk v' {S with R := Function.update S.R dst (List.replicate e tick)}) := by
    simpa [unaryPowerExponent,M,Action.run,dropTop,update_rt] using Exec.seq he hp
  have hnative : mnNativePushBound 2 (unaryPowerExponent (P := P) (Q := Q) (A := A) (U := U)
      src dst a half par bits saved) := by
    exact ⟨unaryBitLength_native _ _ _ _ _ _ _ _,by simp [dropTop,mnNativePushBound,mnActPush]⟩
  exact ⟨v',m+1,hu,by omega,mn_native_exec_within he' 2 hnative depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Host
