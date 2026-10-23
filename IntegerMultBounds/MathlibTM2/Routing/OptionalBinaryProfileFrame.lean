module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryActiveProfileFrame
public import IntegerMultBounds.MathlibTM2.Routing.BinaryInactiveProfileFrame

/-! Emit an active computed selector or an inactive zero frame according to
the current activity flag. Both branches restore all operands and scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def optionalBinaryProfileFrameProgram (src dst tmp work : Fin T)
    (zr : BinaryZeroReg → Fin T) : Pr P T Q A U :=
  .cond (·.flag) (binaryActiveProfileFrameProgram src dst tmp work) (binaryInactiveProfileFrameProgram zr)

def optionalBinaryProfileFrameCost (Lw L : ℕ) :=
  max (6 * L + 9) (Lw * (4 * L + 11) + 8 * L + 15) + 1

theorem optionalBinaryProfileFrame_exec (body : P → Pr P T Q A U)
    (src dst tmp work : Fin T) (hreg : [src, dst, tmp, work].Nodup)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = dst)
    (Lw L q : ℕ) (hwidth : L < 2 ^ Lw) (enabled : Bool)
    (v : HS T Q A U) (S : Stacks T A) (hflag : v.flag = enabled)
    (hsrc : S.R src = binSyms L q) (htmp : S.R tmp = []) (hwork : S.R work = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw L)
    (hunary : S.R (zr .unary) = []) (hscratch : ∀ r, S.R (zr (.scratch r)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ optionalBinaryProfileFrameCost Lw L ∧
      Exec body (optionalBinaryProfileFrameProgram src dst tmp work zr) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (affineProfileFrames L [(enabled, if enabled then q else 0)] ++ S.R dst) }) := by
  cases enabled with
  | false =>
    obtain ⟨v', m, hu, hm, hx⟩ := binaryInactiveProfileFrame_exec body zr hzr Lw L hwidth v S
      hwidthInput hunary hscratch
    rw [hdst] at hx
    refine ⟨v', m + 1, hu, ?_, Exec.cond_false (by simpa only [mk_var] using hflag) hx⟩
    have hb := le_max_right (6 * L + 9) (Lw * (4 * L + 11) + 8 * L + 15)
    unfold optionalBinaryProfileFrameCost
    omega
  | true =>
    obtain ⟨v', hu, hx⟩ := binaryActiveProfileFrame_exec body src dst tmp work hreg L q v S hsrc htmp hwork
    refine ⟨v', (6 * L + 9) + 1, hu, ?_, Exec.cond_true (by simpa only [mk_var] using hflag) hx⟩
    have hb := le_max_left (6 * L + 9) (Lw * (4 * L + 11) + 8 * L + 15)
    unfold optionalBinaryProfileFrameCost
    omega

end IntegerMultBounds.MathlibTM2.Routing
