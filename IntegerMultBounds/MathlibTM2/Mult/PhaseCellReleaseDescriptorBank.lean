module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorRetire
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorBank

/-! Retire any one-record descriptor and its generated clock, preserving the
following queue. Field lengths are read from the physical packets. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def releaseDescriptorBank (src count tmp clock : Fin T) (N : ℕ) : Pr P T Q A U :=
  .seq (retireDescriptorBank src count tmp N) (uclear clock)

theorem releaseDescriptorBank_exec (work : Fin N → Fin T) (words : Fin N → List (Fin (A+4)))
    (src count tmp clock : Fin T) (hreg : [src,count,tmp,clock].Nodup)
    (rest : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = descriptorBankTape (placedDescriptorFields work words)++rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hclock : (S.R clock).length = 1) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 9*(descriptorBankTape (placedDescriptorFields work words)).length+5 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (9*(descriptorBankTape (placedDescriptorFields work words)).length+5)) depth
        (releaseDescriptorBank src count tmp clock N) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R src rest) clock [])}) := by
  have hr := hreg
  regs_ne hr
  let fields := placedDescriptorFields work words
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := retireDescriptorBank_exec (body := body) src count tmp
    (by regs_nodup) fields rest v S hsrc hcount htmp
  have hfields : fields.length = N := List.length_ofFn
  rw [hfields] at he₁
  let M : Stacks T A := {S with R := Function.update S.R src rest}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body clock v₁ M
  have hc : (M.R clock).length = 1 := by
    simpa only [M,Function.update_of_ne ‹src ≠ clock›.symm] using hclock
  rw [hc] at he₂
  have hwhole := Exec.seq he₁ he₂
  have htime : n₁+4 ≤ 9*(descriptorBankTape fields).length+5 := by omega
  refine ⟨v₂,n₁+4,hu₂.trans hu₁,htime,?_⟩
  apply mn_native_exec_within hwhole 1
  · exact ⟨retireDescriptorBank_native _ _ _ _,by
      simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]⟩
  · dsimp only [fields] at hn₁
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
