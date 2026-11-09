module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnaryGatherControl
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationSchedule
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Consecutive equal-width cores need one repeated stride. Canonicalize an
owned row counter, append a sentinel, and reuse the restoring unary builder. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def uniformSweepControls (rows count packet advances savedCount tmp : Fin T) : Pr P T Q A U :=
  .seq (umul 1 rows count tmp)
    (.seq (.act (.push (.rt advances) (fun _ => blank) .done))
      (repeatUnaryGatherControl count savedCount packet advances tmp))

def uniformSweepControlsCost (N packet : ℕ) := N*(4*packet+14)+9

theorem uniformSweepControls_native (rows count packet advances savedCount tmp : Fin T) :
    mnNativePushBound 2 (uniformSweepControls (P := P) (Q := Q) (A := A) (U := U)
      rows count packet advances savedCount tmp) := by
  simp [uniformSweepControls,umul,umulSym,repeatUnaryGatherControl,unaryGatherControl,
    scanP,scanR,drainR,popDo,popPush,keepIn,pushN,copyR,copyStep,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

theorem uniformSweepControls_exec_within (body : P → Pr P T Q A U)
    (rows count packet advances savedCount tmp : Fin T)
    (hreg : [rows,count,packet,advances,savedCount,tmp].Nodup) (N d depth : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R rows).length = N) (hpacket : S.R packet = List.replicate d tick)
    (hcount : S.R count = []) (hadvances : S.R advances = [])
    (hsaved : S.R savedCount = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ uniformSweepControlsCost N d ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        2*uniformSweepControlsCost N d) depth (uniformSweepControls rows count packet advances savedCount tmp)
        (mk v S) n (mk v' {S with R := (Function.update
          (Function.update S.R count (List.replicate N tick)) advances
          (gatherControls A (List.replicate N d++[0])))}) := by
  regs_ne hreg
  obtain ⟨v₁,hu₁,he₁⟩ := umul_exec body 1 ‹rows ≠ count› ‹rows ≠ tmp› ‹count ≠ tmp› v S htmp
  let M : Stacks T A := {S with R := Function.update S.R count (List.replicate N tick)}
  have he₁' : Exec body (umul 1 rows count tmp) (mk v S) (4*N+4) (mk v₁ M) := by
    simpa only [hrows,Nat.one_mul,hcount,List.append_nil,M] using he₁
  let B : Stacks T A := {M with R := Function.update M.R advances [blank]}
  have hp : Exec body (.act (.push (.rt advances) (fun _ => blank) .done)) (mk v₁ M) 1 (mk v₁ B) := by
    simpa [M,B,Action.run,update_rt,‹count ≠ advances›.symm,hadvances] using
      Exec.act (body := body) (.push (.rt advances) (fun _ => blank) .done) (mk v₁ M)
  obtain ⟨v',n,hu₂,hn,he₂⟩ := repeatUnaryGatherControl_exec (body := body)
    (show [count,savedCount,packet,advances,tmp].Nodup by regs_nodup) N d v₁ B
    (by simp [B,M,‹count ≠ advances›])
    (by simp [B,M,‹packet ≠ advances›,‹count ≠ packet›.symm,hpacket])
    (by simp [B,M,‹advances ≠ savedCount›.symm,‹count ≠ savedCount›.symm,hsaved])
    (by simp [B,M,‹advances ≠ tmp›.symm,‹count ≠ tmp›.symm,htmp])
  have he : Exec body (uniformSweepControls rows count packet advances savedCount tmp) (mk v S) ((4*N+4)+(1+n))
      (mk v' {S with R := (Function.update (Function.update S.R count (List.replicate N tick)) advances
        (gatherControls A (List.replicate N d++[0])))}) := by
    simpa only [uniformSweepControls,B,M,Function.update_idem,gatherControls_append,gatherControls,
      Function.update_self,List.replicate_zero,List.nil_append,List.append_nil] using Exec.seq he₁' (Exec.seq hp he₂)
  have htime : (4*N+4)+(1+n) ≤ uniformSweepControlsCost N d := by
    unfold uniformSweepControlsCost
    nlinarith only [hn]
  exact ⟨v',_,hu₂.trans hu₁,htime,mn_native_exec_within he 2 (uniformSweepControls_native ..) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 htime) _)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
