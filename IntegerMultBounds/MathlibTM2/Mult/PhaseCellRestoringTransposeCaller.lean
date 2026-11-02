module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFixedTransposeFrame

/-! A composable bit-plane kernel: retire the prepared width after the
transpose, restoring every stack except the owned payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace FixedStreamedBank
noncomputable section
variable {Q K : ℕ} {P U : Type}

def restoringCaller (hstates : stateCount ≤ Q) : Pr P (tapeCount+117) Q (prime+K) U :=
  .seq (initializedCaller hstates) (uclear (callerWorker (control 5)))

theorem restoringCaller_exec_within (body : P → Pr P (tapeCount+117) Q (prime+K) U)
    (hstates : stateCount ≤ Q) (a b C V : ℕ) (hC : 0 < C)
    (hbits : a+b < V) (hfit : C*2^(a+b) < 2^V)
    (f : Fin (2^a) → Fin (2^b) → Fin C → Bool)
    (v : HS (tapeCount+117) Q (prime+K) U) (S : Stacks (tapeCount+117) (prime+K))
    (ha : S.R (callerGenerator 97) = binSyms V a) (hb : S.R (callerGenerator 98) = binSyms V b)
    (hseed : S.R (callerGenerator 102) = binSyms V C) (hz : S.R (callerGenerator 106) = [])
    (hwidth : (S.R (callerGenerator 115)).length = V)
    (hblank : ∀ r, S.R (callerGenerator (originReg r)) = [])
    (hcount : S.R (callerGenerator 116) = []) (hL : ∀ i, S.L (callerWorker i) = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ control 7 → S.R (callerWorker i) = [])
    (hsrc : S.R (callerWorker (workerReg (reg pay))) = (replicaKeyWords f).map bitSymbol) :
    let rs := (dyadicTransposePlan (a+b) a b C (by omega)).wiredStages (fun _ => (bank hstates).dims)
    ∃ v' n, v'.user = v.user ∧
      n ≤ (116*V+143+32921*(V+1)^5)+(rs.map (fun r => (bank hstates).stageTimeCost V
        (∑ j, ((embStk callerWorker S).R ((bank hstates).ι j)).length) r+3)).sum+2 ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((342*V+423+98763*(V+1)^5)+(bank hstates).scheduleStockAllowance V rs)) depth
        (restoringCaller hstates) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (callerWorker (workerReg (reg pay)))
          ((keyReplicaWords f).map bitSymbol))}) := by
  obtain ⟨v₁,F,m,hu,hm,ht,hcounter,hworker,hclear,hretain,hready,hleft,hoff⟩ :=
    initializedCaller_exec_within body hstates a b C V hC hbits hfit f v S ha hb hseed hz hwidth
      hblank hcount hL hfresh hsrc
  have hF := initializedCaller_frame hstates V (keyReplicaWords f) S F hblank hcount hcounter
    hworker hclear hretain hleft hoff
  let E : Stacks (tapeCount+117) (prime+K) := {widthState V S with R :=
    (Function.update (widthState V S).R (callerWorker (workerReg (reg pay))) ((keyReplicaWords f).map bitSymbol))}
  change F = E at hF
  subst F
  have hwp : callerWorker (control 5) ≠ callerWorker (workerReg (reg pay)) :=
    TransposeRegisterPlacement.worker_injective.ne (control_ne_workerReg 5 _)
  have hwE : (E.R (callerWorker (control 5))).length = V := by
    simp [E,widthState,Function.update_of_ne hwp]
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec (body := body) (callerWorker (control 5)) v₁ E
  rw [hwE] at he₂
  have hfinal : {E with R := Function.update E.R (callerWorker (control 5)) []} =
      {S with R := Function.update S.R (callerWorker (workerReg (reg pay))) ((keyReplicaWords f).map bitSymbol)} := by
    refine Stacks.ext (by rfl) (by rfl) (by rfl) ?_
    funext i
    by_cases hw : i = callerWorker (control 5)
    · subst i
      have hb := hfresh (control 5) (control_ne_workerReg _ _)
        (control_injective.ne (by decide : (5 : Fin 19) ≠ 7))
      simp [E,widthState,hwp,hb]
    · by_cases hp : i = callerWorker (workerReg (reg pay))
      · subst i; simp [E,widthState,hwp.symm]
      · simp [E,widthState,hw,hp]
  rw [hfinal] at he₂
  refine ⟨v₂,m+(2*V+2),hu₂.trans hu,by omega,?_⟩
  intro depth
  have hc := mn_native_exec_within he₂ 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth (mnSize (Host.mk v₁ E)+depth) (by omega)
  have hs := mn_seq_within_add (b := 0) (ht depth) (by simpa only [Nat.add_zero] using hc)
  exact hs.mono (by intro d z hz; omega)

end
end FixedStreamedBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
