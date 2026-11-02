module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedTransposePlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedRestoringTranspose
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRouterCodecStock

/-! Actual real and imaginary plane execution through the same restoring
private bank. Both runs use shared read-only dimension headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank
variable {Q K : ℕ} {P U : Type}

def planeProgram (imaginary : Bool) (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P tapeCount Q (prime+K) U :=
  embProg (placement imaginary) Empty.elim (restoringCaller (P := Empty) hstates)

theorem plane_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (imaginary : Bool) (hstates : FixedStreamedBank.stateCount ≤ Q) (a b C V : ℕ)
    (hC : 0 < C) (hbits : a+b < V) (hfit : C*2^(a+b) < 2^V)
    (f : Fin (2^a) → Fin (2^b) → Fin C → Bool) (depth : ℕ)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V C)
    (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hcount : S.R (base (callerGenerator 116)) = []) (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hsrc : S.R (planeReg imaginary) = (replicaKeyWords f).map bitSymbol) :
    ∃ v' n, v'.user = v.user ∧ n ≤ restoringTimeCost hstates a b C V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+restoringStockAllowance hstates a b C V)
        depth (planeProgram imaginary hstates) (mk v S) n
        (mk v' {S with R := Function.update S.R (planeReg imaginary) ((keyReplicaWords f).map bitSymbol)}) := by
  have hp : placement imaginary (callerWorker (workerReg (reg pay))) = planeReg imaginary := placement_owned imaginary
  have hr := placedRestoring_exec_within body (placement imaginary) (placement_injective imaginary)
    hstates a b C V hC hbits hfit f depth v S
    (by simpa only [placement_generator] using ha) (by simpa only [placement_generator] using hb)
    (by simpa only [placement_generator] using hseed) (by simpa only [placement_generator] using hz)
    (by simpa only [placement_generator] using hwidth)
    (by intro r; simpa only [placement_generator] using hblank r)
    (by simpa only [placement_generator] using hcount) (by intro i; exact hL _)
    (by
      intro i hip hiq
      simp only [callerWorker]
      rw [placement_off imaginary _ (TransposeRegisterPlacement.worker_injective.ne hip)]
      exact hfresh i hip hiq)
    (by simpa only [hp] using hsrc)
  simpa only [planeProgram,hp] using hr

def planesProgram (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P tapeCount Q (prime+K) U :=
  .seq (planeProgram false hstates) (planeProgram true hstates)

theorem planes_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b C V : ℕ)
    (hC : 0 < C) (hbits : a+b < V) (hfit : C*2^(a+b) < 2^V)
    (realBits imagBits : Fin (2^a) → Fin (2^b) → Fin C → Bool) (depth : ℕ)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V C)
    (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hcount : S.R (base (callerGenerator 116)) = []) (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hreal : S.R (planeReg false) = (replicaKeyWords realBits).map bitSymbol)
    (himag : S.R (planeReg true) = (replicaKeyWords imagBits).map bitSymbol) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 2*restoringTimeCost hstates a b C V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+restoringStockAllowance hstates a b C V)
        depth (planesProgram hstates) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R (planeReg false)
          ((keyReplicaWords realBits).map bitSymbol)) (planeReg true) ((keyReplicaWords imagBits).map bitSymbol))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,ht₁⟩ := plane_exec_within body false hstates a b C V hC hbits hfit realBits depth
    v S ha hb hseed hz hwidth hblank hcount hL hfresh hreal
  let M : Stacks tapeCount (prime+K) := {S with R := (Function.update S.R (planeReg false)
    ((keyReplicaWords realBits).map bitSymbol))}
  have hmeta (j : Fin 117) : M.R (base (callerGenerator j)) = S.R (base (callerGenerator j)) := by
    have hne : base (callerGenerator j) ≠ planeReg false := base_injective.ne (payload_off_generator j)
    exact Function.update_of_ne hne _ _
  obtain ⟨v₂,n₂,hu₂,hn₂,ht₂⟩ := plane_exec_within body true hstates a b C V hC hbits hfit imagBits depth
    v₁ M (by rw [hmeta]; exact ha) (by rw [hmeta]; exact hb) (by rw [hmeta]; exact hseed)
    (by rw [hmeta]; exact hz) (by rw [hmeta]; exact hwidth)
    (by intro r; rw [hmeta]; exact hblank r) (by rw [hmeta]; exact hcount) hL
    (by
      intro i hip hiq
      have hne : base (callerWorker i) ≠ planeReg false :=
        base_injective.ne (TransposeRegisterPlacement.worker_injective.ne hip)
      rw [show M.R (base (callerWorker i)) = S.R (base (callerWorker i)) from Function.update_of_ne hne _ _]
      exact hfresh i hip hiq)
    (by simpa only [M,Function.update_of_ne planeReg_ne.symm] using himag)
  have hsize : mnSize (mk v₁ M) = mnSize (mk v S) := by
    have hh : mnSize (mk v₁ M)+(S.R (planeReg false)).length =
        mnSize (mk v S)+((keyReplicaWords realBits).map (bitSymbol (a := prime+K))).length := by
      simpa only [M,Host.mk,update_rt,get_rt] using
        mn_size_update (mk v S) v₁ (.rt (planeReg false)) ((keyReplicaWords realBits).map bitSymbol)
    have hlen : ((keyReplicaWords realBits).map (bitSymbol (a := prime+K))).length =
        (S.R (planeReg false)).length := by
      rw [hreal]
      simp [keyReplicaWords,replicaKeyWords,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
    omega
  rw [hsize] at ht₂
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,ExecWithin.seq ht₁ ht₂⟩

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
