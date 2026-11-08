module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringRolePacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedDiagonalProduct

/-! Consume one published packet using a retained D' coefficient page. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {s t α p w c n T Q A : ℕ} [NeZero s] [NeZero t]
  {P U : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

noncomputable def diagonalPacketWorker (count queue saved tmp : Fin T) (x y o : RsbR)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  retiringPacketWorker count queue (rg x) saved tmp
    (cmulStream (rsbCr rg x y o) (rmulOne ι hι hT hQ (rsbCr rg x y o)))

theorem diagonalPacketWorker_exec
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (count queue saved tmp : Fin T) (x y o : RsbR) (hfree : RsbFree x y o)
    (hreg : [count,queue,rg x,rg o,saved,tmp].Nodup)
    (hoff : ∀ r, rg r ≠ queue) (hqueueWork : ∀ j, queue ≠ ι j)
    (ρ : RsbR → List (Fin (A+4))) (hr : RsbReady ρ w p) (hw : p+2 ≤ w)
    (hp : 13 ≤ p) (hα : 1 ≤ α) (hαp : α^2 ≤ p)
    (D : ZMod s → GaussianInt) (hfit : c+n ≤ s)
    (hD : ∀ z ∈ packedInterval c n D, Fits w z)
    (hy : ρ y = cstream A w (packedInterval c n (diagonalField s t α p)))
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg x y o)) ≤ C)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (hqueue : S.R queue = cstream A w (packedInterval c n D)++tail)
    (hcount : (S.R count).length = n*w) (hinput : S.R (rg x) = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (hclean : RsbClean ι S) (hS : RsbHolds rg S ρ) :
    let packet := cstream A w (packedInterval c n (diagonalProduct s t α p D))
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ (6*(n*w)+6)+(n*(rmulCost w+6*w+2)+8)+(2*(n*w)+2) ∧
      Exec body (diagonalPacketWorker (rg := rg) count queue saved tmp x y o hι hT hQ) (Host.mk v S) steps
        (Host.mk v' {S with R := Function.update (Function.update S.R queue tail) (rg o) (packet++S.R (rg o))}) ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        (2*(6*(n*w)+6)+realWeightWorkspace C w n)) depth
        (diagonalPacketWorker (rg := rg) count queue saved tmp x y o hι hT hQ) (Host.mk v S) steps
        (Host.mk v' {S with R := Function.update (Function.update S.R queue tail) (rg o) (packet++S.R (rg o))})) ∧
      mnSize (Host.mk v' {S with R := Function.update (Function.update S.R queue tail) (rg o) (packet++S.R (rg o))}) =
        mnSize (Host.mk v S) := by
  dsimp only
  let payload := cstream A w (packedInterval c n D)
  let packet := cstream A w (packedInterval c n (diagonalProduct s t α p D))
  have hlen : payload.length = n*w := by simp only [payload,length_cstream,packedInterval_length D hfit]
  have hpacket : packet.length = payload.length := by simp only [packet,payload,length_cstream,packedInterval_length _ hfit]
  have hrun := rsb_diagonalInterval_runs_within (body := body) hrg hdisj hι hT hQ hA hfree
    (Function.update ρ x payload) (hr.update x (fun c => (hfree.2.2.2 c).1) payload) hw hp hα hαp D hfit hD
    (by simp [payload]) (by simpa only [Function.update_of_ne hfree.1.symm] using hy) C hpush
  have he := retiringRolePacket_exec hrg hdisj count queue saved tmp x o hreg hoff hqueueWork
    _ payload packet tail hpacket (n*(rmulCost w+6*w+2)+8) (realWeightWorkspace C w n)
    ρ v S hqueue (by simpa only [hlen] using hcount) hinput hsaved htmp hclean hS hrun
  simpa only [diagonalPacketWorker,hlen] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
