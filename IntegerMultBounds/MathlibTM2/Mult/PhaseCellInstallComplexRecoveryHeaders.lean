module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexRecoveryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallSparseUnaryHeaders

/-! Retained ordinary metadata and an exposed payload install the exact complex
recovery input bank. Sources are borrowed and scratch is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def complexRecoveryHeaderCopies (source work : Fin 392 → Fin T) : List (Fin T × Fin T) :=
  complexRecoveryHeaderPorts.map (fun k => (source k,work k))

def installComplexRecoveryHeaders (source work : Fin 392 → Fin T) (tmp : Fin T) : Pr P T Q A U :=
  copyUnaryHeaders tmp (complexRecoveryHeaderCopies source work)

theorem installComplexRecoveryHeaders_exec (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (source work : Fin 392 → Fin T)
    (hwork : Function.Injective work) (tmp : Fin T)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (hworkTmp : ∀ i, work i ≠ tmp) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i ∈ complexRecoveryHeaderPorts,
      (S.R (source i)).length = complexRecoveryHeader H W Fs.length i)
    (hblank : ∀ i, i ≠ 124 → S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hpayload : S.R (work 124) = cstream A W (Fs.map (packedInterval H.origin H.span)).flatten)
    (htmp : S.R tmp = []) :
    let rs := complexRecoveryHeaderCopies source work
    let cost := copyUnaryHeadersCost (fun k => (S.R k).length) rs
    let F : Stacks T A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R rs}
    ∃ v', v'.user = v.user ∧ embStk work F = complexRecoveryInput H W Fs S.inp S.out ∧
      (∀ k, (∀ i, k ≠ work i) → F.R k = S.R k) ∧
      Exec body (installComplexRecoveryHeaders source work tmp) (Host.mk v S) cost (Host.mk v' F) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*cost) depth
        (installComplexRecoveryHeaders source work tmp) (Host.mk v S) cost (Host.mk v' F) := by
  obtain ⟨v',hu,hready,hframe,he,ht⟩ := installSparseUnaryHeaders_exec (body := body)
    complexRecoveryHeaderPorts (by decide) 124 (by decide) (complexRecoveryHeader H W Fs.length)
    (complexRecoveryHeader_off H W Fs.length) source work hwork tmp hsourceOff hsourceTmp hworkTmp v S
    hvalues hblank _ hpayload htmp
  refine ⟨v',hu,?_,hframe,he,ht⟩
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i; exact hleft i
  · funext i
    exact (hready i).trans (complexRecoveryInput_right H W Fs S.inp S.out i).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
