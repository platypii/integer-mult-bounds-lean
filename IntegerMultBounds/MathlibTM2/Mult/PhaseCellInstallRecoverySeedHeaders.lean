module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallSparseUnaryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteComplexRecoveryHeaders

/-! Only computed masters and ordinary p/W/N dimensions are borrowed. The five
remaining header values are generated after this sparse seed installation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def recoverySeedHeaderPorts : List (Fin 392) :=
  complexRecoveryHeaderPorts.filter (fun k => decide (k ∉ derivedRecoveryHeaderPorts))

noncomputable def recoverySeedHeader (H : ReplicaHaloProblem s) (W N : ℕ) (k : Fin 392) : ℕ :=
  if k ∈ derivedRecoveryHeaderPorts then 0 else complexRecoveryHeader H W N k

theorem recoverySeedHeader_off (H : ReplicaHaloProblem s) (W N : ℕ) (k : Fin 392)
    (hk : k ∉ recoverySeedHeaderPorts) : recoverySeedHeader H W N k = 0 := by
  by_cases hd : k ∈ derivedRecoveryHeaderPorts
  · simp only [recoverySeedHeader,hd,ite_true]
  · have hoff : k ∉ complexRecoveryHeaderPorts := by
      intro hm
      exact hk (List.mem_filter.mpr ⟨hm,by simpa only [decide_eq_true_eq] using hd⟩)
    simp only [recoverySeedHeader,hd,ite_false,complexRecoveryHeader_off H W N k hoff]

theorem complexRecoverySeedInput_right (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (inp : List (Bool ⊕ Bool)) (out : List Bool) (k : Fin 392) :
    (complexRecoverySeedInput (A := A) H W Fs inp out).R k =
      if k = 124 then cstream A W (Fs.map (packedInterval H.origin H.span)).flatten
      else List.replicate (recoverySeedHeader H W Fs.length k) tick := by
  by_cases hp : k = 124
  · subst k
    simp [complexRecoverySeedInput,derivedRecoveryHeaderPorts,complexRecoveryInput_right]
  · by_cases hd : k ∈ derivedRecoveryHeaderPorts
    all_goals simp only [complexRecoverySeedInput,complexRecoveryInput_right,recoverySeedHeader,
      hp,hd,ite_true,ite_false,List.replicate_zero]

def recoverySeedHeaderCopies (source work : Fin 392 → Fin T) : List (Fin T × Fin T) :=
  recoverySeedHeaderPorts.map (fun k => (source k,work k))

def installRecoverySeedHeaders (source work : Fin 392 → Fin T) (tmp : Fin T) : Pr P T Q A U :=
  copyUnaryHeaders tmp (recoverySeedHeaderCopies source work)

theorem installRecoverySeedHeaders_exec (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (source work : Fin 392 → Fin T)
    (hwork : Function.Injective work) (tmp : Fin T)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (hworkTmp : ∀ i, work i ≠ tmp) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (source i)).length = recoverySeedHeader H W Fs.length i)
    (hblank : ∀ i, i ≠ 124 → S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hpayload : S.R (work 124) = cstream A W (Fs.map (packedInterval H.origin H.span)).flatten)
    (htmp : S.R tmp = []) :
    let rs := recoverySeedHeaderCopies source work
    let cost := copyUnaryHeadersCost (fun k => (S.R k).length) rs
    let F : Stacks T A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R rs}
    ∃ v', v'.user = v.user ∧ embStk work F = complexRecoverySeedInput H W Fs S.inp S.out ∧
      (∀ k, (∀ i, k ≠ work i) → F.R k = S.R k) ∧
      Exec body (installRecoverySeedHeaders source work tmp) (Host.mk v S) cost (Host.mk v' F) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*cost) depth
        (installRecoverySeedHeaders source work tmp) (Host.mk v S) cost (Host.mk v' F) := by
  obtain ⟨v',hu,hready,hframe,he,ht⟩ := installSparseUnaryHeaders_exec (body := body)
    recoverySeedHeaderPorts (by decide) 124 (by decide) (recoverySeedHeader H W Fs.length)
    (recoverySeedHeader_off H W Fs.length) source work hwork tmp hsourceOff hsourceTmp hworkTmp v S
    hvalues hblank _ hpayload htmp
  refine ⟨v',hu,?_,hframe,he,ht⟩
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i; exact hleft i
  · funext i
    exact (hready i).trans (complexRecoverySeedInput_right H W Fs S.inp S.out i).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
