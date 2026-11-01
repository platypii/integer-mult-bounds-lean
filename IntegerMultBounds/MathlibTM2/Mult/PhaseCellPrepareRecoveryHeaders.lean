module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallRecoverySeedHeaders
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.StackInvariantShift

/-! Install only seed metadata, then execute all derived-header arithmetic.
The returned bank is ready for physical complex recovery with no derived values supplied. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def prepareRecoveryHeaders (source work : Fin 392 → Fin T) (tmp : Fin T) : Pr P T Q A U :=
  .seq (installRecoverySeedHeaders source work tmp) (embProg work Empty.elim completeComplexRecoveryHeaders)

theorem prepareRecoveryHeaders_exec (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (hN : H.Fs.length = 2*Fs.length)
    (source work : Fin 392 → Fin T) (hwork : Function.Injective work) (tmp : Fin T)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (hworkTmp : ∀ i, work i ≠ tmp) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (source i)).length = recoverySeedHeader H W Fs.length i)
    (hblank : ∀ i, i ≠ 124 → S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hpayload : S.R (work 124) = cstream A W (Fs.map (packedInterval H.origin H.span)).flatten)
    (htmp : S.R tmp = []) :
    let cost := copyUnaryHeadersCost (fun k => (S.R k).length) (recoverySeedHeaderCopies source work)
    ∃ v' G steps, v'.user = v.user ∧ steps ≤ cost+completeComplexRecoveryHeadersCost H Fs.length ∧
      embStk work G = complexRecoveryInput H W Fs S.inp S.out ∧
      G.inp = S.inp ∧ G.out = S.out ∧ G.L = S.L ∧
      (∀ k, (∀ i, k ≠ work i) → G.R k = S.R k) ∧
      Exec body (prepareRecoveryHeaders source work tmp) (Host.mk v S) steps (Host.mk v' G) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          (2*cost+18*completeComplexRecoveryHeadersCost H Fs.length)) depth
        (prepareRecoveryHeaders source work tmp) (Host.mk v S) steps (Host.mk v' G) := by
  dsimp only
  let rs := recoverySeedHeaderCopies source work
  let cost := copyUnaryHeadersCost (fun k => (S.R k).length) rs
  let F : Stacks T A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R rs}
  obtain ⟨v₁,hu₁,hseed,hframe,he₁,htrace₁⟩ := installRecoverySeedHeaders_exec (body := body)
    H W Fs source work hwork tmp hsourceOff hsourceTmp hworkTmp v S hvalues hblank hleft hpayload htmp
  obtain ⟨vf,n₂,hu₂,hn₂,he₂⟩ := completeComplexRecoveryHeaders_exec H W Fs hN S.inp S.out (embDn work v₁)
  have ht₂ := completeComplexRecoveryHeaders_within_stock he₂ hn₂ 0
  obtain ⟨v₂,G,_,hu₂',ht₂',hbank,hoff⟩ := exec_emb_within_stock (e := work) (body' := body) (ι := Empty.elim)
    hwork (fun f => nomatch f) ht₂ v₁ rfl F hseed
  have hI : G.inp = S.inp := congrArg (fun B : Stacks 392 A => B.inp) hbank
  have hO : G.out = S.out := congrArg (fun B : Stacks 392 A => B.out) hbank
  have hL : G.L = S.L := by
    funext k
    by_cases hm : ∃ i, work i = k
    · obtain ⟨i,rfl⟩ := hm
      have hh := congrArg (fun B : Stacks 392 A => B.L i) hbank
      exact hh.trans (hleft i).symm
    · exact (hoff k (by intro i heq; exact hm ⟨i,heq⟩)).1
  have hR (k : Fin T) (hk : ∀ i, k ≠ work i) : G.R k = S.R k :=
    ((hoff k (fun i => (hk i).symm)).2).trans (hframe k hk)
  have hwhole := mn_seq_within_add (htrace₁ 0) ht₂'
  refine ⟨v₂,G,cost+n₂,hu₂'.trans (hu₂.trans hu₁),?_,hbank,hI,hO,hL,hR,hwhole.toExec,?_⟩
  · exact Nat.add_le_add_left hn₂ _
  · intro depth
    have ht := hwhole.shift depth (J := fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
      (2*cost+18*completeComplexRecoveryHeadersCost H Fs.length)) (by
        intro d z hz
        dsimp -failIfUnchanged only [cost,rs] at hz ⊢
        omega)
    simpa only [Nat.zero_add,cost,rs,prepareRecoveryHeaders] using ht

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
